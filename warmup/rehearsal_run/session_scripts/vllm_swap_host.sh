#!/usr/bin/env bash
# ON the A100 host: stop the running vLLM (by pid, never by group: it lives in pgid 1) and start it with the recipe named by $1:
#   std  = /workspace/run_vllm_std.sh (run_vllm.sh minus --disable-custom-all-reduce and minus the NCCL_ALGO/NCCL_PROTO export)
#   orig = /workspace/run_vllm.sh (unchanged)
# The sessions must already be frozen. Waits until READY (bounded 20 min).
set -u
W=/workspace; ts() { date -u +%H:%M:%S; }
case "${1:?std|orig}" in
  std) sed -e '/--disable-custom-all-reduce/d' -e 's/^export NCCL_ALGO=Ring NCCL_PROTO=Simple$/# NCCL defaults (vLLM custom all-reduce on NVLink)/' $W/run_vllm.sh > $W/run_vllm_std.sh
       grep -c "disable-custom-all-reduce\|NCCL_PROTO=Simple" $W/run_vllm_std.sh | sed 's/^/  std recipe, old flags left: /'; S=$W/run_vllm_std.sh ;;
  orig) S=$W/run_vllm.sh ;;
esac
M=$(pgrep -f "^/usr/bin/python3 /usr/local/bin/[v]llm serve" | head -1)
echo "$(ts) stopping vLLM main pid ${M:-none}"
PIDS="$M $(pgrep -f '^VLLM::' | tr '\n' ' ')"
[ -n "$M" ] && kill -TERM "$M"
for i in $(seq 1 60); do alive=0; for p in $PIDS; do kill -0 "$p" 2>/dev/null && alive=1; done; [ $alive = 0 ] && break; sleep 1; done
for p in $PIDS; do kill -0 "$p" 2>/dev/null && { kill -KILL "$p"; echo "  SIGKILL $p"; }; done
for i in $(seq 1 60); do u=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits | sort -n | tail -1); [ "${u:-99999}" -lt 2000 ] && break; sleep 2; done
echo "$(ts) GPUs free (max used ${u} MiB); starting $S"
cp $W/vllm.log $W/vllm.log.before-$1-$(date -u +%H%M) 2>/dev/null
setsid nohup bash $S > $W/run_vllm_$1.out 2>&1 < /dev/null &
for i in $(seq 1 80); do [ -e $W/READY ] && break; sleep 15; done
[ -e $W/READY ] && echo "$(ts) READY ($1)" || { echo "$(ts) NOT READY after 20 min ($1)"; tail -5 $W/vllm.log; }
grep -aiE "custom.?all.?reduce|nccl|error|Traceback" $W/vllm.log | grep -v "GET \|POST " | tail -6 | cut -c1-200
