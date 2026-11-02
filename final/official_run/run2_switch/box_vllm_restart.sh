#!/usr/bin/env bash
# ON the box: restart vLLM with the same recipe script (/workspace/run_vllm.sh): stop its process group (never a bare pkill), check the
# GPUs are free, start run_vllm.sh detached, wait for READY (bounded 30 min).
set -u; W=/workspace; log() { echo "[$(date -u +%T)] $*" | tee -a $W/run2_switch.log; }
V=$(pgrep -f "[v]llm serve" | head -1); G=$(ps -o pgid= -p ${V:-1} | tr -d ' ')
[ -n "$V" ] && [ "${G:-1}" -gt 1 ] || { log "ABORT: vLLM not found"; exit 3; }
[ -z "$(pgrep -f '[o]pen_package.py run ')" ] || { log "ABORT: a package driver is alive"; exit 2; }
log "vLLM $V group $G: SIGTERM"; kill -TERM -- -$G; for i in $(seq 1 45); do pgrep -f "[v]llm serve" >/dev/null || break; sleep 2; done
pgrep -f "[v]llm serve" >/dev/null && { log "still alive: SIGKILL group $G"; kill -KILL -- -$G; sleep 5; }
for i in $(seq 1 30); do u=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits | sort -n | tail -1); [ "${u:-99999}" -lt 2000 ] && break; sleep 2; done
log "GPU memory after stop (MiB): $(nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits | tr '\n' ' ')"
rm -f $W/READY; cd $W && setsid nohup bash $W/run_vllm.sh > $W/run_vllm.restart.out 2>&1 < /dev/null &
t0=$(date +%s); until [ -e $W/READY ] || [ $(( $(date +%s) - t0 )) -gt 1800 ]; do sleep 15; done
[ -e $W/READY ] && log "vLLM READY after $(( $(date +%s) - t0 )) s ($(grep -m1 'GPU KV cache size' $W/vllm.log | tail -1 | grep -o 'size: [0-9,]* tokens'))" || { log "vLLM NOT READY after 30 min"; exit 4; }
