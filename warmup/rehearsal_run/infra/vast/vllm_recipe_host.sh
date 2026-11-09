#!/usr/bin/env bash
# ON the A100 host: put vLLM on a named recipe for the next run (docs/open_official_run_runbook.md section 6).
#   bash /workspace/vllm_recipe_host.sh std|std32 [check]
#     std    /workspace/run_vllm_std.sh   (= infra/vast/run_vllm.sh of 2026-10-31: custom all-reduce on, --max-num-seqs 16, graphs 1..16)
#     std32  /workspace/run_vllm_std32.sh (std + --max-num-seqs 32 + graphs 1,2,4,8,12,16,24,32; made by the scaling test, or here the same way)
# The recipe is installed as /workspace/run_vllm.sh (the old one kept as run_vllm.sh.before-<recipe>-<ts>), so onstart.sh brings the SAME
# server back after an outbid resume. The live server is restarted only when its --max-num-seqs differs from the recipe's, and only when no
# package driver runs (FORCE=1 overrides): main pid stopped by pid (vLLM may live in pgid 1: never a group or pattern kill), its VLLM::
# workers by pid, GPU memory checked free, READY removed, the recipe started detached, READY waited for (bounded 20 min); a recipe that does
# not come up is reverted to std once. `check` only prints the live and the installed recipe. Last line: "VLLM OK <recipe> ..." or "VLLM FAILED ...".
set -u
R=${1:?std or std32}; MODE=${2:-apply}; Wd=${W:-/workspace}
case "$R" in std) F=$Wd/run_vllm_std.sh;; std32) F=$Wd/run_vllm_std32.sh;; *) echo "recipe: std or std32"; exit 2;; esac
log() { echo "[$(date -u -Is)] vllm-recipe: $*"; }
if [ "$R" = std32 ] && [ ! -f "$F" ]; then
  sed -e 's/--max-num-seqs 16/--max-num-seqs 32/' \
      -e 's/"cudagraph_capture_sizes":\[1,2,4,8,16\],"max_cudagraph_capture_size":16/"cudagraph_capture_sizes":[1,2,4,8,12,16,24,32],"max_cudagraph_capture_size":32/' \
      "$Wd/run_vllm_std.sh" > "$F"
  grep -q "max-num-seqs 32" "$F" && grep -q '"max_cudagraph_capture_size":32' "$F" || { log "VLLM FAILED: could not derive $F from run_vllm_std.sh"; exit 1; }
fi
[ -f "$F" ] || { log "VLLM FAILED: no $F"; exit 1; }
want=$(grep -oE -- "--max-num-seqs [0-9]+" "$F" | awk '{print $2}')
M=$(pgrep -f "^/usr/bin/python3 /usr/local/bin/[v]llm serve" | head -n 1)
live=$([ -n "$M" ] && tr '\0' ' ' < "/proc/$M/cmdline" | grep -oE -- "--max-num-seqs [0-9]+" | awk '{print $2}')
inst=$(grep -oE -- "--max-num-seqs [0-9]+" "$Wd/run_vllm.sh" 2>/dev/null | awk '{print $2}')
log "recipe $R (max-num-seqs $want); live server pid ${M:-none} max-num-seqs ${live:-?}; installed run_vllm.sh max-num-seqs ${inst:-?}"
[ "$MODE" = check ] && exit 0
if ! cmp -s "$F" "$Wd/run_vllm.sh"; then
  cp "$Wd/run_vllm.sh" "$Wd/run_vllm.sh.before-$R-$(date +%s)" 2>/dev/null; cp "$F" "$Wd/run_vllm.sh"; chmod +x "$Wd/run_vllm.sh"; log "installed $F as run_vllm.sh (onstart.sh uses it)"
fi
if [ -n "$M" ] && [ "$live" = "$want" ] && [ -e "$Wd/READY" ]; then log "VLLM OK $R: the live server already runs it (pid $M)"; exit 0; fi
if pgrep -f "[o]pen_package.py run" > /dev/null && [ "${FORCE:-0}" != 1 ]; then log "VLLM FAILED: a package driver is alive; stop it first (or FORCE=1)"; exit 1; fi
start() {   # $1 = recipe file
  rm -f "$Wd/READY"; setsid nohup bash "$1" > "$Wd/run_vllm_$(basename "$1" .sh).out" 2>&1 < /dev/null &
  for i in $(seq 1 80); do [ -e "$Wd/READY" ] && return 0; sleep 15; done; return 1
}
if [ -n "$M" ]; then
  PIDS="$M $(pgrep -f '^VLLM::' | tr '\n' ' ')"
  log "stopping vLLM pid $M (+ workers $(echo $PIDS | wc -w))"; kill -TERM "$M"
  for i in $(seq 1 60); do a=0; for p in $PIDS; do kill -0 "$p" 2>/dev/null && a=1; done; [ $a = 0 ] && break; sleep 1; done
  for p in $PIDS; do kill -0 "$p" 2>/dev/null && kill -KILL "$p"; done
  for i in $(seq 1 60); do u=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits | sort -n | tail -n 1); [ "${u:-99999}" -lt 2000 ] && break; sleep 2; done
  cp "$Wd/vllm.log" "$Wd/vllm.log.before-$R-$(date -u +%H%M)" 2>/dev/null
fi
if start "$F"; then log "VLLM OK $R: READY ($(grep -a 'all-reduce backends' "$Wd/vllm.log" | tail -n 1 | grep -o 'Using \[[^]]*\]'))"; exit 0; fi
log "$R NOT READY after 20 min: reverting to std"
[ "$R" != std ] && { M=$(pgrep -f "^/usr/bin/python3 /usr/local/bin/[v]llm serve" | head -n 1); [ -n "$M" ] && kill -TERM "$M"; sleep 30
  cp "$Wd/run_vllm_std.sh" "$Wd/run_vllm.sh"; start "$Wd/run_vllm_std.sh" && { log "VLLM FAILED $R; std READY instead (run_vllm.sh = std)"; exit 1; }; }
log "VLLM FAILED: no server READY"; exit 1
