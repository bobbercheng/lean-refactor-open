#!/usr/bin/env bash
# Harness worker-scaling test on the rented A100 (2026-10-07: test the harness at 8-12 workers on this A100 after the eval
# and before releasing the instance). The 3-worker limit is for the z.ai API; on our own 4xA100 the question is how many
# harness workers the server sustains (KV cache 1.87 M tokens; harness context p90 ~56k) and what aggregate throughput they get.
#   Usage: infra/vast/scale_test.sh <instance_id>    (systemd user service lra-scale; holds the instance via probe/a100-hold-<id>)
# Steps: wait for the LR-eval chain to end -> restart the bridge -> phases of W workers x M minutes on FRESH scratch workspaces
# (z.ai-identical flags: effort low, --max-tokens 4000, 40 turns) -> per phase: aggregate tok/s and queueing from vLLM /metrics,
# turns and seconds per turn from the harness, memgate holds on the GB10 -> summary in docs/a100_scale_test.md -> release
# (only when the eval chain itself succeeded; otherwise the instance is kept for a manual decision).
set -u
main() {
  cd "${REPO_ROOT:-$(dirname "$0")/../..}" || exit 2
  . infra/vast/common.sh; require vastai curl python3 ssh
  local ID=${1:?instance id} HOLD; HOLD=probe/a100-hold-$ID
  local K; K=$(cat ~/.config/vexorium/vllm_api_key)
  log "waiting for the LR-eval chain to finish"
  # explicit markers written by lreval_chain.sh (an old "KEEPING instance" line from the 21:00 failed start is still in the log)
  until { [ -e probe/lr_eval/A100_EVAL_DONE ] || [ -e probe/lr_eval/A100_EVAL_KEPT ]; } && ! systemctl --user is-active -q lra-lreval; do sleep 30; done
  local EVAL_OK=1; [ -e probe/lr_eval/A100_EVAL_DONE ] || EVAL_OK=0
  log "eval chain ended (ok=$EVAL_OK); restarting the bridge"
  systemctl --user stop lra-bridge 2>/dev/null
  systemd-run --user --unit=lra-bridge --collect -p WorkingDirectory="$PWD" /usr/bin/bash -c "exec infra/vast/tls_bridge.sh $ID >> probe/a100-tls-bridge.log 2>&1" >/dev/null
  local V; for k in $(seq 1 12); do sleep 10; V=$(infra/vast/server_up.sh "$ID" --bridge 2>&1) && break; done
  log "$V"; case "$V" in UP*) ;; *) log "server/bridge not up; instance KEPT"; exit 1;; esac
  local OUT=docs/a100_scale_test.md
  { echo "# A100 harness worker-scaling test ($(date -u +%F))"; echo
    echo "Instance $ID (4x A100 SXM4 80 GB, vLLM backport, TP4, MTP-3, max-num-seqs 16, KV cache 1.87 M tokens). Harness flags as A100 pass 3 (z.ai-identical:"
    echo "effort low, --max-tokens 4000, 40 turns), fresh scratch workspaces, all 15 problems. Lean compiles run on the GB10 (shared with POC 2 and the miner),"
    echo "behind the memory gate, so holds are reported; in the official run compiles run on the A100 host."; echo
    echo "| workers | minutes | turns | turns/min | out tok/s (vLLM) | mean running | mean waiting | p50 s/turn | memgate holds |"
    echo "|---|---|---|---|---|---|---|---|---|"; } > "$OUT"
  for spec in 4:10 8:20 12:20; do phase "$ID" "${spec%%:*}" "${spec##*:}" "$OUT" "$K"; done
  python3 infra/vast/scale_report.py >> "$OUT" 2>&1
  log "summary written to $OUT"
  if [ "$EVAL_OK" = 1 ]; then
    rm -f "$HOLD"
    printf -- "- %s UTC scale test done (docs/a100_scale_test.md); releasing instance %s\n" "$(date -u +%Y-%m-%dT%H:%M)" "$ID" >> accounting/a100_poc.md
    CONFIRM=yes infra/vast/destroy.sh "$ID"
    systemctl --user stop lra-bridge 2>/dev/null
    log "released"
  else
    log "eval chain did not succeed: instance $ID KEPT for a manual decision (hold file left in place)"
  fi
}
phase() {  # phase <id> <workers> <minutes> <out> <key>
  local ID=$1 W=$2 M=$3 OUT=$4 K=$5 RUN="scale-a100-w$2" WR; WR=$(mktemp -d)
  log "phase: $W workers for $M min (run $RUN)"
  ( while true; do
      curl -sS --max-time 10 -H "Authorization: Bearer $K" http://127.0.0.1:8000/metrics 2>/dev/null \
        | awk -v t="$(date +%s)" '/^vllm:num_requests_running/{r=$2} /^vllm:num_requests_waiting\{/{if(w=="")w=$2} /^vllm:generation_tokens_total/{g+=$2} END{print t, r+0, w+0, g+0}'
      sleep 30; done ) > "probe/$RUN.metrics" &
  local MP=$!
  timeout --signal=TERM $((M * 60)) python3 harness/agent.py --turns 40 --workers "$W" --max-tokens 4000 --model glm-5.3-flash --reasoning-effort low \
    --endpoint openai --base-url http://localhost:8000/v1 --api-key-file "$HOME/.config/vexorium/vllm_api_key" --api-model glm-5.3-flash \
    --serving-tag vllm-a100-awq-w4a16 --max-api-retries 20 --work-root "$WR" --fresh --run-id "$RUN" > "probe/$RUN.log" 2>&1
  kill "$MP" 2>/dev/null
  python3 infra/vast/scale_report.py --row "$RUN" "$W" "$M" >> "$OUT"
}
log() { echo "[$(date -u -Is)] $*"; }
main "$@"
