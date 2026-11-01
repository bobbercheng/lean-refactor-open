#!/usr/bin/env bash
# A100 side of the Lean-refactor skill eval (2026-10-07: identify the difference between A100 and z.ai in output quality).
#   Usage: infra/vast/lreval_chain.sh <instance_id>      (run as a systemd user service; the TLS bridge must answer on :8000)
# Generates samples for three effort settings (low / high / none=template Max) with the SAME frozen items as the z.ai side,
# verifies that >= 90% of the expected samples came back without error, and only then releases the instance (evidence-based
# release, runbook §8). Scoring happens afterwards on the GB10 (Lean only, no GPU needed).
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3 curl
main() {
  cd "${REPO_ROOT:-$(dirname "$0")/../..}" || exit 2
  [ -f probe/lr_eval.py ] || { echo "not in the repo root" >&2; exit 2; }
  export PATH="$HOME/.elan/bin:$PATH"
  local ID=${1:?instance id} KEY; KEY=$(cat ~/.config/vexorium/vllm_api_key)
  # samples per item per effort (2026-10-07 22:30: low keeps 3 = the variance reference; high and default run 1 to cut cost,
  # unless the z.ai side shows 3 samples change the result). Override with SAMPLES_LOW / SAMPLES_HIGH / SAMPLES_NONE.
  local N; N=$(wc -l < probe/lr_eval/items.jsonl)
  declare -A S=([low]=${SAMPLES_LOW:-3} [high]=${SAMPLES_HIGH:-1} [none]=${SAMPLES_NONE:-1})
  rm -f probe/lr_eval/A100_EVAL_DONE probe/lr_eval/A100_EVAL_KEPT
  local V; until V=$(infra/vast/server_up.sh "$ID" --bridge 2>&1); do log "waiting: $V"; sleep 30; done; log "$V"
  for E in low high none; do
    log "generate a100-$E ($((N * S[$E])) samples = ${S[$E]}/item, 16 streams = server max-num-seqs)"
    python3 probe/lr_eval.py run --endpoint a100 --effort "$E" --samples "${S[$E]}" --workers 16 --tag "a100-$E" >> probe/lr_eval/a100-gen.log 2>&1
  done
  local ok=1 E got
  for E in low high none; do
    local WANT=$((N * S[$E]))
    got=$(python3 -c "import json; print(sum(1 for l in open('probe/lr_eval/runs/a100-$E.jsonl') if not json.loads(l).get('error') and json.loads(l)['sample'] < ${S[$E]}))" 2>/dev/null || echo 0)
    log "a100-$E: $got/$WANT samples without error"
    [ "$got" -ge $((WANT * 9 / 10)) ] || ok=0
  done
  if [ "$ok" != 1 ]; then log "fewer than 90% samples on some config; KEEPING instance $ID for a manual decision"; touch probe/lr_eval/A100_EVAL_KEPT; exit 1; fi
  touch probe/lr_eval/A100_EVAL_DONE   # explicit end marker (follow-up jobs must not infer it from old log lines)
  printf -- "- %s UTC LR skill eval A100 side generated (low %s/item, high %s/item, default %s/item); releasing instance %s\n" "$(date -u +%Y-%m-%dT%H:%M)" "${S[low]}" "${S[high]}" "${S[none]}" "$ID" >> accounting/a100_poc.md
  CONFIRM=yes infra/vast/destroy.sh "$ID"
  for p in $(ps -eo pid,args | awk '$2=="bash" && $3=="infra/vast/tls_bridge.sh" {print $1}'); do kill "$p"; done
  for p in $(ps -eo pid,args | awk '$2=="socat" && /TCP-LISTEN:8000/ {print $1}'); do kill "$p"; done
  log "A100 side done; score with: python3 probe/lr_eval.py score --tag a100-<effort>"
}
log() { echo "[$(date -u -Is)] $*"; }
main "$@"
