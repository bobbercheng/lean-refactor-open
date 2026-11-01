#!/usr/bin/env bash
# A100 pass 3 chain (2026-10-07 ~16:00 UTC: rent the Japan host again at min bid + $0.01, quick probe first, then pass 3;
# earlier instruction still stands: shut the instance down once pass 3 is complete).
#   Usage: infra/vast/pass3.sh <instance_id>        (run from the repo; the bridge must already answer on localhost:8000)
# Steps, each gated:
#   0 preconditions: server answers through the bridge; local state holds passes 1+2 and no pass 3; harness compiles
#   1 quick probe:   effort probe with the SAME top-level `reasoning_effort` field the harness sends (3 contexts × none/low/high/max
#                    × 6 samples, 72 calls) + a 3-turn functional smoke on one problem through the openai endpoint
#   2 pass 3:        z.ai-identical flags (effort low + structural high bump, cap 4000-base), resumed from passes 1+2, 4 workers,
#                    run from a COPY of replicate.sh with REPO_ROOT exported (immune to edits, runs in the repo)
#   3 validation:    >= 10 of 15 problems DONE with >= 3 turns, else the instance is KEPT for a manual decision
#   4 accounting, then release (destroy) only after validation, then stop the bridge
# Body in a function (bash parses it fully before running); every external step logs before and after.
set -u
main() {
  cd "${REPO_ROOT:-$(dirname "$0")/../..}" || exit 2
  [ -f harness/agent.py ] || { echo "not in the repo root" >&2; exit 2; }
  export PATH="$HOME/.elan/bin:$PATH"
  ID=${1:?vast instance id}
  KEY=$(cat ~/.config/vexorium/vllm_api_key)
  LEDGER=accounting/a100_poc.md
  log "step 0: preconditions"
  curl -sf --max-time 30 -H "Authorization: Bearer $KEY" http://localhost:8000/v1/models >/dev/null || { log "server not reachable through the bridge; aborting (instance kept)"; exit 1; }
  python3 - <<'PY' || { log "local state check failed; aborting (instance kept)"; exit 1; }
import json, glob, sys
runs = set()
for f in glob.glob('harness/work_fresh-a100/*/state.json'):
    runs |= {r.get('run_id') for r in json.load(open(f)).get('runs', [])}
assert runs == {'fresh-a100-p1', 'fresh-a100-p2'}, runs
print("state ok:", sorted(runs))
PY
  python3 -c "import ast; ast.parse(open('harness/agent.py').read()); ast.parse(open('probe/effort_probe.py').read())" || { log "harness syntax error; aborting"; exit 1; }
  note "pass-3 chain started on instance $ID; preconditions OK (bridge answers, state = passes 1+2, harness compiles)"

  log "step 1a: effort probe (same top-level field as the harness), 72 calls, 4 workers"
  python3 probe/effort_probe.py --endpoint a100 --tag a100-effort-pass3 --mode thinkpoints --points 3 --samples 6 --workers 4 \
      --efforts none,low,high,max --max-tokens 12000 > probe/effort-probe-a100-pass3.log 2>&1
  SUMMARY=$(grep -A6 "SUMMARY" probe/effort-probe-a100-pass3.log | tr '\n' ' ' | tr -s ' ')
  log "probe summary: $SUMMARY"
  note "effort probe (top-level field, n=6 per label): $SUMMARY"
  log "step 1b: 3-turn functional smoke on one problem (scratch work root)"
  SMOKE=$(mktemp -d)
  timeout 900 python3 harness/agent.py --problems Core.InitsUpdatesComm --turns 3 --no-adaptive-turns --workers 1 --max-tokens 4000 --model glm-5.3-flash --reasoning-effort low \
      --endpoint openai --base-url http://localhost:8000/v1 --api-key-file "$HOME/.config/vexorium/vllm_api_key" --api-model glm-5.3-flash --serving-tag vllm-a100-awq-w4a16 \
      --work-root "$SMOKE" --fresh --run-id a100-pass3-smoke > probe/a100-pass3-smoke.log 2>&1
  if grep -qE "turn [0-9]+: api error|Traceback" probe/a100-pass3-smoke.log; then log "smoke FAILED (see probe/a100-pass3-smoke.log); aborting (instance kept)"; note "smoke test FAILED; instance kept"; exit 1; fi
  log "smoke ok: $(grep -c ' DONE ' probe/a100-pass3-smoke.log) problem done"

  log "step 2: pass 3 (resumed from passes 1+2; z.ai-identical flags; 4 workers)"
  SCRATCH=$(mktemp -d); cp harness/replicate.sh "$SCRATCH/replicate.sh"; export REPO_ROOT="$PWD"
  AGENT_EXTRA="--base-url http://localhost:8000/v1 --api-key-file $HOME/.config/vexorium/vllm_api_key --api-model glm-5.3-flash --serving-tag vllm-a100-awq-w4a16 --max-api-retries 20" \
    START=3 bash "$SCRATCH/replicate.sh" fresh-a100 openai 3 4
  log "step 3: validation"
  GOOD=$(grep -cE " DONE .* turns=([3-9]|[1-9][0-9])" probe/fresh-a100-p3.log 2>/dev/null)
  if [ "${GOOD:-0}" -lt 10 ]; then
    log "pass 3 did NOT run to completion ($GOOD/15 problems with >= 3 turns); KEEPING instance $ID for a manual decision"
    note "pass 3 validation FAILED ($GOOD/15); instance $ID kept"; exit 1
  fi
  log "step 4: accounting"
  python3 bank/import_verified.py > /dev/null
  SC=$(python3 assemble/best.py --include-dev-only --only-run-prefix fresh-a100- | head -n 1)
  SC3=$(python3 assemble/best.py --include-dev-only --only-run-prefix fresh-a100-p3 | head -n 1)
  log "after pass 3: $SC | pass 3 alone: $SC3"
  note "pass 3 complete ($GOOD/15 worked): ${SC#assembled score: } over passes 1-3; pass 3 alone ${SC3#assembled score: }"
  touch probe/A100_PASS3_DONE
  log "releasing instance $ID (shut down once pass 3 is complete)"
  CONFIRM=yes infra/vast/destroy.sh "$ID"
  for p in $(ps -eo pid,args | awk '$2=="bash" && $3=="infra/vast/tls_bridge.sh" {print $1}'); do kill "$p"; done
  for p in $(ps -eo pid,args | awk '$2=="socat" && /TCP-LISTEN:8000/ {print $1}'); do kill "$p"; done
  log "chain done"
}
log() { echo "[$(date -u -Is)] $*"; }
note() { printf -- "- %s %s\n" "$(date -u +%Y-%m-%dT%H:%M) UTC" "$*" >> "$LEDGER"; }
main "$@"
