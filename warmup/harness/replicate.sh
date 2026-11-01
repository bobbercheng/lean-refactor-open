#!/usr/bin/env bash
# Replication run (2026-10-06): FRESH per-problem state, N resumed passes, the same harness, on a chosen
# serving endpoint. Rung 1 = z.ai (control), rung 2 = OpenRouter pinned to a quantization (nvfp4), rung 3 = self-served A100.
# Usage: harness/replicate.sh <tag> <zai|openrouter> [passes=5] [workers=3] [quant=nvfp4]
# State: harness/work_<tag>/ ; logs: probe/<tag>-pN.log ; per-pass scores: accounting/replication_<tag>.md
set -u
cd "${REPO_ROOT:-$(dirname "$0")/..}"   # REPO_ROOT lets a COPY of this script (chain scripts run copies to survive edits) still run in the repo
[ -f harness/agent.py ] || { echo "replicate.sh: not in the repo root ($PWD); set REPO_ROOT" >&2; exit 2; }
TAG=$1; EP=$2; PASSES=${3:-5}; WORKERS=${4:-3}; QUANT=${5:-nvfp4}
AGENT_EXTRA=${AGENT_EXTRA:-}   # e.g. for EP=openai: --base-url http://host:8000/v1 --api-model glm-5.3-flash --serving-tag vllm-a100-awq-w4a16
export PATH="$HOME/.elan/bin:$PATH"
ROOT="harness/work_$TAG"; OUT="accounting/replication_$TAG.md"
echo "# Replication $TAG — endpoint=$EP quant=$QUANT workers=$WORKERS passes=$PASSES (started $(date -u -Is))" >> "$OUT"
START=${START:-1}   # resume a replication at pass START (pass 1 is the only fresh one)
for i in $(seq "$START" "$PASSES"); do
  RUN="$TAG-p$i"; FRESH=""; [ "$i" = 1 ] && FRESH="--fresh"
  echo "[$(date -u -Is)] pass $i/$PASSES run=$RUN"
  python3 harness/agent.py --turns 40 --workers "$WORKERS" --max-tokens 4000 --model glm-5.3-flash --reasoning-effort low \
      --endpoint "$EP" --quant "$QUANT" --work-root "$ROOT" $FRESH --run-id "$RUN" $AGENT_EXTRA > "probe/$RUN.log" 2>&1
  python3 bank/import_verified.py > /dev/null
  SC=$(python3 assemble/best.py --include-dev-only --only-run-prefix "$TAG-" | head -1)
  echo "[$(date -u -Is)] after pass $i: $SC"
  printf -- "- %s pass %s (%s): %s\n" "$(date -u +%Y-%m-%dT%H:%M)" "$i" "$RUN" "${SC#assembled score: }" >> "$OUT"
done
echo "[$(date -u -Is)] replication $TAG done"
