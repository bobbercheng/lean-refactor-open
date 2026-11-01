#!/usr/bin/env bash
# A100-80 run (2026-10-08; the A100 passes run in parallel with the Leanstral screen; at >= 80
# document only, no upload). docs/a100_80_plan.md.
# Waits for provision.sh's READY line, then runs passes 4..7 of the fresh-a100 line ONE AT A TIME from a COPY of replicate.sh (immune to
# edits while running; REPO_ROOT keeps it in the repo): harness HEAD tagged a100-80-run, 4 workers, effort low, budget forcing on, the line's
# own ledger (harness/discover.py backfilled it from passes 1-3).
# Stop rules (checked after every pass): assembled >= 82.00; two passes in a row gaining < 0.3; below 79.0 after pass 5 (plan).
# Release guard (lesson 18): a pass with fewer than 10 DONE lines keeps the instance for a manual decision; otherwise release after the last pass.
set -u
cd /home/user/source/lean-refactor || exit 2
export PATH="$HOME/miniconda3/bin:$HOME/.local/bin:$HOME/.elan/bin:$PATH"
L=probe/a100-80-chain.log
log() { echo "[$(date -u -Is)] $*" >> "$L"; }
num() { python3 assemble/best.py --include-dev-only --only-run-prefix fresh-a100- | head -1 | grep -oE '[0-9]+\.[0-9]+' | head -1; }
log "chain start; waiting for READY from provision.sh"
PL=${PROVISION_LOG:-probe/a100-provision-1008.log}
until grep -q "^READY " "$PL" 2>/dev/null; do
  if ! systemctl --user is-active -q lra-provision && ! grep -q "^READY " "$PL" 2>/dev/null; then
    log "STOP: provisioning ended without READY: $(tail -n 3 "$PL" | tr '\n' ' ')"; exit 1
  fi
  sleep 30
done
ID=$(cat probe/a100-instance-id); log "instance $ID ready"
SCRATCH=$(mktemp -d); cp harness/replicate.sh "$SCRATCH/replicate.sh"; export REPO_ROOT="$PWD"
export AGENT_EXTRA="--base-url http://127.0.0.1:8000/v1 --api-key-file $HOME/.config/vexorium/vllm_api_key --api-model glm-5.3-flash --serving-tag vllm-a100-awq-w4a16 --max-api-retries 20"
prev=$(num); small=0; documented=0
log "line before pass 4: $prev (harness $(git rev-parse --short HEAD), tag $(git describe --tags --exact-match 2>/dev/null || echo none))"
for i in 4 5 6 7; do
  infra/vast/server_up.sh "$ID" --bridge >> "$L" 2>&1 || log "server_up not UP before pass $i; continuing (the harness retries each call for ~1.5 h)"
  log "pass $i starts"
  START=$i bash "$SCRATCH/replicate.sh" fresh-a100 openai "$i" 4 >> "$L" 2>&1
  n=$(grep -c ' DONE ' "probe/fresh-a100-p$i.log" 2>/dev/null); n=${n:-0}
  sc=$(num); gain=$(python3 -c "print(round($sc - $prev, 2))")
  log "after pass $i: assembled $sc (gain $gain), $n/15 problems DONE"
  if [ "$n" -lt 10 ]; then log "STOP: pass $i did not run to completion ($n DONE); instance $ID KEPT for a manual decision"; exit 1; fi
  if [ "$documented" = 0 ] && python3 -c "import sys; sys.exit(0 if $sc >= 80 else 1)"; then log "PASSED 80: $sc after pass $i (document only, no upload)"; documented=1; fi
  if python3 -c "import sys; sys.exit(0 if $sc >= 82 else 1)"; then log "STOP: target 82 reached ($sc)"; break; fi
  if python3 -c "import sys; sys.exit(0 if $gain < 0.3 else 1)"; then small=$((small + 1)); else small=0; fi
  if [ "$small" -ge 2 ]; then log "STOP: two passes in a row gained < 0.3"; break; fi
  if [ "$i" = 5 ] && python3 -c "import sys; sys.exit(0 if $sc < 79.0 else 1)"; then log "STOP: below 79.0 after pass 5 (plan's no-progress rule)"; break; fi
  prev=$sc
done
log "passes finished at $(num); releasing instance $ID"
CONFIRM=yes infra/vast/destroy.sh "$ID" >> "$L" 2>&1
systemctl --user stop lra-bridge lra-health 2>/dev/null
log "chain done"
