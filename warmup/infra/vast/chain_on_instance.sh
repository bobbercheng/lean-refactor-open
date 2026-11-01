#!/usr/bin/env bash
# A100-80 passes run ON the instance. Same protocol as
# infra/vast/chain_a100_80.sh: the fresh-a100 line, one pass at a time from a COPY of replicate.sh, the frozen harness (HARNESS_COMMIT;
# harness files unchanged since bbfcd4c), 4 workers, effort low, budget forcing on; stop at >= 82.00, after two passes in a row gaining
# < 0.3, or below 79.0 after pass 5; at >= 80 document only, no upload. Differences: the model is local (127.0.0.1:8000, no bridge); the
# GCS sidecar and the W&B live updater run beside it when their credentials exist (optional; replication needs neither); the instance never releases itself (no vast credentials here): it writes
# "chain done" / "STOP" and the babysitter destroys it from the GB10.
#   infra/vast/chain_on_instance.sh FIRST_PASS LAST_PASS     (e.g. 6 7), run from /workspace/lra
set -u
cd "$(dirname "$0")/../.." || exit 2
export PATH="$HOME/.elan/bin:/opt/google-cloud-sdk/bin:$PATH"
FIRST=${1:?first pass}; LAST=${2:?last pass}
L=probe/a100-80-chain-instance.log; mkdir -p probe
log() { echo "[$(date -u -Is)] $*" >> "$L"; }
num() { python3 assemble/best.py --include-dev-only --only-run-prefix fresh-a100- | head -1 | grep -oE '[0-9]+\.[0-9]+' | head -1; }
python3 bank/import_verified.py > /dev/null 2>&1
SCRATCH=$(mktemp -d); cp harness/replicate.sh "$SCRATCH/replicate.sh"; export REPO_ROOT="$PWD"
. infra/vast/endpoint.sh   # LRA_BASE_URL for a plain local server (replication); else our vast TLS setup (2026-10-09 lesson: plain http to a TLS-only server failed every call)
pre=$(preflight)
[ "$pre" = ok ] || { log "STOP: real-path preflight to the model failed: $pre"; exit 1; }
prev=$(num); small=0; documented=0
log "chain on instance start: passes $FIRST-$LAST; line $prev; harness $(cat HARNESS_COMMIT 2>/dev/null | cut -c1-7)"
for i in $(seq "$FIRST" "$LAST"); do
  log "pass $i starts"
  START=$i bash "$SCRATCH/replicate.sh" fresh-a100 openai "$i" 4 >> "$L" 2>&1
  n=$(grep -c ' DONE ' "probe/fresh-a100-p$i.log" 2>/dev/null); n=${n:-0}
  sc=$(num); gain=$(python3 -c "print(round($sc - $prev, 2))")
  log "after pass $i: assembled $sc (gain $gain), $n/15 problems DONE"
  if [ "$n" -lt 10 ]; then log "STOP: pass $i did not run to completion ($n DONE)"; exit 1; fi
  if [ "$documented" = 0 ] && python3 -c "import sys; sys.exit(0 if $sc >= 80 else 1)"; then log "PASSED 80: $sc after pass $i (document only, no upload)"; documented=1; fi
  if python3 -c "import sys; sys.exit(0 if $sc >= 82 else 1)"; then log "STOP: target 82 reached ($sc)"; break; fi
  if python3 -c "import sys; sys.exit(0 if $gain < 0.3 else 1)"; then small=$((small + 1)); else small=0; fi
  if [ "$small" -ge 2 ]; then log "STOP: two passes in a row gained < 0.3"; break; fi
  if [ "$i" = 5 ] && python3 -c "import sys; sys.exit(0 if $sc < 79.0 else 1)"; then log "STOP: below 79.0 after pass 5"; break; fi
  prev=$sc
done
log "chain done at $(num); waiting for release from the GB10"
