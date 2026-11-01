#!/usr/bin/env bash
# 2026-10-07: test the thinking budget set by the prompt on the A100, then use it for pass 3; shut the instance down once
# pass 3 is complete.  Waits for the running pass-2 agent to exit AND for probe/A100_PASS3_GO (extra agent flags decided by the
# nudge probe), runs pass 3 from a COPY of replicate.sh (immune to edits while running), then releases the instance.
set -u
ID=${1:?vast instance id}
cd "$(dirname "$0")/../.."
log() { echo "[$(date -u -Is)] $*"; }
while pgrep -f "run-id fresh-a100-p2" >/dev/null; do sleep 60; done
log "pass-2 agent exited; waiting 90 s for replicate.sh's accounting, then for probe/A100_PASS3_GO"
sleep 90
while [ ! -f probe/A100_PASS3_GO ]; do sleep 30; done
EXTRA=$(cat probe/A100_PASS3_GO)
SCRATCH=$(mktemp -d); cp harness/replicate.sh "$SCRATCH/replicate.sh"; export REPO_ROOT="$PWD"
log "starting pass 3 with extra flags: $EXTRA (script copy: $SCRATCH/replicate.sh)"
export PATH="$HOME/.elan/bin:$PATH"
AGENT_EXTRA="--base-url http://localhost:8000/v1 --api-key-file $HOME/.config/vexorium/vllm_api_key --api-model glm-5.3-flash --serving-tag vllm-a100-awq-w4a16 --max-api-retries 20 --max-tokens 6000 $EXTRA" \
  START=3 bash "$SCRATCH/replicate.sh" fresh-a100 openai 3 4
# release guard (2026-10-07 incident: the pass failed instantly — the script copy ran outside the repo — and the chain released the
# instance anyway): only release when the pass log shows the problems actually completed.
if [ "$(grep -c ' DONE ' probe/fresh-a100-p3.log 2>/dev/null)" -lt 10 ]; then
  log "pass 3 did NOT run to completion (fewer than 10 DONE lines); keeping instance $ID for a manual decision"; exit 1
fi
log "pass 3 finished; final accounting"
python3 bank/import_verified.py > /dev/null
python3 assemble/best.py --include-dev-only --only-run-prefix fresh-a100- | head -n 1
touch probe/A100_PASS3_DONE
log "releasing instance $ID (shut down once pass 3 is complete)"
CONFIRM=yes infra/vast/destroy.sh "$ID"
log "chain done"
