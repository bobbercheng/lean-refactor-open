#!/usr/bin/env bash
# Wait for the running A100 pass-1 driver (PID $1) to exit AND for the go-file probe/A100_PASS2_GO, then run the resumed pass 2.
# The go-file holds the extra agent flags for pass 2 (2026-10-06: after the first A100 pass, align the A100 settings
# with the z.ai line) — written once the effort/think-history experiments on the idle server have decided them.
set -u
PID=${1:?driver pid}
cd "$(dirname "$0")/../.."
while kill -0 "$PID" 2>/dev/null; do sleep 60; done
echo "[$(date -u -Is)] pass-1 driver $PID exited; waiting for probe/A100_PASS2_GO"
touch probe/A100_PASS1_DONE
while [ ! -f probe/A100_PASS2_GO ]; do sleep 30; done
EXTRA=$(cat probe/A100_PASS2_GO)
echo "[$(date -u -Is)] starting pass 2 with extra flags: $EXTRA"
export PATH="$HOME/.elan/bin:$PATH"
AGENT_EXTRA="--base-url http://localhost:8000/v1 --api-key-file $HOME/.config/vexorium/vllm_api_key --api-model glm-5.3-flash --serving-tag vllm-a100-awq-w4a16 --max-api-retries 20 --max-tokens 6000 $EXTRA" \
  START=2 harness/replicate.sh fresh-a100 openai 2 4
