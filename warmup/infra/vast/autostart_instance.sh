#!/usr/bin/env bash
# Start the on-instance chain the moment the Lean environment build finishes clean (no idle GPU time while waiting for a babysitter):
# waits for "SETUP DONE" in the setup output, then starts chain_on_instance.sh and the W&B live updater detached; if any env failed it
# starts nothing and says so in the chain log.
#   setsid nohup infra/vast/autostart_instance.sh envs_setup2.out 6 7 > /dev/null 2>&1 < /dev/null &      (from /workspace/lra)
set -u
cd "$(dirname "$0")/../.." || exit 2
OUT=${1:?setup output}; FIRST=${2:?first pass}; LAST=${3:?last pass}; L=probe/a100-80-chain-instance.log; mkdir -p probe
until grep -q "SETUP DONE" "$OUT"; do sleep 10; done
if grep -q "SETUP DONE ok=15 failed=0" "$OUT"; then
  setsid nohup infra/vast/chain_on_instance.sh "$FIRST" "$LAST" > probe/chain-instance.out 2>&1 < /dev/null &
  runs=$(seq -f "fresh-a100-p%g" "$FIRST" "$LAST" | tr '\n' ' ')
  . infra/vast/endpoint.sh; wandb_on && setsid nohup infra/sync/wandb_live.sh $runs > probe/wandb-live-instance.out 2>&1 < /dev/null &   # optional
  echo "[$(date -u -Is)] autostart: setup clean; chain $FIRST-$LAST and W&B live ($runs) started" >> "$L"
else
  echo "[$(date -u -Is)] autostart: NOT started: $(grep "SETUP DONE" "$OUT")" >> "$L"
fi
