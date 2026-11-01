#!/usr/bin/env bash
# Start new passes of the on-instance chain (2026-10-09, pass 8 toward 82 after the line closed at 81.72): the GCS sidecar first when its
# key exists (optional), the W&B live updater when its credential exists (optional), then chain_on_instance.sh FIRST LAST in this process
# (its real-call preflight, one pass at a time, stop rules). The line's extra agent flags come from AGENT_FLAGS (infra/vast/endpoint.sh).
#   cd /workspace/lra; setsid nohup infra/vast/start_chain_instance.sh 8 9 > /dev/null 2>&1 < /dev/null &
set -u
cd "$(dirname "$0")/../.." || exit 2
export PATH="$HOME/.elan/bin:/opt/google-cloud-sdk/bin:$PATH"
FIRST=${1:?first pass}; LAST=${2:?last pass}; L=probe/a100-80-chain-instance.log; mkdir -p probe
log() { echo "[$(date -u -Is)] $*" >> "$L"; }
if pgrep -f "^(/usr/bin/|/bin/)?bash [^ ]*(chain_on_instance|replicate|resume_pass_instance)\.sh|^python3 harness/agent\.py" > /dev/null; then
  log "start refused: a chain or agent is already running on this instance"; exit 1
fi
. infra/vast/endpoint.sh
if gcs_on; then
  pgrep -f "[i]nfra/sync/sidecar.py" > /dev/null || setsid nohup python3 -u infra/sync/sidecar.py --label a100-80-dev \
    --watch "probe/runs/fresh-a100-p*/verified.jsonl" --paths $(sidecar_paths "$FIRST" "$LAST") >> probe/a100-sidecar-instance.log 2>&1 < /dev/null &
else log "start: GCS backup off (no key; optional)"; fi
runs=$(seq -f "fresh-a100-p%g" "$FIRST" "$LAST" | tr '\n' ' ')
wandb_on && ! pgrep -f "[w]andb_live.sh" > /dev/null && setsid nohup infra/sync/wandb_live.sh $runs >> probe/wandb-live-instance.out 2>&1 < /dev/null &
log "start: passes $FIRST-$LAST; sidecar $(pgrep -f '[i]nfra/sync/sidecar.py' > /dev/null && echo up || echo off); W&B live $(pgrep -f '[w]andb_live.sh' > /dev/null && echo up || echo off); agent flags: ${LRA_AGENT_FLAGS:-none}"
exec infra/vast/chain_on_instance.sh "$FIRST" "$LAST"
