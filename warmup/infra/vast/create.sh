#!/usr/bin/env bash
# Rent the A100 POC instance on vast.ai as an INTERRUPTIBLE (bid) instance. Prints the command and exits unless CONFIRM=yes.
# Usage: CONFIRM=yes infra/vast/create.sh <offer_id> <bid_price_per_hour>
#   offer ids come from infra/vast/search.sh; bid a little above min_bid (e.g. min_bid + 0.10) to reduce pre-emption.
# Pins: image lazymio/vllm-backport:v0.13.1-sm80 (sha256:8094fcbab905…, 2026-09-16); checkpoint revision in onstart.sh.
set -eu
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai
OFFER=${1:?offer id}; BID=${2:?bid price per hour}
HERE=$(cd "$(dirname "$0")" && pwd)
CMD=(vastai create instance "$OFFER"
  --image lazymio/vllm-backport:v0.13.1-sm80
  --disk "${DISK:-300}"   # DISK=800 for the harness-on-A100 setup (Lean envs + toolchains need ~122 GB beyond the 191 GB model)
  --ssh --direct
  --env "-p 8000:8000 -e HF_HUB_ENABLE_HF_TRANSFER=1 -e VLLM_API_KEY=$(cat ~/.config/vexorium/vllm_api_key)"   # the public port requires this bearer token
  --onstart "$HERE/onstart.sh"
  --label "${LABEL:-lra-a100-poc}"
  --bid_price "$BID"
  --cancel-unavail
  --raw)
echo "would run: ${CMD[*]}"
if [ "${CONFIRM:-}" != "yes" ]; then echo "(dry run: set CONFIRM=yes to rent; account balance must be > 0 first: vastai show user)"; exit 0; fi
"${CMD[@]}" | tee "$HERE/last_create.json"
echo; echo "created. Next: infra/vast/status.sh ; then infra/vast/tunnel.sh <instance_id> ; destroy with infra/vast/destroy.sh <instance_id>"
