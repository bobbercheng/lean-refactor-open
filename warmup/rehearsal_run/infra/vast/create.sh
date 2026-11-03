#!/usr/bin/env bash
# Rent the A100 POC instance on vast.ai as an INTERRUPTIBLE (bid) instance. Prints the command and exits unless CONFIRM=yes.
# Usage: CONFIRM=yes infra/vast/create.sh <offer_id> <bid_price_per_hour>
#   offer ids come from infra/vast/search.sh; bid a little above min_bid (e.g. min_bid + 0.10) to reduce pre-emption.
# Pins: image lazymio/vllm-backport:v0.13.1-sm80 (sha256:8094fcbab905…, 2026-09-16); checkpoint revision in onstart.sh.
# Review 2026-10-28: the vLLM bearer key is no longer in --env (bootstrap.sh writes it to /workspace/env, the only key path, and
# run_vllm.sh reads it there), the echoed command masks any key, and vast's reply (it carries the instance's own API key) goes to
# probe/a100-last-create.log (ignored by git), never to a tracked file.
set -eu
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai
OFFER=${1:?offer id}; BID=${2:?bid price per hour}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
CMD=(vastai create instance "$OFFER"
  --image lazymio/vllm-backport:v0.13.1-sm80
  --disk "${DISK:-300}"   # provision.sh exports DISK (420 for the rehearsal: model + 16 envs + the LeanPool build and pack)
  --ssh --direct
  --env "-p 8000:8000 -e HF_HUB_ENABLE_HF_TRANSFER=1"
  --onstart "${ONSTART_FILE:-$HERE/onstart.sh}"   # ONSTART_FILE=infra/vast/onstart_tunnel.sh for hosts without a working inbound port map
  --label "${LABEL:-lra-a100-poc}"
  --cancel-unavail
  --raw)
# ONDEMAND=1 (operator 2026-10-29: "just go $3.47 on-demand price" after two outbids): no --bid_price = an on-demand rental at the
# offer's dph_total, which cannot be outbid; the BID argument is then only logged. Otherwise an interruptible rental at $BID.
[ "${ONDEMAND:-0}" = 1 ] || CMD+=(--bid_price "$BID")
SHOWN="${CMD[*]}"; SHOWN=$(sed -E 's/(VLLM_API_KEY|api_key|API_KEY)=[^ ]*/\1=***/g' <<< "$SHOWN")
echo "would run: $SHOWN"
if [ "${CONFIRM:-}" != "yes" ]; then echo "(dry run: set CONFIRM=yes to rent; account balance must be > 0 first: vastai show user)"; exit 0; fi
mkdir -p "$ROOT/probe"
"${CMD[@]}" | tee "$ROOT/probe/a100-last-create.log" | sed -E 's/"instance_api_key": *"[^"]*"/"instance_api_key": "***"/'
echo; echo "created. Next: infra/vast/status.sh ; destroy with infra/vast/destroy.sh <instance_id>"
