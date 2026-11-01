#!/usr/bin/env bash
# Win back an outbid instance in small bid steps up to a cap (2026-10-09: do not wait long after an outbid; raise the bid in small
# steps up to a cap, else switch to a new instance). Raises the bid by STEP every INTERVAL seconds, checking every 20 s
# whether vast runs the instance again; never above CAP. Exit 0 = running again (lra-a100-resume then restarts the run), 3 = cap reached
# and still stopped (switch instances). Log: probe/a100-bid.log.
#   infra/vast/bid_ladder.sh INSTANCE_ID [CAP=2.00] [STEP=0.05] [INTERVAL=180]
set -u
cd "$(dirname "$0")/../.." || exit 2
ID=${1:?instance id}; CAP=${2:-2.00}; STEP=${3:-0.05}; INTERVAL=${4:-180}; L=probe/a100-bid.log
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
st() { vastai show instance "$ID" --raw 2>/dev/null | python3 -c "import json, sys; d = json.load(sys.stdin); print(d.get('actual_status'), d.get('dph_base'))" 2>/dev/null; }
# a failed vast read prints nothing; acting on it once sent "min( + 0.05, cap)" = a $0.05 bid in a dry run (2026-10-09 review): keep the
# last good reading instead, and never bid below the bid read at the start
rd() { local a b; read -r a b <<< "$(st)"; if [ -n "$a" ] && [[ "$b" =~ ^[0-9]+(\.[0-9]+)?$ ]]; then s=$a; cur=$b; return 0; fi; return 1; }
s=""; cur=""; until rd; do sleep 20; done; base=$cur
log "ladder for $ID: status $s, bid \$$cur, cap \$$CAP, +\$$STEP every ${INTERVAL}s"
while [ "$s" != running ]; do
  if python3 -c "import sys; sys.exit(0 if $cur >= $CAP - 1e-9 else 1)"; then
    for i in $(seq 1 $((INTERVAL / 20))); do rd; [ "$s" = running ] && break; sleep 20; done
    [ "$s" = running ] && break
    log "cap \$$CAP reached and still $s: switch instances"; exit 3
  fi
  nxt=$(python3 -c "print(f'{max(min($cur + $STEP, $CAP), $base):.2f}')")
  vastai change bid "$ID" --price "$nxt" > /dev/null 2>&1 && log "bid \$$cur -> \$$nxt" || log "change bid to \$$nxt FAILED"
  for i in $(seq 1 $((INTERVAL / 20))); do sleep 20; rd; [ "$s" = running ] && break; done
done
log "RUNNING again at bid \$$cur"
