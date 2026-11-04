#!/usr/bin/env bash
# Win back an outbid instance in small bid steps up to a cap (operator 2026-10-09: "don't wait a long time for outbid, raise the bid in small
# steps up to a cap. If still not available, switch to new instance"). Raises the bid by STEP every INTERVAL seconds, checking every 20 s
# whether vast runs the instance again; never above CAP. Exit 0 = running again (lra-a100-resume then restarts the run), 3 = cap reached
# and still stopped (switch instances). Log: probe/a100-bid.log.
#   infra/vast/bid_ladder.sh INSTANCE_ID [CAP=$BID_CAP_DEFAULT] [STEP=0.05] [INTERVAL=180]
# The effective $/h after every step is logged here and, when the instance runs again, in accounting/a100_poc.md (review 2026-10-28).
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3
cd "$(dirname "$0")/../.." || exit 2
ID=${1:?instance id}; CAP=${2:-$BID_CAP_DEFAULT}; STEP=${3:-0.05}; INTERVAL=${4:-${LADDER_INTERVAL_S:-180}}; L=probe/a100-bid.log; TICK=${TICK_S:-20}
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
st() { vastai show instance "$ID" --raw 2>/dev/null | python3 -c "import json, sys; d = json.load(sys.stdin); print(d.get('actual_status'), d.get('dph_base'))" 2>/dev/null; }
# a failed vast read prints nothing; acting on it once sent "min( + 0.05, cap)" = a $0.05 bid in a dry run (2026-10-09 review): keep the
# last good reading instead, and never bid below the bid read at the start
rd() { local a b; read -r a b <<< "$(st)"; if [ -n "$a" ] && [[ "$b" =~ ^[0-9]+(\.[0-9]+)?$ ]]; then s=$a; cur=$b; return 0; fi; return 1; }
s=""; cur=""; until rd; do sleep "$TICK"; done; base=$cur
log "ladder for $ID: status $s, bid \$$cur, cap \$$CAP, +\$$STEP every ${INTERVAL}s"
while [ "$s" != running ]; do
  if python3 -c "import sys; sys.exit(0 if $cur >= $CAP - 1e-9 else 1)"; then
    for i in $(seq 1 $((INTERVAL / TICK))); do rd; [ "$s" = running ] && break; sleep "$TICK"; done
    [ "$s" = running ] && break
    vastai start instance "$ID" > /dev/null 2>&1; for i in $(seq 1 $((INTERVAL / TICK))); do rd; [ "$s" = running ] && break; sleep "$TICK"; done
    [ "$s" = running ] && break
    log "cap \$$CAP reached and still $s after a start request: switch instances"; exit 3
  fi
  nxt=$(python3 -c "print(f'{max(min($cur + $STEP, $CAP), $base):.2f}')")
  vastai change bid "$ID" --price "$nxt" > /dev/null 2>&1 && log "bid \$$cur -> \$$nxt" || log "change bid to \$$nxt FAILED"
  # 2026-10-29 23:41 lesson: an outbid instance stays intended=stopped; a higher bid alone never restarts it (the 13:13 and 14:35 ladders
  # "lost" at the cap for this reason). `start instance` asks vast to run it again as soon as the bid wins.
  vastai start instance "$ID" > /dev/null 2>&1 && log "start requested at \$$nxt" || log "start instance FAILED"
  for i in $(seq 1 $((INTERVAL / TICK))); do sleep "$TICK"; rd; [ "$s" = running ] && break; done
done
log "RUNNING again at bid \$$cur"
printf -- "- %s UTC bid ladder: instance %s runs again at \$%s/h (started at \$%s, cap \$%s)\n" "$(date -u +%Y-%m-%dT%H:%M)" "$ID" "$cur" "$base" "$CAP" >> accounting/a100_poc.md
