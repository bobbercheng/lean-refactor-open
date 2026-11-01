#!/usr/bin/env bash
# Act on an outbid within a minute, in every phase (2026-10-09: act on an outbid at once
# next time; instance <instance> was outbid mid-bootstrap at about 20:33 and nothing reacted until it was noticed by hand at about 20:43: the
# health watchdog starts only after a good bootstrap, the resume watcher only after launch). Armed by provision.sh the moment an instance
# is rented; runs until the instance is gone. Every 30 s it reads vast; on a stop it starts infra/vast/bid_ladder.sh ID CAP at once (unit
# lra-a100-bid) unless a ladder for this instance already runs. After a ladder ends at the cap ("switch instances") it does not restart it
# until the instance has run again. A stop with the credit nearly gone is a credit stop: no ladder, a CREDIT line instead (top-up needed).
# Phase-specific recovery stays where it was: provision.sh re-runs the bootstrap when the instance runs again; during a run,
# resume_watch.sh (LOOP=1) resumes the harness.
#   infra/vast/outbid_sentry.sh INSTANCE_ID [CAP=3.17]          (unit lra-a100-sentry; log probe/a100-sentry.log)
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3
cd "$(dirname "$0")/../.." || exit 2
ID=${1:?instance id}; CAP=${2:-3.17}; L=probe/a100-sentry.log
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
state() { vastai show instances --raw 2>/dev/null | python3 -c "
import json, sys
try:
    rows = json.load(sys.stdin)
except Exception:
    print('? ?'); sys.exit()
i = next((r for r in rows if r.get('id') == $ID), None)
print('gone gone' if i is None else f\"{i.get('actual_status') or '?'} {i.get('intended_status') or '?'}\")"; }
credit() { vastai show user --raw 2>/dev/null | python3 -c "import json, sys; print(json.load(sys.stdin).get('credit') or 0)" 2>/dev/null || echo 99; }
log "sentry on $ID: bid ladder up to \$$CAP at once on any stop"
was=""; gone=0; capped=0; credit_said=0
while :; do
  read -r act want <<< "$(state)"
  if [ "$act" = gone ]; then
    gone=$((gone + 1)); [ "$gone" -ge 3 ] && { log "instance $ID no longer listed: sentry exits"; exit 0; }
    sleep 30; continue
  fi
  gone=0
  [ "$act $want" != "$was" ] && { log "status $act (intended $want)"; was="$act $want"; }
  if [ "$act" = running ]; then capped=0; credit_said=0
  elif [ "$act" = exited ] || [ "$act" = stopped ] || [ "$want" = stopped ]; then
    c=$(credit)
    if python3 -c "import sys; sys.exit(0 if float('$c') < 1.0 else 1)" 2>/dev/null; then
      [ "$credit_said" = 1 ] || { log "CREDIT stop (credit \$$c): no ladder; top-up needed, then vastai start instance $ID"; credit_said=1; }
    elif [ "$capped" = 0 ] && ! pgrep -f "[b]id_ladder.sh $ID" > /dev/null; then
      if tail -n 1 probe/a100-bid.log 2>/dev/null | grep -q "cap .* reached and still" && [ "$(stat -c %Y probe/a100-bid.log)" -gt "$(( $(date +%s) - 120 ))" ]; then
        capped=1; log "ladder ended at the cap \$$CAP and $ID is still $act: SWITCH INSTANCES (provision.sh, then migrate_harness.sh)"
      else
        systemctl --user reset-failed lra-a100-bid 2>/dev/null
        systemd-run --user --unit lra-a100-bid --working-directory="$PWD" -E PATH="$PATH" -E HOME="$HOME" \
          bash -c "infra/vast/bid_ladder.sh $ID $CAP >> probe/a100-bid.out 2>&1" > /dev/null 2>&1 \
          && log "stop ($act, intended $want): bid ladder started at once (cap \$$CAP)"
      fi
    fi
  fi
  sleep 30
done
