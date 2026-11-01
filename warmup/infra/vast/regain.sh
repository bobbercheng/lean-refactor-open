#!/usr/bin/env bash
# Get a running A100 back as fast as possible after an outbid (2026-10-09 ~20:55: instance <instance> outbid, its machine held whole, a
# cheaper verified offer appeared and was taken by someone else within a minute). Races two paths and keeps whichever wins first:
#   (a) OLD runs again (the outbid sentry's bid ladder fights for it): winback.sh re-runs its bootstrap, bridge and health -> READY OLD;
#   (b) a verified 4xA100 bid offer with min_bid <= NEW_CAP is listed (checked every 20 s): the sentry and ladder on OLD are stopped
#       first (never two rentals), provision.sh rents it at min_bid + $0.01 and arms the sentry on it; on READY the OLD instance is
#       destroyed; if the rental fails, the sentry is re-armed on OLD and the race goes on.
#   infra/vast/regain.sh OLD_ID [NEW_CAP=2.75] [OLD_CAP=3.17]        (unit lra-a100-regain; log probe/a100-regain.log)
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3
cd "$(dirname "$0")/../.." || exit 2
OLD=${1:?old instance id}; NEWCAP=${2:-2.75}; OLDCAP=${3:-3.17}; L=probe/a100-regain.log
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
Q='num_gpus=4 gpu_ram>=80 gpu_name in [A100_SXM4,A100_PCIE] cpu_cores_effective>=64 disk_space>=300'
Q="$Q${VERIFIED:+ verified=$VERIFIED}${MIN_DOWN:+ inet_down>=$MIN_DOWN}"   # same filter as provision.sh (it inherits VERIFIED, MIN_DOWN)
sentry_on_old() {
  systemctl --user reset-failed lra-a100-sentry 2>/dev/null
  systemd-run --user --unit lra-a100-sentry --working-directory="$PWD" -E PATH="$PATH" -E HOME="$HOME" \
    bash -c "infra/vast/outbid_sentry.sh $OLD $OLDCAP > /dev/null 2>&1" > /dev/null 2>&1
}
SKIP="${SKIP_OFFERS:-}"   # offers that failed to rent: a listing can outlive its offer ("no_such_ask"), and retrying it restarts the ladder each time
log "regain: the ladder on $OLD (cap \$$OLDCAP) races new verified offers with min_bid <= \$$NEWCAP"
systemctl --user is-active -q lra-a100-sentry || sentry_on_old
while :; do
  st=$(vastai show instance "$OLD" --raw 2>/dev/null | python3 -c "import json, sys; print(json.load(sys.stdin).get('actual_status'))" 2>/dev/null)
  if [ "$st" = running ]; then
    log "path (a): $OLD runs again; resuming its bootstrap"
    SKIP_LADDER=1 infra/vast/winback.sh "$OLD" >> "$L" 2>&1 && { log "READY $OLD"; exit 0; }
    log "bootstrap of $OLD failed: kept for the babysitter"; exit 1
  fi
  best=$(vastai search offers "$Q" --type bid --storage 300 -o dph_total --limit 20 --raw 2>/dev/null | python3 -c "
import json, sys
skip = set('$SKIP'.split())
o = [x for x in json.load(sys.stdin) if x.get('min_bid') and x['min_bid'] <= $NEWCAP and str(x['id']) not in skip]
o.sort(key=lambda x: x['min_bid'])
print(f\"{o[0]['id']} {o[0]['min_bid']:.3f} {o[0].get('geolocation', '').replace(' ', '_')}\" if o else '')" 2>/dev/null)
  if [ -n "$best" ]; then
    log "path (b): offer listed: $best; stopping the sentry and ladder on $OLD, renting"
    systemctl --user stop lra-a100-sentry lra-a100-bid 2>/dev/null
    out=$(SKIP_OFFERS="$SKIP" BID_CAP=$NEWCAP CONFIRM=yes infra/vast/provision.sh 1 2>&1); rc=$?
    echo "$out" >> probe/a100-provision.log; tail -n 3 <<< "$out" >> "$L"
    if [ "$rc" = 0 ]; then
      NEW=$(tail -n 1 <<< "$out" | sed -n 's/^READY //p')
      log "path (b) won: READY $NEW; destroying $OLD"
      vastai destroy instance "$OLD" -y 2>&1 | grep -v DEPRECATED >> "$L"
      echo "READY $NEW" >> "$L"; exit 0
    fi
    NEWID=$(grep -oE "instance [0-9]+; bootstrapping" <<< "$out" | grep -oE "[0-9]+" | tail -n 1)
    if [ -n "$NEWID" ] && vastai show instances --raw 2>/dev/null | python3 -c "import json, sys; sys.exit(0 if any(i.get('id') == $NEWID for i in json.load(sys.stdin)) else 1)"; then
      log "the new instance $NEWID did not get READY (rc $rc) and is kept: babysitter decides; the sentry stays on it"; exit 1
    fi
    SKIP="$SKIP ${best%% *}"
    log "rental failed (rc $rc, offer likely taken first): offer ${best%% *} skipped from now on; sentry back on $OLD; the race goes on"
    sentry_on_old
  fi
  sleep 20
done
