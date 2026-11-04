#!/usr/bin/env bash
# Get a running A100 back as fast as possible after an outbid (2026-10-09 ~20:55: instance 55088900 outbid, its machine held whole, a
# cheaper verified offer appeared and was taken by someone else within a minute). Races two paths and keeps whichever wins first:
#   (a) OLD runs again (the outbid sentry's bid ladder fights for it): winback.sh re-runs its bootstrap, bridge and health -> READY OLD;
#   (b) a verified 4xA100 bid offer with min_bid <= NEW_CAP is listed (checked every 20 s): the sentry and ladder on OLD are stopped
#       first (never two rentals), provision.sh rents it at min_bid + $0.01 and arms the sentry on it; on READY the OLD instance is
#       destroyed; if the rental fails, the sentry is re-armed on OLD and the race goes on.
#   infra/vast/regain.sh OLD_ID [NEW_CAP=$BID_CAP_DEFAULT] [OLD_CAP=$BID_CAP_DEFAULT]        (unit lra-a100-regain; log probe/a100-regain.log)
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3
cd "$(dirname "$0")/../.." || exit 2
OLD=${1:?old instance id}; NEWCAP=${2:-$BID_CAP_DEFAULT}; OLDCAP=${3:-$BID_CAP_DEFAULT}; L=probe/a100-regain.log
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
DISK=${DISK:-420}; export DISK   # peak on disk = model 178 GiB + Lean envs and toolchains 118 GiB + env archives in flight during a parallel
                                  # restore (<= ~20 GiB) = ~300-318 GiB, at launch and again at every outbid restart (vLLM reloads from disk while
                                  # the envs stay). 55094025 ran at create.sh's 300 GB default: 99% full. Disk costs ~$0.0005/GB/h, a model
                                  # re-download ~$0.76 of bandwidth plus ~20 min of GPU, so keep the model files and size the disk instead.
CPU_MIN=${CPU_MIN:-64}; MIN_DOWN=${MIN_DOWN:-500}
Q="num_gpus=4 gpu_ram>=80 gpu_name=A100_SXM4 cpu_cores_effective>=$CPU_MIN disk_space>=$DISK"
Q="$Q${VERIFIED:+ verified=$VERIFIED}"; [ "$MIN_DOWN" != 0 ] && Q="$Q inet_down>=$MIN_DOWN"   # same filter as provision.sh (it inherits VERIFIED, MIN_DOWN, CPU_MIN)
sentry_on_old() {
  systemctl --user reset-failed "lra-a100-sentry$U" 2>/dev/null
  systemd-run --user --unit "lra-a100-sentry$U" --working-directory="$PWD" -E PATH="$PATH" -E HOME="$HOME" \
    bash -c "infra/vast/outbid_sentry.sh $OLD $OLDCAP > /dev/null 2>&1" > /dev/null 2>&1
}
SKIP="${SKIP_OFFERS:-}"   # offers that failed to rent: a listing can outlive its offer ("no_such_ask"), and retrying it restarts the ladder each time
log "regain: the ladder on $OLD (cap \$$OLDCAP) races new verified offers with min_bid <= \$$NEWCAP"
systemctl --user is-active -q "lra-a100-sentry$U" || sentry_on_old
while :; do
  st=$(vastai show instance "$OLD" --raw 2>/dev/null | python3 -c "import json, sys; print(json.load(sys.stdin).get('actual_status'))" 2>/dev/null)
  if [ "$st" = running ]; then
    log "path (a): $OLD runs again; resuming its bootstrap"
    SKIP_LADDER=1 infra/vast/winback.sh "$OLD" >> "$L" 2>&1 && { log "READY $OLD"; exit 0; }
    log "$(kept "$OLD" "regain: bootstrap failed")"; exit 1
  fi
  best=$(vastai search offers "$Q" --type bid --storage "$DISK" -o dph_total --limit 20 --raw 2>/dev/null | python3 -c "
import json, sys
skip = set('$SKIP'.split())
o = [x for x in json.load(sys.stdin) if x.get('min_bid') and x['min_bid'] <= $NEWCAP and str(x['id']) not in skip]
o.sort(key=lambda x: x['min_bid'])
print(f\"{o[0]['id']} {o[0]['min_bid']:.3f} {o[0].get('geolocation', '').replace(' ', '_')}\" if o else '')" 2>/dev/null)
  if [ -n "$best" ]; then
    log "path (b): offer listed: $best; stopping the sentry and ladder on $OLD, renting"
    systemctl --user stop "lra-a100-sentry$U" "lra-a100-bid$U" 2>/dev/null
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
      log "the new instance $NEWID did not get READY (rc $rc): provision.sh wrote its KEPT marker; the sentry stays on it"; exit 1
    fi
    SKIP="$SKIP ${best%% *}"
    log "rental failed (rc $rc, offer likely taken first): offer ${best%% *} skipped from now on; sentry back on $OLD; the race goes on"
    sentry_on_old
  fi
  sleep 20
done
