#!/usr/bin/env bash
# Win back an instance that vast stopped (outbid) BEFORE the run was on it, then finish its bootstrap (2026-10-09: instance 55088900 was
# outbid during the checkpoint download, 153 of 190.8 GB on its disk; a stopped instance keeps its disk, so winning it back is cheaper
# than a new rental). Operator rule: "raise the bid in small steps up to a cap. If still not available, switch to new instance".
#   1. infra/vast/bid_ladder.sh ID CAP (small steps; exit 3 at the cap = switch instances, left to the babysitter);
#   2. infra/vast/bootstrap.sh ID again (re-runnable; the download resumes);
#   3. as provision.sh does on success: instance id file, TLS bridge (lra-bridge), readiness check, health watchdog (lra-health).
# Prints "READY <ID>" last on success. Log: probe/a100-winback.log.
#   infra/vast/winback.sh INSTANCE_ID [CAP=$BID_CAP_DEFAULT]
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3 ssh
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd); cd "$ROOT" || exit 2
ID=${1:?instance id}; CAP=${2:-$BID_CAP_DEFAULT}; L=probe/a100-winback.log
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
if [ "${SKIP_LADDER:-0}" = 1 ] || pgrep -f "[b]id_ladder.sh $ID" > /dev/null; then   # the sentry's ladder (or the caller) already fights for it
  log "win back $ID: waiting until it runs (ladder elsewhere)"
  until [ "$(vastai show instance "$ID" --raw 2>/dev/null | python3 -c "import json, sys; print(json.load(sys.stdin).get('actual_status'))" 2>/dev/null)" = running ]; do sleep 20; done
else
  log "win back $ID: bid ladder up to \$$CAP"
  "$HERE/bid_ladder.sh" "$ID" "$CAP" >> "$L" 2>&1; rc=$?
  [ "$rc" = 0 ] || { log "ladder exit $rc: not running at the cap; switch instances (babysitter)"; exit 3; }
fi
log "running again; bootstrap resumes (log probe/a100-bootstrap-$ID.log)"
"$HERE/bootstrap.sh" "$ID" >> "probe/a100-bootstrap-$ID.log" 2>&1; rc=$?
tail -n 2 "probe/a100-bootstrap-$ID.log" >> "$L"
[ "$rc" = 0 ] || { log "$(kept "$ID" "winback: bootstrap exit $rc")"; exit 1; }
echo "$ID" > probe/a100-instance-id
systemctl --user stop "lra-bridge$U" 2>/dev/null
systemd-run --user --unit="lra-bridge$U" --collect -p WorkingDirectory="$ROOT" /usr/bin/bash -c "exec infra/vast/tls_bridge.sh $ID >> probe/a100-tls-bridge.log 2>&1" > /dev/null
V=""; for k in 1 2 3 4 5 6; do sleep 10; V=$("$HERE/server_up.sh" "$ID" --bridge 2>&1) && break; done
systemctl --user stop "lra-health$U" 2>/dev/null
systemd-run --user --unit="lra-health$U" --collect -p WorkingDirectory="$ROOT" /usr/bin/bash -c "exec python3 -u infra/vast/health.py $ID >> probe/a100-health.log 2>&1" > /dev/null
log "$V"
case "$V" in UP*) log "READY $ID";; *) log "$(kept "$ID" "winback: server up but bridge failed")"; exit 1;; esac
