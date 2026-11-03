#!/usr/bin/env bash
# GB10: bring-up chain for the Iowa box (autonomy rule after the 10:05 outbid). Bounded waits; logs to probe/a100-reh-p85b/bringup.log.
set -u
cd /home/bobber/source/lra-a100
export XDG_RUNTIME_DIR=/run/user/$(id -u) DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/$(id -u)/bus
S="<scratchpad>"
ID=$(cat $S/new_box_id.txt); L=probe/a100-reh-p85b/bringup.log; log() { echo "[$(date -u +%H:%M:%S)] $*" >> $L; }
end=$(( $(date +%s) + 3600 )); until grep -qE "PREP DONE|prep: .*(fail|missing)|restore failed" probe/a100-reh-p85b/prep.out || [ $(date +%s) -gt $end ]; do sleep 20; done
grep -q "PREP DONE" probe/a100-reh-p85b/prep.out || { log "prep did not finish: $(tail -1 probe/a100-reh-p85b/prep.out)"; exit 1; }
log "prep done"; bash $S/p85b_setup_ia.sh >> $L 2>&1 || { log "setup failed"; exit 1; }
systemctl --user reset-failed lra-a100-p85b-arm-ia 2>/dev/null
systemd-run --user --unit lra-a100-p85b-arm-ia --working-directory=$PWD -E PATH -E HOME -E LRA_FAKE_VAST_BIN= -E LRA_UNIT_SUFFIX=-ia -E "ARM_UNTIL=2026-11-01 01:00 UTC" \
  -p StandardOutput=append:$PWD/probe/a100-reh-p85b/arm-ia.out -p StandardError=append:$PWD/probe/a100-reh-p85b/arm-ia.out bash infra/vast/p85b_arm_gb10.sh $ID && log "GB10 arm started (suffix -ia)"
end=$(( $(date +%s) + 3600 )); until grep -qE "server ready|not ready|failed" probe/a100-bootstrap-$ID.log || [ $(date +%s) -gt $end ]; do sleep 20; done
log "bootstrap: $(tail -1 probe/a100-bootstrap-$ID.log | cut -c1-120)"
systemctl --user stop lra-bridge lra-health 2>/dev/null; systemctl --user reset-failed lra-bridge lra-health 2>/dev/null
systemd-run --user --unit lra-bridge --working-directory=$PWD -E PATH -E HOME bash -c "exec infra/vast/tls_bridge.sh $ID >> probe/a100-tls-bridge.log 2>&1" && log "bridge -> $ID"
systemd-run --user --unit lra-health --working-directory=$PWD -E PATH -E HOME bash -c "exec python3 -u infra/vast/health.py $ID --interval 60 --no-bridge >> probe/a100-health.log 2>&1" && log "health -> $ID"
echo $ID > probe/a100-instance-id
log "bring-up chain done"
