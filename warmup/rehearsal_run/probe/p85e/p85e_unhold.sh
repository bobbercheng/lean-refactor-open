#!/usr/bin/env bash
# ExecStopPost of lra-p85e-final and lra-p85e-stopall: the box is never held past those units. If a final run (stop-all or the 11:30
# final) still holds the lock, it removes the hold itself, so this skips; otherwise the hold (if still there) goes to probe/retired-a100-holds/.
cd "${P85E_ROOT:-/home/bobber/source/lra-a100}" || exit 0
H=probe/a100-hold-p85e-58565100
exec 8> "${P85E_LOCKDIR:-/tmp}/p85e-final.lock"; flock -n 8 || { echo "final run in progress: it removes the hold"; exit 0; }
[ -e "$H" ] && mkdir -p probe/retired-a100-holds && mv "$H" "probe/retired-a100-holds/$(basename $H).$(date -u +%m%d%H%M).stoppost" \
  && echo "[$(date -u +%m-%d\ %H:%M:%S)] ExecStopPost: hold removed" >> probe/p85e/final.log
exit 0
