#!/usr/bin/env bash
# (Re)start the GB10 units of the warm-up climb extension (v3, 2026-11-01): absolute ends, low CPU weight, no Lean.
#   lra-p85e-wbpush        p85e_wbpush.sh        RuntimeMaxSec to 2026-11-02 00:10 UTC (it ends itself at END_AT + 5 min / FINAL_DONE)
#   lra-p85e-final         p85e_final.sh (armed) RuntimeMaxSec to 2026-11-02 00:25 UTC; ExecStopPost p85e_unhold.sh (the box is never
#                                                held past the unit). Replaced while THIS script holds /tmp/p85e-final.lock, so the old
#                                                unit's ExecStopPost skips and the hold stays in place.
#   lra-warmup-resetwatch  warmup_resetwatch.py  RuntimeMaxSec to 2026-11-02 00:06 UTC (it ends itself at 00:05)
#   p85e_units_v3.sh [all|wbpush|final|resetwatch|status]
set -u
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$(id -u)} DBUS_SESSION_BUS_ADDRESS=${DBUS_SESSION_BUS_ADDRESS:-unix:path=/run/user/$(id -u)/bus}
R=/home/bobber/source/lra-a100; P=$R/probe/p85e; H=$R/probe/a100-hold-p85e-58565100; NOW=$(date +%s); CAP=1793577600
UPATH="$HOME/.local/bin:/home/bobber/miniconda3/bin:/usr/local/bin:/usr/bin:/bin"
rt() { local t=$(( $1 - NOW )); [ $t -lt 600 ] && t=600; echo $t; }
start_wbpush() {
  systemctl --user stop lra-p85e-wbpush 2>/dev/null; systemctl --user reset-failed lra-p85e-wbpush 2>/dev/null
  systemd-run --user --unit lra-p85e-wbpush -p RuntimeMaxSec=$(rt $((CAP + 600))) -p CPUWeight=20 -p MemoryMax=2G --working-directory=$R \
    -E PATH="$UPATH" -E HOME="$HOME" /usr/bin/bash $P/p85e_wbpush.sh && echo "lra-p85e-wbpush started (to $(date -u -d @$((CAP + 600)) '+%m-%d %H:%M') UTC)"
}
start_final() {
  exec 8> /tmp/p85e-final.lock
  flock -w 60 8 || { echo "could not take /tmp/p85e-final.lock in 60 s (a final is running?): final unit NOT replaced"; return 1; }
  [ -e "$H" ] || echo "WARN: the hold $H is not present (already removed?)"
  systemctl --user stop lra-p85e-final 2>/dev/null; systemctl --user reset-failed lra-p85e-final 2>/dev/null
  [ -e "$H" ] && echo "hold still present after the old unit's stop (its ExecStopPost skipped: lock held)"
  systemd-run --user --unit lra-p85e-final -p RuntimeMaxSec=$(rt $((CAP + 1500))) -p CPUWeight=20 -p MemoryMax=4G --working-directory=$R \
    -E PATH="$UPATH" -E HOME="$HOME" -p ExecStopPost="/usr/bin/bash $P/p85e_unhold.sh" /usr/bin/bash $P/p85e_final.sh \
    && echo "lra-p85e-final started (armed; hard end $(date -u -d @$((CAP + 1500)) '+%m-%d %H:%M') UTC)"
  sleep 2; flock -u 8; exec 8>&-
}
start_resetwatch() {
  systemctl --user stop lra-warmup-resetwatch 2>/dev/null; systemctl --user reset-failed lra-warmup-resetwatch 2>/dev/null
  systemd-run --user --unit lra-warmup-resetwatch -p RuntimeMaxSec=$(rt $((CAP + 360))) -p CPUWeight=10 -p MemoryMax=1G --working-directory=$R \
    -p StandardOutput=append:$P/resetwatch.log -p StandardError=append:$P/resetwatch.log -E PATH="$UPATH" -E HOME="$HOME" -E PYTHONUNBUFFERED=1 \
    /home/bobber/miniconda3/bin/python3 -u $P/warmup_resetwatch.py && echo "lra-warmup-resetwatch started (to $(date -u -d @$((CAP + 300)) '+%m-%d %H:%M') UTC)"
}
case "${1:-status}" in
  all) start_wbpush; start_final; start_resetwatch;;
  wbpush) start_wbpush;; final) start_final;; resetwatch) start_resetwatch;;
  status) for u in lra-p85e-wbpush lra-p85e-final lra-warmup-resetwatch; do
            echo "$u: $(systemctl --user show $u -p ActiveState --value) pid $(systemctl --user show $u -p MainPID --value) runtime-max $(systemctl --user show $u -p RuntimeMaxUSec --value)"; done
          [ -e "$H" ] && echo "hold: PRESENT" || echo "hold: removed";;
  *) echo "usage: $0 [all|wbpush|final|resetwatch|status]"; exit 2;;
esac
