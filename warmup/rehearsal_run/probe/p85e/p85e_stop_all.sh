#!/usr/bin/env bash
# END the A100 warm-up climb (p85e) now: v3 (2026-11-01 ~00:00 UTC). Returns at once; safe from a Bash tool call.
#   p85e_stop_all.sh [now] [reason...]        END_AT=now in probe/p85e/END_AT + trigger probe/p85e/FINAL_NOW: the armed lra-p85e-final fires
#                                             within 30 s (END_AT now on the box: the v3 sessions stop; STOP + STOP_NOW; final pull of OUT +
#                                             run dirs + /workspace/p85e; pick; hold removed -> the watch releases the box once the driver's
#                                             summary.json exists)
#   p85e_stop_all.sh end-driver [reason...]   the same, and the p85b DRIVER is ended early too (/workspace/package_stop_host.sh, export
#                                             only; its real summary.json awaited <= ~30 min) so the box is released at once
#   p85e_stop_all.sh soft                     v3: alias of now (END_AT=now stops the running sessions anyway)
#   p85e_stop_all.sh status                   final unit state, END_AT, trigger / done markers, hold, last final.log lines
# Fallback when lra-p85e-final is not active: the work runs as the transient unit lra-p85e-stopall (p85e_final.sh now <mode>; RuntimeMaxSec
# 2700 s, end-driver 4200 s; ExecStopPost p85e_unhold.sh, so the hold goes even if the unit is killed).
set -u
. "${P85E_DIR:-/home/bobber/source/lra-a100/probe/p85e}/p85e_common.sh"
U=${P85E_STOPALL_UNIT:-lra-p85e-stopall}; F=lra-p85e-final
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$(id -u)}
case "${1:-now}" in
  status) echo "unit $F: $($SYSCTL --user show $F -p ActiveState --value 2>/dev/null) / $U: $($SYSCTL --user show $U -p ActiveState --value 2>/dev/null)"
          echo "END_AT $(end_at) ($(hm "$(end_at)") UTC); FINAL_NOW: $(cat "$FINAL_NOW" 2>/dev/null || echo none); FINAL_DONE: $([ -e "$FINAL_DONE" ] && echo yes || echo no)"
          [ -e "$HOLD" ] && echo "hold: PRESENT ($HOLD)" || echo "hold: removed"; tail -n 10 "$ROOT/probe/p85e/final.log"; exit 0;;
  now|soft) SM=now;; end-driver) SM=end-driver;; *) echo "usage: $0 [now|end-driver|soft|status] [reason...]"; exit 2;;
esac
shift || true; REASON=${*:-manual}; REASON=${REASON//$'\n'/ }
[ -e "$FINAL_DONE" ] && { echo "the p85e final is already done ($(stat -c %y "$FINAL_DONE" | cut -c1-19)); hold: $([ -e "$HOLD" ] && echo PRESENT || echo removed)"; exit 0; }
NOW=$(date +%s)
if [ -e "$FINAL_NOW" ]; then
  read -r om _ < "$FINAL_NOW"
  if [ "$om" = end-driver ] || [ "$SM" = now ]; then echo "already triggered ($(cat "$FINAL_NOW"))"; else
    printf '%s %s %s\n' "$SM" "$NOW" "$REASON" > "$FINAL_NOW.tmp" && mv "$FINAL_NOW.tmp" "$FINAL_NOW"; echo "trigger upgraded to end-driver"; fi
else
  set_end_local "$NOW" "stop-all $SM: $REASON"
  printf '%s %s %s\n' "$SM" "$NOW" "$REASON" > "$FINAL_NOW.tmp" && mv "$FINAL_NOW.tmp" "$FINAL_NOW"
fi
if $SYSCTL --user is-active -q $F 2>/dev/null; then
  echo "p85e stop ($SM: $REASON): END_AT=now, FINAL_NOW written; the armed $F fires within 30 s (budget $([ $SM = end-driver ] && echo 40 || echo 20) min). Follow: tail -f $ROOT/probe/p85e/final.log  or: bash $0 status"
  exit 0
fi
if $SYSCTL --user is-active -q $U 2>/dev/null; then echo "$U already running: follow tail -f $ROOT/probe/p85e/final.log"; exit 0; fi
$SYSCTL --user reset-failed $U > /dev/null 2>&1
MAX=2700; [ $SM = end-driver ] && MAX=4200
EX=(); for v in P85E_ROOT P85E_DIR P85E_LOCKDIR P85E_SYSCTL P85E_NTFY P85E_CAP; do [ -n "${!v+x}" ] && EX+=(-E "$v=${!v}"); done   # test hooks only
if systemd-run --user --unit $U --collect -p RuntimeMaxSec=$MAX -p CPUWeight=20 -p MemoryMax=4G --working-directory="$ROOT" \
     -E PATH="$PATH:/home/bobber/miniconda3/bin" -E HOME="$HOME" -E P85E_STOPALL=1 -E P85E_DEADLINE=$((NOW + MAX - 120)) "${EX[@]}" \
     -p ExecStopPost="/usr/bin/bash $PD/p85e_unhold.sh" /usr/bin/bash "$PD/p85e_final.sh" now $SM > /dev/null 2>&1; then
  echo "p85e stop ($SM): $F not active, so the final runs as the transient unit $U (ends by $(hm $((NOW + MAX))) UTC at the latest). Follow: tail -f $ROOT/probe/p85e/final.log"
else
  echo "systemd-run FAILED: run the final in the background instead (Bash run_in_background=true): bash $PD/p85e_final.sh now $SM"; exit 1
fi
