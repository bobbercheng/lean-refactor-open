#!/usr/bin/env bash
# THE release command (2026-11-01; stop rule (a) of the warm-up climb extension, operator 2026-10-31 23:40 UTC). The coordinator's release
# watch runs it ONCE when the official problems are out. Returns within ~30 s; the slow parts run detached.
# v3.1 (00:40 UTC, review fix): the ONLY release entry point. `climb_stop.sh release` execs this script; this script's worker calls it with
# CLIMB_FROM_RELEASE=1, and then it stops the VM squeeze + sync only (the A100 is decided and stopped here alone).
#   bash /home/bobber/source/lra-a100/probe/p85e/warmup_stop_at_release.sh [--end-a100 | --keep-a100] [--keep-driver] [--need USD] [--dry]
# 1. VM squeeze + its GB10 sync stopped NOW (the Azure VM becomes the CLOSED official run's box): detached unit lra-warmup-release.
#    A100 ending: it runs CLIMB_FROM_RELEASE=1 probe/a100-upload/climb/climb_stop.sh release (the climb guard's own stop: VM, sync, markers;
#    with CLIMB_FROM_RELEASE=1 it never touches the A100). A100 kept: climb_stop.sh is NOT run (v1 reason: its credit rule could override the keep; v2 never touches the A100); the
#    same steps are done here and its markers written (VM /scratch/sqvm/loop/CLIMB_STOPPED, GB10 climb/VM_RELEASED). Either way it then
#    makes sure: on the closed-track VM every lra-sqvm-* unit other than the loop stopped (lra-sqvm-ctl would restart the loop), STOP + CLIMB_STOPPED
#    touched, lra-sqvm-loop stopped if still active after 90 s; on the GB10 probe/a100-upload/sqvm/STOP touched (the sync does one last
#    pull + merge) and every lra-sqvm-* unit stopped if still active after 300 s. The GB10 dialect loop is left to the climb guard.
# 2. The A100 climb (p85e on box 58565100): default = by credit: it ENDS when vast credit - (box $/h x hours to END_AT) < NEED (default
#    $375, the official open run's need; env NEED or --need), else it is KEPT and the reset watcher re-checks that rule every 10 min.
#    --end-a100 always ends it, --keep-a100 always keeps it. Ending = p85e_stop_all.sh end-driver: END_AT=now, the armed final (STOP, the
#    p85b driver ended early with an export unless --keep-driver, final pull, pick, hold removed -> the watch destroys the box).
# Writes probe/p85e/RELEASE_SEEN (json: decision, credit, need, dph) and a babysit line BEFORE acting. --dry: the decision only.
# Test hooks: P85E_DIR / P85E_ROOT (common), RS_BABYSIT (babysit file), RS_UNIT (worker unit name), RS_NO_WORKER=1 (no VM / sync stop).
set -u
. "${P85E_DIR:-/home/bobber/source/lra-a100/probe/p85e}/p85e_common.sh"
BABYSIT=${RS_BABYSIT:-/home/bobber/source/lean-refactor/docs/a100_80_babysit.md}; RU=${RS_UNIT:-lra-warmup-release}
L=$ROOT/probe/p85e/release.log; RS=$ROOT/probe/p85e/RELEASE_SEEN
VMIP=${LRA_VM_IP:?set LRA_VM_IP}; VMSSH=(ssh -i "$HOME/.ssh/lra_azure_ed25519" -o IdentitiesOnly=yes -o UserKnownHostsFile="$HOME/.ssh/known_hosts_lra_azure" -o StrictHostKeyChecking=yes -o BatchMode=yes -o ConnectTimeout=15 "${LRA_VM_USER:?set LRA_VM_USER}@$VMIP")
SQ=$ROOT/probe/a100-upload/sqvm; CLIMB=$ROOT/probe/a100-upload/climb/climb_stop.sh
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$(id -u)} DBUS_SESSION_BUS_ADDRESS=${DBUS_SESSION_BUS_ADDRESS:-unix:path=/run/user/$(id -u)/bus}
rlog() { echo "[$(date -u +%m-%d\ %H:%M:%S)] $*" | tee -a "$L"; }
if [ "${1:-}" = --worker-vm ]; then   # ---- the detached part: VM squeeze + GB10 sync ($2 = the A100 decision: end | keep)
  rlog "worker: VM squeeze + sync stop (A100 decision ${2:-end})"
  if [ "${2:-end}" = end ] && [ -f "$CLIMB" ]; then rlog "climb_stop.sh release: $(CLIMB_FROM_RELEASE=1 timeout 150 bash "$CLIMB" release 2>&1 | tail -n 3 | tr '\n' ' ')"
  else
    mkdir -p "$(dirname "$CLIMB")"; echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) release warmup_stop_at_release.sh (A100 kept)" > "$(dirname "$CLIMB")/.VM_RELEASED.tmp" \
      && mv "$(dirname "$CLIMB")/.VM_RELEASED.tmp" "$(dirname "$CLIMB")/VM_RELEASED" && rlog "climb marker VM_RELEASED written (climb_stop.sh not run: A100 kept)"
  fi
  out=$(timeout 120 "${VMSSH[@]}" 'bash -s' 2>&1 <<'VM'
export XDG_RUNTIME_DIR=/run/user/$(id -u)
for u in $(systemctl --user list-units 'lra-sqvm-*' --plain --no-legend | awk '{print $1}'); do
  case "$u" in lra-sqvm-loop*) ;; *) systemctl --user stop "$u" && echo "stopped $u";; esac
done
touch /scratch/sqvm/loop/STOP /scratch/sqvm/loop/CLIMB_STOPPED && echo "STOP + CLIMB_STOPPED touched"
for i in $(seq 9); do systemctl --user is-active -q lra-sqvm-loop || break; sleep 10; done
for u in $(systemctl --user list-units 'lra-sqvm-loop*' --plain --no-legend | awk '{print $1}'); do
  systemctl --user is-active -q "$u" && { systemctl --user stop "$u"; echo "stopped $u (still active after 90 s)"; }
done
echo "VM lra-sqvm units now: $(systemctl --user list-units 'lra-sqvm-*' --plain --no-legend | awk '{print $1":"$4}' | tr '\n' ' ')"
VM
)
  rlog "VM: $(tr '\n' ';' <<< "$out")"
  touch "$SQ/STOP"; rlog "GB10: $SQ/STOP touched (the sync does one last pull + merge)"
  for i in $(seq 30); do
    act=$(systemctl --user list-units 'lra-sqvm-*' --plain --no-legend 2>/dev/null | awk '$3=="active"{print $1}')
    [ -z "$act" ] && break; sleep 10
  done
  for u in $act; do systemctl --user stop "$u" && rlog "GB10: stopped $u (still active after 300 s)"; done
  if [ "${2:-end}" = keep ] && [ -f "$SQ/sync2.sh" ]; then   # climb_stop.sh's last pull + merge after the VM stop (STOP present: no push)
    timeout 900 nice -n 19 /bin/bash "$SQ/sync2.sh" >> "$SQ/sync.log" 2>&1; rlog "GB10: final pull + merge rc $?"
  fi
  rlog "worker done; GB10 lra-sqvm units active: $(systemctl --user list-units 'lra-sqvm-*' --plain --no-legend 2>/dev/null | awk '$3=="active"{print $1}' | tr '\n' ' ')"
  exit 0
fi
MODE=auto; KEEPDRV=0; NEED=${NEED:-375}; DRY=0
while [ $# -gt 0 ]; do case "$1" in
  --end-a100) MODE=end;; --keep-a100) MODE=keep;; --keep-driver) KEEPDRV=1;; --need) NEED=$2; shift;; --dry) DRY=1;;
  *) echo "usage: $0 [--end-a100|--keep-a100] [--keep-driver] [--need USD] [--dry]"; exit 2;; esac; shift; done
NOW=$(date +%s); END=$(end_at)
CR=$(timeout 60 vastai show user --raw 2>/dev/null | python3 -c "import json,sys; d=json.load(sys.stdin); print('%.2f' % float(d['credit']))" 2>/dev/null)
DPH=$(timeout 60 vastai show instance $ID0 --raw 2>/dev/null | python3 -c "import json,sys; d=json.load(sys.stdin); print('%.3f' % float(d.get('dph_total') or 0))" 2>/dev/null)
case "$DPH" in ''|0.000) DPH=3.92;; esac
read -r LEFT WHY < <(python3 -c "
c, dph, need, h = '${CR}', float('$DPH'), float('$NEED'), max(0.0, ($END - $NOW) / 3600)
if not c: print('nan credit unreadable')
else:
    left = float(c) - dph * h; print('%.2f' % left, 'credit \$%s - \$%.2f/h x %.1f h to END_AT = \$%.2f vs need \$%.0f' % (c, dph, h, left, need))")
case "$MODE" in
  end) DEC=end; WHY2="--end-a100";;
  keep) DEC=keep; WHY2="--keep-a100";;
  *) if [ "$LEFT" = nan ]; then DEC=end; WHY2="credit unreadable: the official run comes first";
     elif python3 -c "import sys; sys.exit(0 if float('$LEFT') >= float('$NEED') else 1)"; then DEC=keep; WHY2="credit suffices";
     else DEC=end; WHY2="credit short"; fi;;
esac
SUM="release stop: VM squeeze + sync stop now; A100 climb $DEC ($WHY2; $WHY)$( [ $DEC = end ] && echo "; driver $([ $KEEPDRV = 1 ] && echo 'left to finish' || echo 'ended early (export only)')")"
echo "$SUM"
[ $DRY = 1 ] && { echo "(--dry: nothing done)"; exit 0; }
S=$(mktemp); printf '\n- %s UTC (warmup_stop_at_release.sh, BEFORE acting): %s\n' "$(date -u +%Y-%m-%dT%H:%M)" "$SUM" > "$S"
flock -w 60 /tmp/babysit.lock -c "cat $S >> $BABYSIT"; rm -f "$S"
rlog "$SUM"
python3 -c "
import json, time
json.dump({'t': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), 'decision': '$DEC', 'mode': '$MODE', 'credit': '${CR}', 'need': float('$NEED'),
           'dph': float('$DPH'), 'end_at': $END, 'keep_driver': $KEEPDRV}, open('$RS.tmp', 'w'))" && mv "$RS.tmp" "$RS"
if [ "${RS_NO_WORKER:-0}" = 1 ]; then echo "(RS_NO_WORKER: VM squeeze + sync NOT stopped)"
else
  systemctl --user reset-failed "$RU" > /dev/null 2>&1
  if systemd-run --user --unit "$RU" --collect -p RuntimeMaxSec=900 -p CPUWeight=20 -p MemoryMax=1G --working-directory="$ROOT" \
       -E PATH="/home/bobber/miniconda3/bin:/usr/bin:/bin" -E HOME="$HOME" /usr/bin/bash "$PD/warmup_stop_at_release.sh" --worker-vm $DEC > /dev/null 2>&1; then
    echo "VM squeeze + sync: stopping in the detached unit $RU (<= 15 min; log $L)"
  else
    echo "systemd-run FAILED for the VM stop: run in the background instead: bash $PD/warmup_stop_at_release.sh --worker-vm $DEC"
  fi
fi
if [ $DEC = end ]; then
  pre=$( [ -e "$FINAL_NOW" ] && cat "$FINAL_NOW")
  out=$(bash "$PD/p85e_stop_all.sh" $([ $KEEPDRV = 1 ] && echo now || echo end-driver) release 2>&1 | tail -n 1); echo "A100: $out"; rlog "A100: $out"
  if [ -n "$pre" ] && [ $KEEPDRV = 0 ] && grep -q "final v3: start" "$ROOT/probe/p85e/final.log" 2>/dev/null; then   # a final already fired in now mode
    if resolve; then o=$(bsh "bash /workspace/p85e/p85e_ctl.sh end-driver" 60 | tail -n 1); echo "A100 driver (final already running): $o"; rlog "driver: $o"
    else echo "A100 driver: box not reachable now ($ST): end it with: bash $PD/p85e_stop_all.sh end-driver (or ssh: p85e_ctl.sh end-driver)"; fi
  fi
else
  echo "A100: KEPT climbing (END_AT $(hm "$END") UTC); lra-warmup-resetwatch re-checks credit - cost to END_AT >= \$$NEED every 10 min and ends it when short. Official script note: run it with P85B_END=\"$(date -u -d @$END '+%Y-%m-%d %H:%M UTC')\" so its credit math counts this box."
  rlog "A100 kept"
fi
