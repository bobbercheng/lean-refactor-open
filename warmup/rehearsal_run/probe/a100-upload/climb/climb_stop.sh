#!/usr/bin/env bash
# climb_stop.sh — the ONE stop command of the warm-up climb, GB10 / VM side (2026-10-31 23:50 UTC; operator 23:40 "Keep A100 do warm-up
# climbing until the board is reset on Nov 1"). Returns at once: the work runs DETACHED in the unit lra-climb-stop-<mode> (log climb/stop.log).
#
#   climb_stop.sh release      v2 (2026-11-01 00:40 UTC, review fix): NOT a release entry point any more. THE release command is
#                              bash /home/bobber/source/lra-a100/probe/p85e/warmup_stop_at_release.sh   (it decides the A100: end when
#                              vast credit - box cost to END_AT < need, or when credit is unreadable; ending = the p85b driver ended early
#                              with an export too). Called without CLIMB_FROM_RELEASE=1, `climb_stop.sh release` execs that script.
#                              Called by its worker (CLIMB_FROM_RELEASE=1): (1) the VM squeeze stops NOW (STOP + CLIMB_STOPPED files,
#                              systemctl stop lra-sqvm-ctl + lra-sqvm-loop on the closed-track VM: the VM is the closed official run's box); (2) the
#                              GB10 sync does its last pull + merge (no push) and ends; (3) the A100 is NOT touched here (decided and
#                              stopped by warmup_stop_at_release.sh; probe/p85e/RELEASE_SEEN). The GB10 dialect loop goes on.
#   climb_stop.sh board-reset  the board reset was observed (the guard lra-climb-guard or lra-warmup-resetwatch runs this): everything
#                              stops: VM squeeze, sync (last pull + merge), dialect loop (after its current pass), and the A100 climb
#                              (climb/p85e_stop_cmd). v2: also writes climb/BOARD_RESET (if absent) so the pick watcher wakes.
#   climb_stop.sh cap          the hard cap 2026-11-02 00:00 UTC: VM squeeze, sync, dialect loop (the A100 side ends by its own deadline).
#   climb_stop.sh status       units (GB10 + VM), markers, the last lines of stop.log / guard.log.
# Markers in climb/: VM_RELEASED (release), STOPPED (board-reset / cap), A100_STOPPED, BOARD_RESET (guard evidence). The v2 start scripts
# refuse to start while a marker applies. Idempotent: safe to run twice.
set -uo pipefail
export XDG_RUNTIME_DIR=/run/user/$(id -u) DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/$(id -u)/bus
A=/home/bobber/source/lra-a100; U=$A/probe/a100-upload; C=$U/climb; LOG=$C/stop.log
VM=${LRA_VM_USER:?set LRA_VM_USER}@${LRA_VM_IP:?set LRA_VM_IP}
E="ssh -i $HOME/.ssh/lra_azure_ed25519 -o IdentitiesOnly=yes -o UserKnownHostsFile=$HOME/.ssh/known_hosts_lra_azure -o StrictHostKeyChecking=yes -o BatchMode=yes -o ConnectTimeout=15"
mode=${1:-status}
log() { echo "[$(date -u +%Y-%m-%dT%H:%M:%SZ)] [$mode] $*"; }
mark() { echo "$(date -u +%Y-%m-%dT%H:%M:%SZ) $mode ${2:-}" > $C/.$1.tmp && mv $C/.$1.tmp $C/$1; }

if [ "$mode" = status ]; then
  echo "GB10 units:"; for u in lra-sqvm-sync lra-dialect-loop lra-climb-guard lra-climb-stop-release lra-climb-stop-board-reset lra-climb-stop-cap; do
    printf '  %-28s %s\n' $u "$(systemctl --user show $u -p ActiveState --value 2>/dev/null) $(systemctl --user show $u -p MainPID --value 2>/dev/null)"; done
  echo "markers:"; for m in VM_RELEASED STOPPED A100_STOPPED BOARD_RESET; do [ -f $C/$m ] && echo "  $m: $(head -c 300 $C/$m)"; done
  echo "VM:"; timeout 40 $E $VM 'export XDG_RUNTIME_DIR=/run/user/$(id -u); for u in lra-sqvm-loop lra-sqvm-ctl; do echo "  $u $(systemctl --user show $u -p ActiveState --value)"; done; ls /scratch/sqvm/loop/STOP /scratch/sqvm/loop/CLIMB_STOPPED /scratch/sqvm/loop/JOBS 2>/dev/null | sed "s/^/  file /"' || echo "  (VM unreachable)"
  echo "p85e: hold $([ -f $A/probe/a100-hold-p85e-58565100 ] && echo PRESENT || echo removed)"
  echo "--- stop.log"; tail -n 12 $LOG 2>/dev/null; echo "--- guard.log"; tail -n 4 $C/guard.log 2>/dev/null
  exit 0
fi
case "$mode" in release|board-reset|cap) ;; *) echo "usage: $0 release|board-reset|cap|status"; exit 2;; esac
REL=/home/bobber/source/lra-a100/probe/p85e/warmup_stop_at_release.sh
if [ "$mode" = release ] && [ "${CLIMB_FROM_RELEASE:-0}" != 1 ]; then   # v2: ONE release entry point
  echo "climb_stop.sh release is not the release entry point: running THE release command $REL (it stops the VM squeeze + sync through this script and decides the A100)"
  exec /bin/bash "$REL"
fi

if [ "${2:-}" != "--fg" ]; then   # detach: a caller's tool call may be killed after 120-600 s
  unit=lra-climb-stop-$mode
  if systemctl --user is-active -q $unit; then echo "$unit already running (bash $0 status)"; exit 0; fi
  systemctl --user reset-failed $unit 2>/dev/null
  systemd-run --user --unit $unit --collect -p CPUWeight=20 -p MemoryMax=1G -p RuntimeMaxSec=3000 --working-directory=$C \
    -E PATH=$HOME/miniconda3/bin:/usr/local/bin:/usr/bin:/bin -E HOME=$HOME -E CLIMB_FROM_RELEASE=${CLIMB_FROM_RELEASE:-0} -E CLIMB_CALLER=${CLIMB_CALLER:-?} \
    -p StandardOutput=append:$LOG -p StandardError=append:$LOG /bin/bash $C/climb_stop.sh $mode --fg >/dev/null 2>&1 \
    && echo "started $unit (detached); check: bash $C/climb_stop.sh status" || { echo "systemd-run failed: running in the foreground"; exec /bin/bash $C/climb_stop.sh $mode --fg; }
  exit 0
fi

exec 8>$C/stop.lock; flock -w 600 8 || { log "another climb_stop holds the lock for 10 min: giving up"; exit 1; }
log "start"
# (1) the VM squeeze: immediate
vm_stop() {
  local i
  for i in 1 2 3; do
    if timeout 150 $E $VM 'touch /scratch/sqvm/loop/STOP /scratch/sqvm/loop/CLIMB_STOPPED; export XDG_RUNTIME_DIR=/run/user/$(id -u); systemctl --user stop lra-sqvm-ctl lra-sqvm-loop 2>/dev/null; echo "loop=$(systemctl --user show lra-sqvm-loop -p ActiveState --value) ctl=$(systemctl --user show lra-sqvm-ctl -p ActiveState --value)"'; then
      log "VM squeeze stopped (try $i)"; return 0; fi
    log "VM stop try $i failed"; sleep 20
  done
  log "VM squeeze stop FAILED 3x: run by hand on the closed-track VM: touch /scratch/sqvm/loop/STOP; systemctl --user stop lra-sqvm-ctl lra-sqvm-loop"; return 1
}
# (2) the GB10 sync: last pull + merge, no push
sync_stop() {
  touch $U/sqvm/STOP
  local t=0
  while systemctl --user is-active -q lra-sqvm-sync; do
    [ $t -ge 600 ] && { log "sync still active after 10 min: systemctl stop"; systemctl --user stop lra-sqvm-sync; break; }
    sleep 5; t=$((t + 5))
  done
  log "sync ended: $(tail -n 1 $U/sqvm/sync.log)"
  # one more pull + merge after the VM stop (STOP present: sync2.sh skips the push, pulls, merges, exits)
  timeout 900 nice -n 19 /bin/bash $U/sqvm/sync2.sh >> $U/sqvm/sync.log 2>&1; log "final pull + merge rc $? ($(tail -n 1 $U/sqvm/sync.log))"
}
dialect_stop() {
  touch $U/dialect/STOP_LOOP
  local t=0
  while systemctl --user is-active -q lra-dialect-loop; do
    [ $t -ge 1200 ] && { log "dialect loop still active after 20 min: systemctl stop"; systemctl --user stop lra-dialect-loop; break; }
    sleep 10; t=$((t + 10))
  done
  log "dialect loop ended: $(tail -n 1 $U/dialect/logs/loop.log)"
}
a100_stop() {
  local cmd; cmd=$(cat $C/p85e_stop_cmd 2>/dev/null || echo "bash $A/probe/p85e/p85e_stop_all.sh")
  if [ -z "${cmd// }" ]; then log "A100 stop command empty (climb/p85e_stop_cmd): skipped"; return 0; fi
  log "A100 climb stop: $cmd"
  timeout 300 bash -c "$cmd" 2>&1 | tail -n 5 | sed 's/^/    /'
  mark A100_STOPPED "$cmd"
}

case "$mode" in
  release)
    mark VM_RELEASED
    vm_stop; sync_stop
    if [ "${CLIMB_FROM_RELEASE:-0}" = 1 ]; then
      log "A100: decided and stopped by warmup_stop_at_release.sh, not here ($(head -c 300 $A/probe/p85e/RELEASE_SEEN 2>/dev/null || echo 'RELEASE_SEEN not written'))"
    else   # not reached (the dispatcher execs warmup_stop_at_release.sh); kept aligned with it: unreadable credit = end
      need=$(cat $C/official_need_usd 2>/dev/null | tr -dc '0-9.'); need=${need:-375}
      credit=$(timeout 60 vastai show user --raw 2>/dev/null | python3 -c "import json,sys; d=json.load(sys.stdin); print('%.2f' % float(d['credit']))" 2>/dev/null)
      if [ -z "$credit" ]; then log "vast credit UNREADABLE: the A100 climb stops (the official run comes first)"; a100_stop
      elif python3 -c "import sys; sys.exit(0 if float('$credit') < float('$need') else 1)"; then log "vast credit \$$credit < need \$$need: the A100 climb stops"; a100_stop
      else log "vast credit \$$credit >= need \$$need: the A100 climb goes on (until the board reset / the hard cap)"; fi
    fi
    log "dialect loop (GB10, \$0) goes on until the board reset / the hard cap";;
  board-reset)
    mark STOPPED "board reset"
    [ -e $C/BOARD_RESET ] || { mark BOARD_RESET "climb_stop.sh board-reset (caller: ${CLIMB_CALLER:-?}): the pick watcher wakes"; log "BOARD_RESET marker written"; }
    vm_stop; sync_stop; a100_stop; dialect_stop;;
  cap)
    mark STOPPED "hard cap"
    vm_stop; sync_stop; dialect_stop;;
esac
log "done"
