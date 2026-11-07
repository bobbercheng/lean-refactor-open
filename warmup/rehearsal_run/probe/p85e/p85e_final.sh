#!/usr/bin/env bash
# GB10 unit lra-p85e-final (v3, 2026-11-01 ~00:00 UTC; operator 2026-10-31 23:40 "Keep A100 do warm-up climbing until the board is reset
# on Nov 1"): ARMED until the first of END_AT (probe/p85e/END_AT, re-read every 30 s; default and cap 2026-11-02 00:00 UTC) or the trigger
# file probe/p85e/FINAL_NOW (p85e_stop_all.sh: the release command, the board-reset watcher, a manual stop). Then: END_AT=now on the box
# (the v3 scheduler stops its sessions within ~20 s), STOP + STOP_NOW (a draining v2 instance's sessions too), [end-driver: the p85b driver
# ended early by /workspace/package_stop_host.sh RUN_DIR 0 (export only) and its real summary.json awaited], final rsync of OUT/ +
# probe/runs/p85b-* + /workspace/p85e into the GB10 mirrors (retried), the pick (no Lean) over the open-line roots incl. the p85e twin root,
# then the hold probe/a100-hold-p85e-58565100 is REMOVED so lra-a100-watch-p85b-ms2 releases the box once the driver's summary.json
# exists. Budget after the trigger: 20 min (+20 min in end-driver mode); a failing pull keeps the hold (salvage pulls every 60 s) only until
# that budget; the unit's hard end is 00:25 Nov 2 and its ExecStopPost (p85e_unhold.sh) removes the hold on any exit.
#   p85e_final.sh                     the armed run (the unit)
#   p85e_final.sh now [now|end-driver] at once (the transient lra-p85e-stopall fallback of p85e_stop_all.sh when this unit is not active)
# Kept from v2: box re-resolved from vastai (never probe/a100-instance-id), STOP retried 3x, pull until all three rsyncs return 0, trap
# TERM/INT/HUP moves the hold once the lock is held, single run per lock /tmp/p85e-final.lock.
set -u
. "${P85E_DIR:-/home/bobber/source/lra-a100/probe/p85e}/p85e_common.sh"
PLOG=$ROOT/probe/p85e/final.log
MODE=${1:-}; SMODE=${2:-now}; WHY="manual ($MODE ${2:-})"
HARD=${P85E_HARD:-$((CAP_EPOCH + 1500))}; RETRY_S=${P85E_RETRY_S:-20}; POLL_S=${P85E_POLL_S:-60}; ARM_S=${P85E_ARM_S:-30}
if [ "$MODE" != now ]; then
  plog "final v3 armed: fires at END_AT $(hm "$(end_at)") UTC or on $(basename "$FINAL_NOW"); hard end $(hm "$HARD") UTC"
  while :; do
    if [ -e "$FINAL_NOW" ]; then read -r SMODE _ WHY_ < "$FINAL_NOW"; WHY="FINAL_NOW: $(cut -d' ' -f3- "$FINAL_NOW" | head -c 120)"; break; fi
    [ "$(date +%s)" -ge "$(end_at)" ] && { SMODE=now; WHY="END_AT $(hm "$(end_at)") reached"; break; }
    sleep "$ARM_S"
  done
fi
case "$SMODE" in now|end-driver) ;; soft) SMODE=now;; *) SMODE=now;; esac
T0=$(date +%s); BUDGET=${P85E_BUDGET_S:-1200}; [ "$SMODE" = end-driver ] && BUDGET=$((BUDGET + 1200))
DEADLINE=${P85E_DEADLINE:-$((T0 + BUDGET))}; [ "$DEADLINE" -gt $((HARD - 120)) ] && DEADLINE=$((HARD - 120)); LAST_TRY=$((DEADLINE - 180))
exec 8> "$LOCKDIR/p85e-final.lock"; flock -n 8 || { plog "another p85e final holds the lock: it does the stop, pull and hold removal; exit"; exit 0; }
[ -e "$HOLD" ] || [ "$MODE" = now ] || { plog "hold already removed (a stop-all ran): nothing to do"; touch "$FINAL_DONE"; exit 0; }
unhold() {   # $1 = suffix of the retired name, $2 = log note
  mkdir -p probe/retired-a100-holds
  [ -e "$HOLD" ] && mv "$HOLD" "probe/retired-a100-holds/$(basename "$HOLD").$(date -u +%m%d%H%M)${1:-}" \
    && plog "hold removed${2:-}: the watch releases the box after the driver's summary.json"
  true
}
STOPPED=0
on_sig() { trap - TERM INT HUP; plog "final: SIG$1 received$( [ "$STOPPED" = 1 ] && echo ' after STOP was sent')"; unhold .trap " (SIG$1 trap)"; exit 143; }
trap 'on_sig TERM' TERM; trap 'on_sig INT' INT; trap 'on_sig HUP' HUP
plog "final v3: start ($WHY; mode $SMODE; no new pull try after $(hm $LAST_TRY), deadline $(hm $DEADLINE) UTC)"
set_end_local "$T0" "final: $WHY"
if [ "${P85E_STOPALL:-0}" = 1 ]; then   # the transient fallback: the armed unit is not needed any more (its ExecStopPost skips: lock held)
  $SYSCTL --user stop lra-p85e-final > /dev/null 2>&1; plog "stop-all: armed unit lra-p85e-final stopped"
fi
rc=1
while :; do   # a vastai or Wi-Fi flake must not skip the stop and the pull
  resolve; rc=$?
  { [ $rc = 0 ] || [ $rc = 2 ]; } && break
  [ "$(date +%s)" -ge "$LAST_TRY" ] && break
  plog "box not reachable ($ST $IP:$PT): retry in ${RETRY_S}s"; sleep "$RETRY_S"
done
PULLED=0; tries=0
pull_try() {   # one bounded pull_all; sets PULLED=1 on success
  local now left r; now=$(date +%s); left=$((DEADLINE - now)); [ $left -lt 60 ] && left=60
  r=$(pull_all "$left") && PULLED=1; plog "$1: $r"
}
if [ $rc = 0 ]; then
  STOPPED=1
  plog "box END_AT -> now: $(push_end "$T0" final || true)"
  for k in 1 2 3; do   # a dropped ssh must not leave the scheduler without STOP (any reply line means ctl ran: STOP is set)
    out=$(bsh "bash /workspace/p85e/p85e_ctl.sh stop now" 450 | tail -n 1)
    [ -n "$out" ] && break; [ "$(date +%s)" -ge "$LAST_TRY" ] && break
    plog "STOP via ssh got no reply (try $k/3): retry in ${RETRY_S}s"; sleep "$RETRY_S"; resolve > /dev/null || true
  done
  plog "box $IP:$PT: ${out:-NO REPLY to STOP (END_AT=now still stops the v3 sessions)}"
  if [ "$SMODE" = end-driver ]; then   # the p85b driver ended early (export only), then its real summary.json awaited (bounded)
    d=$(bsh "bash /workspace/p85e/p85e_ctl.sh driver" 60)
    if grep -q "^driver [1-9]" <<< "$d" || grep -q "^summary none" <<< "$d"; then
      plog "end-driver: $(tr '\n' ' ' <<< "$d"): ending the driver early (export only)"
      bsh "bash /workspace/p85e/p85e_ctl.sh end-driver" 60 | tail -n 1 | sed 's/^/  /' | tee -a "$PLOG"
    else plog "end-driver: $(tr '\n' ' ' <<< "$d"): nothing to stop"; fi
    WBY=$((DEADLINE - 420))
    while [ "$(date +%s)" -lt "$WBY" ]; do
      r=$(bsh "bash /workspace/p85e/p85e_ctl.sh driver" 60)
      grep -q '^summary real' <<< "$r" && grep -q '^stopper 0' <<< "$r" && { plog "end-driver: real summary.json present"; break; }
      sleep 30; resolve > /dev/null || true
    done
    grep -q '^summary real' <<< "${r:-}" || plog "end-driver: no real summary.json by $(hm $WBY) (the bests are banked in OUT/work; pulling anyway)"
  fi
  while [ $tries -lt 4 ] && [ $PULLED = 0 ]; do
    [ $tries -gt 0 ] && [ "$(date +%s)" -ge "$LAST_TRY" ] && break
    tries=$((tries + 1)); pull_try "final pull $tries/4"
    [ $PULLED = 1 ] && break
    sleep "$RETRY_S"; resolve || plog "re-resolve: $ST $IP:$PT"
  done
  [ $PULLED = 1 ] && plog "p85e sessions: $(python3 -c "
import json
L=[json.loads(l) for l in open('$MIR/ext_sessions.jsonl') if l.strip()]
g=sum(max(0,r.get('main_after',0)-r.get('main_before',0)) for r in L)
print(len(L),'external sessions; summed main gain at their ends', round(g,3))" 2>/dev/null)"
elif [ $rc = 2 ]; then
  plog "instance $ID0 is gone (not in vastai's instance list): no stop / pull possible"; PULLED=gone
else
  plog "box not reachable up to $(hm $LAST_TRY) ($ST $IP:$PT): no stop / pull possible"
fi
do_pick() {
  mkdir -p probe/a100-upload/p85e-final
  local RUNS="probe/a100-reh-p85/out probe/a100-reh-p85b/out probe/a100-upload/squeeze-out probe/a100-reh-p85b-blind/out" t
  [ -d "$MIR/twin/work" ] && RUNS="$RUNS probe/a100-reh-p85e/twin"
  t=$((DEADLINE - $(date +%s))); [ $t -gt 300 ] && t=300; [ $t -lt 30 ] && t=30
  plog "pick: $(timeout $t python3 probe/a100/warmup_upload_measure.py pick --runs $RUNS --dir probe/a100-upload/p85e-final 2>&1 | head -n 1)"
}
do_pick
if [ "$PULLED" != 0 ]; then
  unhold "" ""
else
  push "CRITICAL p85e final: no clean final pull from box $ID0 ($tries tries; box state $ST). The hold stays until $(hm $DEADLINE) UTC (salvage pulls every ${POLL_S} s), then it goes and the watch releases the box. Fallback copy: the box's GCS sidecar snapshot of out-p85b."
  plog "CRITICAL: no clean final pull: hold KEPT; salvage pulls every ${POLL_S} s until $(hm $((DEADLINE - 90))), then the hold goes"
  while [ "$(date +%s)" -lt $((DEADLINE - 90)) ]; do
    sleep "$POLL_S"; [ "$(date +%s)" -lt $((DEADLINE - 90)) ] || break
    if resolve; then pull_try "salvage pull"; [ $PULLED = 1 ] && break; else [ $? = 2 ] && { plog "instance $ID0 gone during salvage"; PULLED=gone; break; }; fi
  done
  if [ "$PULLED" != 0 ]; then do_pick; unhold "" " (after a salvage pull)"
  else unhold .nopull " (budget over without a clean pull)"; fi
fi
touch "$FINAL_DONE"
$SYSCTL --user stop lra-p85e-wbpush > /dev/null 2>&1
plog "final: done"
