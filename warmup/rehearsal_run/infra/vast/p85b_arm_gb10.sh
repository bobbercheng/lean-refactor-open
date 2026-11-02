#!/usr/bin/env bash
# GB10 side of the p85b continuation (operator 2026-10-31 07:15 UTC; docs/open_official_run_runbook.md section 1). Runs as the unit
# lra-a100-p85b-arm (started once; exits after arming). Control plane only (vast API + SSH), never the model path.
#   1. waits, bounded by ARM_UNTIL (default 2026-10-31 19:00 UTC: the box launcher gives up at 18:00), every POLL_S (120 s), for the box's
#      p85b driver: RUN_DIR/LAUNCHED.json and a live `open_package.py run ... --out OUT ` process;
#   2. watch: unit lra-a100-watch-p85b = package_watch.sh ID (TAG=p85b RUN_DIR OUT LOCAL=probe/a100-reh-p85b HOLD_MAX_S=259200; the hold file
#      probe/a100-hold-keepofficial-<ID> stays: at p85b's end the watch pulls, then waits on the hold, never releases before it is removed or
#      72 h pass);
#   3. alarm: unit lra-a100-alarm-p85b (alarm.py on probe/a100-reh-p85b, the p85b run dir / out dir); the p85 alarm unit is stopped once p85's
#      watch logged "run finished" (its run is over; ALARM.log stays);
#   4. the p85 watch (lra-a100-watch) is stopped once it logged "run finished" (its final pull is done): it only waits on the hold file and
#      would DESTROY the box HOLD_MAX_S (72 h) after p85's end (~2026-11-03 15:50 UTC), inside the official run's window;
#   5. spend guard re-armed (unit lra-a100-spendguard restarted): credit now, SPEND_CAP=GUARD_ADD ($40) counted from now (= what the p85 guard
#      had counted + $40), ask-first unchanged (spend_guard.sh), BUSY_CHECK on the a100-p85b status, PRE_DESTROY = a p85b pull;
#   6. babysit entry (lean-refactor docs/a100_80_babysit.md), accounting line, ntfy push.
# Not armed when the box never launches p85b by ARM_UNTIL: the line "NOT ARMED" + a push (p85's units stay as they are).
# Dry run: REH_LOCAL_DIR (the box is a local directory), LRA_FAKE_VAST_BIN, LRA_UNIT_SUFFIX, BABYSIT, ACC, NO_ALARM_LIVE=1.
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3 ssh
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd); cd "$ROOT" || exit 2
ID=${1:-$(cat probe/a100-instance-id 2>/dev/null)}; [ -n "$ID" ] || { echo "no instance id"; exit 2; }
TAG=p85b; RUN_DIR=${RUN_DIR:-/workspace/lra-run-p85b}; OUT=${OUT:-/workspace/out-p85b}; EXPORT_ROOT=${EXPORT_ROOT:-/workspace/lra}
LOCAL=${LOCAL:-probe/a100-reh-p85b}; P85_LOCAL=${P85_LOCAL:-probe/a100-reh-p85}; GUARD_ADD=${GUARD_ADD:-40}; POLL_S=${POLL_S:-120}
ARM_UNTIL=${ARM_UNTIL:-2026-10-31 19:00 UTC}; HOLD_MAX_S=${HOLD_MAX_S:-259200}; LAUNCH_LOG=${LAUNCH_LOG:-/workspace/p85b_launch.log}
BABYSIT=${BABYSIT:-/home/bobber/source/lean-refactor/docs/a100_80_babysit.md}; ACC=${ACC:-accounting/a100_poc.md}
mkdir -p "$LOCAL"; L=$LOCAL/arm.log
log() { echo "[$(date -u -Is)] p85b-arm: $*" | tee -a "$L"; }
NTFY=$(cat probe/a100-ntfy-topic 2>/dev/null); push() { [ -n "$NTFY" ] && [ -z "${REH_LOCAL_DIR:-}" ] && curl -fsS -m 20 -H "Title: A100 p85b" -d "$*" "https://ntfy.sh/$NTFY" > /dev/null 2>&1; true; }
credit() { vastai show user --raw 2>/dev/null | python3 -c "import json, sys; d = json.load(sys.stdin); print('%.2f' % float(d['credit'])) if isinstance(d, dict) and d.get('credit') is not None else None" 2>/dev/null; }
addr() { vastai show instance "$ID" --raw 2>/dev/null | python3 -c "import json, sys; d = json.load(sys.stdin); p = (d.get('ports') or {}).get('22/tcp') or [{}]; print(d.get('actual_status') or '?', d.get('public_ipaddr') or '-', p[0].get('HostPort') or '-')" 2>/dev/null; }
rsh() { if [ -n "${REH_LOCAL_DIR:-}" ]; then (cd "$REH_LOCAL_DIR" && timeout 60 bash -c "$1"); else
  read -r ST IP PT <<< "$(addr)"; [ "$ST" = running ] && [ "$PT" != - ] || return 1
  timeout 60 ssh -i "$HOME/.ssh/id_ed25519" -o BatchMode=yes -o ConnectTimeout=15 -o StrictHostKeyChecking=accept-new -p "$PT" "root@$IP" "$1" 2>/dev/null | grep -v "^Welcome\|^Have fun"; fi; }
deadline=$(date -u -d "$ARM_UNTIL" +%s)
log "waiting for the p85b driver on $ID ($OUT) until $ARM_UNTIL"
said=""
while :; do
  st=$(rsh "[ -f $RUN_DIR/LAUNCHED.json ] && cat $RUN_DIR/LAUNCHED.json; pgrep -f '[o]pen_package.py run .*--out $OUT ' > /dev/null && echo DRIVER-ALIVE; tail -n 1 $LAUNCH_LOG 2>/dev/null | cut -c1-160")
  if grep -q DRIVER-ALIVE <<< "$st" && grep -q launched_at <<< "$st"; then break; fi
  last=$(tail -n 1 <<< "$st"); [ "$last" != "$said" ] && [ -n "$last" ] && { log "box: $last"; said=$last; }
  grep -q "NOT launched\|disarmed" <<< "$st" && { log "NOT ARMED: the box launcher gave up ($last)"; push "p85b not launched on the box: GB10 side not armed ($last)"; exit 1; }
  [ "$(date +%s)" -ge "$deadline" ] && { log "NOT ARMED: no p85b driver by $ARM_UNTIL"; push "p85b: no driver by $ARM_UNTIL; GB10 side not armed"; exit 1; }
  sleep "$POLL_S"
done
LJ=$(grep launched_at <<< "$st" | head -n 1); log "p85b driver alive: $LJ"
WK=$(python3 -c "import json,sys; print(json.loads(sys.argv[1])['workers'])" "$LJ" 2>/dev/null); WHY=$(python3 -c "import json,sys; print(json.loads(sys.argv[1])['workers_why'])" "$LJ" 2>/dev/null)
ENDT=$(python3 -c "import json,sys,time; print(time.strftime('%Y-%m-%dT%H:%MZ', time.gmtime(json.loads(sys.argv[1])['end_at'])))" "$LJ" 2>/dev/null)
# ---- watch
systemctl --user stop "lra-a100-watch-p85b$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-watch-p85b$U" 2>/dev/null
systemd-run --user --unit "lra-a100-watch-p85b$U" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" -E LRA_FAKE_VAST_BIN="${LRA_FAKE_VAST_BIN:-}" -E LRA_UNIT_SUFFIX="$U" \
  -E TAG=$TAG -E RUN_DIR="$RUN_DIR" -E OUT="$OUT" -E EXPORT_ROOT="$EXPORT_ROOT" -E REH_LOCAL_DIR="${REH_LOCAL_DIR:-}" -E LOCAL="$LOCAL" -E POLL_S="${WATCH_POLL_S:-60}" \
  -E PULL_EVERY_S="${PULL_EVERY_S:-300}" -E STALL_MIN="${STALL_MIN:-20}" -E HOLD_MAX_S="$HOLD_MAX_S" \
  bash -c "infra/vast/package_watch.sh $ID >> $LOCAL/watch.out 2>&1" > /dev/null && log "watch armed: lra-a100-watch-p85b$U (HOLD_MAX_S $HOLD_MAX_S; log $LOCAL/watch.log)"
# ---- alarm
systemctl --user stop "lra-a100-alarm-p85b$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-alarm-p85b$U" 2>/dev/null
systemd-run --user --unit "lra-a100-alarm-p85b$U" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" \
  python3 probe/a100-alarm/alarm.py --reh "$LOCAL" --id "$ID" --run-dir "$RUN_DIR" --out-dir "$OUT" ${NO_ALARM_LIVE:+--no-live --no-push} > /dev/null && log "alarm armed: lra-a100-alarm-p85b$U"
# ---- p85's watch and alarm: done
if grep -q "run finished" "$P85_LOCAL/watch.log" 2>/dev/null; then
  for u in "lra-a100-watch$U" "lra-a100-alarm$U"; do systemctl --user is-active -q "$u" && { systemctl --user stop "$u"; log "stopped $u (p85 finished and pulled: $(grep 'run finished' "$P85_LOCAL/watch.log" | tail -n 1 | cut -c1-90))"; }; done
else log "WARN p85's watch has no 'run finished' line yet: lra-a100-watch (HOLD_MAX_S 72 h after p85's end) left running; stop it after its final pull"; fi
# ---- spend guard
c=$(credit); prev=$(grep -oE 'spent \$[0-9.]+' probe/a100-spend-guard.log 2>/dev/null | tail -n 1 | tr -dc '0-9.')
if [ -n "$c" ]; then
  systemctl --user stop "lra-a100-spendguard$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-spendguard$U" 2>/dev/null
  systemd-run --user --unit "lra-a100-spendguard$U" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" -E LRA_FAKE_VAST_BIN="${LRA_FAKE_VAST_BIN:-}" -E LRA_UNIT_SUFFIX="$U" \
    -E SPEND_CAP="$GUARD_ADD" -E CREDIT_FLOOR="${CREDIT_FLOOR:-5}" -E KEPT_GRACE_MIN="${KEPT_GRACE_MIN:-45}" -E GUARD_POLL_S="${GUARD_POLL_S:-60}" \
    -E STALE_S="${STALE_S:-1800}" -E IDLE_MIN="${IDLE_MIN:-30}" -E IDLE_GPU="${IDLE_GPU:-5}" -E IDLE_CPU="${IDLE_CPU:-5}" -E REMIND_MIN="${REMIND_MIN:-30}" \
    -E BUSY_CHECK="${BUSY_CHECK-python3 probe/a100-alarm/run_busy.py --label a100-p85b}" \
    -E PRE_DESTROY="TAG=$TAG LOCAL=$LOCAL RUN_DIR=$RUN_DIR OUT=$OUT EXPORT_ROOT=$EXPORT_ROOT infra/vast/package_watch.sh {ID} pull" -E PRE_DESTROY_MAX_S=600 -E TAG=$TAG -E REH_LOCAL_DIR="${REH_LOCAL_DIR:-}" \
    bash -c "infra/vast/spend_guard.sh $ID $c 2>> probe/a100-spend-guard.log > /dev/null" > /dev/null \
    && log "spend guard re-armed for p85b: cap \$$GUARD_ADD more from credit \$$c (the p85 guard had counted \$${prev:-?}; total \$${prev:+$(python3 -c "print('%.2f' % ($prev + $GUARD_ADD))")}); ask-first, BUSY_CHECK a100-p85b"
else log "WARN vast credit unreadable: the spend guard was NOT re-armed (the p85 guard keeps its \$60 cap); re-arm by hand: docs/open_official_run_runbook.md 1.5"; fi
# ---- records
G=$(grep "spend guard re-armed" "$L" | tail -n 1 | sed 's/.*p85b-arm: //')
{ printf '\n## %s UTC — p85b continuation launched by the armed host launcher; GB10 side armed (p85b_arm_gb10.sh)\n' "$(date -u +'%Y-%m-%d %H:%M')"
  printf -- '- Box: %s (workers %s: %s; end %s; rows and seeds in /workspace/lra-run-p85b/SEED.json; driver log /workspace/lra-run-p85b/driver.log).\n' "$LJ" "$WK" "$WHY" "$ENDT"
  printf -- '- GB10: lra-a100-watch-p85b (HOLD_MAX_S %s, hold file kept), lra-a100-alarm-p85b; %s.\n' "$HOLD_MAX_S" "${G:-spend guard NOT re-armed (see $L)}"
  printf -- '- p85 units: %s\n' "$(grep -E 'stopped lra-a100-(watch|alarm)|WARN p85' "$L" | sed 's/.*p85b-arm: //' | tr '\n' ';')"
  printf -- '- Stop p85b any time (bests kept, export written): ssh the box, `bash /workspace/package_stop_host.sh /workspace/lra-run-p85b [END_S]`.\n'
} >> "$BABYSIT"
printf -- "- %s UTC p85b continuation on %s: workers %s, end %s; %s\n" "$(date -u +%Y-%m-%dT%H:%M)" "$ID" "$WK" "$ENDT" "${G:-guard not re-armed}" >> "$ACC"
push "p85b armed on the GB10: watch + alarm; ${G:-spend guard NOT re-armed}"
log "ARMED"
