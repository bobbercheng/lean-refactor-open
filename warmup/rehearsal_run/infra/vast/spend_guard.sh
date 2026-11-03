#!/usr/bin/env bash
# Hard stop-loss for a vast.ai rental (review 2026-10-28, finding 1: every "KEPT for the operator" exit, every finalize block and the
# bootstrap's exit 4 left the instance billing; the operator's "stop by ~$70" of the $74.35 credit was enforced by nothing). Armed by
# provision.sh the moment an instance is rented (unit lra-a100-spendguard); runs until no instance is listed.
# Every GUARD_POLL_S (60 s) it reads `vastai show user` (credit) and `vastai show instances`. A STOP REASON is
#   * spend since the rental (credit at arming - credit now) >= SPEND_CAP ($68), or credit < CREDIT_FLOOR ($5), or
#   * a KEPT marker probe/a100-kept-<id> is older than KEPT_GRACE_MIN (45) and probe/a100-ack-<id> does not exist, or
#   * probe/a100-stop-now exists (the operator's manual kill switch: destroys at once).
# ASK BEFORE DESTROY (operator 2026-10-30 20:50 UTC: "It should ask me to confirm it before deleting unless it's idle"): on any other
# stop reason it destroys EVERY listed instance only when the operator confirmed (probe/a100-destroy-ok-<id> for every listed id) or
# every instance has been IDLE for IDLE_MIN (30) minutes in a row: running, vast gpu_util < IDLE_GPU (5) and cpu_util < IDLE_CPU (5),
# and BUSY_CHECK (optional command; exit 1 = the run reports idle, e.g. no driver / agent process in the GCS status) agrees; any
# unreadable signal counts as busy. While busy it keeps billing, logs ASK and pushes to the private ntfy topic at once and every
# REMIND_MIN (30) minutes. (vast itself stops, not deletes, an instance when the credit reaches $0.)
# Before destroying it writes probe/a100-pause-<id> (the sentry's ladder must not fight the stop), runs the optional PRE_DESTROY hook
# (the rehearsal's final results pull, bounded by PRE_DESTROY_MAX_S), then CONFIRM=yes FORCE=yes destroy.sh (verified gone, 3 attempts),
# stops the sentry / bid / bridge / health units and logs CREDIT-STOP (probe/a100-spend-guard.log, accounting/a100_poc.md). A failed
# destroy is retried every poll and logged DESTROY-FAILED (the operator must act). Every reading is logged once per LOG_EVERY polls.
#   infra/vast/spend_guard.sh INSTANCE_ID CREDIT_AT_RENTAL          (unit lra-a100-spendguard; log probe/a100-spend-guard.log)
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd); cd "$ROOT" || exit 2
ID=${1:?instance id}; C0=${2:?credit at rental}
SPEND_CAP=${SPEND_CAP:-68}; CREDIT_FLOOR=${CREDIT_FLOOR:-5}; KEPT_GRACE_MIN=${KEPT_GRACE_MIN:-45}; POLL=${GUARD_POLL_S:-60}; LOG_EVERY=${LOG_EVERY:-10}
L=probe/a100-spend-guard.log; ACC=accounting/a100_poc.md
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
# a reply without a `credit` field (an error object, a changed API) prints NOTHING: "unreadable", never $0.00 (which would read as "credit
# below the floor" and destroy a healthy rental; verify 2026-10-28)
credit() { vastai show user --raw 2>/dev/null | python3 -c "import json, sys; d = json.load(sys.stdin); print('%.2f' % float(d['credit'])) if isinstance(d, dict) and d.get('credit') is not None else None" 2>/dev/null; }
instances() { vastai show instances --raw 2>/dev/null | python3 -c "
import json, sys
try:
    rows = json.load(sys.stdin)
except Exception:
    print('?'); sys.exit()
u = lambda v: '?' if v is None else '%.1f' % float(v)
print(' '.join(f\"{r.get('id')}:{r.get('actual_status') or '?'}:{float(r.get('dph_total') or 0):.3f}:{u(r.get('gpu_util'))}:{u(r.get('cpu_util'))}\" for r in rows))" 2>/dev/null; }
stop_units() { systemctl --user stop "lra-a100-sentry$U" "lra-a100-bid$U" "lra-bridge$U" "lra-health$U" "lra-a100-watch$U" 2>/dev/null; true; }
destroy_all() {   # $1 = reason; destroys every listed instance; returns 0 when none is listed afterwards
  local reason=$1 ids ok=1 i id
  ids=$(instances); [ "$ids" = "?" ] && { log "vast unreadable while stopping ($reason): retry next poll"; return 1; }
  for i in $ids; do id=${i%%:*}; touch "probe/a100-pause-$id"; done
  if [ -n "${PRE_DESTROY:-}" ]; then
    log "pre-destroy hook ($PRE_DESTROY, at most ${PRE_DESTROY_MAX_S:-600}s)"
    local first=${ids%% *}; first=${first%%:*}
    timeout "${PRE_DESTROY_MAX_S:-600}" bash -c "${PRE_DESTROY//\{ID\}/$first}" >> "$L" 2>&1 || log "pre-destroy hook rc $? (continuing with the destroy)"
    PRE_DESTROY=""   # once
  fi
  for i in $ids; do
    id=${i%%:*}
    if CONFIRM=yes FORCE=yes "$HERE/destroy.sh" "$id" >> "$L" 2>&1; then log "destroyed $id ($reason)"; else log "DESTROY-FAILED $id ($reason): still listed, retrying next poll"; ok=0; fi
  done
  [ "$ok" = 1 ] || return 1
  ids=$(instances); [ -z "$ids" ] || { log "instances still listed after the destroy: $ids"; return 1; }
  return 0
}
log "spend guard on $ID: credit at rental \$$C0, cap \$$SPEND_CAP spent, floor \$$CREDIT_FLOOR, kept grace ${KEPT_GRACE_MIN} min, poll ${POLL}s"
# 2026-10-30 20:24 UTC this guard destroyed a healthy rehearsal: its belt (dph x running time since the arming) passed the $68 cap
# armed at the 01:19 rental although the operator had topped up twice (credit $55.44) and two fresh runs had started. Now:
#   spent  = the sum of credit DROPS since the arming (a top-up is logged, never counted, never offsets real spend);
#   belt   = dph x running time only while the credit reading has not moved for STALE_S seconds (stale credit; default 1800), reset when it moves;
#   warn   = at 80% and 95% of the cap: a WARN line + a push to the private ntfy topic (the operator hears before any destroy).
n=0; stopping=""; gone=0; est=0; last_t=$(date +%s); prevc=$C0; spent_acc=0; last_move=$(date +%s); warned=0
STALE_S=${STALE_S:-1800}; case "$STALE_S" in (*[!0-9]*|"") STALE_S=1800;; esac; NTFY=${GUARD_NTFY-$(cat probe/a100-ntfy-topic 2>/dev/null)}
IDLE_MIN=${IDLE_MIN:-30}; IDLE_GPU=${IDLE_GPU:-5}; IDLE_CPU=${IDLE_CPU:-5}; REMIND_MIN=${REMIND_MIN:-30}; quiet_since=0; asked=0
busy() {   # $1 = the instances line (id:status:dph:gpu:cpu ...); returns 1 only when every instance is affirmatively idle, else 0 (busy/unknown)
  python3 -c "
import sys
for i in '$1'.split():
    p = i.split(':')
    if len(p) < 5 or p[1] != 'running': sys.exit(0)
    try: g, c = float(p[3]), float(p[4])
    except ValueError: sys.exit(0)
    if g >= $IDLE_GPU or c >= $IDLE_CPU: sys.exit(0)
sys.exit(1)" && return 0
  [ -z "${BUSY_CHECK:-}" ] && return 1
  timeout 180 bash -c "$BUSY_CHECK" > /dev/null 2>&1; [ $? = 1 ] && return 1
  return 0
}
push() { [ -n "$NTFY" ] && curl -fsS -m 20 -H "Title: A100 spend guard" -H "Priority: high" -d "$*" "https://ntfy.sh/$NTFY" >/dev/null 2>&1; true; }
while :; do
  c=$(credit); ids=$(instances); n=$((n + 1))
  if [ -z "$ids" ] && [ -n "$c" ]; then
    gone=$((gone + 1))
    if [ "$gone" -ge 3 ]; then
      [ -n "$stopping" ] && { stop_units; log "CREDIT-STOP done: no instance listed (credit \$$c, spent \$$(python3 -c "print('%.2f' % ($C0 - $c))"))"; printf -- "- %s UTC spend guard: %s; credit \$%s, spent \$%s\n" "$(date -u +%Y-%m-%dT%H:%M)" "$stopping" "$c" "$(python3 -c "print('%.2f' % ($C0 - $c))")" >> "$ACC"; }
      log "no instance listed: spend guard exits (credit \$$c)"; exit 0
    fi
    sleep "$POLL"; continue
  fi
  gone=0
  if [ -z "$c" ] || [ "$ids" = "?" ]; then log "vast unreadable (credit '$c', instances '$ids')"; sleep "$POLL"; continue; fi
  read -r spent_acc prevc moved < <(python3 -c "
c, p, a = float('$c'), float('$prevc'), float('$spent_acc')
if c < p - 0.004: a += p - c
print('%.4f %.2f %d' % (a, c, 1 if abs(c - p) > 0.004 else 0))")
  python3 -c "import sys; sys.exit(0 if float('$c') > float('${prevc_old:-$c}') + 0.5 else 1)" 2>/dev/null && log "top-up seen: credit up to \$$c (spend so far \$$spent_acc unchanged)"
  prevc_old=$c; spent=$(printf '%.2f' "$spent_acc")
  # belt to the credit reading (verify 2026-10-28: a stale `credit` would never trip the cap): the metered estimate sum(dph x running time)
  # from the arming; it trips the same cap, so it can only fire earlier than the credit when the credit stops moving
  now=$(date +%s); [ "$moved" = 1 ] && { last_move=$now; est=0; }
  stale=$(( (now - last_move) >= STALE_S ? 1 : 0 ))
  prev_est=$est; [ "$stale" = 1 ] && est=$(python3 -c "
e = float('$est'); dt = max(0, $now - $last_t)
for i in '$ids'.split():
    iid, st, dph = i.split(':')[:3]
    if st == 'running': e += float(dph) * dt / 3600
print('%.6f' % e)" 2>/dev/null); [ -n "$est" ] || est=$prev_est; last_t=$now
  tot=$(python3 -c "print('%.2f' % ($spent_acc + $est))")
  for lvl in 80 95; do
    if [ "$warned" -lt "$lvl" ] && python3 -c "import sys; sys.exit(0 if $tot >= $SPEND_CAP * $lvl / 100 else 1)"; then
      warned=$lvl; log "WARN guard at ${lvl}% of its cap: \$$tot of \$$SPEND_CAP (spent \$$spent, stale-credit belt \$$(printf '%.2f' "$est")); at 100% it asks the operator (destroys alone only when idle for ${IDLE_MIN} min)"
      push "A100 spend guard at ${lvl}% of its cap: \$$tot of \$$SPEND_CAP. At 100% it ASKS you before deleting (it deletes alone only after ${IDLE_MIN} idle minutes; credit \$$c). Raise SPEND_CAP or top up and re-arm."
    fi
  done   # full precision: a 2-decimal print would round each poll's cents away and never accumulate
  [ $((n % LOG_EVERY)) = 1 ] && log "credit \$$c, spent \$$spent (metered estimate \$$(printf '%.2f' "$est")) of \$$SPEND_CAP; $ids"
  why=""
  python3 -c "import sys; sys.exit(0 if $spent >= $SPEND_CAP else 1)" && why="spend \$$spent >= cap \$$SPEND_CAP"
  python3 -c "import sys; sys.exit(0 if $tot >= $SPEND_CAP and $est > 0 else 1)" && why="spend \$$spent + stale-credit belt \$$(printf '%.2f' "$est") (credit unchanged for >= ${STALE_S} s) >= cap \$$SPEND_CAP"
  python3 -c "import sys; sys.exit(0 if $c < $CREDIT_FLOOR else 1)" && why="credit \$$c < floor \$$CREDIT_FLOOR"
  [ -e probe/a100-stop-now ] && why="probe/a100-stop-now exists (manual stop)"
  for i in $ids; do
    id=${i%%:*}; k="probe/a100-kept-$id"
    if [ -e "$k" ] && [ ! -e "probe/a100-ack-$id" ] && [ $(( ( $(date +%s) - $(stat -c %Y "$k") ) / 60 )) -ge "$KEPT_GRACE_MIN" ]; then
      why="instance $id KEPT for more than ${KEPT_GRACE_MIN} min without probe/a100-ack-$id ($(tail -n 1 "$k"))"
    fi
  done
  go=""
  if [ -n "$why" ]; then
    [ -e probe/a100-stop-now ] && go="manual stop"
    if [ -z "$go" ]; then
      allok=1; for i in $ids; do [ -e "probe/a100-destroy-ok-${i%%:*}" ] || allok=0; done
      [ "$allok" = 1 ] && go="operator confirmed (probe/a100-destroy-ok-<id>)"
    fi
    if [ -z "$go" ]; then
      now=$(date +%s)
      if busy "$ids"; then quiet_since=0; else [ "$quiet_since" = 0 ] && quiet_since=$now; fi
      [ "$quiet_since" != 0 ] && [ $((now - quiet_since)) -ge $((IDLE_MIN * 60)) ] && go="idle for ${IDLE_MIN} min (gpu < ${IDLE_GPU}, cpu < ${IDLE_CPU}${BUSY_CHECK:+, run idle})"
    fi
    if [ -z "$go" ]; then
      if [ "$asked" = 0 ] || [ $((now - asked)) -ge $((REMIND_MIN * 60)) ]; then
        asked=$now; first=${ids%% *}; first=${first%%:*}
        log "ASK: $why; NOT destroying: the instance is busy or not yet idle ${IDLE_MIN} min (quiet since ${quiet_since}); billing continues; to destroy: touch probe/a100-destroy-ok-$first; to continue: re-arm with a higher SPEND_CAP; $ids"
        push "A100 over its guard limit ($why) but BUSY: NOT deleted, still billing (credit \$$c). Reply to Claude: delete (touch probe/a100-destroy-ok-$first) or raise the cap. It deletes alone only after ${IDLE_MIN} idle minutes."
      fi
      why=""
    fi
  else quiet_since=0; asked=0
  fi
  if [ -n "$why" ]; then
    [ -n "$stopping" ] || log "CREDIT-STOP: $why; $go; destroying every instance ($ids)"
    stopping="CREDIT-STOP: $why"
    if destroy_all "$why"; then stop_units; log "CREDIT-STOP done: all instances destroyed (credit \$$c, spent \$$spent)"
      printf -- "- %s UTC spend guard: %s; all instances destroyed; credit \$%s, spent \$%s\n" "$(date -u +%Y-%m-%dT%H:%M)" "$why" "$c" "$spent" >> "$ACC"; exit 0; fi
  fi
  sleep "$POLL"
done
