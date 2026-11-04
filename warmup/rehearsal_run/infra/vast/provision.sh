#!/usr/bin/env bash
# Rent + bootstrap with automatic replacement of bad hosts (operator 2026-10-07: "drop the bad instance as early as possible";
# "if [nvtop install] is very slow and time out for the provision, just destroy it and ask for new instance").
# Usage: CONFIRM=yes infra/vast/provision.sh [max_attempts=3]
#   each attempt: cheapest verified interruptible 4xA100-80GB offer whose machine is not in bad_machines.txt, ranked by min_bid plus the
#   host's per-GB bandwidth price over the rehearsal's transfer (~240 GB down, 5 GB up, spread over 12 h; review 2026-10-28: a $0.04/GB
#   host cost ~$5 for 120 GB on 2026-10-08), inet_down_cost <= MAX_DOWN_COST ($/GB), inet_down >= MIN_DOWN Mb/s (500: 191 GB in < 1 h);
#   bid = min_bid + $0.01 (operator rule), then bootstrap.sh (log: probe/a100-bootstrap-<id>.log).
#   bootstrap exit 3 (SSH port never opened / occupied GPUs) or 5 (apt or the download too slow) = bad host, already destroyed -> record its
#   machine, retry (only after destroy.sh verified the id is gone: a still-listed instance stops the loop with a KEPT marker).
#   Any other failure stops with the instance KEPT and a KEPT marker (probe/a100-kept-<id>): the spend guard destroys it after
#   KEPT_GRACE_MIN (45) unless probe/a100-ack-<id> says the operator took it over. On success the instance id is written to
#   probe/a100-instance-id and printed last.
# Money (review 2026-10-28, finding 1): infra/vast/spend_guard.sh (unit lra-a100-spendguard) is armed the moment an instance is rented:
#   spend since the rental >= SPEND_CAP ($68) or credit < CREDIT_FLOOR ($5) -> every instance destroyed, units stopped, CREDIT-STOP logged.
# Outbids (operator 2026-10-09: "We need to take actions immediately for outbid incident next time"): the outbid sentry
# (infra/vast/outbid_sentry.sh, unit lra-a100-sentry) is armed the moment an instance is rented, so a stop starts the bid ladder within
# ~30 s in every phase; a bootstrap cut by a stop is re-run (it resumes the download) once vast runs the instance again, up to 4 times.
# Overrides for the $0 dry run (probe/a100/dry_run.sh): BOOTSTRAP_SH, SERVER_UP_SH (fakes), LRA_FAKE_VAST_BIN (vastai shim),
# LRA_UNIT_SUFFIX (unit names), LRA_NO_BRIDGE=1 (READY without the GB10 TLS bridge: the on-instance package never uses it).
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3 ssh
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
MAX=${1:-3}; BAD=$HERE/bad_machines.txt; touch "$BAD"; CAP=$BID_CAP_DEFAULT
BOOTSTRAP_SH=${BOOTSTRAP_SH:-$HERE/bootstrap.sh}; SERVER_UP_SH=${SERVER_UP_SH:-$HERE/server_up.sh}
ACC=$ROOT/accounting/a100_poc.md; mkdir -p "$ROOT/probe" "$(dirname "$ACC")"
wait_running() {   # 0 when vast runs the instance again (the sentry's ladder fights for it); 1 when gone or the ladder ended at the cap
  local since; since=$(date +%s)
  while :; do
    local s; s=$(vastai show instances --raw 2>/dev/null | python3 -c "import json, sys; i = next((r for r in json.load(sys.stdin) if r.get('id') == $1), None); print('gone' if i is None else i.get('actual_status'))" 2>/dev/null)
    [ "$s" = running ] && return 0
    [ "$s" = gone ] && return 1
    grep -q "SWITCH INSTANCES" <(awk -v t="$(date -u -d "@$since" -Is)" '$1 >= "["t' "$ROOT/probe/a100-sentry.log" 2>/dev/null) && return 1
    [ $(( $(date +%s) - since )) -gt "${WAIT_RUNNING_MAX_S:-7200}" ] && { echo "  instance $1 not running again after 2 h"; return 1; }
    sleep "${POLL_S:-30}"
  done
}
gone() { vastai show instances --raw 2>/dev/null | python3 -c "import json, sys; sys.exit(1 if any(r.get('id') == $1 for r in json.load(sys.stdin)) else 0)" 2>/dev/null; }
DISK=${DISK:-420}; export DISK   # peak on disk = model 178 GiB + Lean envs and toolchains 118 GiB + env archives in flight during a parallel
                                  # restore (<= ~20 GiB) = ~300-318 GiB (55094025 ran at create.sh's 300 GB default: 99% full), plus the
                                  # rehearsal's LeanPool build (~15 GiB .lake + clone + toolchain + Mathlib cache) and its pack output (~10 GiB)
                                  # -> 420 (review 2026-10-28). Disk costs ~$0.0005/GB/h; a model re-download costs bandwidth and ~20 min of GPU.
CPU_MIN=${CPU_MIN:-64}; MIN_DOWN=${MIN_DOWN:-500}; MAX_DOWN_COST=${MAX_DOWN_COST:-0.01}
Q="num_gpus=4 gpu_ram>=80 gpu_name=A100_SXM4 cpu_cores_effective>=$CPU_MIN disk_space>=$DISK"
# VERIFIED=any admits unverified/deverified hosts (operator 2026-10-09 ~21:05, no verified 4xA100 offer listed: "can we get new vast
# instance?"); MIN_DOWN (Mb/s) keeps out hosts whose link cannot fetch the 190.8 GB checkpoint in reasonable time (MIN_DOWN=0 disables)
Q="$Q${VERIFIED:+ verified=$VERIFIED}"; [ "$MIN_DOWN" != 0 ] && Q="$Q inet_down>=$MIN_DOWN"
[ "${CONFIRM:-}" = yes ] || { echo "dry run: set CONFIRM=yes (rents up to $MAX instances in turn); query: $Q"; exit 0; }
# the manual kill switch of an earlier rental would destroy the new one within a minute of the spend guard's arming: remove it first
[ -e "$ROOT/probe/a100-stop-now" ] && { echo "refused: probe/a100-stop-now exists (the spend guard's manual stop); rm it before renting"; exit 2; }
for a in $(seq 1 "$MAX"); do
  CREDIT=$(vastai show user --raw | python3 -c 'import json,sys; d=json.load(sys.stdin); c=float(d.get("credit") or 0); print("%.2f" % c); sys.exit(0 if d.get("can_pay") and c > 5 else 1)') \
    || { echo "credit too low (vastai show user: credit $CREDIT); stopping"; exit 2; }
  # OFFER_TYPE=on-demand (operator 2026-10-29, after two outbids): rank by the on-demand price (dph_total), which cannot be outbid;
  # create.sh then rents without a bid (ONDEMAND=1). Default: interruptible, ranked by min_bid.
  PICK=$(vastai search offers "$Q" --type "${OFFER_TYPE:-bid}" --storage "$DISK" -o dph_total --limit 30 --raw | MAX_DOWN_COST="$MAX_DOWN_COST" OFFER_TYPE="${OFFER_TYPE:-bid}" python3 -c '
import json,sys
import os
bad=set(open(sys.argv[1]).read().split()); skip=set(os.environ.get("SKIP_OFFERS", "").split())   # SKIP_OFFERS: listings that failed to rent
maxdc=float(os.environ["MAX_DOWN_COST"])
ok=[o for o in json.load(sys.stdin) if str(o.get("machine_id")) not in bad and str(o.get("id")) not in skip and o.get("min_bid")
    and float(o.get("inet_down_cost") or 0) <= maxdc]
# rank: bid plus the bandwidth bill of the rehearsal (~240 GB down, ~5 GB up) spread over a 12 h rental
if os.environ.get("OFFER_TYPE") == "on-demand":   # the on-demand price is the price; report it in the bid slot (create.sh ignores it)
    for o in ok: o["min_bid"] = float(o.get("dph_total") or 0) - 0.01
ok.sort(key=lambda o: o["min_bid"] + (float(o.get("inet_down_cost") or 0) * 240 + float(o.get("inet_up_cost") or 0) * 5) / 12)
# operator 2026-10-29: a bid never exceeds the on-demand price (dph_total); at or above it the rental is on-demand instead
if ok: o=ok[0]; print(o["id"], o["machine_id"], "%.3f" % min(round(o["min_bid"], 3) + 0.01, float(o.get("dph_total") or 1e9)), o.get("geolocation","").replace(" ", "_"),
                      int(o.get("disk_space") or 0), "%.4f" % float(o.get("inet_down_cost") or 0), "%.4f" % float(o.get("inet_up_cost") or 0),
                      int(o.get("inet_down") or 0), "%.3f" % float(o.get("dph_total") or 0))' "$BAD")
  [ -n "$PICK" ] || { echo "no acceptable offer (query: $Q; inet_down_cost <= \$$MAX_DOWN_COST/GB)"; exit 2; }
  set -- $PICK; OFFER=$1; MACH=$2; BIDP=$3; GEO=$4; ODISK=$5; DCOST=$6; UCOST=$7; DOWN=$8; DPH=$9
  echo "[attempt $a/$MAX] offer $OFFER machine $MACH ($GEO) bid \$$BIDP (dph \$$DPH, disk ${ODISK} GB, down ${DOWN} Mb/s at \$$DCOST/GB, up \$$UCOST/GB; credit \$$CREDIT)"
  OD=$([ "${OFFER_TYPE:-bid}" = on-demand ] && echo 1 || echo 0)
  # a bid at the on-demand price IS an on-demand rental (operator 2026-10-29: "bid price cannot [be] more than on-demand price")
  python3 -c "import sys; sys.exit(0 if float('$BIDP') >= float('$DPH') - 1e-9 else 1)" && { OD=1; echo "  bid \$$BIDP reaches the on-demand price \$$DPH: renting on-demand"; }
  OUT=$(CONFIRM=yes ONDEMAND=$OD "$HERE/create.sh" "$OFFER" "$BIDP" 2>&1)
  ID=$(printf '%s' "$OUT" | python3 -c 'import json,sys,re; t=sys.stdin.read(); m=re.search(r"\{.*\}", t, re.S); print(json.loads(m.group(0)).get("new_contract",""))' 2>/dev/null)
  # a refused create skips that listing for the rest of this call (2026-10-28: the UK unverified offer 51417952 answered 410 no_such_ask
  # six times while still listed as rentable; the old loop re-picked the same cheapest offer on every attempt)
  [ -n "$ID" ] || { echo "create failed for offer $OFFER: $(printf '%s' "$OUT" | grep -o '"msg": *"[^"]*"' | head -n 1 | cut -c1-160); skipping it for this call (machine not blacklisted)"
                    SKIP_OFFERS="${SKIP_OFFERS:-} $OFFER"; export SKIP_OFFERS; continue; }
  echo "  instance $ID; bootstrapping (log probe/a100-bootstrap-$ID.log)"
  # the money guard first (review 2026-10-28, finding 1), then the outbid sentry
  systemctl --user stop "lra-a100-spendguard$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-spendguard$U" 2>/dev/null
  systemd-run --user --unit "lra-a100-spendguard$U" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" -E LRA_FAKE_VAST_BIN="${LRA_FAKE_VAST_BIN:-}" -E LRA_UNIT_SUFFIX="$U" \
    -E SPEND_CAP="${SPEND_CAP:-68}" -E CREDIT_FLOOR="${CREDIT_FLOOR:-5}" -E KEPT_GRACE_MIN="${KEPT_GRACE_MIN:-45}" -E GUARD_POLL_S="${GUARD_POLL_S:-60}" \
    -E STALE_S="${STALE_S:-1800}" -E IDLE_MIN="${IDLE_MIN:-30}" -E IDLE_GPU="${IDLE_GPU:-5}" -E IDLE_CPU="${IDLE_CPU:-5}" -E REMIND_MIN="${REMIND_MIN:-30}" -E BUSY_CHECK="${BUSY_CHECK:-}" -E PRE_DESTROY="${PRE_DESTROY:-}" -E PRE_DESTROY_MAX_S="${PRE_DESTROY_MAX_S:-600}" -E TAG="${TAG:-reh}" -E REH_LOCAL_DIR="${REH_LOCAL_DIR:-}" \
    bash -c "infra/vast/spend_guard.sh $ID $CREDIT 2>> probe/a100-spend-guard.log > /dev/null" > /dev/null && echo "  spend guard armed (cap \$${SPEND_CAP:-68} from credit \$$CREDIT, floor \$${CREDIT_FLOOR:-5})"
  systemctl --user stop "lra-a100-sentry$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-sentry$U" 2>/dev/null
  systemd-run --user --unit "lra-a100-sentry$U" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" -E LRA_FAKE_VAST_BIN="${LRA_FAKE_VAST_BIN:-}" -E LRA_UNIT_SUFFIX="$U" -E BID_CAP="$CAP" \
    -E POLL_S="${POLL_S:-30}" -E LADDER_INTERVAL_S="${LADDER_INTERVAL_S:-180}" -E TICK_S="${TICK_S:-20}" \
    bash -c "infra/vast/outbid_sentry.sh $ID $CAP > /dev/null 2>&1" > /dev/null && echo "  outbid sentry armed (bid ladder up to \$$CAP on any stop)"
  printf -- "- %s UTC provision attempt %s: instance %s (offer %s, machine %s, %s, bid \$%s, dph \$%s, disk %s GB, down %s Mb/s, inet \$%s/GB down \$%s/GB up; credit \$%s)\n" \
    "$(date -u +%Y-%m-%dT%H:%M)" "$a" "$ID" "$OFFER" "$MACH" "$GEO" "$BIDP" "$DPH" "$ODISK" "$DOWN" "$DCOST" "$UCOST" "$CREDIT" >> "$ACC"
  : > "$ROOT/probe/a100-bootstrap-$ID.log"
  for b in 1 2 3 4 5; do
    "$BOOTSTRAP_SH" "$ID" >> "$ROOT/probe/a100-bootstrap-$ID.log" 2>&1; RC=$?
    case $RC in 0|3|5) break;; esac
    case $RC in 6|7) break;; esac   # final verdicts; anything else is re-run while the instance runs (a stop cut it, a transient SSH failure)
    # a stop (outbid) cut the bootstrap: the sentry's ladder fights for the machine; re-run the resumable bootstrap when it runs again
    wait_running "$ID" || break
    echo "  instance $ID running again after a stop: bootstrap re-run $((b + 1))"
  done
  tail -n 2 "$ROOT/probe/a100-bootstrap-$ID.log"
  case $RC in
    0) echo "$ID" > "$ROOT/probe/a100-instance-id"
       if [ "${SKIP_MODEL:-0}" = 1 ]; then   # LeanPool-only rental: no server to probe, no health watchdog (it would report the server CRITICAL)
         V="UP (SKIP_MODEL=1: no server)"
       elif [ "${LRA_NO_BRIDGE:-0}" = 1 ]; then
         for k in 1 2 3 4 5 6; do V=$("$SERVER_UP_SH" "$ID" 2>&1) && break; sleep "${POLL_S:-10}"; done
       else
         # bridge as its own service, started now (no waiter on a log line); then prove the harness path end to end
         systemctl --user stop "lra-bridge$U" 2>/dev/null
         systemd-run --user --unit="lra-bridge$U" --collect -p WorkingDirectory="$ROOT" -E LRA_FAKE_VAST_BIN="${LRA_FAKE_VAST_BIN:-}" /usr/bin/bash -c "exec infra/vast/tls_bridge.sh $ID >> probe/a100-tls-bridge.log 2>&1" >/dev/null
         for k in 1 2 3 4 5 6; do sleep "${POLL_S:-10}"; V=$("$SERVER_UP_SH" "$ID" --bridge 2>&1) && break; done
       fi
       systemctl --user stop "lra-health$U" 2>/dev/null   # continuous health watchdog (exits by itself when the instance is released)
       [ "${SKIP_MODEL:-0}" = 1 ] || systemd-run --user --unit="lra-health$U" --collect -p WorkingDirectory="$ROOT" -E LRA_FAKE_VAST_BIN="${LRA_FAKE_VAST_BIN:-}" /usr/bin/bash -c "exec python3 -u infra/vast/health.py $ID --interval ${HEALTH_INTERVAL_S:-60} ${LRA_NO_BRIDGE:+--no-bridge} >> probe/a100-health.log 2>&1" >/dev/null
       echo "$V"; case "$V" in UP*) echo "READY $ID"; exit 0;; *) kept "$ID" "server up but the readiness check failed: $V"; exit 1;; esac;;
    3|5) if gone "$ID"; then
           echo "$MACH" >> "$BAD"; printf -- "- %s UTC instance %s dropped as a bad host (bootstrap exit %s); machine %s blacklisted\n" "$(date -u +%Y-%m-%dT%H:%M)" "$ID" "$RC" "$MACH" >> "$ACC"
         else kept "$ID" "bad host (bootstrap exit $RC) but the instance is still listed: not renting another"; exit 1; fi;;
    4) kept "$ID" "SSH login failed (bootstrap exit 4: keys/modes, or a changed host key)"; exit 1;;
    6) kept "$ID" "checkpoint download failed (bootstrap exit 6); the server was not started"; exit 1;;
    7) kept "$ID" "destroy of a bad host failed (bootstrap exit 7): still billing"; exit 1;;
    *) kept "$ID" "bootstrap exit $RC (not a bad-host signal)"; exit 1;;
  esac
done
echo "no healthy host after $MAX attempts"; exit 1
