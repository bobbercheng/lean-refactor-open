#!/usr/bin/env bash
# Rent + bootstrap with automatic replacement of bad hosts (2026-10-07;
# a provision whose nvtop install is very slow or times out destroys the instance and rents a new one).
# Usage: CONFIRM=yes infra/vast/provision.sh [max_attempts=3]
#   each attempt: cheapest verified interruptible 4xA100-80GB offer whose machine is not in bad_machines.txt,
#   bid = min_bid + $0.01 (house rule), then bootstrap.sh (log: probe/a100-bootstrap-<id>.log).
#   bootstrap exit 3 (SSH port never opened) or 5 (apt/nvtop too slow) = bad host, already destroyed -> record its machine, retry.
#   Any other failure stops with the instance KEPT for a manual decision (likely our own bug). On success the instance id is written
#   to probe/a100-instance-id and printed last; start the bridge with infra/vast/tls_bridge.sh <id>.
# Outbids: the outbid sentry
# (infra/vast/outbid_sentry.sh, unit lra-a100-sentry) is armed the moment an instance is rented, so a stop starts the bid ladder within
# ~30 s in every phase; a bootstrap cut by a stop is re-run (it resumes the download) once vast runs the instance again, up to 4 times.
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3 ssh
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
MAX=${1:-3}; BAD=$HERE/bad_machines.txt; touch "$BAD"; CAP=${BID_CAP:-3.17}
wait_running() {   # 0 when vast runs the instance again (the sentry's ladder fights for it); 1 when gone or the ladder ended at the cap
  local since; since=$(date +%s)
  while :; do
    local s; s=$(vastai show instances --raw 2>/dev/null | python3 -c "import json, sys; i = next((r for r in json.load(sys.stdin) if r.get('id') == $1), None); print('gone' if i is None else i.get('actual_status'))" 2>/dev/null)
    [ "$s" = running ] && return 0
    [ "$s" = gone ] && return 1
    grep -q "SWITCH INSTANCES" <(awk -v t="$(date -u -d "@$since" -Is)" '$1 >= "["t' "$ROOT/probe/a100-sentry.log" 2>/dev/null) && return 1
    sleep 30
  done
}
Q='num_gpus=4 gpu_ram>=80 gpu_name in [A100_SXM4,A100_PCIE] cpu_cores_effective>=64 disk_space>=300'
# VERIFIED=any admits unverified/deverified hosts (2026-10-09 ~21:05, no verified 4xA100 offer listed;
# a new instance was needed); MIN_DOWN (Mb/s) keeps out hosts whose link cannot fetch the 190.8 GB checkpoint in reasonable time
Q="$Q${VERIFIED:+ verified=$VERIFIED}${MIN_DOWN:+ inet_down>=$MIN_DOWN}"
[ "${CONFIRM:-}" = yes ] || { echo "dry run: set CONFIRM=yes (rents up to $MAX instances in turn)"; exit 0; }
for a in $(seq 1 "$MAX"); do
  vastai show user --raw | python3 -c 'import json,sys; d=json.load(sys.stdin); sys.exit(0 if d.get("can_pay") and (d.get("credit") or 0) > 5 else 1)' \
    || { echo "credit too low (vastai show user: credit); stopping"; exit 2; }
  PICK=$(vastai search offers "$Q" --type bid --storage 300 -o dph_total --limit 30 --raw | python3 -c '
import json,sys
import os
bad=set(open(sys.argv[1]).read().split()); skip=set(os.environ.get("SKIP_OFFERS", "").split())   # SKIP_OFFERS: listings that failed to rent
ok=[o for o in json.load(sys.stdin) if str(o.get("machine_id")) not in bad and str(o.get("id")) not in skip and o.get("min_bid")]
ok.sort(key=lambda o: o["min_bid"])
if ok: o=ok[0]; print(o["id"], o["machine_id"], "%.3f" % (round(o["min_bid"], 3) + 0.01), o.get("geolocation","").replace(" ", "_"))' "$BAD")
  [ -n "$PICK" ] || { echo "no acceptable offer"; exit 2; }
  set -- $PICK; OFFER=$1; MACH=$2; BIDP=$3
  echo "[attempt $a/$MAX] offer $OFFER machine $MACH ($4) bid \$$BIDP"
  ID=$(CONFIRM=yes "$HERE/create.sh" "$OFFER" "$BIDP" | python3 -c 'import json,sys,re; t=sys.stdin.read(); m=re.search(r"\{.*\}", t, re.S); print(json.loads(m.group(0)).get("new_contract",""))' 2>/dev/null)
  [ -n "$ID" ] || { echo "create failed for offer $OFFER (usually taken by someone else first; machine not blacklisted)"; continue; }
  echo "  instance $ID; bootstrapping (log probe/a100-bootstrap-$ID.log)"
  systemctl --user stop lra-a100-sentry 2>/dev/null; systemctl --user reset-failed lra-a100-sentry 2>/dev/null
  systemd-run --user --unit lra-a100-sentry --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" \
    bash -c "infra/vast/outbid_sentry.sh $ID $CAP > /dev/null 2>&1" > /dev/null && echo "  outbid sentry armed (bid ladder up to \$$CAP on any stop)"
  printf -- "- %s UTC provision attempt %s: instance %s (offer %s, machine %s, bid \$%s)\n" "$(date -u +%Y-%m-%dT%H:%M)" "$a" "$ID" "$OFFER" "$MACH" "$BIDP" >> "$ROOT/accounting/a100_poc.md"
  : > "$ROOT/probe/a100-bootstrap-$ID.log"
  for b in 1 2 3 4 5; do
    "$HERE/bootstrap.sh" "$ID" >> "$ROOT/probe/a100-bootstrap-$ID.log" 2>&1; RC=$?
    case $RC in 0|3|5) break;; esac
    # a stop (outbid) cut the bootstrap: the sentry's ladder fights for the machine; re-run the resumable bootstrap when it runs again
    wait_running "$ID" || break
    echo "  instance $ID running again after a stop: bootstrap re-run $((b + 1))"
  done
  tail -n 2 "$ROOT/probe/a100-bootstrap-$ID.log"
  case $RC in
    0) echo "$ID" > "$ROOT/probe/a100-instance-id"
       # bridge as its own service, started now (no waiter on a log line); then prove the harness path end to end
       systemctl --user stop lra-bridge 2>/dev/null
       systemd-run --user --unit=lra-bridge --collect -p WorkingDirectory="$ROOT" /usr/bin/bash -c "exec infra/vast/tls_bridge.sh $ID >> probe/a100-tls-bridge.log 2>&1" >/dev/null
       for k in 1 2 3 4 5 6; do sleep 10; V=$("$HERE/server_up.sh" "$ID" --bridge 2>&1) && break; done
       systemctl --user stop lra-health 2>/dev/null   # continuous health watchdog (exits by itself when the instance is released)
       systemd-run --user --unit=lra-health --collect -p WorkingDirectory="$ROOT" /usr/bin/bash -c "exec python3 -u infra/vast/health.py $ID >> probe/a100-health.log 2>&1" >/dev/null
       echo "$V"; case "$V" in UP*) echo "READY $ID"; exit 0;; *) echo "server up but bridge failed: instance $ID KEPT"; exit 1;; esac;;
    3|5) echo "$MACH" >> "$BAD"; printf -- "- %s UTC instance %s dropped as a bad host (bootstrap exit %s); machine %s blacklisted\n" "$(date -u +%Y-%m-%dT%H:%M)" "$ID" "$RC" "$MACH" >> "$ROOT/accounting/a100_poc.md";;
    *) echo "bootstrap exit $RC (not a bad-host signal): instance $ID KEPT for a manual decision"; exit 1;;
  esac
done
echo "no healthy host after $MAX attempts"; exit 1
