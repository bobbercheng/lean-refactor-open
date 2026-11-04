#!/usr/bin/env bash
# The A100 rehearsal of the open package (operator 2026-10-28; docs/a100_rehearsal.md): rent 4x A100 80 GB on vast.ai (interruptible),
# ship the F.4 release export, restore FRESH Lean environments from the public Kaggle datasets, build + pack + publish the missing LeanPool
# environment, run harness/open_package.py on the 15 warm-up rows + 3 non-sealed LeanPool dev rows, pull the results to the GB10, release.
# Money: SPEND_CAP ($68 of the $74.35 credit) is enforced by infra/vast/spend_guard.sh from the moment of the rental; the bid cap is
# BID_CAP (default $2.00); the job clock is sized from the budget at `run`. NOTHING here rents without CONFIRM=yes on the `rent` phase.
# Phases (each idempotent, run in this order; ID = the instance id, probe/a100-instance-id after `rent`):
#   plan       $0: the budget arithmetic, the offer search (read-only), the checklist
#   export     $0: probe/open_package/export_release.py -> REH/export.tar.gz (+ sha256, EXPORT.json, leak scan 0 hits)
#   rows       $0: infra/open_package/rehearsal_rows.py -> REH/rows/{rows,heartbeats}.jsonl, harness_envs.{leanpool,run}.json
#   rent       CONFIRM=yes: provision.sh (DISK=420, LRA_NO_BRIDGE=1, spend guard + sentry armed) -> READY ID; writes REH/rental.json
#   prep ID    ship the export to EXPORT_ROOT, tools (pip incl. kaggle, rg, jq, zstd), restore the 15 envs + 10 toolchains from Kaggle
#   leanpool ID  build_publish_leanpool.sh all on the instance (bounded, polled), publish with the Kaggle key piped over SSH, copy the
#              merged envs_kaggle.tsv back into the branch, prove a fresh restore of the new dataset rows into a scratch root there
#   run ID     ship rows, package_run.sh (START = rental time, JOB from the budget), arm package_watch.sh (unit lra-a100-watch)
#   status ID  one line: instance, spend, driver, progress
#   release ID final pull, destroy (verified), units stopped
#   watch ID   package_watch.sh in the foreground (the unit does this)
# $0 dry run (probe/a100/dry_run.sh): REH_LOCAL_DIR=<dir> makes the "instance" a local directory (commands run there, copies instead of
# scp), LRA_FAKE_VAST_BIN the vastai shim, REH_SKIP_RESTORE=1 links the dev box's environments, LRA_BASE_URL the fake model.
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3 ssh rsync
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd); cd "$ROOT" || exit 2
PHASE=${1:?phase}; ID=${2:-$(cat probe/a100-instance-id 2>/dev/null)}
TAG=${TAG:-reh}; REH=${REH:-probe/a100-reh-$TAG}; mkdir -p "$REH"
EXPORT_ROOT=${EXPORT_ROOT:-/workspace/lra}; RUN_DIR=${RUN_DIR:-/workspace/lra-run}; OUT=${OUT:-/workspace/out}; WS=/workspace
if [ -n "${REH_LOCAL_DIR:-}" ]; then   # dry run: every instance path lives under the local directory
  EXPORT_ROOT=$REH_LOCAL_DIR$EXPORT_ROOT; RUN_DIR=$REH_LOCAL_DIR$RUN_DIR; OUT=$REH_LOCAL_DIR$OUT; WS=$REH_LOCAL_DIR/workspace; mkdir -p "$WS"
fi
SPEND_CAP=${SPEND_CAP:-68}; CREDIT_FLOOR=${CREDIT_FLOOR:-5}; RESERVE=${RESERVE:-3}; BID_CAP=${BID_CAP:-2.00}; DISK=${DISK:-420}
WORKERS=${WORKERS:-4}; MAX_SESSIONS=${MAX_SESSIONS:-3}; END_SECONDS=${END_SECONDS:-7200}; MAX_JOB_S=${MAX_JOB_S:-57600}
L=$REH/rehearsal.log; ACC=accounting/a100_poc.md; DEV_ROOT=${DEV_ROOT:-$ROOT}   # DEV_ROOT: the dev checkout (export, rows); the dry run runs this script from a scratch copy
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
credit() { vastai show user --raw 2>/dev/null | python3 -c "import json, sys; print('%.2f' % float(json.load(sys.stdin).get('credit') or 0))" 2>/dev/null; }
addr() { vastai show instance "$ID" --raw 2>/dev/null | python3 -c "import json, sys; d = json.load(sys.stdin); p = (d.get('ports') or {}).get('22/tcp') or [{}]; print(d.get('actual_status') or '?', d.get('public_ipaddr') or '-', p[0].get('HostPort') or '-', float(d.get('dph_total') or 0))" 2>/dev/null; }
# control plane: SSH / scp, or the local directory of the dry run
SSHO="-i $HOME/.ssh/id_ed25519 -o BatchMode=yes -o ConnectTimeout=20 -o StrictHostKeyChecking=accept-new"
connect() { if [ -n "${REH_LOCAL_DIR:-}" ]; then ST=running; IP=local; PT=0; DPH=0; mkdir -p "$REH_LOCAL_DIR"; return 0; fi
  read -r ST IP PT DPH <<< "$(addr)"; [ "$ST" = running ] && [ "$PT" != - ] || { log "instance $ID is $ST (no SSH port): not now"; return 1; }; }
rsh() {   # $1 = command (run with cwd EXPORT_ROOT when it exists), $2 = timeout (default 600)
  local t=${2:-600}
  if [ -n "${REH_LOCAL_DIR:-}" ]; then timeout "$t" bash -c "cd '$EXPORT_ROOT' 2>/dev/null || cd '$WS'; $1"
  else timeout "$t" ssh $SSHO -p "$PT" "root@$IP" "cd $EXPORT_ROOT 2>/dev/null; $1" 2>/dev/null | grep -v "^Welcome\|^Have fun"; fi
}
rcp() {   # $1 = local file, $2 = remote path
  if [ -n "${REH_LOCAL_DIR:-}" ]; then mkdir -p "$(dirname "$2")"; cp "$1" "$2"; else timeout 1800 scp -q $SSHO -P "$PT" "$1" "root@$IP:$2"; fi
}
rget() {   # $1 = remote file, $2 = local path
  if [ -n "${REH_LOCAL_DIR:-}" ]; then cp "$1" "$2"; else timeout 600 scp -q $SSHO -P "$PT" "root@$IP:$1" "$2"; fi
}
case "$PHASE" in
plan)
  c=$(credit); echo "credit \$$c; spend cap \$$SPEND_CAP (stop-loss: spend_guard.sh), floor \$$CREDIT_FLOOR, reserve \$$RESERVE, bid cap \$$BID_CAP, disk $DISK GB"
  python3 - "$c" "$SPEND_CAP" "$RESERVE" "$BID_CAP" <<'PY'
import sys
c, cap, res, bid = map(float, sys.argv[1:5])
for dph in (0.9, 1.2, 1.5, 2.0):
    print(f"  at ${dph:.2f}/h: {(cap - res) / dph:.1f} h of rental in the cap (setup ~2.5 h: bootstrap + restore + LeanPool build + pack + publish; the run gets the rest)")
print(f"  budget-derived bid cap at 12 h: min({bid:.2f}, (credit - floor - reserve) / 12 h = {(c - 5 - res) / 12:.2f}) = {min(bid, (c - 5 - res) / 12):.2f}")
PY
  echo "offers now (read-only; provision.sh's filter: 4x A100 80 GB, >= ${CPU_MIN:-64} vCPU, >= $DISK GB, inet_down >= ${MIN_DOWN:-500} Mb/s, inet_down_cost <= \$${MAX_DOWN_COST:-0.01}/GB):"
  vastai search offers "num_gpus=4 gpu_ram>=80 gpu_name=A100_SXM4 cpu_cores_effective>=${CPU_MIN:-64} disk_space>=$DISK${VERIFIED:+ verified=$VERIFIED}" --type bid --storage "$DISK" -o dph_total --limit 10 --raw 2>/dev/null | python3 "$HERE/_fmt.py"
  echo "checklist: export (EXPORT.json leak scan 0 hits), rows (18), ~/.config/vexorium/vllm_api_key, ~/.kaggle/kaggle.json, ssh key, no probe/a100-hold*, units idle: $(systemctl --user list-units --no-legend 'lra-*' 2>/dev/null | wc -l) lra-* unit(s) active";;
export)
  python3 "$DEV_ROOT/probe/open_package/export_release.py" --commit "${EXPORT_COMMIT:-HEAD}" --out "$REH/export" | tee -a "$L"; exit "${PIPESTATUS[0]}";;
rows)
  python3 "$DEV_ROOT/infra/open_package/rehearsal_rows.py" --out "$REH/rows" ${ROWS_PICK:+--pick $ROWS_PICK} 2>&1 | tee -a "$L"; exit "${PIPESTATUS[0]}";;
rent)
  [ "${CONFIRM:-}" = yes ] || { echo "rent: set CONFIRM=yes (this spends money: provision.sh rents the cheapest acceptable 4x A100 offer at min_bid + \$0.01)"; exit 2; }
  [ -f "$REH/export.tar.gz" ] && [ -f "$REH/rows/rows.jsonl" ] || { log "rent refused: run the export and rows phases first"; exit 2; }
  c0=$(credit); log "rent: credit \$$c0, cap \$$SPEND_CAP, bid cap \$$BID_CAP, disk $DISK"
  DISK=$DISK BID_CAP=$BID_CAP SPEND_CAP=$SPEND_CAP CREDIT_FLOOR=$CREDIT_FLOOR LRA_NO_BRIDGE=1 CONFIRM=yes PRE_DESTROY="TAG=$TAG LOCAL=$REH RUN_DIR=$RUN_DIR OUT=$OUT EXPORT_ROOT=$EXPORT_ROOT infra/vast/package_watch.sh {ID} pull" "$HERE/provision.sh" "${ATTEMPTS:-3}" 2>&1 | tee -a "$L"
  rc=${PIPESTATUS[0]}; ID=$(cat probe/a100-instance-id 2>/dev/null)
  [ "$rc" = 0 ] && [ -n "$ID" ] || { log "rent: provision rc $rc (a KEPT instance is destroyed by the spend guard after ${KEPT_GRACE_MIN:-45} min unless acked)"; exit 1; }
  python3 -c "import json, time; json.dump({'id': '$ID', 'rented_at': time.time(), 'credit_at_rental': float('$c0'), 'tag': '$TAG'}, open('$REH/rental.json', 'w'))"
  log "READY $ID (rental.json written; next: prep $ID)";;
prep)
  connect || exit 1
  [ -f "$REH/export.tar.gz" ] || { log "prep: no $REH/export.tar.gz (export phase)"; exit 2; }
  log "prep $ID: shipping the export ($(du -h "$REH/export.tar.gz" | cut -f1)) to $EXPORT_ROOT"
  rcp "$REH/export.tar.gz" $WS/export.tar.gz || { log "prep: scp failed"; exit 1; }
  rcp "$REH/export.sha256" $WS/export.sha256 || exit 1
  rsh "cd $WS && sha256sum -c --quiet export.sha256 && rm -rf $EXPORT_ROOT && mkdir -p $EXPORT_ROOT && tar -xzf export.tar.gz -C $EXPORT_ROOT --strip-components=1 && cat $EXPORT_ROOT/HARNESS_COMMIT" | tee -a "$L" | grep -qE '^[0-9a-f]{8}$' || { log "prep: export unpack failed"; exit 1; }
  log "prep: tools (pip incl. kaggle, rg, jq, zstd)"
  rsh "mkdir -p envs/logs && SKIP_ENVS=1 LRA_WITH_KAGGLE=${LRA_WITH_KAGGLE:-1} bash infra/vast/harness_setup.sh 2>&1 | tail -n 1" 1800 | tee -a "$L"
  rsh "command -v rg > /dev/null && command -v zstd > /dev/null && command -v jq > /dev/null && echo tools-ok" | grep -q tools-ok || { log "prep: tools missing"; exit 1; }
  if [ "${REH_SKIP_RESTORE:-0}" = 1 ]; then
    log "prep: REH_SKIP_RESTORE=1: linking the dev box's environments (dry run only)"
    rsh "mkdir -p envs; for e in ${REH_ENVS_SRC:-$DEV_ROOT/envs}/*; do b=\$(basename \$e); [ -e envs/\$b ] || ln -s \$e envs/\$b; done; ls envs | wc -l"
  else
    log "prep: restoring the 15 envs + 10 toolchains from Kaggle (PAR=${RESTORE_PAR:-8}; ~3 min on a 1 Gbps link)"
    rsh "infra/sync/restore_envs.sh ${RESTORE_PAR:-8} > envs/logs/restore.log 2>&1; tail -n 2 envs/logs/restore.log" 5400 | tee -a "$L" | grep -q "^RESTORE DONE" || { log "prep: restore failed (envs/logs/restore.log on the instance)"; exit 1; }
  fi
  rcp "$REH/rows/rows.jsonl" "$RUN_DIR/rows.jsonl"; rcp "$REH/rows/heartbeats.jsonl" "$RUN_DIR/heartbeats.jsonl"
  rcp "$REH/rows/harness_envs.leanpool.json" "$EXPORT_ROOT/infra/vast/harness_envs.leanpool.json"; rcp "$REH/rows/harness_envs.run.json" "$EXPORT_ROOT/infra/vast/harness_envs.run.json"
  log "PREP DONE on $ID (next: leanpool $ID, then run $ID)";;
leanpool)
  connect || exit 1
  log "leanpool $ID: build (${LEANPOOL_BUILD:-full}) + pack on the instance, detached; polled every 60 s, at most ${LEANPOOL_MAX_S:-14400}s"
  rsh "rm -f envs/logs/leanpool.rc; setsid nohup bash -c 'ROWS=$RUN_DIR/rows.jsonl LEANPOOL_BUILD=${LEANPOOL_BUILD:-full} OUT=$WS/envpack DF_PATH=$WS infra/vast/build_publish_leanpool.sh all > envs/logs/leanpool.log 2>&1; echo \$? > envs/logs/leanpool.rc' > /dev/null 2>&1 < /dev/null & echo started"
  t0=$(date +%s)
  while :; do
    sleep "${LP_POLL_S:-60}"
    st=$(rsh "cat envs/logs/leanpool.rc 2>/dev/null; echo ---; tail -n 1 envs/logs/leanpool.log 2>/dev/null; df --output=avail -BG $WS | tail -n 1")
    rc=$(head -n 1 <<< "$st"); [ "$rc" = --- ] && rc=""
    log "  $(( ($(date +%s) - t0) / 60 )) min: $(tail -n 2 <<< "$st" | tr '\n' ' ')"
    [ -n "$rc" ] && break
    [ $(( $(date +%s) - t0 )) -ge "${LEANPOOL_MAX_S:-14400}" ] && { log "leanpool: not done in ${LEANPOOL_MAX_S:-14400}s; leaving it (resumable); not publishing"; exit 1; }
  done
  [ "$rc" = 0 ] || { log "leanpool: build/pack rc $rc (envs/logs/leanpool.log on the instance)"; exit 1; }
  if [ "${REH_SKIP_PUBLISH:-0}" = 1 ]; then log "leanpool: REH_SKIP_PUBLISH=1: DRY publish (merged tsv only)"; rsh "DRY=1 ENVS_JSON=infra/vast/harness_envs.leanpool.json infra/sync/publish_envs_kaggle.sh $WS/envpack 2>&1 | tail -n 3" | tee -a "$L"
  else
    [ -f "$HOME/.kaggle/kaggle.json" ] || { log "leanpool: no ~/.kaggle/kaggle.json on the GB10"; exit 1; }
    log "leanpool: publishing (key piped over SSH into the process environment; never on the instance's disk)"
    KU=$(python3 -c "import json,os; print(json.load(open(os.path.expanduser('~/.kaggle/kaggle.json')))['username'])")
    if [ -n "${REH_LOCAL_DIR:-}" ]; then log "leanpool: local mode never publishes"; exit 1; fi
    python3 -c "import json,os; print(json.load(open(os.path.expanduser('~/.kaggle/kaggle.json')))['key'])" |
      timeout 60 ssh $SSHO -p "$PT" "root@$IP" "read -r KAGGLE_KEY; export KAGGLE_KEY KAGGLE_USERNAME=$KU ENVS_JSON=infra/vast/harness_envs.leanpool.json; cd $EXPORT_ROOT; setsid nohup infra/sync/publish_envs_kaggle.sh /workspace/envpack > /workspace/envpack/PUBLISH.log 2>&1 < /dev/null & echo publishing" 2>/dev/null | grep -v "^Welcome\|^Have fun"
    t0=$(date +%s)
    while :; do
      sleep 60; last=$(rsh "tail -n 1 /workspace/envpack/PUBLISH.log 2>/dev/null"); log "  publish: $last"
      grep -q "PUBLISH DONE\|PUBLISH FAILED\|refused" <<< "$last" && break
      [ $(( $(date +%s) - t0 )) -ge "${PUBLISH_MAX_S:-5400}" ] && { log "leanpool: publish not done in ${PUBLISH_MAX_S:-5400}s"; exit 1; }
    done
    grep -q "PUBLISH DONE" <<< "$last" || exit 1
    rsh "grep -c KAGGLE /workspace/env /workspace/envpack/PUBLISH.log 2>/dev/null; ls ~/.kaggle 2>/dev/null | wc -l" | tee -a "$L"   # the key must not be on the disk: 0 0
  fi
  rget "$EXPORT_ROOT/infra/vast/envs_kaggle.tsv" "$REH/envs_kaggle.tsv" && cp "$REH/envs_kaggle.tsv" infra/vast/envs_kaggle.tsv && log "leanpool: merged envs_kaggle.tsv copied into the branch ($(wc -l < infra/vast/envs_kaggle.tsv) lines; commit it)"
  if [ "${REH_SKIP_PUBLISH:-0}" != 1 ]; then
    log "leanpool: proof: fresh restore of the new rows into a scratch root on the instance"
    rsh "rm -rf $WS/lra-rt && mkdir -p $WS/lra-rt && tar -xzf $WS/export.tar.gz -C $WS/lra-rt --strip-components=1 && cp infra/vast/envs_kaggle.tsv $WS/lra-rt/infra/vast/ && cp infra/vast/harness_envs.leanpool.json $WS/lra-rt/infra/vast/ && cd $WS/lra-rt && HOME=$WS/lra-rt-home ENVS_JSON=infra/vast/harness_envs.leanpool.json ONLY_DATASETS='lean-env-leanpool-x86-64 lean4-toolchains-x86-64' infra/sync/restore_envs.sh 2 2>&1 | tail -n 3; rm -rf $WS/lra-rt $WS/lra-rt-home $WS/envpack" 5400 | tee -a "$L" | grep -q "RESTORE DONE" || { log "leanpool: the fresh restore of the published rows FAILED"; exit 1; }
  fi
  log "LEANPOOL DONE on $ID";;
run)
  connect || exit 1
  rented=$(python3 -c "import json; print(int(json.load(open('$REH/rental.json'))['rented_at']))" 2>/dev/null || date +%s)
  c=$(credit); c0=$(python3 -c "import json; print(json.load(open('$REH/rental.json'))['credit_at_rental'])" 2>/dev/null || echo "$c")
  JOB=$(python3 -c "
import time
spent = float('$c0') - float('$c'); dph = float('${DPH:-0}') or 1.0
left_money = $SPEND_CAP - spent - $RESERVE
elapsed = time.time() - $rented
job = min($MAX_JOB_S, elapsed + left_money / dph * 3600)   # the clock started at the rental, so setup counts
print(int(max(job, elapsed + 3600)))")
  # 2026-10-30 20:24 UTC: the guard armed at the rental kept that rental's whole budget ($68) through two top-ups and two fresh runs and
  # destroyed a healthy run. Every run now RE-ARMS the guard with its own SPEND_CAP counted from now (warnings at 80% / 95% by push).
  # the guard counts from now, so it gets what is left of the rental's SPEND_CAP (spent = credit_at_rental - credit; rental.json's
  # credit_at_rental includes any top-up, 2026-10-30 21:04: a $24.96 top-up must not read as negative spend)
  GCAP=$(python3 -c "print('%.2f' % max(1.0, float('$SPEND_CAP') - (float('$c0') - float('$c'))))")
  systemctl --user stop "lra-a100-spendguard$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-spendguard$U" 2>/dev/null
  systemd-run --user --unit "lra-a100-spendguard$U" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" -E LRA_FAKE_VAST_BIN="${LRA_FAKE_VAST_BIN:-}" -E LRA_UNIT_SUFFIX="$U" \
    -E SPEND_CAP="$GCAP" -E CREDIT_FLOOR="${CREDIT_FLOOR:-5}" -E KEPT_GRACE_MIN="${KEPT_GRACE_MIN:-45}" -E GUARD_POLL_S="${GUARD_POLL_S:-60}" \
    -E STALE_S="${STALE_S:-1800}" -E IDLE_MIN="${IDLE_MIN:-30}" -E IDLE_GPU="${IDLE_GPU:-5}" -E IDLE_CPU="${IDLE_CPU:-5}" -E REMIND_MIN="${REMIND_MIN:-30}" \
    -E BUSY_CHECK="${BUSY_CHECK-python3 probe/a100-alarm/run_busy.py --label a100-$TAG}" \
    -E PRE_DESTROY="${PRE_DESTROY:-}" -E PRE_DESTROY_MAX_S="${PRE_DESTROY_MAX_S:-600}" -E TAG="$TAG" -E REH_LOCAL_DIR="${REH_LOCAL_DIR:-}" \
    bash -c "infra/vast/spend_guard.sh $ID $c 2>> probe/a100-spend-guard.log > /dev/null" > /dev/null && log "spend guard re-armed for this run: cap \$$GCAP more from credit \$$c (the rental's \$$SPEND_CAP minus the \$$(python3 -c "print('%.2f' % (float('$c0') - float('$c')))") spent since it) (warns at 80% and 95%; at the cap it asks before deleting a busy instance)"
  log "run $ID: credit \$$c (spent \$$(python3 -c "print('%.2f' % (float('$c0') - float('$c')))"), dph \$$DPH -> job ${JOB}s from the rental ($(( (JOB - ($(date +%s) - rented)) / 60 )) min left), workers $WORKERS, max sessions $MAX_SESSIONS, end ${END_SECONDS}s"
  # the rows and the run's env list again (idempotent): after `rows` was re-run (e.g. ROWS_PICK=0 when the LeanPool build failed) the
  # node must run what the GB10 has now, not what prep shipped
  rcp "$REH/rows/rows.jsonl" "$RUN_DIR/rows.jsonl" && rcp "$REH/rows/heartbeats.jsonl" "$RUN_DIR/heartbeats.jsonl" && rcp "$REH/rows/harness_envs.run.json" "$EXPORT_ROOT/infra/vast/harness_envs.run.json" || { log "run: shipping the rows failed"; exit 1; }
  [ -n "${LRA_BASE_URL:-}" ] && EP="LRA_BASE_URL=$LRA_BASE_URL LRA_API_KEY_FILE=${LRA_API_KEY_FILE:-}" || EP=""
  rsh "cp infra/vast/harness_envs.run.json infra/vast/harness_envs.json 2>/dev/null; $EP RUN_DIR=$RUN_DIR OUT=$OUT TAG=$TAG START=$rented JOB=$JOB WORKERS=$WORKERS MAX_SESSIONS=$MAX_SESSIONS END_SECONDS=$END_SECONDS EXTRA='${EXTRA:-}' MIN_FREE_GB=${MIN_FREE_GB:-40} DF_PATH=${DF_PATH:-$WS} bash infra/vast/package_run.sh" 900 | tee -a "$L" | grep -q "driver running" || { log "run: package_run.sh refused or failed (above)"; exit 1; }
  systemctl --user stop "lra-a100-watch$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-watch$U" 2>/dev/null
  systemd-run --user --unit "lra-a100-watch$U" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" -E LRA_FAKE_VAST_BIN="${LRA_FAKE_VAST_BIN:-}" -E LRA_UNIT_SUFFIX="$U" \
    -E TAG="$TAG" -E RUN_DIR="$RUN_DIR" -E OUT="$OUT" -E EXPORT_ROOT="$EXPORT_ROOT" -E REH_LOCAL_DIR="${REH_LOCAL_DIR:-}" -E LOCAL="$REH" -E POLL_S="${WATCH_POLL_S:-60}" -E PULL_EVERY_S="${PULL_EVERY_S:-300}" -E STALL_MIN="${STALL_MIN:-20}" \
    bash -c "infra/vast/package_watch.sh $ID >> $REH/watch.out 2>&1" > /dev/null && log "watch armed (unit lra-a100-watch$U; log $REH/watch.log)"
  printf -- "- %s UTC rehearsal run %s started on %s: job %s s from the rental, credit \$%s\n" "$(date -u +%Y-%m-%dT%H:%M)" "$TAG" "$ID" "$JOB" "$c" >> "$ACC";;
status)
  c=$(credit); read -r ST IP PT DPH <<< "$(addr)"; c0=$(python3 -c "import json; print(json.load(open('$REH/rental.json'))['credit_at_rental'])" 2>/dev/null || echo "$c")
  echo "instance $ID: $ST at \$$DPH/h; credit \$$c, spent \$$(python3 -c "print('%.2f' % (float('$c0') - float('$c')))") of \$$SPEND_CAP; units: $(systemctl --user list-units --no-legend 'lra-*' 2>/dev/null | awk '{print $1}' | tr '\n' ' ')"
  tail -n 3 "$REH/watch.log" 2>/dev/null; [ -f "$REH/out/agent_sessions.jsonl" ] && echo "sessions: $(wc -l < "$REH/out/agent_sessions.jsonl")";;
release)
  connect && TAG=$TAG LOCAL=$REH RUN_DIR=$RUN_DIR OUT=$OUT EXPORT_ROOT=$EXPORT_ROOT "$HERE/package_watch.sh" "$ID" pull
  touch "probe/a100-pause-$ID"
  CONFIRM=yes FORCE=yes "$HERE/destroy.sh" "$ID" | tee -a "$L"; rc=${PIPESTATUS[0]}
  systemctl --user stop "lra-a100-watch$U" "lra-a100-sentry$U" "lra-a100-bid$U" "lra-bridge$U" "lra-health$U" 2>/dev/null
  [ "$rc" = 0 ] && log "released $ID (the spend guard exits by itself when no instance is listed)" || { log "RELEASE FAILED: $ID still listed (rc $rc); the spend guard retries every minute"; exit 1; };;
watch)
  TAG=$TAG LOCAL=$REH RUN_DIR=$RUN_DIR OUT=$OUT EXPORT_ROOT=$EXPORT_ROOT exec "$HERE/package_watch.sh" "$ID";;
*) echo "phases: plan export rows rent prep leanpool run status release watch"; exit 2;;
esac
