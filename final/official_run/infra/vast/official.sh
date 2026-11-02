#!/usr/bin/env bash
# The OFFICIAL open-track run on the kept A100 box (operator 2026-10-31 07:15 UTC; docs/open_official_run_runbook.md): the 60 rows released
# Nov 1, the package from the SEED, 48 h from the release, proofs + code by Nov 3 AoE. Phases, each idempotent, in this order (ID defaults
# to probe/a100-instance-id). Decisions live in OFF/DECISIONS.env (written with defaults by `plan`; the operator's answers go there).
#   plan               $0: state (instance, credit, units, the box's disk / runs / vLLM), the decisions, the checklist
#   rows R [H]         $0: the released rows + reference heartbeats -> OFF/rows/{rows,heartbeats}.jsonl, validated (fields, unique names,
#                      heartbeats for every row, known sources, the warm-up 15's statements vs data/benchmark_warmup.jsonl), the env list
#                      OFF/rows/harness_envs.official.json (infra/open_package/envs_from_rows.py; EXTRA_URLS="src=url ..." for a new project).
#                      b100 (2026-11-01: the final's heartbeats stay private): H omitted or `measure` -> OFF/rows/HB_MEASURE, no heartbeat check
#                      here; the refhb phase measures them on the box after the envs. A given H is used as is (the default path, unchanged)
#   refhb ID           (after `envs ID check` says ENVS OK; before start) a provided heartbeats file: used as is, shipped (with the rows) to
#                      RUN_DIR on the box. HB_MEASURE: the reference proofs
#                      measured ON THE BOX by infra/refhb/make_ref_heartbeats.py (direct path + 2, newest pin; warm-up rows reuse the published
#                      values; REFHB_JOBS 8, detached, polled up to REFHB_MAX_S 3600, resumable) -> RUN_DIR/heartbeats.jsonl, pulled to
#                      OFF/rows/heartbeats.jsonl (+ .meta.json), every row covered -> OFF/rows/REFHB_OK (the rows' sha256).
#                      REFHB_ALLOW_MISSING=1 (opt-in, for an unattended release): a row without a reading gets a FLAGGED placeholder
#                      (--allow-missing: despite-error / older-pin / length-scaled), listed in OFF/rows/REFHB_PLACEHOLDERS and pushed as an
#                      alert, and start may proceed; without it such a row stops the phase (rc 1) as before
#   export             $0: probe/open_package/export_release.py --commit FINAL_COMMIT -> OFF/export.tar.gz (leak scan must pass)
#   envs ID [build]    ships the rows + env list; official_envs_host.sh plan (default) or build (detached; poll with `envs ID check`)
#   stop-p85b ID [END_S]  package_stop_host.sh on p85b (bests kept, export written, no relaunch after), final pull, its watch + alarm stopped
#   ship ID            (no driver alive) the final export over EXPORT_ROOT (envs/, .envs-download/, probe/runs/ kept); HARNESS_COMMIT checked
#   vllm ID            vllm_recipe_host.sh RECIPE (std32 when WORKERS > 12, else std; installed as run_vllm.sh for onstart; restart by pid only
#                      if the live server differs); refuses while a driver runs
#   start ID           package_run.sh on the box: RUN_DIR /workspace/lra-run-off, OUT /workspace/out-off, TAG off, START = RELEASE_AT,
#                      JOB 172800, WORKERS, MAX_SESSIONS, END_SECONDS, EXTRA "--end-pipeline on" (+ "--auto-brief on" if AUTO_BRIEF=on,
#                      + "--dialect-card on" if DIALECT_CARD=on; the b94b write-back is the package default with the pipeline);
#                      check_envs + preflight inside; then the host status writer + GCS sidecar a100-off
#   arm ID             GB10: older watches / alarms stopped (each after its run's final pull), spend guard re-armed (SPEND_CAP GUARD_ADD
#                      $200 from now, ask-first), lra-a100-watch-off (HOLD_MAX_S 345600, the hold file kept), lra-a100-alarm-off; records
#   status ID          one screen        upload             pull; OFF/upload/<file>.jsonl ({name, proof}) checked; the code zip
# Local dry run (probe/a100/official_dry_run.sh): REH_LOCAL_DIR = the "box" directory, LRA_FAKE_VAST_BIN, LRA_UNIT_SUFFIX, LRA_BASE_URL.
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3 ssh rsync
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd); cd "$ROOT" || exit 2
PHASE=${1:?phase}; shift || true
OFF=${OFF:-probe/a100-official}; mkdir -p "$OFF/rows"; L=$OFF/official.log; D=$OFF/DECISIONS.env
EXPORT_ROOT=${EXPORT_ROOT:-/workspace/lra}; RUN_DIR=${RUN_DIR:-/workspace/lra-run-off}; OUT=${OUT:-/workspace/out-off}; WS=/workspace
P85B_RUN=${P85B_RUN:-/workspace/lra-run-p85b}; P85B_OUT=${P85B_OUT:-/workspace/out-p85b}; TAG=${TAG:-off}
if [ -n "${REH_LOCAL_DIR:-}" ]; then
  EXPORT_ROOT=$REH_LOCAL_DIR$EXPORT_ROOT; RUN_DIR=$REH_LOCAL_DIR$RUN_DIR; OUT=$REH_LOCAL_DIR$OUT; WS=$REH_LOCAL_DIR/workspace
  P85B_RUN=$REH_LOCAL_DIR$P85B_RUN; P85B_OUT=$REH_LOCAL_DIR$P85B_OUT
fi
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
push() { [ -n "${NO_PUSH:-}" ] || [ -n "${REH_LOCAL_DIR:-}" ] && return 0; local t; t=$(cat probe/a100-ntfy-topic 2>/dev/null)   # b100: the private topic
  [ -n "$t" ] && curl -fsS -m 20 -H "Title: A100 official" -H "Priority: high" -d "$*" "https://ntfy.sh/$t" > /dev/null 2>&1; true; }
[ -f "$D" ] || cat > "$D" <<'DEC'
# Official open run decisions (infra/vast/official.sh reads this file at every phase). Fill in before `start`.
RELEASE_AT=""            # the organizers' release time, e.g. "2026-11-01 05:00 UTC" (recorded; the clock start follows CLOCK_START)
CLOCK_START=launch       # operator 2026-11-01 ~06:05 UTC: launch = the 48 h job clock starts when `start` runs (vLLM up, setup done), as the
                         # organizers' run.sh does after their setup step; release = it starts at RELEASE_AT (setup counts). Both times disclosed.
FINAL_COMMIT=""          # the package commit to export (a100-rehearsal after the auto-brief readout; b91-autobrief merged if AUTO_BRIEF=on)
WORKERS=14               # operator 2026-10-31 15:30 UTC (docs/operator_ideas_2026-10-31.md: +8.7% tokens, KV p99 ~0.85); never from WORKERS_WHY
MAX_SESSIONS=12          # operator 2026-10-31 15:30 UTC: the package default; the deadline + room schedule decide (5 left 8-11 h idle)
VLLM_RECIPE=std          # operator 2026-10-31: keep the production recipe at 14 workers (max-num-seqs 16 suffices; std32 never ran under load)
END_SECONDS=7200         # the end stage's R5 clock at the agent deadline (the pipeline polishes rows during the agent stage)
AUTO_BRIEF=off           # on only if the b91 A/B readout says so (needs the b91-autobrief code in FINAL_COMMIT)
DIALECT_CARD=off         # b94b: on = every session gets the generic dialect card (--dialect-card on; needs b94b in FINAL_COMMIT; frozen per run)
GUARD_ADD=200            # the official run's spend guard cap from the arming (ask-first)
HOLD_MAX_S=345600        # the official watch's hold wait after the run (96 h; the hold file stays until the upload is verified)
DEC
. "$D"
ID=${1:-$(cat probe/a100-instance-id 2>/dev/null)}
credit() { vastai show user --raw 2>/dev/null | python3 -c "import json, sys; d = json.load(sys.stdin); print('%.2f' % float(d['credit'])) if isinstance(d, dict) and d.get('credit') is not None else None" 2>/dev/null; }
addr() { vastai show instance "$ID" --raw 2>/dev/null | python3 -c "import json, sys; d = json.load(sys.stdin); p = (d.get('ports') or {}).get('22/tcp') or [{}]; print(d.get('actual_status') or '?', d.get('public_ipaddr') or '-', p[0].get('HostPort') or '-', float(d.get('dph_total') or 0))" 2>/dev/null; }
SSHO="-i $HOME/.ssh/id_ed25519 -o BatchMode=yes -o ConnectTimeout=20 -o StrictHostKeyChecking=accept-new"
connect() { if [ -n "${REH_LOCAL_DIR:-}" ]; then ST=running; IP=local; PT=0; DPH=0; return 0; fi
  read -r ST IP PT DPH <<< "$(addr)"; [ "$ST" = running ] && [ "$PT" != - ] || { log "instance $ID is ${ST:-?} (no SSH port): not now"; return 1; }; }
rsh() { local t=${2:-600}
  if [ -n "${REH_LOCAL_DIR:-}" ]; then timeout "$t" bash -c "cd '$EXPORT_ROOT' 2>/dev/null || cd '$WS'; $1"
  else timeout "$t" ssh $SSHO -p "$PT" "root@$IP" "cd $EXPORT_ROOT 2>/dev/null; $1" 2>/dev/null | grep -v "^Welcome\|^Have fun"; fi; }
rcp() { if [ -n "${REH_LOCAL_DIR:-}" ]; then mkdir -p "$(dirname "$2")"; cp "$1" "$2"; else timeout 1800 scp -q $SSHO -P "$PT" "$1" "root@$IP:$2"; fi; }
rget() { if [ -n "${REH_LOCAL_DIR:-}" ]; then cp "$1" "$2"; else timeout 600 scp -q $SSHO -P "$PT" "root@$IP:$1" "$2"; fi; }   # b100: box -> here
UENV=(-E "PATH=$PATH" -E "HOME=$HOME" -E "LRA_FAKE_VAST_BIN=${LRA_FAKE_VAST_BIN:-}" -E "LRA_UNIT_SUFFIX=$U")
pull_run() {   # $1 tag, $2 local dir, $3 run dir, $4 out
  TAG=$1 LOCAL=$2 RUN_DIR=$3 OUT=$4 EXPORT_ROOT=$EXPORT_ROOT "$HERE/package_watch.sh" "$ID" pull 2>&1 | tail -n 1; }
case "$PHASE" in
plan)
  c=$(credit); log "plan: instance $ID, credit \$${c:-?}; decisions $D:"; grep -E '^[A-Z_]+=' "$D" | sed 's/^/    /'
  echo "units: $(systemctl --user list-units --no-legend 'lra-a100*' 2>/dev/null | awk '{print $1}' | tr '\n' ' ')"
  connect && rsh "df -h $WS | tail -n 1; echo drivers: \$(pgrep -af '[o]pen_package.py run' | grep -oE -- '--out [^ ]+' | tr '\n' ' '); for f in $WS/out*/summary.json; do [ -f \$f ] && echo done: \$f; done; bash $WS/vllm_recipe_host.sh std check 2>/dev/null | tail -n 1; cat $P85B_RUN/WORKERS_WHY 2>/dev/null"
  echo "checklist: RELEASE_AT and FINAL_COMMIT set; rows (+ heartbeats if the organizers give them, else refhb after the envs); export leak scan pass; envs ok on the box; p85b stopped and pulled; vLLM recipe; credit >= ~\$150 + the guard; hold file probe/a100-hold-keepofficial-$ID present";;
rows)
  R=${1:?released rows jsonl}; H=${2:-measure}
  SHA=$(sha256sum "$R" | cut -c1-64); cp "$R" "$OFF/rows/rows.jsonl"
  if [ "$H" != measure ]; then   # given: used as is
    [ "$(realpath "$H")" = "$(realpath -m "$OFF/rows/heartbeats.jsonl")" ] || cp "$H" "$OFF/rows/heartbeats.jsonl" || { log "rows: cannot read $H"; exit 1; }
    rm -f "$OFF/rows/HB_MEASURE" "$OFF/rows/REFHB_OK" "$OFF/rows/REFHB_PLACEHOLDERS"
  else   # b100: measured by the refhb phase; a measurement of these same rows is kept
    [ "$(cat "$OFF/rows/REFHB_OK" 2>/dev/null)" = "$SHA" ] || rm -f "$OFF/rows/heartbeats.jsonl" "$OFF/rows/REFHB_OK" "$OFF/rows/REFHB_PLACEHOLDERS"
    date -u -Is > "$OFF/rows/HB_MEASURE"
  fi
  python3 - "$OFF/rows" <<'PY' 2>&1 | tee -a "$L"; [ "${PIPESTATUS[0]}" = 0 ] || exit 1
import json, sys
from pathlib import Path
d = Path(sys.argv[1]); rows = [json.loads(l) for l in (d / "rows.jsonl").read_text().splitlines() if l.strip()]
measure = (d / "HB_MEASURE").exists()   # b100: the refhb phase measures them after the envs
hp = d / "heartbeats.jsonl"
hbs = {json.loads(l)["name"]: json.loads(l) for l in hp.read_text().splitlines() if l.strip()} if hp.exists() else {}
need = ("name", "statement", "src", "proof_length", "version_info", "source", "file_path")
bad = [f"{r.get('name', '?')}: lacks {[k for k in need if k not in r]}" for r in rows if any(k not in r for k in need)]
names = [r["name"] for r in rows]
bad += ["duplicate names"] if len(set(names)) != len(names) else []
bad += [] if measure else [f"{n}: no reference heartbeats" for n in names if n not in hbs]
print("heartbeats: " + ("to measure (refhb phase, after the envs)" if measure else f"provided ({sum(1 for n in names if n in hbs)} of {len(names)} rows)"))
known = {"strata", "physlib", "cslib", "arklib", "putnambench", "leanpool"}
newsrc = sorted({r["source"] for r in rows} - known)
warm = {json.loads(l)["name"]: json.loads(l) for l in open("data/benchmark_warmup.jsonl") if l.strip()}
same = [n for n in names if n in warm]; diff = [n for n in same if warm[n]["statement"] != next(r for r in rows if r["name"] == n)["statement"]]
pins = sorted({(r["source"], v) for r in rows for vi in r["version_info"] for v in vi})
print(f"rows: {len(rows)} ({', '.join(f'{s} {sum(1 for r in rows if r['source'] == s)}' for s in sorted({r['source'] for r in rows}))}); "
      f"warm-up rows inside: {len(same)} (statement changed: {len(diff)}); (source, pin) pairs: {len(pins)}; new sources: {newsrc or 'none'}")
for b in bad:
    print("ROWS-PROBLEM", b)
sys.exit(1 if bad else 0)
PY
  args=""; for u in ${EXTRA_URLS:-}; do args="$args --url $u"; done
  python3 infra/open_package/envs_from_rows.py --rows "$OFF/rows/rows.jsonl" --out "$OFF/rows/harness_envs.official.json" $args 2>&1 | tail -n 3 | tee -a "$L"
  HBW=$([ -f "$OFF/rows/HB_MEASURE" ] && echo "heartbeats: to measure (refhb ID after the envs)" || echo "heartbeats: provided file")
  [ -s "$OFF/rows/harness_envs.official.json" ] && log "ROWS OK: $(python3 -c "import json; d=json.load(open('$OFF/rows/harness_envs.official.json')); print(len(d), 'env(s):', ' '.join(sorted(d)))") ($HBW)" || { log "envs_from_rows.py failed (a new source needs EXTRA_URLS=src=url)"; exit 1; };;
export)
  [ -n "$FINAL_COMMIT" ] || { log "export: FINAL_COMMIT is empty in $D"; exit 2; }
  python3 probe/open_package/export_release.py --commit "$FINAL_COMMIT" --out "$OFF/export" > "$OFF/export.out" 2>&1; tail -n 2 "$OFF/export.out" | tee -a "$L"
  [ -f "$OFF/export.tar.gz" ] && grep -q "leak scan pass" "$OFF/export.out" && log "EXPORT OK $(cat "$OFF/export/HARNESS_COMMIT") ($(du -h "$OFF/export.tar.gz" | cut -f1))" || { log "export FAILED"; exit 1; };;
envs)
  connect || exit 1; MODE=${2:-plan}
  [ -f "$OFF/rows/rows.jsonl" ] && [ -f "$OFF/rows/harness_envs.official.json" ] || { log "envs: run the rows phase first"; exit 2; }
  rsh "mkdir -p $RUN_DIR" >/dev/null
  # b100: the heartbeats file only when there is one (HB_MEASURE: the refhb phase writes it on the box after the envs)
  rcp "$OFF/rows/rows.jsonl" "$RUN_DIR/rows.jsonl" && { [ ! -f "$OFF/rows/heartbeats.jsonl" ] || rcp "$OFF/rows/heartbeats.jsonl" "$RUN_DIR/heartbeats.jsonl"; } && rcp "$OFF/rows/harness_envs.official.json" "$EXPORT_ROOT/infra/vast/harness_envs.official.json" || { log "envs: shipping failed"; exit 1; }
  rcp "$HERE/official_envs_host.sh" "$EXPORT_ROOT/infra/vast/official_envs_host.sh"
  rsh "bash infra/vast/official_envs_host.sh $RUN_DIR/rows.jsonl infra/vast/harness_envs.official.json $MODE" 1200 | tee -a "$L" | tail -n 25;;
refhb)   # b100 (2026-11-01): reference heartbeats measured on the box when the organizers' file is not available
  if [ ! -f "$OFF/rows/HB_MEASURE" ]; then
    [ -s "$OFF/rows/heartbeats.jsonl" ] && [ -f "$OFF/rows/rows.jsonl" ] || { log "refhb: no OFF/rows/heartbeats.jsonl and no HB_MEASURE: run the rows phase first"; exit 2; }
    # shipped every time: a file given after the envs phase (e.g. `rows R H` once a measured file is on the box) must reach RUN_DIR before start
    connect || exit 1; rsh "mkdir -p $RUN_DIR" > /dev/null
    rcp "$OFF/rows/heartbeats.jsonl" "$RUN_DIR/heartbeats.jsonl" && rcp "$OFF/rows/rows.jsonl" "$RUN_DIR/rows.jsonl" || { log "refhb: shipping the provided file failed"; exit 1; }
    log "REFHB OK: provided file used as is ($OFF/rows/heartbeats.jsonl, $(grep -c . "$OFF/rows/heartbeats.jsonl") rows; shipped to $RUN_DIR)"; exit 0
  fi
  [ -f "$OFF/rows/rows.jsonl" ] || { log "refhb: run the rows phase first"; exit 2; }
  SHA=$(sha256sum "$OFF/rows/rows.jsonl" | cut -c1-64); connect || exit 1
  if [ "$(cat "$OFF/rows/REFHB_OK" 2>/dev/null)" = "$SHA" ] && [ -s "$OFF/rows/heartbeats.jsonl" ]; then
    rcp "$OFF/rows/heartbeats.jsonl" "$RUN_DIR/heartbeats.jsonl" || { log "refhb: shipping the measured file failed"; exit 1; }
    [ -s "$OFF/rows/REFHB_PLACEHOLDERS" ] && log "refhb: NOTE $(grep -c . "$OFF/rows/REFHB_PLACEHOLDERS") placeholder row(s) in it ($OFF/rows/REFHB_PLACEHOLDERS); to measure them again: rm $OFF/rows/REFHB_OK and re-run this phase"
    log "REFHB OK: measured earlier for these rows ($OFF/rows/heartbeats.jsonl, shipped to $RUN_DIR)"; exit 0
  fi
  rsh "python3 infra/open_package/check_envs.py --rows $RUN_DIR/rows.jsonl --root \$PWD > /dev/null 2>&1 && echo envs-ok" 900 | grep -q envs-ok \
    || { log "refhb: the environments are not ready on the box (\`$0 envs $ID check\` must say ENVS OK first)"; exit 1; }
  # the tool from this checkout (the export of a FINAL_COMMIT without b100 lacks it; it imports only harness/hb_tool_eval, scorer, probe/verify_candidates)
  rsh "mkdir -p infra/refhb $RUN_DIR" > /dev/null; rcp "$ROOT/infra/refhb/make_ref_heartbeats.py" "$EXPORT_ROOT/infra/refhb/make_ref_heartbeats.py" || { log "refhb: shipping the tool failed"; exit 1; }
  AM=""; [ "${REFHB_ALLOW_MISSING:-0}" = 1 ] && AM=" --allow-missing"
  log "refhb: measuring the reference proofs on $ID (REFHB_JOBS ${REFHB_JOBS:-8}${AM:+, REFHB_ALLOW_MISSING=1: placeholders for rows without a reading}; log $RUN_DIR/refhb.log on the box)"
  # one measurement at a time (its pid file; a pgrep pattern would match the remote shell's own command line)
  rsh "rm -f $RUN_DIR/refhb.rc; if [ -f $RUN_DIR/refhb.pid ] && kill -0 \$(cat $RUN_DIR/refhb.pid) 2>/dev/null; then echo launched already-running; else (setsid nohup bash -c 'echo \$\$ > $RUN_DIR/refhb.pid; python3 infra/refhb/make_ref_heartbeats.py --rows $RUN_DIR/rows.jsonl --out $RUN_DIR/heartbeats.jsonl --jobs ${REFHB_JOBS:-8} --resume$AM > $RUN_DIR/refhb.log 2>&1; echo \$? > $RUN_DIR/refhb.rc' > /dev/null 2>&1 < /dev/null &); echo launched; fi" 120 | grep -q launched || { log "refhb: could not launch on the box"; exit 1; }
  t0=$(date +%s); rc=""
  while :; do
    sleep "${REFHB_POLL_S:-20}"; rc=$(rsh "cat $RUN_DIR/refhb.rc 2>/dev/null" 60 | tr -dc 0-9)
    [ -n "$rc" ] && break
    [ $(( $(date +%s) - t0 )) -ge "${REFHB_MAX_S:-3600}" ] && { log "refhb: not done after ${REFHB_MAX_S:-3600}s (still running on the box: $RUN_DIR/refhb.log; re-run this phase to wait again, it resumes)"; exit 1; }
  done
  rsh "grep -E 'REFHB|FAILED|PLACEHOLDER|WARNING' $RUN_DIR/refhb.log | tail -n 8 | cut -c1-400" 60 | tee -a "$L"
  [ "$rc" = 0 ] || { log "refhb FAILED (rc $rc): rows without a reading are listed above ($RUN_DIR/refhb.log); fix their envs and re-run \`$0 refhb $ID\` (it resumes), give the organizers' file: \`$0 rows R H\`, or let start proceed with flagged placeholders: REFHB_ALLOW_MISSING=1 \`$0 refhb $ID\`"; push "official refhb FAILED on $ID (rc $rc): see $RUN_DIR/refhb.log"; exit 1; }
  rget "$RUN_DIR/heartbeats.jsonl" "$OFF/rows/heartbeats.jsonl.new" && rget "$RUN_DIR/heartbeats.jsonl.meta.json" "$OFF/rows/heartbeats.jsonl.meta.json" || { log "refhb: pulling the measured file failed"; exit 1; }
  python3 - "$OFF/rows" <<'PY' 2>&1 | tee -a "$L"; [ "${PIPESTATUS[0]}" = 0 ] || exit 1
import json, sys
from pathlib import Path
d = Path(sys.argv[1]); rows = [json.loads(l) for l in (d / "rows.jsonl").read_text().splitlines() if l.strip()]
hbs = {h["name"]: h["heartbeat"] for l in (d / "heartbeats.jsonl.new").read_text().splitlines() if l.strip() for h in [json.loads(l)]}
miss = [k for k, r in enumerate(rows) if not (isinstance(hbs.get(r["name"]), int) and hbs[r["name"]] > 0)]
meta = json.loads((d / "heartbeats.jsonl.meta.json").read_text()).get("rows", {})
how = {}
for m in meta.values():
    how[str(m.get("method"))] = how.get(str(m.get("method")), 0) + 1
print(f"refhb coverage: {len(rows) - len(miss)}/{len(rows)} rows; methods {how}" + (f"; MISSING row#{miss[:10]}" if miss else ""))
full = json.loads((d / "heartbeats.jsonl.meta.json").read_text())
ph, warns = full.get("placeholders") or {}, full.get("env_warnings") or {}
idx = {r["name"]: k for k, r in enumerate(rows)}
(d / "REFHB_PLACEHOLDERS.new").write_text("".join(f"row#{idx.get(n, -1):02d}\t{n}\t{k}\n" for n, k in sorted(ph.items(), key=lambda x: idx.get(x[0], -1))))
if ph:
    print(f"refhb PLACEHOLDERS: {len(ph)} row(s) carry a flagged stand-in, not a reading: "
          + ", ".join(f"row#{idx.get(n, -1):02d} ({k})" for n, k in sorted(ph.items(), key=lambda x: idx.get(x[0], -1))[:12]))
if warns:
    print(f"refhb WARNING env pin: {len(warns)} row(s) measured on an environment not at the row's pin commit: "
          + ", ".join(f"row#{idx.get(n, -1):02d}" for n in sorted(warns, key=lambda n: idx.get(n, -1))[:12]) + " (meta file: env_warning)")
sys.exit(1 if miss else 0)
PY
  mv "$OFF/rows/heartbeats.jsonl.new" "$OFF/rows/heartbeats.jsonl" && mv "$OFF/rows/REFHB_PLACEHOLDERS.new" "$OFF/rows/REFHB_PLACEHOLDERS" && echo "$SHA" > "$OFF/rows/REFHB_OK"
  if [ -s "$OFF/rows/REFHB_PLACEHOLDERS" ]; then
    n=$(grep -c . "$OFF/rows/REFHB_PLACEHOLDERS")
    log "REFHB OK WITH $n PLACEHOLDER(S) (REFHB_ALLOW_MISSING=1): $(cut -f1,3 "$OFF/rows/REFHB_PLACEHOLDERS" | tr '\t\n' ' ;' | cut -c1-300)"
    push "official refhb on $ID: $n row(s) got a PLACEHOLDER reference (no reading; $OFF/rows/REFHB_PLACEHOLDERS); start may proceed"
  fi
  log "REFHB OK: $(grep -c . "$OFF/rows/heartbeats.jsonl") rows measured on $ID -> $RUN_DIR/heartbeats.jsonl (+ $OFF/rows/heartbeats.jsonl)";;
stop-p85b)
  connect || exit 1; END_S=${2:-0}
  rcp "$HERE/package_stop_host.sh" "$WS/package_stop_host.sh"
  rsh "[ -f $P85B_RUN/RUN_CMD ] || { echo 'no p85b run: nothing to stop'; exit 0; }; bash $WS/package_stop_host.sh $P85B_RUN $END_S" $((END_S + 7200)) | tee -a "$L" | tail -n 4
  pull_run p85b "${P85B_LOCAL:-probe/a100-reh-p85b}" "$P85B_RUN" "$P85B_OUT" | tee -a "$L"
  for u in "lra-a100-watch-p85b$U" "lra-a100-alarm-p85b$U"; do systemctl --user is-active -q "$u" && { systemctl --user stop "$u"; log "stopped $u (p85b stopped and pulled)"; }; done; true;;
ship)
  connect || exit 1
  [ -f "$OFF/export.tar.gz" ] || { log "ship: no $OFF/export.tar.gz (export phase)"; exit 2; }
  rsh "pgrep -af '[o]pen_package.py run' | grep -F -- '--out $WS/' | head -n 3" | grep -q . && { log "ship REFUSED: a package driver is alive on the box (stop it first: stop-p85b)"; exit 1; }
  rcp "$OFF/export.tar.gz" "$WS/export-official.tar.gz" && rcp "$OFF/export.sha256" "$WS/export-official.sha256" || exit 1
  rsh "cd $WS && sed 's/export.tar.gz/export-official.tar.gz/' export-official.sha256 | sha256sum -c --quiet - && C=$WS/lra-code-official-\$(date +%s) && mkdir -p \$C && tar -xzf export-official.tar.gz -C \$C --strip-components=1 && rsync -a --exclude envs --exclude .envs-download --exclude probe/runs \$C/ $EXPORT_ROOT/ && cat $EXPORT_ROOT/HARNESS_COMMIT" 900 | tee -a "$L" | tail -n 1 > "$OFF/shipped"
  [ "$(cat "$OFF/shipped")" = "$(cat "$OFF/export/HARNESS_COMMIT")" ] && log "SHIP OK: $EXPORT_ROOT runs $(cat "$OFF/shipped")" || { log "ship FAILED (box HARNESS_COMMIT '$(cat "$OFF/shipped")')"; exit 1; };;
vllm)
  connect || exit 1; RECIPE=${VLLM_RECIPE:-$([ "${WORKERS:-12}" -gt 12 ] && echo std32 || echo std)}
  [ -n "${REH_LOCAL_DIR:-}" ] && { log "vllm: local mode has no vLLM (recipe would be $RECIPE)"; exit 0; }
  rcp "$HERE/vllm_recipe_host.sh" "$WS/vllm_recipe_host.sh"
  rsh "bash $WS/vllm_recipe_host.sh $RECIPE" 1800 | tee -a "$L" | tail -n 3;;
start)
  connect || exit 1
  [ -n "$RELEASE_AT" ] || { log "start: RELEASE_AT is empty in $D"; exit 2; }
  if [ -f "$OFF/rows/HB_MEASURE" ] && [ "$(cat "$OFF/rows/REFHB_OK" 2>/dev/null)" != "$(sha256sum "$OFF/rows/rows.jsonl" | cut -c1-64)" ]; then
    log "start REFUSED: the reference heartbeats are to be measured and are not yet (\`$0 refhb $ID\` after ENVS OK)"; exit 1; fi
  REL=$(date -u -d "$RELEASE_AT" +%s) || { log "start: bad RELEASE_AT"; exit 2; }
  [ "$REL" -le $(( $(date +%s) + 600 )) ] || { log "start REFUSED: RELEASE_AT $RELEASE_AT is in the future"; exit 2; }
  JOB=${JOB:-172800}; CK="$OFF/clock_start.json"
  # CLOCK_START (operator 2026-11-01 ~06:05 UTC, default launch): the first start records its clock in $CK; a later start (a resume after
  # a box restart) reuses it, so the 48 h never restart. release = START at RELEASE_AT (the setup counts inside the 48 h).
  if [ -s "$CK" ] && [ -z "${CLOCK_RESET:-}" ]; then
    START=$(python3 -c 'import json,sys; print(int(json.load(open(sys.argv[1]))["start_epoch"]))' "$CK") || { log "start: unreadable $CK"; exit 2; }
    log "start: clock reused from $CK (START $START)"
  else
    case "${CLOCK_START:-launch}" in
      launch) START=$(date +%s);;
      release) START=$REL;;
      *) log "start: CLOCK_START must be launch or release (got '${CLOCK_START}')"; exit 2;;
    esac
    python3 - "$CK" "$RELEASE_AT" "$REL" "$START" "$JOB" "${CLOCK_START:-launch}" <<'PY' || { log "start: could not write $CK"; exit 2; }
import json, sys, time
ck, rel_at, rel, start, job, mode = sys.argv[1:]
g = lambda e: time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(int(e)))
json.dump({"clock_start": mode, "release_at": rel_at, "release_epoch": int(rel), "release_utc": g(rel), "start_epoch": int(start),
           "start_utc": g(start), "job_seconds": int(job), "end_utc": g(int(start) + int(job)), "setup_seconds": int(start) - int(rel)},
          open(ck, "w"), indent=1)
PY
    log "start: clock $(tr -d '\n' < "$CK")"
  fi
  left=$((START + JOB - $(date +%s))); [ "$left" -gt "${MIN_LEFT_S:-10800}" ] || { log "start REFUSED: only ${left}s left on the 48 h clock"; exit 1; }
  X="--end-pipeline on"; [ "$AUTO_BRIEF" = on ] && X="$X --auto-brief on"; [ "${DIALECT_CARD:-off}" = on ] && X="$X --dialect-card on"; X="$X${DRY_EXTRA:+ $DRY_EXTRA}"
  [ -n "${LRA_BASE_URL:-}" ] && EP="LRA_BASE_URL=$LRA_BASE_URL LRA_API_KEY_FILE=${LRA_API_KEY_FILE:-}" || EP=""
  log "start: TAG $TAG START $START (clock ${CLOCK_START:-launch}; release $RELEASE_AT) JOB $JOB (${left}s left) WORKERS $WORKERS MAX_SESSIONS $MAX_SESSIONS END_SECONDS $END_SECONDS EXTRA '$X'"
  rsh "$EP RUN_DIR=$RUN_DIR OUT=$OUT TAG=$TAG START=$START JOB=$JOB WORKERS=$WORKERS MAX_SESSIONS=$MAX_SESSIONS END_SECONDS=$END_SECONDS EXTRA='$X' MIN_FREE_GB=${MIN_FREE_GB:-20} DF_PATH=${DF_PATH:-$WS} bash infra/vast/package_run.sh" 900 | tee -a "$L" | grep -q "driver running" || { log "start: package_run.sh refused or failed (above)"; exit 1; }
  if [ -z "${REH_LOCAL_DIR:-}" ]; then
    rsh "for p in \$(pgrep -f '[t]unnel_watch_host.sh'); do grep -qa STATUS_ONLY=1 /proc/\$p/environ && kill -TERM \$p; done; sleep 2; STATUS_ONLY=1 RUN_DIR=$RUN_DIR OUT_DIR=$OUT setsid nohup bash $WS/tunnel_watch_host.sh > $WS/tunnel_watch_off.log 2>&1 < /dev/null & pgrep -f '[s]idecar.py --label a100-off' > /dev/null || (cd $WS && PATH=/opt/google-cloud-sdk/bin:\$PATH setsid nohup python3 $WS/infra/sync/sidecar.py --label a100-off --key /root/.config/vexorium/gcs_sync_key.json --watch 'lra/probe/runs/off-*/verified.jsonl' --paths lra/reh/status.json lra-run-off out-off --snapshot-every 120 > $WS/sidecar_off.log 2>&1 < /dev/null &); sleep 3; echo status-writer \$(pgrep -fc '[t]unnel_watch_host.sh') sidecar \$(pgrep -fc '[s]idecar.py --label a100-off')" 60 | tee -a "$L"
  fi
  log "STARTED official run on $ID";;
arm)
  c=$(credit); [ -n "$c" ] || { log "arm: vast credit unreadable; not armed"; exit 1; }
  for spec in "lra-a100-watch$U:probe/a100-reh-p85/watch.log" "lra-a100-watch-p85b$U:probe/a100-reh-p85b/watch.log"; do
    u=${spec%%:*}; wl=${spec#*:}
    systemctl --user is-active -q "$u" || continue
    if grep -q "run finished" "$wl" 2>/dev/null; then systemctl --user stop "$u"; log "stopped $u (its run finished and was pulled; it would release the box when its hold wait ends)"
    else log "WARN $u: no 'run finished' line in $wl; stopped anyway (an older run's watch must not relaunch its run or release the box during the official run; stop-p85b pulled p85b)"; systemctl --user stop "$u"; fi
  done
  for u in "lra-a100-alarm$U" "lra-a100-alarm-p85b$U"; do systemctl --user is-active -q "$u" && { systemctl --user stop "$u"; log "stopped $u"; }; done
  systemctl --user stop "lra-a100-spendguard$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-spendguard$U" 2>/dev/null
  systemd-run --user --unit "lra-a100-spendguard$U" --working-directory="$ROOT" "${UENV[@]}" \
    -E SPEND_CAP="$GUARD_ADD" -E CREDIT_FLOOR="${CREDIT_FLOOR:-5}" -E KEPT_GRACE_MIN="${KEPT_GRACE_MIN:-45}" -E GUARD_POLL_S="${GUARD_POLL_S:-60}" -E STALE_S="${STALE_S:-1800}" \
    -E IDLE_MIN="${IDLE_MIN:-30}" -E IDLE_GPU="${IDLE_GPU:-5}" -E IDLE_CPU="${IDLE_CPU:-5}" -E REMIND_MIN="${REMIND_MIN:-30}" -E BUSY_CHECK="${BUSY_CHECK-python3 probe/a100-alarm/run_busy.py --label a100-off}" \
    -E PRE_DESTROY="TAG=$TAG LOCAL=probe/a100-reh-$TAG RUN_DIR=$RUN_DIR OUT=$OUT EXPORT_ROOT=$EXPORT_ROOT infra/vast/package_watch.sh {ID} pull" -E PRE_DESTROY_MAX_S=900 -E TAG=$TAG -E REH_LOCAL_DIR="${REH_LOCAL_DIR:-}" \
    bash -c "infra/vast/spend_guard.sh $ID $c 2>> probe/a100-spend-guard.log > /dev/null" > /dev/null && log "spend guard re-armed for the official run: cap \$$GUARD_ADD more from credit \$$c (ask-first)"
  systemctl --user stop "lra-a100-watch-$TAG$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-watch-$TAG$U" 2>/dev/null; mkdir -p "probe/a100-reh-$TAG"
  systemd-run --user --unit "lra-a100-watch-$TAG$U" --working-directory="$ROOT" "${UENV[@]}" -E TAG=$TAG -E RUN_DIR="$RUN_DIR" -E OUT="$OUT" -E EXPORT_ROOT="$EXPORT_ROOT" \
    -E REH_LOCAL_DIR="${REH_LOCAL_DIR:-}" -E LOCAL="probe/a100-reh-$TAG" -E POLL_S="${WATCH_POLL_S:-60}" -E PULL_EVERY_S="${PULL_EVERY_S:-300}" -E STALL_MIN="${STALL_MIN:-20}" -E HOLD_MAX_S="$HOLD_MAX_S" \
    bash -c "infra/vast/package_watch.sh $ID >> probe/a100-reh-$TAG/watch.out 2>&1" > /dev/null && log "watch armed: lra-a100-watch-$TAG$U (HOLD_MAX_S $HOLD_MAX_S)"
  ls probe/a100-hold*-"$ID" > /dev/null 2>&1 || log "WARN no hold file probe/a100-hold*-$ID: the watch RELEASES the box right after the final pull"
  systemctl --user stop "lra-a100-alarm-$TAG$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-alarm-$TAG$U" 2>/dev/null
  systemd-run --user --unit "lra-a100-alarm-$TAG$U" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" \
    python3 probe/a100-alarm/alarm.py --reh "probe/a100-reh-$TAG" --id "$ID" --run-dir "$RUN_DIR" --out-dir "$OUT" ${NO_ALARM_LIVE:+--no-live --no-push} > /dev/null && log "alarm armed: lra-a100-alarm-$TAG$U"
  printf -- "- %s UTC official open run on %s armed: guard +\$%s from credit \$%s, watch HOLD_MAX_S %s\n" "$(date -u +%Y-%m-%dT%H:%M)" "$ID" "$GUARD_ADD" "$c" "$HOLD_MAX_S" >> "${ACC:-accounting/a100_poc.md}"
  log "ARMED official run";;
status)
  c=$(credit); connect || exit 1
  echo "instance $ID: $ST at \$$DPH/h; credit \$$c; units: $(systemctl --user list-units --no-legend 'lra-a100*' 2>/dev/null | awk '{print $1}' | tr '\n' ' ')"
  rsh "tail -n 3 $RUN_DIR/driver.log 2>/dev/null | cut -c1-160; echo sessions \$(wc -l < $OUT/agent_sessions.jsonl 2>/dev/null); [ -f $OUT/summary.json ] && echo DONE; df -h $WS | tail -n 1";;
upload)
  LOC=probe/a100-reh-$TAG; [ -n "${REH_LOCAL_DIR:-}" ] || { connect && pull_run "$TAG" "$LOC" "$RUN_DIR" "$OUT"; }
  [ -n "${REH_LOCAL_DIR:-}" ] && { mkdir -p "$LOC/out"; cp "$OUT/proofs.jsonl" "$OUT/summary.json" "$LOC/out/" 2>/dev/null; }
  [ -f "$LOC/out/proofs.jsonl" ] && [ -f "$LOC/out/summary.json" ] || { log "upload: no proofs.jsonl + summary.json in $LOC/out yet"; exit 1; }
  mkdir -p "$OFF/upload"; F=$OFF/upload/open_official_$(date -u +%Y%m%dT%H%M).jsonl
  python3 - "$LOC/out/proofs.jsonl" "$OFF/rows/rows.jsonl" "$F" <<'PY' 2>&1 | tee -a "$L"; rc=${PIPESTATUS[0]}
import json, sys
from scorer.forbidden import check_forbidden
from scorer.tokenize import split_declaration
P, R, F = sys.argv[1:4]
rows = [json.loads(l) for l in open(R) if l.strip()]; got = {json.loads(l)["name"]: json.loads(l) for l in open(P) if l.strip()}
out, bad = [], []
for r in rows:
    e = got.get(r["name"])
    if not e:
        bad.append(f"{r['name']}: no proof"); continue
    p = e["proof"].rstrip() + "\n"
    if split_declaration(p.rstrip(), r["statement"]) is None: bad.append(f"{r['name']}: statement prefix")
    if check_forbidden(p) is not None: bad.append(f"{r['name']}: forbidden {check_forbidden(p)}")
    if len(p.encode()) > 256 * 1024: bad.append(f"{r['name']}: proof > 256 KB")
    out.append({"name": r["name"], "proof": p})
blob = "".join(json.dumps(x, ensure_ascii=False) + "\n" for x in out)
if len(blob.encode()) > 8 * 1024 * 1024: bad.append("file > 8 MB")
open(F, "w").write(blob)
s = json.load(open(P.replace("proofs.jsonl", "summary.json")))
print(f"upload file {F}: {len(out)} of {len(rows)} rows; stored mean {s.get('stored_mean')}; sources {s.get('sources')}")
for b in bad: print("UPLOAD-PROBLEM", b)
sys.exit(1 if bad else 0)
PY
  [ "$rc" = 0 ] && log "UPLOAD FILE OK: $F (the coordinator registers + uploads it: submit/ledger.py; code: the export of $(cat "$OFF/export/HARNESS_COMMIT" 2>/dev/null) zipped + README)" || exit 1
  if [ -f "$OFF/export.tar.gz" ]; then C=$(cat "$OFF/export/HARNESS_COMMIT"); Z=$OFF/upload/vexorium_open_code_$C.zip
    [ -f "$Z" ] || python3 -c "import shutil, sys; shutil.make_archive(sys.argv[1], 'zip', sys.argv[2])" "${Z%.zip}" "$OFF/export"; log "code zip: $Z (README: docs/open_package_readme.md inside)"; fi;;
*) echo "phases: plan rows export envs refhb stop-p85b ship vllm start arm status upload"; exit 2;;
esac
