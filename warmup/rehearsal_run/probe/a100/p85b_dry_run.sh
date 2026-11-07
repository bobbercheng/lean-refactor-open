#!/usr/bin/env bash
# $0 dry run of the p85b continuation path (2026-10-31; infra/vast/p85b_launch_host.sh, package_stop_host.sh, p85b_arm_gb10.sh). Nothing is
# rented, no model is called, no live unit is touched (units suffixed -dry<pid>; the GB10 scripts run from a scratch copy with their own
# probe/ and accounting). The "box" is SCRATCH/workspace: the box's export tarball (BOX_EXPORT, c29a8183, scp'd from /workspace) unpacked into
# workspace/lra with the dev envs linked, a fake finished p85 (lra-run + out with 2 non-benchmark abpool rows: row 0 banked, row 1 never
# ran), a fake scaling summary, the fake model (probe/open_package/fake_model.py), fake vastai. Real Lean: run it in a capped unit:
#   systemd-run --user --collect -u lra-p85b-dry -p MemoryMax=48G -p OOMPolicy=continue -p CPUWeight=50 -p RuntimeMaxSec=5400 \
#     -p WorkingDirectory=$PWD -E PATH -E HOME /bin/bash probe/a100/p85b_dry_run.sh [SCRATCH]
# Checks (PASS/FAIL lines): the launcher waits for p85 and the scaling test, picks the workers from the summary, copies state (no session
# log), seeds from the export when asked, starts the driver through package_run.sh with p85's command shape, the first sessions resume
# (no --fresh) except the row without state; a second launcher leaves; the GB10 arm script arms watch / alarm / guard and writes the
# babysit entry; an outbid-style kill is resumed by relaunch.sh; package_stop_host.sh stops it with the export written and no relaunch after.
set -u
cd "$(dirname "$0")/../.." || exit 2
ROOT=$PWD; S=$(realpath -m "${1:-$ROOT/probe/a100/dry/p85b-$(date -u +%Y%m%dT%H%M%S)}"); W=$S/workspace
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$(id -u)} DBUS_SESSION_BUS_ADDRESS=${DBUS_SESSION_BUS_ADDRESS:-unix:path=/run/user/$(id -u)/bus}
U="-dry$$"; PASS=0; FAIL=0
ok() { echo "PASS: $*"; PASS=$((PASS + 1)); }
bad() { echo "FAIL: $*"; FAIL=$((FAIL + 1)); }
check() { if eval "$1"; then ok "$2"; else bad "$2"; fi; }
wait_for() { local i; for i in $(seq 1 "$2"); do eval "$1" && { ok "$3 (after ${i}s)"; return 0; }; sleep 1; done; bad "$3 (not within $2 s)"; return 1; }
FAKES=""
cleanup() { for p in $FAKES; do kill "$p" 2>/dev/null; done
  for d in $(pgrep -f "[o]pen_package.py run .*--out $W/out-p85b "); do kill -KILL "$d" 2>/dev/null; done
  pkill -KILL -f "[h]arness/agent.py .*--run-id p85b-s" 2>/dev/null
  systemctl --user stop "lra-a100-watch-p85b$U" "lra-a100-alarm-p85b$U" "lra-a100-spendguard$U" 2>/dev/null; systemctl --user reset-failed 2>/dev/null; true; }
trap cleanup EXIT
mkdir -p "$W" "$S/gb10"
echo "== p85b dry run in $S (units suffixed $U)"
# ---- the box: export of the box's code, envs linked
# the box's own export (scp'd from /workspace/export.tar.gz: c29a8183; export_release.py at HEAD cannot re-export an older commit)
BOX_EXPORT=${BOX_EXPORT:-$ROOT/probe/a100/dry/box-export/export.tar.gz}; cp "$BOX_EXPORT" "$S/export.tar.gz"
check '[ -f "$S/export.tar.gz" ] && [ "$(tar -xzOf "$S/export.tar.gz" --wildcards "*/HARNESS_COMMIT")" = "${EXPORT_COMMIT:-c29a8183}" ]' "D1 the box's export (${EXPORT_COMMIT:-c29a8183})"
mkdir -p "$W/lra" && tar -xzf "$S/export.tar.gz" -C "$W/lra" --strip-components=1
mkdir -p "$W/lra/envs"; for e in "$ROOT"/envs/*; do b=$(basename "$e"); [ -e "$W/lra/envs/$b" ] || ln -s "$e" "$W/lra/envs/$b"; done
cp infra/vast/p85b_launch_host.sh infra/vast/package_stop_host.sh "$W/"
# ---- fake p85 (finished): rows, run dir, out with one banked row and one row without state
mkdir -p "$W/lra-run" "$W/out/work" "$W/scale"
python3 - "$W" <<'PY'
import json, re, sys
W = sys.argv[1]
pick = ["CallElimCorrect.normalizeOldExprInVars", "Code.closeToWord_iff_exists_agreementCols"]
rows = {json.loads(l)["name"]: l for l in open("data/abpool/abpool.jsonl") if l.strip()}
hbs = {json.loads(l)["name"]: l for l in open("data/abpool/heartbeats.jsonl") if l.strip()}
warm = {json.loads(l)["name"] for l in open("data/benchmark_warmup.jsonl") if l.strip()}
assert not (set(pick) & warm)
open(f"{W}/lra-run/rows.jsonl", "w").write("".join(rows[n].rstrip("\n") + "\n" for n in pick))
open(f"{W}/lra-run/heartbeats.jsonl", "w").write("".join(hbs[n].rstrip("\n") + "\n" for n in pick))
r0 = json.loads(rows[pick[0]]); safe = lambda n: re.sub(r"[^A-Za-z0-9_.-]", "_", n)
import os
d = f"{W}/out/work/{safe(pick[0])}"; os.makedirs(d)
st = {"problem": pick[0], "best": {"score": 41.0, "proof": r0["src"].rstrip() + "\n", "tokens": r0["proof_length"], "heartbeats": 5000},
      "attempts": [{"sha": "aaaa", "tokens": 200, "heartbeats": 5000, "ok": True, "error": None, "run_id": "p85-s00-k1", "t": "2026-10-31T01:00:00Z"}],
      "runs": [{"run_id": "p85-s00-k1", "model": "glm-5.3-flash", "started": "2026-10-31T01:00:00Z"}], "ledger": {"wins": []}}
open(f"{d}/state.json", "w").write(json.dumps(st)); open(f"{d}/notes.md", "w").write("# Notes (yours to keep; persisted across runs)\n- p85 note\n")
open(f"{W}/out/agent_sessions.jsonl", "w").write(json.dumps({"problem": pick[0], "row": 0, "k": 1, "run_id": "p85-s00-k1"}) + "\n")
open(f"{W}/out/proofs.jsonl", "w").write(json.dumps({"name": pick[0], "proof": r0["src"].rstrip() + "\n", "source": "normalize", "stored_score": 42.5,
                                                     "tokens": r0["proof_length"], "heartbeats": 4900}) + "\n")
json.dump({"p12": {"gen_tok_s": 520.0, "kv_max": 0.31, "waiting_mean": 0.0}, "p16": {"gen_tok_s": 610.0, "kv_max": 0.44, "waiting_mean": 0.0},
           "p20": {"gen_tok_s": 640.0, "kv_max": 0.58, "waiting_mean": 0.4}}, open(f"{W}/scale/summary.json", "w"))
PY
echo "python3 harness/open_package.py run --rows $W/lra-run/rows.jsonl --heartbeats $W/lra-run/heartbeats.jsonl --out $W/out --tag p85 --base-url https://lra-a100:8000/v1 --api-key-file /root/.config/vexorium/vllm_api_key --api-model glm-5.3-flash --started-at 1793401053 --job-seconds 60560 --workers 12 --max-sessions 4 --end-seconds 7200 --end-pipeline on" > "$W/lra-run/RUN_CMD"
echo "[06:42:28] waiting for p85's end stage" > "$W/scale/scale.log"
# fake p85 driver + fake scaling test (argv only: pgrep -f matches the command line)
bash -c "exec -a 'python3 harness/open_package.py run --rows x --out $W/out --tag p85' sleep 600" & FAKES="$FAKES $!"; P85FAKE=$!
bash -c "exec -a 'bash $W/scale_test_host.sh' sleep 600" & FAKES="$FAKES $!"; SCALEFAKE=$!
# ---- the fake model
PORT=$(python3 -c 'import socket; s=socket.socket(); s.bind(("127.0.0.1",0)); print(s.getsockname()[1])')
python3 probe/open_package/fake_model.py --port "$PORT" --log "$S/fake_requests.jsonl" > "$S/fake_model.log" 2>&1 & FAKES="$FAKES $!"
for i in $(seq 1 50); do curl -s "http://127.0.0.1:$PORT/v1/models" > /dev/null && break; sleep 0.2; done
END_AT=$(date -u -d "@$(( $(date +%s) + 4200 ))" '+%Y-%m-%d %H:%M:%S UTC')
cat > "$W/p85b.conf" <<CONF
END_AT="$END_AT"
ROWS_SET=all18
MAX_SESSIONS=2
SEED_FROM_EXPORT=1
MIN_JOB_S=600
WAIT_UNTIL="$(date -u -d "@$(( $(date +%s) + 900 ))" '+%Y-%m-%d %H:%M:%S UTC')"
CONF
# ---- launcher, armed while "p85" still runs
export W LRA_BASE_URL="http://127.0.0.1:$PORT/v1" SKIP_AUX=1 POLL_S=2 END_SECONDS=900 DF_PATH=$S MIN_FREE_GB=5 \
  DRY_EXTRA="--turns 9 --no-adaptive-turns --max-api-retries 2 --min-session-seconds 300 --compile-slots 3 --end-jobs 2 --normalize-seconds 600 --normalize-row-seconds 300 --export-margin 300 --connect-budget-seconds 120"
setsid nohup bash "$W/p85b_launch_host.sh" > "$S/launcher.out" 2>&1 < /dev/null &
LP=$!
wait_for 'grep -q "waiting: p85 not done" "$W/p85b_launch.log" 2>/dev/null' 30 "L1 launcher waits while p85's driver is alive"
echo '{"rows": 2, "stored_mean": 41.0}' > "$W/out/summary.json"; kill "$P85FAKE"
wait_for 'grep -q "waiting: scaling test still running" "$W/p85b_launch.log"' 30 "L2 then waits for the scaling test (process alive, no done line)"
bash "$W/p85b_launch_host.sh" > "$S/launcher2.out" 2>&1; check 'grep -q "another p85b launcher holds" "$S/launcher2.out"' "L3 a second launcher leaves at once (flock)"
echo "[14:10:00] scale test done" >> "$W/scale/scale.log"; kill "$SCALEFAKE"
wait_for 'grep -q "LAUNCHED p85b\|NOT launched" "$W/p85b_launch.log"' 240 "L4 launcher finished"
check 'grep -q "LAUNCHED p85b" "$W/p85b_launch.log"' "L5 LAUNCHED: $(grep -E 'LAUNCHED|NOT launched' "$W/p85b_launch.log" | tail -n 1 | cut -c1-160)"
R=$W/lra-run-p85b; O=$W/out-p85b
check 'grep -q "workers 16: p16/p12 total gen 610.0/520.0" "$W/p85b_launch.log"' "L6 workers 16 from the scaling summary (1.173 >= 1.10, kv 0.44, no waiting)"
check 'grep -q -- "--out $O --tag p85b " "$R/RUN_CMD" && grep -q -- "--workers 16 --max-sessions 2 --end-seconds 900 --end-pipeline on" "$R/RUN_CMD" && ! grep -q -- "--style-rw\|--blind-start" "$R/RUN_CMD" && grep -q -- "--rows $R/rows.jsonl" "$R/RUN_CMD"' "L7 RUN_CMD: $(cut -c1-150 "$R/RUN_CMD")..."
check '[ -f "$R/RUN_ENV" ] && [ -x "$R/relaunch.sh" ] && grep -q "OUT=$O" "$R/RUN_ENV"' "L8 RUN_ENV + relaunch.sh installed in the p85b run dir"
check '[ ! -e "$O/agent_sessions.jsonl" ] || ! grep -q "p85-s00-k1" "$O/agent_sessions.jsonl"' "L9 p85's session log not copied"
python3 - "$O/work/CallElimCorrect.normalizeOldExprInVars/state.json" > "$S/l10.out" 2>&1 <<'PY2'
import json, sys
s = json.load(open(sys.argv[1]))
assert s["best"]["score"] >= 42.5, s["best"].get("score")
assert any(r["run_id"] == "p85-s00-k1" for r in s["runs"]), s["runs"]
PY2
r=$?; check '[ "$r" = 0 ]' "L10 row 0 resumes p85's state (p85 run kept in runs), seeded from the export (42.5 > 41.0): $(tail -n 1 "$S/l10.out")"
check 'grep -q "p85 note" "$O/work/CallElimCorrect.normalizeOldExprInVars/notes.md"' "L11 notes.md copied"
wait_for 'ls "$O"/logs/s00.k1.log "$O"/logs/s01.k1.log > /dev/null 2>&1' 120 "L12 both rows' first p85b sessions started"
check '! grep -q -- "--fresh" "$O/logs/s00.k1.log" && grep -q -- "--fresh" "$O/logs/s01.k1.log"' "L13 row 0 resumes (no --fresh), row 1 without state starts --fresh"
check 'grep -q "row#00 session 1 starts .*best 42.50" "$R/driver.log"' "L14 driver: row 0 session 1 starts from the seeded best 42.50"
bash "$W/p85b_launch_host.sh" > "$S/launcher3.out" 2>&1; check 'grep -q "already launched" "$W/p85b_launch.log"' "L15 a launcher after the launch leaves (RUN_CMD exists)"
# ---- the GB10 arm script (scratch copy: its own probe/, accounting/, fake vastai with the instance listed)
G=$S/gb10; mkdir -p "$G/infra" "$G/probe" "$G/accounting" "$G/bin"; cp -r infra/vast infra/sync "$G/infra/"; cp -r probe/a100-alarm "$G/probe/"
cat > "$G/bin/vastai" <<VB
#!/usr/bin/env bash
FAKE_VASTAI_STATE=$G/fake_state.json exec python3 $ROOT/probe/a100/fake_vastai.py "\$@"
VB
chmod +x "$G/bin/vastai"
python3 - "$G/fake_state.json" "$ROOT" <<'PY'
import json, sys
sys.path.insert(0, sys.argv[2] + "/probe/a100"); import fake_vastai as F
s = F.default_state(); s["user"]["credit"] = 200.0
s["instances"]["90000001"] = {"id": 90000001, "machine_id": 1, "actual_status": "running", "intended_status": "running", "status_msg": "", "public_ipaddr": "127.0.0.1",
                              "ports": {"22/tcp": [{"HostPort": "22"}]}, "dph_total": 2.5, "dph_base": 2.48, "min_bid": 2.0, "is_bid": True, "gpu_name": "A100 SXM4",
                              "num_gpus": 4, "label": "", "inet_down_cost": 0.004, "gpu_util": 90.0, "cpu_util": 50.0}
json.dump(s, open(sys.argv[1], "w"))
PY
mkdir -p "$S/p85local"; echo "[x] run finished: {}" > "$S/p85local/watch.log"
( cd "$G" && LRA_FAKE_VAST_BIN=$G/bin LRA_UNIT_SUFFIX=$U REH_LOCAL_DIR=$S RUN_DIR=$R OUT=$O EXPORT_ROOT=$W/lra LAUNCH_LOG=$W/p85b_launch.log \
    LOCAL=$S/gb10/reh-p85b P85_LOCAL=$S/p85local BABYSIT=$S/babysit.md ACC=$S/acc.md NO_ALARM_LIVE=1 POLL_S=2 WATCH_POLL_S=10 PULL_EVERY_S=20 BUSY_CHECK="" \
    GUARD_POLL_S=5 bash infra/vast/p85b_arm_gb10.sh 90000001 > "$S/arm.out" 2>&1 )
check 'grep -q "ARMED" "$S/arm.out"' "A1 arm script: $(tail -n 1 "$S/arm.out" | cut -c1-120)"
check 'systemctl --user is-active -q "lra-a100-watch-p85b$U" && systemctl --user is-active -q "lra-a100-alarm-p85b$U" && systemctl --user is-active -q "lra-a100-spendguard$U"' "A2 units active: watch, alarm, spend guard (suffixed)"
check 'systemctl --user show "lra-a100-spendguard$U" -p Environment | grep -q "SPEND_CAP=40 " && grep -qF "cap \$40 more from credit \$200.00" "$S/arm.out"' "A3 guard re-armed: cap \$40 from the credit now, ask-first"
check 'systemctl --user show "lra-a100-watch-p85b$U" -p Environment | grep -q "HOLD_MAX_S=259200" && systemctl --user show "lra-a100-watch-p85b$U" -p Environment | grep -q "TAG=p85b"' "A4 watch: TAG p85b, HOLD_MAX_S 259200"
check 'grep -q "p85b continuation launched" "$S/babysit.md" && grep -q "p85b continuation on 90000001: workers 16" "$S/acc.md"' "A5 babysit entry + accounting line"
wait_for 'grep -q "pulled:" "$S/gb10/reh-p85b/watch.log" 2>/dev/null' 90 "A6 the p85b watch pulls"
# ---- outbid-style cut: everything killed, relaunch.sh resumes with new ks
D=$(pgrep -f "[o]pen_package.py run .*--out $O "); kill -KILL $D; pkill -KILL -f "[h]arness/agent.py .*--run-id p85b-s"; sleep 3
( RUN_DIR=$R bash "$R/relaunch.sh" > "$S/relaunch.out" 2>&1 )
check 'grep -q "driver running again" "$S/relaunch.out"' "R1 relaunch.sh restarts the killed driver"
wait_for 'grep -q "row#00 session [2-9] starts" "$R/driver.log"' 120 "R2 the restarted driver resumes row 0 at a new k ($(grep -c "resume: .*cut k" "$R/driver.log") cut-session line(s))"
wait_for 'ls "$O"/logs/s00.k2.log > /dev/null 2>&1' 120 "R3 row 0 session k2 started after the restart"
check '! grep -q -- "--fresh" "$O/logs/s00.k2.log" && ! grep -q -- "--fresh" "$O/logs/s01.k2.log" 2>/dev/null' "R4 no --fresh after the restart (row 1 banked state in its cut session or not yet started)"
# ---- stop with the export; no relaunch afterwards
( bash "$W/package_stop_host.sh" "$R" > "$S/stop.out" 2>&1 )
check 'grep -q "STOPPED + exported" "$S/stop.out"' "S1 package_stop_host.sh: $(grep -E 'STOPPED|FAILED' "$S/stop.out" | tail -n 1 | cut -c1-140)"
check '[ -z "$(pgrep -f "[o]pen_package.py run .*--out $O ")" ] && [ -z "$(pgrep -f "[h]arness/agent.py .*--run-id p85b-s")" ]' "S2 no p85b driver or session left"
check '[ -f "$O/proofs.jsonl" ] && [ "$(wc -l < "$O/proofs.jsonl")" = 2 ] && ! grep -q placeholder "$O/summary.json"' "S3 proofs.jsonl (2 rows) + a real summary.json"
( RUN_DIR=$R bash "$R/relaunch.sh" > "$S/relaunch2.out" 2>&1 ); check 'grep -q "run finished (summary.json exists)" "$S/relaunch2.out"' "S4 relaunch.sh refuses after the stop"
( bash "$W/package_stop_host.sh" "$R" > "$S/stop2.out" 2>&1 ); check 'grep -q "nothing to do" "$S/stop2.out"' "S5 a second stop is a no-op"
python3 probe/a100/warmup_upload_measure.py pick --runs "$W/out" "$O" --dir "$S/pick" --rows "$W/lra-run/rows.jsonl" > "$S/pick.out" 2>&1; rc=$?
check '[ "$rc" != 0 ] && grep -q "expected the warm-up 15" "$S/pick.out"' "M1 the upload pick refuses a non-warm-up rows file"
echo "== p85b dry run: $PASS passed, $FAIL failed (scratch $S)"
[ "$FAIL" = 0 ]
