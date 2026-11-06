#!/usr/bin/env bash
# ON the NC box (operator 2026-10-31 ~17:10 UTC: "Go ahead to take actions to close 90 gap for A100. There is nothing to lose now"):
# one coordinated restart of the warm-up run p85b with (1) a generic compact-dialect card appended to every session's opening
# (agent.py --open-card PATH: patched into this box's harness copy only; leak scan 0 hits), (2) the eager end pipeline's polished proofs
# written back as the rows' agent bests where they score higher (so sessions continue from them), (3) the job end moved from
# 2026-11-01 04:00 to 12:00 UTC (agent deadline 09:15; the official run's stop-p85b ends it earlier at the release).
set -u
W=/workspace; R=$W/lra-run-p85b; OUT=$W/out-p85b; L=$W/p85c_restart.log; log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a $L; }
cd $W/lra || exit 1
# (0) patch agent.py (idempotent)
python3 - <<'PY' || { log "agent.py patch FAILED: nothing stopped"; exit 1; }
import ast, pathlib
p = pathlib.Path("harness/agent.py"); s = p.read_text()
if "--open-card" not in s:
    a = '    ap.add_argument("--brief-dir", default=None,'
    b = '    if args.brief != "none":\n'
    assert s.count(a) == 1 and s.count(b) == 1, "anchors"
    s = s.replace(a, '    ap.add_argument("--open-card", default=None, help="2026-10-31 p85b: append this generic card (the same for every row) to the opening; honoured under --open-package")\n' + a)
    s = s.replace(b, '    if getattr(args, "open_card", None):   # 2026-10-31 p85b (operator: close the gap): one generic card, the same for every row\n'
                     '        _oc = Path(args.open_card)\n'
                     '        if _oc.exists():\n'
                     '            msgs[0]["content"] += "\\n\\n" + _oc.read_text()\n'
                     '            print(f"{name[:18]:18s} open card: {_oc.name}", flush=True)\n' + b)
    ast.parse(s); p.with_suffix(".py.before-p85c").write_text(pathlib.Path("harness/agent.py").read_text()); p.write_text(s)
print("agent.py patched")
PY
python3 harness/agent.py --help 2>/dev/null | grep -q -- "--open-card" || { log "patched agent.py does not show --open-card: restore and stop"; cp harness/agent.py.before-p85c harness/agent.py; exit 1; }
log "agent.py patched (--open-card)"
# (1) stop the driver and every session (bests are banked continuously)
D=$(pgrep -f "[o]pen_package.py run" | head -n 1); [ -n "$D" ] && kill -STOP $D && log "driver $D frozen"
for g in $(ps -eo pgid,args | grep -E "[h]arness/agent.py|[h]arness/endstage.py" | awk '{print $1}' | sort -u); do kill -TERM -- -$g 2>/dev/null; done
sleep 15
for g in $(ps -eo pgid,args | grep -E "[h]arness/agent.py|[h]arness/endstage.py" | awk '{print $1}' | sort -u); do kill -KILL -- -$g 2>/dev/null; done
[ -n "$D" ] && kill -KILL $D 2>/dev/null; sleep 5
log "left: driver $(pgrep -fc '[o]pen_package.py run') agents $(pgrep -fc '[h]arness/agent.py') lean $(pgrep -fc '[l]ean ')"
# (2) write the end pipeline's better proofs back as the rows' agent bests
python3 - "$OUT" <<'PY' | tee -a $L
import json, sys, glob, pathlib
out = pathlib.Path(sys.argv[1])
for row in sorted((out / "end-pipe").iterdir()):
    st = out / "work" / row.name / "state.json"
    if not st.exists(): continue
    s = json.loads(st.read_text()); b = s.get("best") or {}
    top = None
    for f in glob.glob(str(row / "*" / "end" / "finals.json")):
        for name, e in (json.loads(pathlib.Path(f).read_text()) or {}).items():
            if isinstance(e, dict) and e.get("proof") and e.get("score") is not None and e.get("verified", True) is not False:
                if top is None or float(e["score"]) > float(top[1]["score"]): top = (name, e)
    if top and float(top[1]["score"]) > float(b.get("score") or 0) + 0.005:
        e = top[1]
        s["best"] = {k: e[k] for k in ("score", "proof", "tokens", "heartbeats", "L", "H", "Z", "compat") if k in e}
        pathlib.Path(str(st) + ".before-p85c").write_text(st.read_text()); st.write_text(json.dumps(s, ensure_ascii=False, indent=1))
        (st.parent / "best.lean").write_text(e["proof"].rstrip() + "\n")
        print(f"write-back {row.name[:40]}: {b.get('score')} -> {e['score']}")
PY
# (3) RUN_CMD: job end 2026-11-01 12:00 UTC + the card
cp $R/RUN_CMD $R/RUN_CMD.before-p85c
python3 - "$R/RUN_CMD" <<'PY'
import re, sys, datetime as dt
p = sys.argv[1]; s = open(p).read()
st = int(re.search(r"--started-at (\d+)", s).group(1))
end = int(dt.datetime(2026, 11, 1, 12, 0, tzinfo=dt.timezone.utc).timestamp())
s = re.sub(r"--job-seconds \d+", f"--job-seconds {end - st}", s)
if "--open-card" not in s:
    s = s.rstrip("\n") + " --agent-arg=--open-card=/workspace/p85c/open_card_dialect.md\n"
open(p, "w").write(s); print(s)
PY
log "RUN_CMD: $(grep -oE -- '--(workers|max-sessions|job-seconds) [0-9]+|--agent-arg=[^ ]+' $R/RUN_CMD | tr '\n' ' ')"
chmod +x $R/relaunch.sh
RUN_DIR=$R setsid nohup bash $R/relaunch.sh >> $R/relaunch.out 2>&1 < /dev/null &
sleep 20; log "relaunch: $(tail -n 1 $R/relaunch.out)"; log "agents $(pgrep -fc '[h]arness/agent.py')"
