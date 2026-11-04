#!/usr/bin/env bash
# ON the A100 box (operator "close the 90 gap"): planned restart of the p85b DRIVER only (blind lineages untouched) that writes the
# squeeze's better proofs (official-meter verified; /workspace/p85c/squeeze_best.jsonl) and the end pipeline's better proofs back as the
# rows' agent bests, then relaunches with RUN_CMD unchanged (15 workers, cap 12, card, job end 12:00).
set -u
W=/workspace; R=$W/lra-run-p85b; OUT=$W/out-p85b; L=$W/p85d.log; log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a $L; }
cd $W/lra || exit 1
D=$(pgrep -f "[o]pen_package.py run" | head -n 1); [ -n "$D" ] && kill -STOP $D && log "driver $D frozen"
for g in $(ps -eo pgid,args | grep -E "[h]arness/agent.py .*--run-id p85b-s|[h]arness/endstage.py" | awk '{print $1}' | sort -u); do kill -TERM -- -$g 2>/dev/null; done
sleep 15
for g in $(ps -eo pgid,args | grep -E "[h]arness/agent.py .*--run-id p85b-s|[h]arness/endstage.py" | awk '{print $1}' | sort -u); do kill -KILL -- -$g 2>/dev/null; done
[ -n "$D" ] && kill -KILL $D 2>/dev/null; sleep 5
log "left: driver $(pgrep -fc '[o]pen_package.py run') main agents $(pgrep -fc '[r]un-id p85b-s') blind $(pgrep -fc 'python3 harness/agent.py.*[r]un-id p85b-blind')"
python3 - "$OUT" "$W/p85c/squeeze_best.jsonl" <<'PY' | tee -a $L
import json, sys, glob, pathlib, re
out = pathlib.Path(sys.argv[1]); sq = [json.loads(l) for l in open(sys.argv[2]) if l.strip()]
safe = lambda n: re.sub(r"[^A-Za-z0-9_.-]", "_", n)
cands = {}
for e in sq: cands.setdefault(e["name"], []).append(e)
for row in (out / "end-pipe").iterdir() if (out / "end-pipe").exists() else []:
    for f in glob.glob(str(row / "*" / "end" / "finals.json")):
        for name, e in (json.loads(pathlib.Path(f).read_text()) or {}).items():
            if isinstance(e, dict) and e.get("proof") and e.get("score") is not None and e.get("verified", True) is not False:
                cands.setdefault(name, []).append(e)
for name, es in cands.items():
    st = out / "work" / safe(name) / "state.json"
    if not st.exists(): continue
    s = json.loads(st.read_text()); b = s.get("best") or {}
    top = max(es, key=lambda e: float(e["score"]))
    if float(top["score"]) > float(b.get("score") or 0) + 0.005:
        nb = {k: top[k] for k in ("score", "proof", "tokens", "heartbeats", "L", "H", "Z", "compat") if k in top}
        for k in ("tokens", "heartbeats", "L", "H", "Z", "compat"):
            nb.setdefault(k, b.get(k))
        s["best"] = nb
        pathlib.Path(str(st) + ".before-p85d").write_text(st.read_text()); st.write_text(json.dumps(s, ensure_ascii=False, indent=1))
        (st.parent / "best.lean").write_text(nb["proof"].rstrip() + "\n")
        print(f"write-back {name[:40]}: {b.get('score')} -> {nb['score']}")
PY
chmod +x $R/relaunch.sh
RUN_DIR=$R setsid nohup bash $R/relaunch.sh >> $R/relaunch.out 2>&1 < /dev/null &
sleep 20; log "relaunch: $(tail -n 1 $R/relaunch.out)"; log "main agents $(pgrep -fc '[r]un-id p85b-s') blind $(pgrep -fc 'python3 harness/agent.py.*[r]un-id p85b-blind')"
