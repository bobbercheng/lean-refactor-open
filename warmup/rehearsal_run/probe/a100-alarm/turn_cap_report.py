#!/usr/bin/env python3
"""What do the turns past 60 buy? (2026-10-30: the fresh rehearsal pkg2 gives sessions that start below 45 a 90-turn budget instead of 60,
because fold's sessions were the only ones ending on the cap. One run's fold score cannot judge that: two runs with the same 60-turn
setting gave fold 63.5 and 41.5 after one session. So the fix is judged on its mechanism, per session, from the trajectories' turn
events (turn, checks_so_far, best_so_far, seconds) and the header (turn_budget, best_at_start):
  ended_at_cap      turns used >= the budget
  late_gain         best at the session's end minus best after turn 60 (0 when the session ended before turn 60)
  late_checks       checks made after turn 60
  improving_at_end  a new best in the last 10 turns of a session that ended on its cap (= the cap still binds)
  late_seconds      wall time spent after turn 60
    python3 probe/a100-alarm/turn_cap_report.py RUNS_DIR [--tag pkg2] [--json OUT]"""
import argparse, glob, json, os, re, statistics

ap = argparse.ArgumentParser(); ap.add_argument("runs"); ap.add_argument("--logs", help="the run's out/logs (session DONE lines: the turn count the agent itself uses)")
ap.add_argument("--tag", default=""); ap.add_argument("--json"); a = ap.parse_args()
done_turns = {}   # (row, k) -> turns from the session log's DONE line (the trajectory skips turn events on some forced/retried turns)
if a.logs:
    for lf in glob.glob(os.path.join(a.logs, "s*.k*.log")):
        m = re.search(r"s(\d+)\.k(\d+)\.log$", lf)
        for line in open(lf, errors="replace"):
            t = re.search(r"DONE best=\S+ checks=\d+ tool_calls=\d+ turns=(\d+)", line)
            if m and t:
                done_turns[(int(m.group(1)), int(m.group(2)))] = int(t.group(1))
rows = []
for d in sorted(glob.glob(os.path.join(a.runs, f"{a.tag}*-s*-k*"))):
    for f in glob.glob(os.path.join(d, "trajectories", "*.jsonl")):
        head, turns = {}, []
        for line in open(f, errors="replace"):
            try:
                e = json.loads(line)
            except Exception:  # noqa: BLE001
                continue
            if e.get("type") == "header":
                head = e
            elif e.get("type") == "turn" and e.get("turn") is not None:
                turns.append(e)
        if not head or not turns:
            continue
        budget = int(head.get("turn_budget") or 0); b0 = float(head.get("best_at_start") or 33.33)
        mm = re.search(r"-s(\d+)-k(\d+)$", os.path.basename(d))
        used = done_turns.get((int(mm.group(1)), int(mm.group(2)))) if mm else None
        used = used or (max(int(t["turn"]) for t in turns) + 1)
        best = lambda t: float(t.get("best_so_far") or b0)
        end_best = max(best(t) for t in turns)
        upto60 = [t for t in turns if int(t["turn"]) < 60]
        best60 = max([best(t) for t in upto60] or [b0])
        chk60 = max([int(t.get("checks_so_far") or 0) for t in upto60] or [0]); chk_end = max(int(t.get("checks_so_far") or 0) for t in turns)
        last10 = [t for t in turns if int(t["turn"]) >= used - 10]
        before10 = max([best(t) for t in turns if int(t["turn"]) < used - 10] or [b0])
        rows.append({"session": os.path.basename(d), "problem": head.get("problem", "")[:44], "budget": budget, "b0": b0, "turns": used,
                     "end_best": round(end_best, 2), "ended_at_cap": used >= budget > 0, "late_gain": round(end_best - best60, 2) if used > 60 else 0.0,
                     "late_checks": chk_end - chk60 if used > 60 else 0,
                     "improving_at_end": used >= budget > 0 and max(best(t) for t in last10) > before10 + 1e-9,
                     "late_seconds": round(sum(float(t.get("seconds") or 0) for t in turns if int(t["turn"]) >= 60))})
print(f"{'session':16s} {'problem':44s} {'bud':>3s} {'b0':>6s} {'turns':>5s} {'end':>6s} cap  late_gain late_chk impr_end late_s")
for r in rows:
    print(f"{r['session']:16s} {r['problem']:44s} {r['budget']:3d} {r['b0']:6.2f} {r['turns']:5d} {r['end_best']:6.2f} {'Y' if r['ended_at_cap'] else '-':3s} {r['late_gain']:9.2f} {r['late_checks']:8d} {'Y' if r['improving_at_end'] else '-':8s} {r['late_seconds']:6d}")
past60 = [r for r in rows if r["turns"] > 60]
print(f"\nsessions {len(rows)}; ended on their cap {sum(r['ended_at_cap'] for r in rows)}; went past turn 60: {len(past60)}")
if past60:
    print(f"  past turn 60: new best after turn 60 in {sum(r['late_gain'] > 0 for r in past60)} of {len(past60)}; late gain mean "
          f"{statistics.mean(r['late_gain'] for r in past60):+.2f}; late checks mean {statistics.mean(r['late_checks'] for r in past60):.1f}; "
          f"late wall mean {statistics.mean(r['late_seconds'] for r in past60) / 60:.0f} min; still improving at a 90 cap: "
          f"{sum(r['improving_at_end'] and r['budget'] >= 90 for r in past60)}")
if a.json:
    json.dump(rows, open(a.json, "w"), indent=1)
