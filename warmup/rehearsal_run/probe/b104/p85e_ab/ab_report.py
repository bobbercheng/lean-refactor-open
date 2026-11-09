#!/usr/bin/env python3
"""b104 box A/B readout (run ON the box, read-only): python3 ab_report.py [--json OUT] [--since EPOCH]
Per arm: sessions, turns, output tokens (turn events; budget-forced continuations included), model minutes (turn 'seconds'), gains
(per session, per 1k output tokens, per model-minute), compile success (arm state attempts of the arm's run ids), cut / rescued /
harness-truncated turns, relief events, cap per turn index (B must show 18000 on turns 0-3, 6000 from 4, never 24000), checks per turn,
turn of the first new best; KV pressure from p85e's vllm lines; paired per-row table + P1 with a one-sided bootstrap 90% lower bound."""
import calendar, collections, gzip, json, random, re, statistics, sys, time
from pathlib import Path

X = Path("/workspace/p85e"); AB = X / "ab"; RUNS = Path("/workspace/lra/probe/runs")
args = sys.argv[1:]
since = float(args[args.index("--since") + 1]) if "--since" in args else 0.0


def jl(p):
    out = []
    try:
        txt = gzip.decompress(p.read_bytes()).decode(errors="replace") if p.name.endswith(".gz") else p.read_text(errors="replace")
        for l in txt.splitlines():
            try:
                out.append(json.loads(l))
            except ValueError:
                pass
    except OSError:
        pass
    return out


def safe(n):
    return re.sub(r"[^A-Za-z0-9_.-]", "_", n)


def score(st):
    try:
        return float((json.loads(st.read_text()).get("best") or {}).get("score") or 0)
    except (OSError, ValueError, TypeError):
        return 0.0


pairs = {}
for r in jl(AB / "ab_pairs.jsonl"):
    i = r.get("row")
    if r.get("event") == "start" and r.get("seeded"):
        pairs[i] = {"row": i, "problem": r["problem"], "s0": r["s0"], "t0": r["t0"], "t_end": r["t_end"], "kv_start": r.get("kv"), "done": None,
                    "dropped": None}
    elif r.get("event") == "drop" and i in pairs:
        pairs[i]["dropped"] = r.get("why")
    elif r.get("event") == "done" and i in pairs:
        pairs[i]["done"] = r
sess = [r for r in jl(AB / "ab_sessions.jsonl")]
now = time.time()


def traj_stats(run_id):
    d = RUNS / run_id / "trajectories"
    st = {"turns": 0, "out": 0, "secs": 0.0, "cut": 0, "trunc": 0, "bf": 0, "relief": 0, "caps": collections.Counter(), "caps_by_turn": {},
          "checks": 0, "first_best_turn": None, "best_start": None, "best_end": None, "reasoning": 0}
    for f in (sorted(d.glob("*.jsonl")) + sorted(d.glob("*.jsonl.gz"))) if d.exists() else []:
        for e in jl(f):
            t = e.get("type")
            if t == "header":
                st["best_start"] = e.get("best_at_start")
            elif t == "turn":
                st["turns"] += 1; o = int(e.get("output_tokens") or 0); st["out"] += o; st["secs"] += float(e.get("seconds") or 0)
                st["reasoning"] += int(e.get("reasoning_tokens") or 0)
                cap = e.get("max_tokens"); st["caps"][cap] += 1; st["caps_by_turn"].setdefault(int(e.get("turn") or 0), set()).add(cap)
                if str(e.get("stop")) in ("max_tokens", "length"):
                    st["cut"] += 1
                if str(e.get("stop")) in ("max_tokens", "length") or (cap and o >= cap):
                    st["trunc"] += 1
                st["checks"] = max(st["checks"], int(e.get("checks_so_far") or 0))
                b = e.get("best_so_far")
                if b is not None and st["best_start"] is not None and st["first_best_turn"] is None and float(b) > float(st["best_start"]) + 1e-9:
                    st["first_best_turn"] = int(e.get("turn") or 0)
                st["best_end"] = b
            elif t == "budget_forcing":
                st["bf"] += 1
            elif t == "late_cap_relief":
                st["relief"] += 1
    return st


arm = {k: {"sessions": 0, "finished": 0, "turns": 0, "out": 0, "secs": 0.0, "cut": 0, "trunc": 0, "bf": 0, "relief": 0, "caps": collections.Counter(),
           "checks": 0, "reasoning": 0, "att_ok": 0, "att_n": 0, "wall": 0.0, "first_best_turns": [], "cap_turn": collections.defaultdict(collections.Counter)}
       for k in "AB"}
rowarm = collections.defaultdict(lambda: {"turns": 0, "out": 0, "secs": 0.0, "sessions": 0})
run_ids = collections.defaultdict(set)
for i, p in pairs.items():
    for k in "ab":
        pre = f"p85b-{k}{i:02d}-k"
        for d in RUNS.glob(pre + "*"):
            if d.name[len(pre):].isdigit():
                hdr = next((e for f in list((d / "trajectories").glob("*.jsonl")) + list((d / "trajectories").glob("*.jsonl.gz"))
                            for e in jl(f)[:1] if e.get("type") == "header"), None)
                # only this pair's sessions (fake-box / earlier dirs excluded): started at or after the pair start
                if hdr and hdr.get("started"):
                    t = calendar.timegm(time.strptime(hdr["started"], "%Y-%m-%dT%H:%M:%SZ"))
                    if t < p["t0"] - 120:
                        continue
                run_ids[(k, i)].add(d.name)
for (k, i), rids in run_ids.items():
    K = k.upper(); A_ = arm[K]
    for rid in rids:
        s = traj_stats(rid)
        A_["sessions"] += 1
        for f in ("turns", "out", "secs", "cut", "trunc", "bf", "relief", "checks", "reasoning"):
            A_[f] += s[f]
        A_["caps"].update(s["caps"])
        for tn, cs in s["caps_by_turn"].items():
            for c in cs:
                A_["cap_turn"][min(tn, 6)][c] += 1
        if s["first_best_turn"] is not None:
            A_["first_best_turns"].append(s["first_best_turn"])
        ra = rowarm[(K, i)]; ra["turns"] += s["turns"]; ra["out"] += s["out"]; ra["secs"] += s["secs"]; ra["sessions"] += 1
    try:
        att = json.loads((AB / ("A" if k == "a" else "B") / "work" / safe(pairs[i]["problem"]) / "state.json").read_text()).get("attempts") or []
    except (OSError, ValueError):
        att = []
    mine = [x for x in att if x.get("run_id") in rids]
    A_["att_n"] += len(mine); A_["att_ok"] += sum(1 for x in mine if x.get("ok"))
for r in sess:
    arm[r["arm"]]["finished"] += 1; arm[r["arm"]]["wall"] += float(r.get("seconds") or 0)

rows = []
for i, p in sorted(pairs.items(), key=lambda kv: kv[1]["t0"]):
    ba = score(AB / "A" / "work" / safe(p["problem"]) / "state.json"); bb = score(AB / "B" / "work" / safe(p["problem"]) / "state.json")
    fin = p["done"] is not None
    rows.append({"row": i, "problem": p["problem"], "s0": p["s0"], "A": ba, "B": bb, "gA": round(ba - p["s0"], 3), "gB": round(bb - p["s0"], 3),
                 "d": round(bb - ba, 3), "finished": fin, "dropped": p["dropped"], "kv_start": p["kv_start"],
                 "A_turns": rowarm[("A", i)]["turns"], "B_turns": rowarm[("B", i)]["turns"], "A_out": rowarm[("A", i)]["out"], "B_out": rowarm[("B", i)]["out"],
                 "A_min": round(rowarm[("A", i)]["secs"] / 60, 1), "B_min": round(rowarm[("B", i)]["secs"] / 60, 1),
                 "A_sess": rowarm[("A", i)]["sessions"], "B_sess": rowarm[("B", i)]["sessions"],
                 "wall_min": round(((p["done"] or {}).get("wall_s") or (min(now, p["t_end"]) - p["t0"])) / 60, 1)})
fr = [r for r in rows if r["finished"] and not r["dropped"]]
d = [r["d"] for r in fr]
p1 = statistics.mean(d) if d else None
lb = None
if len(d) >= 2:
    rnd = random.Random(104); bs = sorted(statistics.mean(rnd.choice(d) for _ in d) for _ in range(5000)); lb = bs[int(0.10 * len(bs))]
won = sum(1 for x in d if x > 0.005); lost = sum(1 for x in d if x < -0.005)
summ = {}
for K, A_ in arm.items():
    g = sum(r["g" + K] for r in fr)
    summ[K] = {"sessions_started": A_["sessions"], "sessions_finished": A_["finished"], "turns": A_["turns"], "out_tokens": A_["out"],
               "reasoning_tokens": A_["reasoning"], "model_min": round(A_["secs"] / 60, 1), "wall_min": round(A_["wall"] / 60, 1),
               "out_per_turn": round(A_["out"] / A_["turns"]) if A_["turns"] else None,
               "turns_per_Mtok": round(A_["turns"] / (A_["out"] / 1e6), 1) if A_["out"] else None,
               "gain_sum_finished_rows": round(g, 3), "gain_per_session": round(g / A_["finished"], 3) if A_["finished"] else None,
               "gain_per_1k_out": round(g / (A_["out"] / 1e3), 5) if A_["out"] else None,
               "gain_per_model_min": round(g / (A_["secs"] / 60), 5) if A_["secs"] else None,
               "compile_ok": A_["att_ok"], "compile_n": A_["att_n"], "compile_rate": round(A_["att_ok"] / A_["att_n"], 3) if A_["att_n"] else None,
               "checks_per_turn": round(A_["checks"] / A_["turns"], 2) if A_["turns"] else None,
               "cut_turns": A_["cut"], "harness_truncated": A_["trunc"], "budget_forced": A_["bf"], "relief": A_["relief"],
               "trunc_rate": round(A_["trunc"] / A_["turns"], 3) if A_["turns"] else None,
               "caps": {str(k): v for k, v in sorted(A_["caps"].items(), key=lambda kv: str(kv[0]))},
               "caps_by_turn": {str(t): dict(c) for t, c in sorted(A_["cap_turn"].items())},
               "first_best_turn_median": statistics.median(A_["first_best_turns"]) if A_["first_best_turns"] else None}
kv = []
for l in (X / "xloop.log").read_text(errors="replace").splitlines():
    m = re.match(r"\[(\d\d-\d\d \d\d:\d\d:\d\d)\] vllm: running (\d+) waiting (\d+) kv ([\d.]+) gen (\d+) tok/s .* preempt (\d+); agent.py (\d+) \(ours (\d+)\)", l)
    if m:
        t = calendar.timegm(time.strptime("2026-" + m.group(1), "%Y-%m-%d %H:%M:%S"))
        if t >= (since or min((p["t0"] for p in pairs.values()), default=now)):
            kv.append((t, int(m.group(2)), float(m.group(4)), int(m.group(5)), int(m.group(6)), int(m.group(7))))
kvs = {"samples": len(kv), "kv_mean": round(statistics.mean(x[2] for x in kv), 3) if kv else None, "kv_max": max((x[2] for x in kv), default=None),
       "kv_ge_090": sum(1 for x in kv if x[2] >= 0.9), "running_mean": round(statistics.mean(x[1] for x in kv), 1) if kv else None,
       "gen_tok_s_mean": round(statistics.mean(x[3] for x in kv)) if kv else None,
       "preempt_delta": (kv[-1][4] - kv[0][4]) if kv else None, "agents_mean": round(statistics.mean(x[5] for x in kv), 1) if kv else None}
res = {"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now)), "pairs_started": len(pairs), "pairs_finished": len(fr),
       "pairs_dropped": sum(1 for r in rows if r["dropped"]), "P1_mean_d_B_minus_A": round(p1, 3) if p1 is not None else None,
       "P1_boot90_lower": round(lb, 3) if lb is not None else None, "rows_won_B": won, "rows_lost_B": lost,
       "worst_d": min(d) if d else None, "arms": summ, "kv": kvs, "rows": rows}
if "--json" in args:
    Path(args[args.index("--json") + 1]).write_text(json.dumps(res, indent=1))
print(json.dumps({k: v for k, v in res.items() if k != "rows"}, indent=1))
print(f"{'row':>3} {'problem':36} {'s0':>7} {'A':>7} {'B':>7} {'gA':>6} {'gB':>6} {'B-A':>6} {'Aturn':>5} {'Bturn':>5} {'Aout':>7} {'Bout':>7} {'Amin':>5} {'Bmin':>5} {'wall':>5} state")
for r in rows:
    print(f"{r['row']:>3} {r['problem'][:36]:36} {r['s0']:7.3f} {r['A']:7.3f} {r['B']:7.3f} {r['gA']:6.2f} {r['gB']:6.2f} {r['d']:6.2f} {r['A_turns']:>5} "
          f"{r['B_turns']:>5} {r['A_out']:>7} {r['B_out']:>7} {r['A_min']:>5} {r['B_min']:>5} {r['wall_min']:>5} "
          f"{'done' if r['finished'] else 'running'}{' DROPPED ' + str(r['dropped']) if r['dropped'] else ''}")
