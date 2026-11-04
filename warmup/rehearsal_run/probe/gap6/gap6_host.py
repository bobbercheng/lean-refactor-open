#!/usr/bin/env python3
"""ON the A100 warm-up box (gap6 step test, operator 2026-11-01 ~05:30 UTC "yes, build it without workflow and test it in A100";
docs/open_gap6_prompt.md section "step test"). Paired sessions BESIDE the live p85b driver and p85e (no driver/vLLM/harness edit):
per row in PLAN order, arm S (step) and arm C (control) start in the same tick from byte-identical copies of the main row dir, each in
its own work root /workspace/gap6/{S,C}/work. Both run exactly the driver's session command (op.session_cmd from RUN_CMD, never --fresh);
S differs ONLY in its --open-card file = the shipped dialect card + the row's one-move step message (probe/gap6/detect.py). Each arm
chains sessions on its own lineage until BUDGET_S of wall time from the pair start (matched GPU time; the session in flight at the
budget gets SIGTERM, best banked). Arms never write main (no write-back here: the coordinator verifies on the official meter after).
Admission (as b104 / p85e v3.1): running agent.py + 2 <= MAX_TOTAL, vLLM KV <= KV_MAX, 0 waiting, no preemption rise in 300 s (and
300 s of history), >= GAP_S since the last pair start, <= PAIRS pairs at once, and the pair must fit before the end. End = min(own END_AT
file, p85e's END_AT): the release sets p85e's END_AT to now -> every gap6 session stops. STOP file: no new pair, running sessions stop now.
Shed: KV >= 0.95 for 600 s with preemptions rising -> the youngest pair stops (row recorded as shed). Records: pairs.jsonl, sessions.jsonl.
Env: PLAN (json list [{name, step, card}]), BUDGET_S (2400), PAIRS (3), MAX_TOTAL (14), KV_MAX (0.70), GAP_S (120), END_AT (epoch)."""
import calendar, collections, fcntl, hashlib, json, os, re, shlex, shutil, subprocess, sys, threading, time
from pathlib import Path

W = Path("/workspace"); LRA = W / "lra"; OUT = W / "out-p85b"; RUN_DIR = W / "lra-run-p85b"; MAIN = OUT / "work"
G = Path(os.environ.get("GAP6_DIR") or W / "gap6")   # 06:35: a second instance (gap6b) runs the rows the first has not started
ARM = {"S": G / "S" / "work", "C": G / "C" / "work"}
E = os.environ.get
BUDGET_S = float(E("BUDGET_S", "2400")); PAIRS = int(E("PAIRS", "3")); MAX_TOTAL = int(E("MAX_TOTAL", "14"))
KV_MAX = float(E("KV_MAX", "0.70")); GAP_S = float(E("GAP_S", "120")); MIN_CHAIN_S = 300; TICK_S = 20; PWIN = float(E("PWIN", "300"))   # PWIN: preemption window for admission (history must span it)
OWN_END = float(E("END_AT") or 0)
DIALECT = Path("/workspace/p85c/open_card_dialect.md")

sys.path.insert(0, str(LRA)); os.chdir(LRA)
from harness import open_package as op  # noqa: E402

argv = shlex.split((RUN_DIR / "RUN_CMD").read_text())
a = op.build_parser().parse_args(argv[argv.index("harness/open_package.py") + 1:])
names, rows, hbs = op.load_rows(a.rows, a.heartbeats)
IDX = {n: i for i, n in enumerate(names)}
for _r in json.loads(Path(E("PLAN", str(G / "plan.json"))).read_text()):
    if "idx" in _r:
        IDX.setdefault(_r["name"], int(_r["idx"]))
ENV = dict(op.base_env(a))
PLAN = json.loads(Path(E("PLAN", str(G / "plan.json"))).read_text())   # [{name, idx, src (row dir root), rows?, heartbeats?, set}]
LEMMAS = json.loads((G / "lemmas.json").read_text()) if (G / "lemmas.json").exists() else {}
sys.path.insert(0, str(G)); import detect  # noqa: E402  (probe/gap6/detect.py: the step is chosen from the snapshot's best, at pair start)
ROWS = {r["name"]: r for r in PLAN}
LOG = G / "gap6.log"; PAIRS_J = G / "pairs.jsonl"; SESS_J = G / "sessions.jsonl"; STOP = G / "STOP"


def log(m: str) -> None:
    line = f"[{time.strftime('%m-%d %H:%M:%S', time.gmtime())}] {m}"
    print(line, flush=True)
    with open(LOG, "a") as f:
        f.write(line + "\n")


def jappend(p: Path, rec: dict) -> None:
    with open(p, "a") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")


def score_of(st: Path) -> float:
    try:
        return float(json.loads(st.read_text()).get("best", {}).get("score") or 0.0)
    except Exception:  # noqa: BLE001
        return 0.0


def parse_end(txt: str) -> float | None:
    t = (txt.split() or [""])[0]
    if re.fullmatch(r"\d{9,11}(\.\d+)?", t):
        return float(t)
    try:
        return float(calendar.timegm(time.strptime(t.replace("Z", ""), "%Y-%m-%dT%H:%M:%S")))
    except ValueError:
        return None


def end_now() -> float:
    ends = [OWN_END] if OWN_END else []
    for f in (W / "p85e" / "END_AT", G / "END_AT"):
        try:
            v = parse_end(f.read_text())
            if v:
                ends.append(v)
        except OSError:
            pass
    return min(ends) if ends else time.time() + 3600


def agent_count() -> int:
    out = subprocess.run(["ps", "-ww", "-eo", "stat=,args="], capture_output=True, text=True).stdout
    return sum(1 for l in out.splitlines() if re.search(r"harness/agent\.py .*--run-id ", l) and not l.lstrip().startswith("T"))


_ph: collections.deque = collections.deque(); _kvhi: list = []


def vllm() -> dict:
    try:
        import requests
        key = Path(a.api_key_file).read_text().strip() if a.api_key_file else ""
        r = requests.get(re.sub(r"/v1/?$", "", a.base_url) + "/metrics", headers={"Authorization": f"Bearer {key}"} if key else {}, timeout=10)
        r.raise_for_status()
        v: dict = {}
        for l in r.text.splitlines():
            m = re.match(r"^vllm:(num_requests_running|num_requests_waiting|kv_cache_usage_perc|num_preemptions_total)\{[^}]*\} (\S+)", l)
            if m:
                v[m.group(1)] = v.get(m.group(1), 0.0) + float(m.group(2))
        t = time.time()
        if "num_preemptions_total" in v:
            if _ph and v["num_preemptions_total"] < _ph[-1][1]:
                _ph.clear()
            _ph.append((t, v["num_preemptions_total"]))
            while _ph and t - _ph[0][0] > 1200:
                _ph.popleft()
        return v
    except Exception as e:  # noqa: BLE001
        return {"error": type(e).__name__}


def preempt_rose(win: float) -> bool | None:
    if not _ph or _ph[-1][0] - _ph[0][0] < win:
        return None
    old = [p for t, p in _ph if _ph[-1][0] - t <= win]
    return bool(old) and _ph[-1][1] > old[0]


def card_for(row: dict) -> Path | None:
    """The step from the S snapshot's best (detect.plan); None = no move applies now (the pair is skipped)."""
    n = row["name"]; best = json.loads((ARM["S"] / op.safe(n) / "state.json").read_text())["best"]["proof"]
    pl = detect.plan(n, best, LEMMAS.get(n, []))
    if not pl:
        return None
    row["step"] = pl["step"]
    (G / "cards" / f"{op.safe(n)}.plan.json").write_text(json.dumps(pl, indent=1, ensure_ascii=False))
    p = G / "cards" / f"{op.safe(n)}.full.md"
    p.write_text(DIALECT.read_text().rstrip() + "\n\n" + pl["msg"] + "\n")
    return p


def snapshot(n: str, src_root: Path) -> str:
    src = src_root / op.safe(n)
    h = hashlib.sha256((src / "state.json").read_bytes()).hexdigest()[:16]
    for arm, root in ARM.items():
        dst = root / op.safe(n)
        if dst.exists():
            shutil.rmtree(dst)
        root.mkdir(parents=True, exist_ok=True)
        shutil.copytree(src, dst, ignore=shutil.ignore_patterns("*.lock", "scratch.lean", "probe.lean"))
        if hashlib.sha256((dst / "state.json").read_bytes()).hexdigest()[:16] != h:
            raise RuntimeError(f"snapshot of {n} not byte-identical in arm {arm}")
    return h


def arm_cmd(arm: str, n: str, run_id: str, card: Path) -> list:
    cmd = op.session_cmd(a, n, run_id, fresh=False)
    assert "--fresh" not in cmd
    cmd[cmd.index("--work-root") + 1] = str(ARM[arm])
    r = ROWS[n]
    if r.get("rows"):
        cmd[cmd.index("--rows") + 1] = r["rows"]; cmd[cmd.index("--heartbeats") + 1] = r["heartbeats"]
    oc = [i for i, x in enumerate(cmd) if x.startswith("--open-card=") or x == "--open-card"]
    if len(oc) != 1:
        raise RuntimeError(f"expected exactly one --open-card in the session command, found {len(oc)}")
    if arm == "S":
        i = oc[0]
        if cmd[i] == "--open-card":
            cmd[i + 1] = str(card)
        else:
            cmd[i] = f"--open-card={card}"
    return cmd


live: dict = {}   # pair key -> {"t0", "flag", "threads"}


def arm_chain(arm: str, row: dict, t0: float, flag: threading.Event, card: Path) -> None:
    n = row["name"]; i = IDX[n]; st = ARM[arm] / op.safe(n) / "state.json"; k = 0
    while not flag.is_set():
        left = min(t0 + BUDGET_S, end_now()) - time.time()
        if left < (MIN_CHAIN_S if k else 60):
            break
        k += 1; run_id = f"gap6{arm.lower()}{i:02d}-k{k}"
        b0 = score_of(st); ts = time.time()
        cmd = arm_cmd(arm, n, run_id, card)
        log(f"{run_id} starts ({row.get('step')} arm {arm} set {row.get('set')}; own best {b0:.3f}; budget left {left:.0f} s)")
        rc = op.run_session(cmd, ENV, G / "logs" / f"{run_id}.log", min(t0 + BUDGET_S, end_now()),
                            now=lambda: float("inf") if (flag.is_set() or STOP.exists() or time.time() >= end_now()) else time.time())
        b1 = score_of(st)
        rec = {"row": i, "problem": n, "step": row["step"], "arm": arm, "k": k, "run_id": run_id, "rc": rc,
               "seconds": round(time.time() - ts, 1), "out_tokens": op.session_out_tokens(op.RUNS / run_id),
               "tool_errors": op.session_tool_errors(op.RUNS / run_id) if hasattr(op, "session_tool_errors") else None,
               "before": b0, "after": b1, "gain": round(b1 - b0, 4), "stopped": flag.is_set() or STOP.exists(),
               "t_end": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        jappend(SESS_J, rec)
        log(f"{run_id} done rc {rc} in {rec['seconds']:.0f} s: {b0:.3f} -> {b1:.3f}, out_tok {rec['out_tokens']}")


def pair(row: dict, h: str, card: Path) -> None:
    n = row["name"]; key = n; t0 = time.time(); flag = threading.Event()
    s0 = {arm: score_of(ARM[arm] / op.safe(n) / "state.json") for arm in ARM}
    ths = [threading.Thread(target=arm_chain, args=(arm, row, t0, flag, card), daemon=True) for arm in ("S", "C")]
    live[key] = {"t0": t0, "flag": flag, "threads": ths}
    for t in ths:
        t.start()
    for t in ths:
        t.join()
    s1 = {arm: score_of(ARM[arm] / op.safe(n) / "state.json") for arm in ARM}
    rec = {"problem": n, "row": IDX[n], "step": row["step"], "set": row.get("set"), "snapshot": h, "start": s0, "end": s1,
           "gain_S": round(s1["S"] - s0["S"], 4), "gain_C": round(s1["C"] - s0["C"], 4),
           "d": round((s1["S"] - s0["S"]) - (s1["C"] - s0["C"]), 4), "seconds": round(time.time() - t0, 1),
           "stopped": flag.is_set() or STOP.exists(), "shed": live.get(key, {}).get("shed", False),
           "t_end": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    jappend(PAIRS_J, rec)
    log(f"PAIR {n.split('.')[-1]} [{row['step']}]: S {s0['S']:.3f}->{s1['S']:.3f} ({rec['gain_S']:+.3f}) vs C {s0['C']:.3f}->{s1['C']:.3f} "
        f"({rec['gain_C']:+.3f}): d {rec['d']:+.3f}")
    live.pop(key, None)


def dry() -> None:
    """DRY=1: per plan row, the step its CURRENT best would get and arm S's session command (no snapshot, no session, no writes)."""
    for r in PLAN:
        n = r["name"]; src = Path(r.get("src") or MAIN) / op.safe(n) / "state.json"
        best = json.loads(src.read_text())["best"]
        pl = detect.plan(n, best["proof"], LEMMAS.get(n, []))
        print(f"{r.get('set'):8s} {n.split('.')[-1][:40]:40s} best {best.get('score')} step {pl['step'] if pl else '-'}")
    r = PLAN[0]; cmd = arm_cmd("S", r["name"], "gap6dry-k0", G / "cards" / "DRY.md")
    print("S cmd:", " ".join(x for x in cmd if "key" not in x.lower()))


def main() -> None:
    G.mkdir(exist_ok=True); (G / "logs").mkdir(exist_ok=True); (G / "cards").mkdir(exist_ok=True)
    if E("DRY") == "1":
        dry(); return
    lk = open(G / "gap6.lock", "w")
    fcntl.flock(lk, fcntl.LOCK_EX | fcntl.LOCK_NB)
    (G / "gap6.pid").write_text(str(os.getpid()))
    done = {json.loads(l)["problem"] for l in open(PAIRS_J)} if PAIRS_J.exists() else set()
    todo = [r for r in PLAN if r["name"] not in done]
    log(f"gap6 host start: {len(todo)} pairs to run (budget {BUDGET_S:.0f} s/arm, <= {PAIRS} pairs, MAX_TOTAL {MAX_TOTAL}, KV_MAX {KV_MAX}); "
        f"end {time.strftime('%H:%M', time.gmtime(end_now()))}")
    last = 0.0; threads = []
    while True:
        now = time.time(); v = vllm(); kv = v.get("kv_cache_usage_perc")
        if STOP.exists() or now >= end_now():
            for x in list(live.values()):
                x["flag"].set()
            if not any(t.is_alive() for t in threads):
                log(f"gap6 host exit ({'STOP' if STOP.exists() else 'END'})"); return
        elif kv is not None and kv >= 0.95:
            _kvhi.append(now)
            if now - _kvhi[0] >= 600 and preempt_rose(600) and live:
                key = max(live, key=lambda x: live[x]["t0"]); live[key]["shed"] = True; live[key]["flag"].set(); _kvhi.clear()
                log(f"SHED: KV {kv:.2f} >= 0.95 for 600 s with preemptions rising: pair {key} stopped")
        else:
            _kvhi.clear()
        if todo and not STOP.exists() and now < end_now():
            nrun = agent_count(); pr = preempt_rose(PWIN)
            why = None
            if len(live) >= PAIRS: why = f"{len(live)} pairs live"
            elif nrun + 2 > MAX_TOTAL: why = f"{nrun} agent.py running"
            elif kv is None: why = f"no vLLM metrics ({v.get('error')})"
            elif kv > KV_MAX: why = f"KV {kv:.2f} > {KV_MAX}"
            elif v.get("num_requests_waiting", 0) > 0: why = "requests waiting"
            elif pr is None: why = f"preemption history < {PWIN:.0f} s"
            elif pr: why = f"preemptions rose in {PWIN:.0f} s"
            elif now - last < GAP_S: why = "start gap"
            elif end_now() - now < BUDGET_S: why = "pair would not fit before the end"
            if why is None:
                row = todo.pop(0)
                try:
                    h = snapshot(row["name"], Path(row.get("src") or MAIN)); card = card_for(row)
                    if card is None:
                        log(f"pair {row['name']} skipped: no move applies to its current best"); continue
                    last = now
                    log(f"pair start {row['name']} [{row['step']}] snapshot {h} (KV {kv:.2f}, agent.py {nrun})")
                    t = threading.Thread(target=pair, args=(row, h, card), daemon=True); t.start(); threads.append(t)
                except Exception as e:  # noqa: BLE001
                    log(f"pair {row['name']} NOT started: {type(e).__name__}: {e}")
            elif int(now) % 300 < TICK_S:
                log(f"waiting: {why} ({len(todo)} pairs left)")
        if not todo and not any(t.is_alive() for t in threads):
            log("gap6 host: all pairs finished"); return
        time.sleep(TICK_S)


if __name__ == "__main__":
    main()
