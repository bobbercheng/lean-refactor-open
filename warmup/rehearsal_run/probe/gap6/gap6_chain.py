#!/usr/bin/env python3
"""ON the warm-up A100 box: gap6 CHAIN mode (operator 2026-11-01 ~07:15 UTC, "I agree for Proposed redesign of pair, please do it ASAP and test
it"): per warm-up row that has an Azure VM (closed reh92) proof, start from the A100 rehearsal's best proof ONLY (a fresh work dir: best +
original/context, no notes, no attempts, no runs), then apply the detector's moves one after another, one short GLM session per move with
ONLY that move's message (--open-card = the step message, no dialect card), re-detected on the evolving best. Score after every step and the
gap to the Azure VM proof. No control arm. Per row at most MAX_STEPS sessions: the next untried move that applies; else a move that improved
last time and still applies (once); else stop. Rows run in parallel (one session per row at a time). Admission: KV <= KV_MAX, 0 waiting,
>= GAP_S between session starts, agent.py + 1 <= MAX_TOTAL. Ends at its own END_AT file (never p85e's) or STOP. Records: steps.jsonl, chain.log.
Env: STEP_S (1500), MAX_STEPS (3), MAX_TOTAL (14), KV_MAX (0.70), GAP_S (30)."""
import calendar, json, os, re, shlex, shutil, subprocess, sys, threading, time
from pathlib import Path

W = Path("/workspace"); LRA = W / "lra"; OUT = W / "out-p85b"; RUN_DIR = W / "lra-run-p85b"; MAIN = OUT / "work"
G = Path(os.environ.get("GAP6_DIR") or W / "gap6c"); WORK = G / "work"
E = os.environ.get
STEP_S = float(E("STEP_S", "1500")); MAX_STEPS = int(E("MAX_STEPS", "3")); MAX_TOTAL = int(E("MAX_TOTAL", "14"))
KV_MAX = float(E("KV_MAX", "0.70")); GAP_S = float(E("GAP_S", "30"))
sys.path.insert(0, str(LRA)); os.chdir(LRA)
from harness import open_package as op  # noqa: E402
sys.path.insert(0, str(G)); import detect  # noqa: E402

argv = shlex.split((RUN_DIR / "RUN_CMD").read_text())
a = op.build_parser().parse_args(argv[argv.index("harness/open_package.py") + 1:])
names, rows, hbs = op.load_rows(a.rows, a.heartbeats)
IDX = {n: i for i, n in enumerate(names)}
ENV = dict(op.base_env(a))
AZ = json.loads((G / "azure.json").read_text())          # name -> {score, tokens, heartbeats}
LEMMAS = json.loads((G / "lemmas.json").read_text()) if (G / "lemmas.json").exists() else {}
LOG = G / "chain.log"; STEPS_J = G / "steps.jsonl"; STOP = G / "STOP"
_lock = threading.Lock(); _last_start = [0.0]


def log(m):
    line = f"[{time.strftime('%m-%d %H:%M:%S', time.gmtime())}] {m}"
    print(line, flush=True)
    with open(LOG, "a") as f:
        f.write(line + "\n")


def jappend(rec):
    with _lock, open(STEPS_J, "a") as f:
        f.write(json.dumps(rec, ensure_ascii=False) + "\n")


def end_at():
    try:
        t = (G / "END_AT").read_text().split()[0]
        return float(t) if re.fullmatch(r"\d+(\.\d+)?", t) else float(calendar.timegm(time.strptime(t.replace("Z", ""), "%Y-%m-%dT%H:%M:%S")))
    except (OSError, ValueError, IndexError):
        return time.time() + 3600


def best_of(n):
    try:
        return json.loads((WORK / op.safe(n) / "state.json").read_text())["best"]
    except Exception:  # noqa: BLE001
        return {}


def seed(n):
    """A fresh row dir with the A100 rehearsal best only (no notes, attempts, runs, ledger)."""
    src, dst = MAIN / op.safe(n), WORK / op.safe(n)
    st = json.loads((src / "state.json").read_text())
    if dst.exists():
        shutil.rmtree(dst)
    dst.mkdir(parents=True)
    for f in ("original.lean", "context.lean", "best.lean"):
        if (src / f).exists():
            shutil.copy(src / f, dst / f)
    fresh = {"problem": st["problem"], "best": st["best"]}
    for k, v in st.items():
        if k not in fresh:
            fresh[k] = type(v)() if isinstance(v, (list, dict)) else v
    for k in ("attempts", "runs", "ledger"):
        if k in fresh:
            fresh[k] = type(st[k])()
    (dst / "state.json").write_text(json.dumps(fresh, ensure_ascii=False, indent=1))
    (dst / "notes.md").write_text(f"# {n} — notes\n")   # the agent reads notes.md on a resumed session; header only = no history
    return st["best"]


def vllm_ok():
    try:
        import requests
        key = Path(a.api_key_file).read_text().strip() if a.api_key_file else ""
        r = requests.get(re.sub(r"/v1/?$", "", a.base_url) + "/metrics", headers={"Authorization": f"Bearer {key}"} if key else {}, timeout=10)
        kv = wait = 0.0
        for l in r.text.splitlines():
            m = re.match(r"^vllm:(kv_cache_usage_perc|num_requests_waiting)\{[^}]*\} (\S+)", l)
            if m:
                if m.group(1) == "kv_cache_usage_perc": kv += float(m.group(2))
                else: wait += float(m.group(2))
        return kv <= KV_MAX and wait == 0, kv
    except Exception:  # noqa: BLE001
        return False, None


def nrun():
    out = subprocess.run(["ps", "-ww", "-eo", "stat=,args="], capture_output=True, text=True).stdout
    return sum(1 for l in out.splitlines() if re.search(r"harness/agent\.py .*--run-id ", l) and not l.lstrip().startswith("T"))


def admit():
    while not STOP.exists() and time.time() < end_at():
        with _lock:
            ok, kv = vllm_ok()
            if ok and nrun() + 1 <= MAX_TOTAL and time.time() - _last_start[0] >= GAP_S:
                _last_start[0] = time.time()
                return True
        time.sleep(15)
    return False


def sig(step, proof):
    return {"funind": "fun_induction" in proof, "elements": proof.count("∘ₗ") == 0, "mirror": ("case'" in proof or "symm" in proof),
            "restate": len(detect.restate(proof)) < 2}.get(step)


def row_chain(n):
    b0 = seed(n); az = AZ[n]["score"]; i = IDX[n]
    log(f"row {n.split('.')[-1]}: A100 {b0['score']:.3f} vs Azure VM {az:.3f} (gap {az - b0['score']:+.3f})")
    tried, improved, k = [], set(), 0
    while k < MAX_STEPS and not STOP.exists() and time.time() + 600 < end_at():
        best = best_of(n); proof = best.get("proof") or ""
        plans = detect.plan_all(n, proof, LEMMAS.get(n, []))
        nxt = next((p for p in plans if p["step"] not in tried), None) or next((p for p in plans if p["step"] in improved and tried.count(p["step"]) < 2), None)
        if not nxt:
            log(f"row {n.split('.')[-1]}: no further move applies ({[p['step'] for p in plans]}, tried {tried})"); break
        if not admit():
            break
        k += 1; step = nxt["step"]; run_id = f"gap6x{i:02d}-k{k}"
        card = G / "cards" / f"{op.safe(n)}.k{k}.md"; card.parent.mkdir(exist_ok=True); card.write_text(nxt["msg"] + "\n")
        cmd = op.session_cmd(a, n, run_id, fresh=False); assert "--fresh" not in cmd
        cmd[cmd.index("--work-root") + 1] = str(WORK)
        oc = [j for j, x in enumerate(cmd) if x.startswith("--open-card=") or x == "--open-card"]
        if oc:
            j = oc[0]
            if cmd[j] == "--open-card": cmd[j + 1] = str(card)
            else: cmd[j] = f"--open-card={card}"
        else:
            cmd += ["--open-card", str(card)]
        s0 = best.get("score") or 0.0; t0 = time.time()
        log(f"{run_id} starts: {n.split('.')[-1]} step {k} [{step}] from {s0:.3f} (gap {az - s0:+.3f})")
        rc = op.run_session(cmd, ENV, G / "logs" / f"{run_id}.log", min(t0 + STEP_S, end_at()),
                            now=lambda: float("inf") if (STOP.exists() or time.time() >= end_at()) else time.time())
        b1 = best_of(n); s1 = b1.get("score") or s0
        tried.append(step)
        if s1 > s0 + 1e-9:
            improved.add(step)
        rec = {"row": n, "k": k, "step": step, "run_id": run_id, "rc": rc, "seconds": round(time.time() - t0, 1), "before": s0, "after": s1,
               "gain": round(s1 - s0, 4), "azure": az, "gap_before": round(az - s0, 4), "gap_after": round(az - s1, 4),
               "tokens": b1.get("tokens"), "heartbeats": b1.get("heartbeats"), "move_in_best": sig(step, b1.get("proof") or ""),
               "out_tokens": op.session_out_tokens(op.RUNS / run_id), "t_end": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        jappend(rec)
        log(f"STEP {n.split('.')[-1]} {k} [{step}]: {s0:.3f} -> {s1:.3f} ({s1 - s0:+.3f}); gap to Azure {az - s0:+.3f} -> {az - s1:+.3f}; move in best {rec['move_in_best']}")
    b = best_of(n)
    log(f"ROW DONE {n.split('.')[-1]}: A100 {b0['score']:.3f} -> {b.get('score', 0):.3f}; Azure {az:.3f}; gap {az - b0['score']:+.3f} -> {az - (b.get('score') or 0):+.3f}")


def main():
    G.mkdir(exist_ok=True); (G / "logs").mkdir(exist_ok=True); WORK.mkdir(exist_ok=True)
    (G / "chain.pid").write_text(str(os.getpid()))
    todo = []
    for n in AZ:
        if n not in IDX or not (MAIN / op.safe(n) / "state.json").exists():
            continue
        proof = json.loads((MAIN / op.safe(n) / "state.json").read_text())["best"]["proof"]
        pl = detect.plan_all(n, proof, LEMMAS.get(n, []))
        if E("DRY") == "1":
            print(f"{n.split('.')[-1][:36]:36s} moves {[p['step'] for p in pl]}")
        if pl:
            todo.append(n)
    if E("DRY") == "1":
        return
    log(f"gap6 chain start: {len(todo)} rows, STEP_S {STEP_S:.0f}, MAX_STEPS {MAX_STEPS}, MAX_TOTAL {MAX_TOTAL}, end {time.strftime('%H:%M', time.gmtime(end_at()))}")
    ths = [threading.Thread(target=row_chain, args=(n,), daemon=True) for n in todo]
    for t in ths:
        t.start(); time.sleep(1)
    for t in ths:
        t.join()
    log("gap6 chain: all rows done")


if __name__ == "__main__":
    main()
