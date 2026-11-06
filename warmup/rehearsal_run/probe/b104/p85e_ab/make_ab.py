#!/usr/bin/env python3
"""b104 box A/B: build the AB variant of the p85e scheduler (v3.1 -> v3.2-ab) by exact anchors (each must match once).
    python3 make_ab.py p85e_xloop_host.v31.py p85e_xloop_host.py
AB=1 (opt-in; without it the variant behaves as v3.1, except that a/b bookkeeping exists): p85e's own new sessions run as PAIRS on the
rows AB_ROWS (fixed order): arm A (default flags) and arm B (+ AB_FLAGS) start in the same tick from byte-identical copies of the main row
dir (snapshot), each in its own work root /workspace/p85e/ab/{A,B}/work, both with the overlay agent AB_AGENT (md5 AB_AGENT_MD5 checked
before every pair start), run ids <tag>-aNN-kK / <tag>-bNN-kK. Each arm chains sessions on its own lineage until AB_BUDGET_S of wall
time from the pair start (matched GPU time; the session in flight gets SIGTERM, best banked). Pairs need 2 free slots under MAX_TOTAL and
p85e's own gates (KV_HIGH, waiting 0, preemption window, START_GAP_S); while a pair could start, no c/t single takes a slot (reserve). At
most AB_PAIRS pairs; no pair start that would not finish before AB_END_EPOCH (all a/b sessions stop at AB_END_EPOCH); no new pair once
each arm has AB_TARGET finished sessions. After every arm session the arm best goes to main only if better by WB_MARGIN (one-way; the arms
never read main or each other after the seed). Babysit trouble / shed on an a/b session stops that PAIR and drops the row. Harm stop:
after half of AB_ROWS' pairs are finished (min 4), B worse than A by > 1 on >= 75% of finished rows -> all pairs stop, AB off.
/workspace/p85e/ab/STOP -> all pairs stop now (bests banked), AB off. Records: ab/ab_pairs.jsonl, ab/ab_sessions.jsonl."""
import sys
from pathlib import Path

src, out = Path(sys.argv[1]), Path(sys.argv[2])
s = src.read_text()


def rep(old, new, count=1):
    global s
    n = s.count(old)
    if n != count:
        sys.exit(f"anchor {old[:70]!r}: {n} matches (need {count}); nothing written")
    s = s.replace(old, new)


# --- docstring note + gates
rep('''import calendar, collections, fcntl, json, os, re, shlex, shutil, statistics, subprocess, sys, threading, time, traceback''',
    '''import calendar, collections, fcntl, hashlib, json, os, re, shlex, shutil, statistics, subprocess, sys, threading, time, traceback''')
rep('''         "P85E_W", "START_GAP_S", "PREEMPT_WIN_S", "SHED", "SHED_KV", "SHED_HOLD_S", "SHED_GAP_S")''',
    '''         "P85E_W", "START_GAP_S", "PREEMPT_WIN_S", "SHED", "SHED_KV", "SHED_HOLD_S", "SHED_GAP_S",
         "AB", "AB_ROWS", "AB_PAIRS", "AB_BUDGET_S", "AB_END_EPOCH", "AB_AGENT", "AB_AGENT_MD5", "AB_FLAGS", "AB_TARGET", "AB_MIN_CHAIN_S")''')
rep('''GRACE_S, WB_S, TICK_S, BABYSIT_S, DRIVER_WARM_S = 90, 300, 20, 300, 180''',
    '''GRACE_S, WB_S, TICK_S, BABYSIT_S, DRIVER_WARM_S = 90, 300, 20, 300, 180
# b104 box A/B (v3.2-ab, 2026-11-01): see probe/b104/p85e_ab/make_ab.py
AB = E("AB", "0") == "1"
AB_ROWS = [int(r) for r in E("AB_ROWS", "").split(",") if r.strip()]
AB_PAIRS = int(E("AB_PAIRS", "3"))
AB_BUDGET_S = float(E("AB_BUDGET_S", "2400"))
AB_END = float(E("AB_END_EPOCH") or 0)
AB_AGENT = E("AB_AGENT", "/workspace/b104/lra/harness/agent.py")
AB_AGENT_MD5 = E("AB_AGENT_MD5", "")
AB_FLAGS = E("AB_FLAGS", "--late-turn-cap 6000 --late-turn-from 4 --no-trunc-escalation").split()
AB_TARGET = int(E("AB_TARGET", "8"))
AB_MIN_CHAIN_S = float(E("AB_MIN_CHAIN_S", "300"))''')

# --- root of a lineage
rep('''_wlock = threading.Lock()   # serializes this process's own state.json writes (main thread + session threads)''',
    '''_wlock = threading.Lock()   # serializes this process's own state.json writes (main thread + session threads)
AB_ROOT = X / "ab"; AB_ARM = {"a": AB_ROOT / "A" / "work", "b": AB_ROOT / "B" / "work"}
AB_STOP = AB_ROOT / "STOP"; AB_PAIRS_J = AB_ROOT / "ab_pairs.jsonl"; AB_SESS_J = AB_ROOT / "ab_sessions.jsonl"


def root_of(kind: str) -> Path:
    return {"t": TWIN, "a": AB_ARM["a"], "b": AB_ARM["b"]}.get(kind, MAIN)''')

# --- babysit: the lineage's own root; a/b trouble stops the pair
rep('''        own = (TWIN if key[0] == "t" else MAIN) / op.safe(names[key[1]]) / "state.json"
        att = [x for x in (read_state(own).get("attempts") or []) if x.get("run_id") == rid]''',
    '''        own = root_of(key[0]) / op.safe(names[key[1]]) / "state.json"
        att = [x for x in (read_state(own).get("attempts") or []) if x.get("run_id") == rid]''')
rep('''def stop_session(key, why: str, disable: bool) -> None:
    j = ext.get(key)''',
    '''def stop_session(key, why: str, disable: bool) -> None:
    if key[0] in "ab":
        ab_stop_pair(key[1], f"babysit: {why}"); return
    j = ext.get(key)''')

# --- shed: an a/b youngest session stops its pair
rep('''    t0, key = max(live)
    j = ext[key]; j["flag"].set(); last_shed = now''',
    '''    t0, key = max(live)
    if key[0] in "ab":
        last_shed = now
        log(f"CRITICAL shed: vLLM KV {kv:.2f} >= {SHED_KV} for {(now - kv_high_since) / 60:.0f} min with preemptions +{rise:.0f}: the youngest "
            f"own session is A/B {ext[key]['run_id']}: its pair stops and row {key[1]:02d} is dropped")
        ab_stop_pair(key[1], "shed (KV saturation)"); return
    j = ext[key]; j["flag"].set(); last_shed = now''')

# --- tick: AB pairs first (and slot reserve), then c/t as before
rep('''    cands, info = plan(now, ps, vm)
    free = info["cap"] - info["total"]
    if free <= 0 or not cands:
        return
    if now < paused_until:''',
    '''    cands, info = plan(now, ps, vm)
    free = info["cap"] - info["total"]
    abwant = ab_want_pair(now)
    if free <= 0 or not (cands or abwant):
        return
    if now < paused_until:''')
rep('''    if rise > 0:
        say_every("preempt", f"vLLM preemptions +{rise:.0f} within {PREEMPT_WIN_S:.0f} s: no new session", 300); return
    for p, kind, i, best, need, why in cands:''',
    '''    if rise > 0:
        say_every("preempt", f"vLLM preemptions +{rise:.0f} within {PREEMPT_WIN_S:.0f} s: no new session", 300); return
    if abwant:
        if free >= 2:
            if ab_start_pair(now, info, vm):
                last_start = now
            return
        else:
            say_every("abres", f"A/B: a pair is due, {free} free slot(s) of {info['cap']}: slots reserved for the pair (no c/t start)", 600)
            return
    for p, kind, i, best, need, why in cands:''')

# --- the A/B machinery (before dry())
rep('''def dry() -> int:''', r'''# ------------------------------------------------------------------------------------------------------------------------- b104 A/B
ab_pairs: dict = {}        # row -> {"t0", "t_end", "s0", "name", "dropped", "done", "flags": {kind: Event}}
ab_started: set = set()    # rows with a pair start record (this or an earlier instance): never seeded twice
ab_fin = {"a": 0, "b": 0}  # finished arm sessions of this instance
ab_off_why = None
ab_said_done = False


def md5_of(p: str) -> str:
    try:
        return hashlib.md5(Path(p).read_bytes()).hexdigest()
    except OSError:
        return "missing"


def ab_init() -> None:
    global ab_off_why
    if not AB:
        return
    if not DRY:
        AB_ROOT.mkdir(parents=True, exist_ok=True)
    for r in op.read_jsonl_records(AB_PAIRS_J):
        if r.get("event") == "start":
            ab_started.add(int(r["row"]))
    m = md5_of(AB_AGENT)
    if AB_END <= 0 or not AB_ROWS:
        ab_off_why = "AB_END_EPOCH / AB_ROWS not set"
    elif not AB_AGENT_MD5 or m != AB_AGENT_MD5:
        ab_off_why = f"overlay agent md5 {m} != AB_AGENT_MD5 {AB_AGENT_MD5 or '-'}"
    elif any(r < 0 or r >= len(names) for r in AB_ROWS):
        ab_off_why = f"AB_ROWS out of range: {AB_ROWS}"


def ab_running(i: int) -> bool:
    return any((k, i) in ext and ext[(k, i)]["thread"].is_alive() for k in "ab")


def ab_next_row():
    for i in AB_ROWS:
        if i not in ab_started and i not in ab_pairs:
            return i
    return None


def ab_window(now: float) -> bool:
    return AB and ab_off_why is None and now < AB_END and not AB_STOP.exists()


def ab_want_pair(now: float) -> bool:
    if not ab_window(now):
        return False
    if min(ab_fin.values()) >= AB_TARGET:
        return False
    if sum(1 for i in ab_pairs if ab_running(i)) >= AB_PAIRS:
        return False
    if now + AB_BUDGET_S > min(AB_END, END):
        return False
    return ab_next_row() is not None


def ab_stop_pair(i: int, why: str) -> None:
    p = ab_pairs.get(i)
    if not p:
        return
    for f in p["flags"].values():
        f.set()
    if not p.get("dropped"):
        p["dropped"] = why
        jappend(AB_PAIRS_J, {"event": "drop", "row": i, "problem": p["name"], "why": why, "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())})
        log(f"CRITICAL A/B: pair row {i:02d} stopped and dropped from both arms: {why}")


def _sha(p: Path) -> str:
    try:
        return hashlib.sha256(p.read_bytes()).hexdigest()[:16]
    except OSError:
        return "missing"


def ab_seed(i: int):
    """One snapshot of the main row dir, copied into both arms (byte-identical). Returns (s0 best, sha A, sha B) or None (row dropped)."""
    n = names[i]; sd = op.safe(n)
    snap = AB_ROOT / "snap" / sd
    if snap.exists() or (AB_ARM["a"] / sd).exists() or (AB_ARM["b"] / sd).exists():
        log(f"A/B: row {i:02d} already has an arm or snapshot dir (an earlier pair): skipped"); return None
    snap.parent.mkdir(parents=True, exist_ok=True)
    ign = shutil.ignore_patterns("LRAScratch", "*.p85e-tmp", "state.json.before-*", "state.json.tmp*", "*.tmp")
    with _wlock:   # no own write-back into the main row while copying
        shutil.copytree(MAIN / sd, snap, ignore=ign)
    for k in "ab":
        AB_ARM[k].mkdir(parents=True, exist_ok=True)
        tmp = AB_ARM[k] / (sd + ".ab-seed")
        shutil.rmtree(tmp, ignore_errors=True)
        shutil.copytree(snap, tmp)
        os.replace(tmp, AB_ARM[k] / sd)
    sa, sb = _sha(AB_ARM["a"] / sd / "state.json"), _sha(AB_ARM["b"] / sd / "state.json")
    if sa != sb or sa == "missing":
        log(f"CRITICAL A/B: row {i:02d} arm seeds differ ({sa} vs {sb}): row dropped"); return None
    return score_of(snap / "state.json"), sa, sb


def ab_start_pair(now: float, info: dict, vm: dict) -> bool:
    global ab_off_why
    m = md5_of(AB_AGENT)
    if m != AB_AGENT_MD5:
        ab_off_why = f"overlay agent md5 changed: {m}"; log(f"CRITICAL A/B off: {ab_off_why}"); return False
    i = ab_next_row()
    if i is None:
        return False
    ab_started.add(i)
    seed = ab_seed(i)
    if seed is None:
        jappend(AB_PAIRS_J, {"event": "start", "row": i, "problem": names[i], "seeded": False}); return False
    s0, sa, sb = seed
    t0 = time.time(); t_end = min(t0 + AB_BUDGET_S, AB_END)
    p = {"t0": t0, "t_end": t_end, "s0": s0, "name": names[i], "dropped": None, "done": False,
         "flags": {"a": threading.Event(), "b": threading.Event()}}
    ab_pairs[i] = p
    jappend(AB_PAIRS_J, {"event": "start", "row": i, "problem": names[i], "seeded": True, "s0": s0, "sha_a": sa, "sha_b": sb,
                         "t0": round(t0, 1), "t_end": round(t_end, 1), "budget_s": AB_BUDGET_S, "agent_md5": m, "flags_b": AB_FLAGS,
                         "kv": vm.get("kv_cache_usage_perc"), "total_before": info["total"],
                         "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t0))})
    for k in "ab":
        kk = next_k(k, i); kcount[(k, i)] = kk
        th = threading.Thread(target=ab_arm, args=(k, i, p), daemon=False, name=f"{k}{i:02d}")
        ext[(k, i)] = {"thread": th, "run_id": f"{TAG}-{k}{i:02d}-k{kk}", "t0": time.time(), "flag": p["flags"][k], "first": True}
        th.start()
    info["total"] += 2
    log(f"A/B pair start row {i:02d} {names[i][:44]} (s0 {s0:.3f}, seed sha {sa}; budget {AB_BUDGET_S:.0f} s -> stop by "
        f"{time.strftime('%H:%M:%S', time.gmtime(t_end))}; total {info['total'] - 2} -> {info['total']} of cap {info['cap']}; kv "
        f"{vm.get('kv_cache_usage_perc', 0):.2f}; finished arm sessions A {ab_fin['a']} B {ab_fin['b']})")
    return True


def ab_arm(kind: str, i: int, p: dict) -> None:
    """One arm of a pair: sessions chained on the arm's own lineage until the pair's t_end (or a stop)."""
    n = names[i]; root = AB_ARM[kind]; own = root / op.safe(n) / "state.json"; mst = MAIN / op.safe(n) / "state.json"
    flag = p["flags"][kind]; faults = 0; first = True
    try:
        while not flag.is_set() and time.time() < END:
            left = p["t_end"] - time.time()
            if left <= (1 if first else AB_MIN_CHAIN_S):
                break
            k = next_k(kind, i) if not first else kcount[(kind, i)]
            kcount[(kind, i)] = k
            run_id = f"{TAG}-{kind}{i:02d}-k{k}"
            j = ext.get((kind, i))
            if j is not None:
                j["run_id"] = run_id; j["t0"] = time.time(); j["first"] = first
            cmd = op.session_cmd(a, n, run_id, fresh=False)
            assert cmd[1] == "harness/agent.py" and "--fresh" not in cmd
            cmd[1] = AB_AGENT
            cmd[cmd.index("--work-root") + 1] = str(root)
            if kind == "b":
                cmd += AB_FLAGS
            b0 = score_of(own); t0 = time.time()
            log(f"{run_id} starts (A/B arm {kind.upper()}; own best {b0:.3f}, s0 {p['s0']:.3f}; stop by "
                f"{time.strftime('%H:%M:%S', time.gmtime(p['t_end']))})")
            rc = op.run_session(cmd, ENV, X / "logs" / f"{run_id}.log", p["t_end"],
                                now=lambda: float("inf") if (flag.is_set() or time.time() >= END) else time.time())
            b1 = score_of(own); sec = time.time() - t0
            otok = op.session_out_tokens(op.RUNS / run_id)
            rec = {"arm": kind.upper(), "kind": kind, "row": i, "problem": n, "k": k, "run_id": run_id, "rc": rc, "seconds": round(sec, 1),
                   "out_tokens": otok, "tool_errors": op.session_tool_errors(op.RUNS / run_id), "own_before": b0, "own_after": b1,
                   "gain": round(b1 - b0, 4), "s0": p["s0"], "stopped": flag.is_set(), "budget_cut": rc is None and not flag.is_set(),
                   "end_cut": time.time() >= END, "t_end": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
            jappend(AB_SESS_J, rec)
            ab_fin[kind] += 1; first = False
            r = merge_best(mst, best_of(own), WB_MARGIN, backup=True)
            log(f"{run_id} done rc {rc} in {sec:.0f} s: own {b0:.3f}->{b1:.3f} (s0 {p['s0']:.3f}), out_tok {otok}"
                f"{'; arm->main ' + format(r[0], '.3f') + '->' + format(r[1], '.3f') if r else ''}{' (stopped)' if flag.is_set() else ''}")
            if rc is None:
                break
            if rc != 0 and otok == 0 and not flag.is_set():
                faults += 1
                if faults >= 2:
                    ab_stop_pair(i, f"arm {kind.upper()}: two failed sessions in a row (rc {rc}, 0 output tokens)"); break
                time.sleep(30)
            else:
                faults = 0
    except Exception as e:  # noqa: BLE001
        log(f"A/B arm {kind}{i:02d}: thread raised {type(e).__name__}: {e}")
        ab_stop_pair(i, f"arm {kind.upper()} thread raised {type(e).__name__}")


def ab_housekeep(now: float) -> None:
    """Finished pairs (both arm threads ended): readout + one-way write-back; harm stop; STOP file; the end of the window (logged once)."""
    global ab_off_why, ab_said_done
    if not AB:
        return
    if AB_STOP.exists() and ab_off_why is None:
        ab_off_why = "ab/STOP file"
        for i in list(ab_pairs):
            if ab_running(i):
                ab_stop_pair(i, "ab/STOP file")
        log("A/B off: ab/STOP file present (running pairs stopped, bests banked)")
    for i, p in list(ab_pairs.items()):
        if p["done"] or ab_running(i):
            continue
        p["done"] = True
        n = names[i]; ba = score_of(AB_ARM["a"] / op.safe(n) / "state.json"); bb = score_of(AB_ARM["b"] / op.safe(n) / "state.json")
        rec = {"event": "done", "row": i, "problem": n, "s0": p["s0"], "best_a": ba, "best_b": bb, "gain_a": round(ba - p["s0"], 4),
               "gain_b": round(bb - p["s0"], 4), "d_b_minus_a": round(bb - ba, 4), "dropped": p["dropped"], "wall_s": round(now - p["t0"], 1),
               "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        jappend(AB_PAIRS_J, rec)
        for k in "ab":
            r = merge_best(MAIN / op.safe(n) / "state.json", best_of(AB_ARM[k] / op.safe(n) / "state.json"), WB_MARGIN, backup=True)
            if r:
                log(f"A/B write-back row {i:02d} arm {k.upper()} -> main {r[0]:.3f}->{r[1]:.3f}")
        log(f"A/B pair done row {i:02d} {n[:44]}: s0 {p['s0']:.3f}, A {ba:.3f} ({ba - p['s0']:+.3f}), B {bb:.3f} ({bb - p['s0']:+.3f}), "
            f"B-A {bb - ba:+.3f}{' DROPPED: ' + p['dropped'] if p['dropped'] else ''}")
        fin = [q for q in ab_pairs.values() if q["done"] and not q["dropped"]]
        if ab_off_why is None and len(fin) >= max(4, (len(AB_ROWS) + 1) // 2):
            worse = 0
            for q in fin:
                qa = score_of(AB_ARM["a"] / op.safe(q["name"]) / "state.json"); qb = score_of(AB_ARM["b"] / op.safe(q["name"]) / "state.json")
                worse += 1 if qb < qa - 1.0 else 0
            if worse >= 0.75 * len(fin):
                ab_off_why = f"harm stop: B worse than A by > 1 on {worse}/{len(fin)} finished rows"
                for jj in list(ab_pairs):
                    if ab_running(jj):
                        ab_stop_pair(jj, ab_off_why)
                log(f"CRITICAL A/B off: {ab_off_why}")
    over = not ab_window(now) or min(ab_fin.values()) >= AB_TARGET or (ab_next_row() is None)
    if over and not ab_said_done and not any(ab_running(i) for i in ab_pairs) and ab_pairs:
        ab_said_done = True
        log(f"A/B window over ({ab_off_why or ('AB_END' if now >= AB_END else 'target / rows done')}): {len(ab_pairs)} pairs, finished arm "
            f"sessions A {ab_fin['a']} B {ab_fin['b']}; this instance continues as v3.1 (c/t) until p85e_ctl.sh handover reverts it")


def dry() -> int:''')

# --- dry: the A/B plan
rep('''    print(f"candidates (priority order; {free} free slot(s) now -> the first one would start once the gates allow):")''',
    '''    if AB:
        ab_init()
        print(f"A/B {'ON' if ab_off_why is None else 'OFF (' + ab_off_why + ')'}: rows {','.join(f'{r:02d}' for r in AB_ROWS)} (already "
              f"started {sorted(ab_started) or '-'}); pairs <= {AB_PAIRS}; budget {AB_BUDGET_S:.0f} s per row and arm; end "
              f"{hm(AB_END)} UTC; target {AB_TARGET} finished sessions per arm; agent {AB_AGENT} md5 {md5_of(AB_AGENT)} (want "
              f"{AB_AGENT_MD5 or '-'}); arm B flags {' '.join(AB_FLAGS)}; next row {ab_next_row()}; a pair wanted now: {ab_want_pair(now)}")
        for r in AB_ROWS:
            print(f"  A/B row {r:02d} {names[r][:50]:50} main {score_of(MAIN / op.safe(names[r]) / 'state.json'):.3f}")
    print(f"candidates (priority order; {free} free slot(s) now -> the first one would start once the gates allow):")''')

# --- main: init, housekeeping, startup line
rep('''    (X / "xloop.pid").write_text(f"{os.getpid()}\\n")
    read_end()''',
    '''    (X / "xloop.pid").write_text(f"{os.getpid()}\\n")
    read_end()
    ab_init()
    if AB:
        log(f"p85e v3.2-ab A/B {'ON' if ab_off_why is None else 'OFF (' + ab_off_why + ')'}: rows {','.join(f'{r:02d}' for r in AB_ROWS)}; "
            f"pairs <= {AB_PAIRS}; budget {AB_BUDGET_S:.0f} s per row and arm; end {hm(AB_END)} UTC; target {AB_TARGET}/arm; agent "
            f"{AB_AGENT} md5 {md5_of(AB_AGENT)}; arm B {' '.join(AB_FLAGS)}")''')
rep('''            for key in [kk for kk, j in ext.items() if not j["thread"].is_alive()]:
                ext.pop(key)''',
    '''            for key in [kk for kk, j in ext.items() if not j["thread"].is_alive()]:
                ext.pop(key)
            try:
                ab_housekeep(now)
            except Exception as e:  # noqa: BLE001
                say_every("aberr", f"CRITICAL A/B housekeeping raised {type(e).__name__}: {str(e)[:160]}", 300)''')
# the drain loop also finalizes pairs (a handover leaves A/B sessions draining here)
rep('''            twin_sync()
            if time.time() - last_bs >= BABYSIT_S:
                babysit(); last_bs = time.time()
            time.sleep(10)''',
    '''            twin_sync()
            for key in [kk for kk, j in ext.items() if not j["thread"].is_alive()]:
                ext.pop(key)
            try:
                ab_housekeep(time.time())
            except Exception as e:  # noqa: BLE001
                say_every("aberr", f"CRITICAL A/B housekeeping raised {type(e).__name__}: {str(e)[:160]}", 300)
            if time.time() - last_bs >= BABYSIT_S:
                babysit(); last_bs = time.time()
            time.sleep(10)''')
rep('''        twin_sync()
        log("p85e xloop exits")''',
    '''        twin_sync()
        try:
            ab_housekeep(time.time())
        except Exception:  # noqa: BLE001
            pass
        log("p85e xloop exits")''')
rep('''            if (MAX_TOTAL is None or MAX_TOTAL > 0) and (CONT or TWINS):''',
    '''            if (MAX_TOTAL is None or MAX_TOTAL > 0) and (CONT or TWINS or AB):''')
rep('''v3.1 (2026-11-01 ~00:40 UTC; review''', '''v3.2-ab (2026-11-01 ~04:30 UTC, b104 box A/B; opt-in AB=1, see probe/b104/p85e_ab/make_ab.py in lean-refactor branch b104-turncap).
v3.1 (2026-11-01 ~00:40 UTC; review''')
compile(s, str(out), "exec")
out.write_text(s)
print(f"v3.2-ab written: {out}")
