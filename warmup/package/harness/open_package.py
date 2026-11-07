#!/usr/bin/env python3
"""Open-track package driver (2026-10-27; docs/open_package_readme.md, docs/open_package_audit.md). One command runs the whole benchmark on

















































"""
from __future__ import annotations

import argparse, gzip, hashlib, itertools, json, math, os, queue, re, shlex, shutil, signal, statistics, subprocess, sys, threading, time
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait as fwait
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:                                                                                                          
    sys.path.insert(0, str(ROOT))
FROZEN = ROOT / "probe/open_rederive/open_frozen.json"
RUNS = ROOT / "probe/runs"                                                                               
FROZEN_SHA16 = "795c9e3650370ce4"                                                                                 
OPT_IN_FAMILIES = ("hr",)                                                                                      
ASYNC_MAX_DRY = 3                                                                                              
POLL_S = 5.0
EXPORT_MARGIN_S = 900                                                                      
STOP_GRACE_S = 60                                         
                                                                                                                                      
                                                                                                                                    
END_PIPE_JOBS = 2                                                                                                                   
END_PIPE_ROW_S = 3600.0                                                    
END_PIPE_SLOTS = 1                                                                                                                    
END_PIPE_RESERVE_MB = 24000                                                                                                                
END_PIPE_NICE = 10                                                                     
NORMALIZE_SECONDS = 1800                                                                                                              
NORMALIZE_ROW_SECONDS = 900                                                       
NORMALIZE_MIN_START_S = 120                                                                                      
NORMALIZE_RETRY = ("skipped", "stopped", "error")                                                         
                                                                                                                                    
CONNECT_BUDGET_S = 7200                                                                                                                          
                                                                                                                                             
                                                                                                                            
                                                                                                                                 
                                                                                                                                         
                                                                                                                                    
                                                                                                                           
ROOM_FLAT_K = 3
ROOM_FLAT_MULT = 0.3
ROOM_FLAT_EPS = 0.005
SCHEDULES = ("ladder", "room")
                                                                                                                                      
                                                                                                                                    
                                                                                                                               
                                                                                                                                   
                                                                                                                                       
                                                                                                                                       
SORRY_GUARD_ENV = {"LRA_FORCE_WARN_SORRY": "1"}
AUDIT_TIMEOUT_S = 600                                                        
AUDIT_WRITE_S = 60                                                                                                                      
AUDIT_MIN_S = 120                                                                                                         
AUDIT_MIN_PIN_S = 5                                                                                        
AUDIT_JOBS = 4                                                                                                                        
                                                                                            
DEFAULT_SCHEDULE = "room"
                                                                                                                                           
                                                                                                                                         
                                                                                                                                          
                                                              
LOW_TURNS = 90
                                                                                                                                       
                                                                                                                                        
                                                                                                                                             
                                                                                                                            
                                                                                                                                                 
                                           
STYLE_RW_SECONDS = 7200.0                                                                                  
STYLE_RW_WALL_S = 900.0                                      
STYLE_RW_JOBS = 3                                                                                                                    
STYLE_RW_MAX_TOKENS = 7000                                                         
STYLE_RW_EFFORT = "default"
STYLE_RW_EXEMPLARS = "3ed15491e0b5b09a"
STYLE_RW_FLAGS = ("style_rw_seconds", "style_rw_wall_s", "style_rw_jobs", "style_rw_max_tokens", "style_rw_effort", "style_rw_exemplars")
NORMALIZE_FILES = ("harness/__init__.py", "harness/normalize.py", "harness/leantools.py", "probe/verify_candidates.py", "scorer/__init__.py",
                   "scorer/compile.py", "scorer/forbidden.py", "scorer/memgate.py", "scorer/score.py", "scorer/tokenize.py")


def log(msg: str) -> None:
    print(f"[{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}] {msg}", flush=True)


def safe(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", name)                                        


def read_jsonl(p: Path) -> list[dict]:
    return [json.loads(l) for l in Path(p).read_text().splitlines() if l.strip()]


def read_jsonl_records(p: Path) -> list[dict]:
    """The JSON-object lines of a jsonl file another process appends to; a torn line (a writer stopped mid-write: the driver stops the

"""
    out = []
    try:
        lines = Path(p).read_text(errors="replace").splitlines()
    except OSError:
        return out
    for l in lines:
        try:
            r = json.loads(l) if l.strip() else None
        except ValueError:
            continue
        if isinstance(r, dict):
            out.append(r)
    return out


def load_rows(rows_path, hbs_path) -> tuple[list[str], dict, dict]:
    rows = read_jsonl(rows_path)
    hbs = {r["name"]: r for r in read_jsonl(hbs_path)}
    need = ("name", "statement", "src", "proof_length", "version_info", "source")
    for r in rows:
        miss = [k for k in need if k not in r]
        if miss:
            raise SystemExit(f"rows file: {r.get('name', '?')} lacks {miss}")
        if r["name"] not in hbs:
            raise SystemExit(f"heartbeats file: no reference heartbeats for {r['name']}")
    names = [r["name"] for r in rows]
    if len(set(names)) != len(names):
        raise SystemExit("rows file: duplicate names")
    return names, {r["name"]: r for r in rows}, hbs


                                                                                                                                       
class Clock:
    """The job clock: job end = started_at + job_seconds; the agent deadline leaves the end stage, the normalize step (norm_seconds, 0

"""

    def __init__(self, started_at: float, job_seconds: float, end_seconds: float, export_margin: float = EXPORT_MARGIN_S, now=time.time,
                 norm_seconds: float = 0.0, style_seconds: float = 0.0):
        self.t0, self.job_end, self.now = float(started_at), float(started_at) + float(job_seconds), now
        self.end_seconds, self.margin, self.norm_seconds = float(end_seconds), float(export_margin), float(norm_seconds)
        self.style_seconds = float(style_seconds)

    @property
    def agent_deadline(self) -> float:
        return self.job_end - self.end_seconds - self.norm_seconds - self.style_seconds - self.margin

    @property
    def normalize_deadline(self) -> float:
        return self.job_end - self.margin - self.style_seconds

    @property
    def style_deadline(self) -> float:
        return self.job_end - self.margin

    def left(self, until: float | None = None) -> float:
        return (self.job_end if until is None else until) - self.now()


def compile_slots_env(slots: int | None, out: Path, environ=None) -> dict:
    """--compile-slots N (the router's --compile-slots of b63-speed2): {LRA_HBTOOL_SLOTS: N, LRA_HBTOOL_SCRATCH: this run's own scratch
"""
    environ = os.environ if environ is None else environ
    if not slots:
        return {}
    env = {"LRA_HBTOOL_SLOTS": str(int(slots))}
    if not environ.get("LRA_HBTOOL_SCRATCH"):
        env["LRA_HBTOOL_SCRATCH"] = str(ROOT / "probe/hbtool/.scratch" / f"opk-{hashlib.sha256(str(Path(out).resolve()).encode()).hexdigest()[:10]}")
    return env


def auto_slots(cpus: int | None = None, mem_avail_gb: float | None = None) -> int:
    """Compile slots for the end stage: a third of the logical CPUs (a Lean compile is one busy core plus I/O; the model server and the
"""
    cpus = cpus or os.cpu_count() or 4
    if mem_avail_gb is None:
        try:
            kb = next(int(l.split()[1]) for l in Path("/proc/meminfo").read_text().splitlines() if l.startswith("MemAvailable:"))
            mem_avail_gb = kb / 1024 / 1024
        except (OSError, StopIteration, ValueError):
            mem_avail_gb = 48.0
    return max(3, min(32, cpus // 3, int(mem_avail_gb // 8)))


def base_env(a) -> dict:
    """The dataset for harness/leantools (LRA_ROWS_FILE / LRA_HBS_FILE) and the official reference heartbeats for every row (LRA_LOCAL_REF
"""
    env = dict(os.environ)
    env.update({"LRA_ROWS_FILE": str(Path(a.rows).resolve()), "LRA_HBS_FILE": str(Path(a.heartbeats).resolve()), "PYTHONUNBUFFERED": "1"})
    if not a.keep_local_ref:
        env["LRA_LOCAL_REF"] = "none"
    env["LRA_CONNECT_BUDGET_S"] = str(float(getattr(a, "connect_budget_seconds", CONNECT_BUDGET_S)))                         
    env.update(SORRY_GUARD_ENV)                                                                             
    return env


                                                                                                                                       
def state_of(work: Path, name: str) -> dict:
    try:
        return json.loads((work / safe(name) / "state.json").read_text())
    except (OSError, ValueError):
        return {}


def best_score(work: Path, name: str) -> float:
    return float(((state_of(work, name).get("best") or {}).get("score")) or 33.33)


def session_cmd(a, name: str, run_id: str, fresh: bool) -> list[str]:
    cmd = [sys.executable, "harness/agent.py", "--open-package", "--endpoint", "openai", "--base-url", a.base_url, "--model", a.model,
           "--api-model", a.api_model or a.model, "--serving-tag", a.serving_tag, "--problems", name, "--workers", "1",
           "--turns", str(a.turns), "--max-tokens", str(a.max_tokens), "--reasoning-effort", a.reasoning_effort,
           "--work-root", str(Path(a.out).resolve() / "work"), "--run-id", run_id, "--rows", str(Path(a.rows).resolve()),
           "--heartbeats", str(Path(a.heartbeats).resolve()), "--max-api-retries", str(a.max_api_retries)]
    if fresh:
        cmd.append("--fresh")
        if getattr(a, "blind_start", "off") == "on":                                                                                          
            cmd.append("--blind-start")
    if a.api_key_file:
        cmd += ["--api-key-file", a.api_key_file]
    if not a.adaptive_turns:
        cmd.append("--no-adaptive-turns")
    cmd += ["--adaptive-low-turns", str(int(getattr(a, "low_turns", LOW_TURNS)))]                                                           
    if getattr(a, "compact_tool_json", True):                                                                     
        cmd.append("--compact-tool-json")
    if getattr(a, "skeleton_combinator_holes", True):                                                                            
        cmd.append("--skeleton-combinator-holes")
    for x in a.agent_arg or []:
        cmd += x.split()
    return cmd


REAP_ENV = "LRA_OPK_SESSION"                                                                                                          


def reap_tagged(tag: str, proc_root: Path = Path("/proc")) -> list[int]:
    """SIGKILL every process whose environment carries REAP_ENV=tag; returns their pids. Review 2026-10-28: scorer.memgate.run_lean (and


"""
    needle, me, killed = f"{REAP_ENV}={tag}".encode(), os.getpid(), []
    try:
        entries = [d for d in proc_root.iterdir() if d.name.isdigit() and int(d.name) != me]
    except OSError:
        return killed
    for d in entries:
        try:
            if needle not in (d / "environ").read_bytes().split(b"\0"):
                continue
            os.kill(int(d.name), signal.SIGKILL); killed.append(int(d.name))
        except (OSError, ValueError):                               
            continue
    return killed


def run_session(cmd: list[str], env: dict, log_path: Path, deadline: float, now=time.time) -> int | None:
    """One agent.py (end stage, normalize.py) process; stopped at `deadline` (SIGTERM, then SIGKILL after STOP_GRACE_S). Returns its exit
"""
    tag = f"{os.getpid()}-{time.time_ns()}-{threading.get_ident()}"
    with open(log_path, "a") as fh:
        fh.write(f"[open_package] command: {shlex.join(map(str, cmd))}\n"); fh.flush()                                                 
        p = subprocess.Popen(cmd, cwd=ROOT, env=dict(env, **{REAP_ENV: tag}), stdout=fh, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            return _wait_session(p, fh, deadline, now)
        finally:
            left = reap_tagged(tag)
            if left:
                fh.write(f"\n[open_package] {len(left)} process(es) left behind by the session killed: {left[:20]}\n"); fh.flush()


def _wait_session(p, fh, deadline: float, now) -> int | None:
    """run_session's wait: the exit code, or None once stopped at `deadline` (SIGTERM, then SIGKILL)."""
    while True:
        try:
            return p.wait(timeout=max(1.0, min(POLL_S, deadline - now())))
        except subprocess.TimeoutExpired:
            if now() < deadline:
                continue
        fh.write(f"\n[open_package] job deadline: stopping the session\n"); fh.flush()
        for sig, grace in ((signal.SIGTERM, STOP_GRACE_S), (signal.SIGKILL, 30)):
            try:
                os.killpg(p.pid, sig)
            except ProcessLookupError:
                pass
            try:
                p.wait(timeout=grace)
                return None
            except subprocess.TimeoutExpired:
                continue
        return None


def session_tool_errors(run_dir: Path) -> dict:
    """Per-tool exception counts of a finished session (agent.py's summary.json "tool_errors", 2026-10-30); {} when none or unreadable."""
    out: dict = {}
    try:
        for r in json.loads((run_dir / "summary.json").read_text()):
            for k, v in ((r or {}).get("tool_errors") or {}).items():
                out[k] = out.get(k, 0) + int(v)
    except Exception:                
        pass
    return out


def session_blind(run_dir: Path) -> dict | None:
    """A blind first session's numbers (agent.py summary "blind": reveal turn and reason, first banked turn, source reads); None otherwise."""
    try:
        for r in json.loads((run_dir / "summary.json").read_text()):
            if isinstance(r, dict) and isinstance(r.get("blind"), dict):
                return r["blind"]
    except Exception:                
        pass
    return None


def session_out_tokens(run_dir: Path) -> int:
    """Model output tokens of a finished session (agent.py's summary.json); 0 when it wrote none (a crash, a server outage)."""
    try:
        res = json.loads((run_dir / "summary.json").read_text())
        return sum(int(r.get("out_tokens") or 0) for r in res if isinstance(r, dict))
    except (OSError, ValueError, TypeError):
        return 0


def session_gain(line: dict) -> float:
    """One agent_sessions.jsonl line's gain: score_after - score_before (0 when either is missing)."""
    try:
        return float(line.get("score_after")) - float(line.get("score_before"))
    except (TypeError, ValueError):
        return 0.0


def room_priority(best: float, sessions: int, gains: list) -> float:
    """--schedule room (P5): (100 - best) / (sessions + 1), x ROOM_FLAT_MULT while the last ROOM_FLAT_K finished sessions were flat."""
    p = (100.0 - float(best)) / (int(sessions) + 1)
    if len(gains) >= ROOM_FLAT_K and all(g <= ROOM_FLAT_EPS for g in gains[-ROOM_FLAT_K:]):
        p *= ROOM_FLAT_MULT
    return p


def sessions_used(finished_ks: list, cut_ks: list) -> int:
    """A row's sessions against --max-sessions on a resume (2026-10-30): every finished session (an agent_sessions.jsonl line), plus every

"""
    cut = set(cut_ks) - set(finished_ks)
    return len(set(finished_ks)) + sum(1 for k in cut if k - 1 in cut)


def agent_stage(a, names: list[str], clock: Clock, runner=None, on_idle=None, set_busy=None) -> dict:
    """The async ladder (module docstring). `runner(n, k, run_id, fresh, deadline) -> rc` is injectable for tests; the default runs



"""
    out = Path(a.out); work = out / "work"; work.mkdir(parents=True, exist_ok=True); (out / "logs").mkdir(exist_ok=True)
    idx = {n: i for i, n in enumerate(names)}
    sess_path = out / "agent_sessions.jsonl"
    done_k: dict = {n: 0 for n in names}                                                                                
    used: dict = {n: 0 for n in names}                                                                           
    rec_ks: dict = {n: [] for n in names}                                                                             
    gains: dict = {n: [] for n in names}                                                             
    dry: dict = {n: 0 for n in names}
    parked: set = set()
    for l in (read_jsonl_records(sess_path) if sess_path.exists() else []):                                       
        if l.get("problem") in done_k:
            done_k[l["problem"]] = max(done_k[l["problem"]], int(l.get("k") or 0))
            rec_ks[l["problem"]].append(int(l.get("k") or 0))
            gains[l["problem"]].append(session_gain(l))
            dry[l["problem"]] = dry[l["problem"]] + 1 if l.get("dry") else 0                                                               
            if l.get("parked"):
                parked.add(l["problem"])
            elif l["problem"] in parked:
                parked.discard(l["problem"])
                                                                                                                                
                                                                                                                                       
                                                                                                                                
                                                                                                                                       
                                                                                                                                     
                                
    for n in names:
        cut = []
        if (work / safe(n)).exists():
            for d in RUNS.glob(f"{a.tag}-s{idx[n]:02d}-k*"):
                m = re.fullmatch(rf"{re.escape(a.tag)}-s{idx[n]:02d}-k(\d+)", d.name)
                if m:
                    done_k[n] = max(done_k[n], int(m.group(1)))
                    if int(m.group(1)) not in rec_ks[n]:
                        cut.append(int(m.group(1)))
        used[n] = sessions_used(rec_ks[n], cut)
        if cut:
            log(f"row#{idx[n]:02d} resume: {len(rec_ks[n])} finished session(s), cut k {sorted(cut)}: {used[n]} of --max-sessions "
                f"{a.max_sessions} used, next k {done_k[n] + 1}")
    sched = getattr(a, "schedule", DEFAULT_SCHEDULE)
    if sched not in SCHEDULES:
        raise SystemExit(f"--schedule {sched}: one of {SCHEDULES}")

    def order(n):                                                                                                                          
        if sched == "room":
            return (0, 0.0, idx[n]) if used[n] == 0 else (1, -room_priority(best_score(work, n), used[n], gains[n]), idx[n])
        return (used[n], idx[n])
    env = base_env(a)

    def default_runner(n, k, run_id, fresh, deadline):
        return run_session(session_cmd(a, n, run_id, fresh), env, out / "logs" / f"s{idx[n]:02d}.k{k}.log", deadline, now=clock.now)
    runner = runner or default_runner
    log(f"agent stage: {a.workers} worker(s) over {len(names)} row(s), at most {a.max_sessions} session(s) per row, deadline in "
        f"{clock.left(clock.agent_deadline) / 3600:.2f} h, schedule {sched}")
    inflight: dict = {}
    ex = ThreadPoolExecutor(max(1, a.workers), thread_name_prefix="opk")
    try:
        while True:
            busy = {j["n"] for j in inflight.values()}
            need = [n for n in names if n not in parked and used[n] < a.max_sessions]
            room = clock.left(clock.agent_deadline)
            ready = [] if room < a.min_session_seconds else sorted((n for n in need if n not in busy), key=order)
            if on_idle is not None and room >= a.min_session_seconds:
                starting = set(ready[: max(0, a.workers - len(inflight))])
                if set_busy is not None:
                    set_busy(busy | starting)                                                         
                for n in names:
                    if n not in busy and n not in starting:
                        try:
                            on_idle(n, n not in need)
                        except Exception as e:                                                            
                            log(f"end pipeline: offering row#{idx[n]:02d} raised {type(e).__name__}: {e}")
            for n in ready[: max(0, a.workers - len(inflight))]:
                k = done_k[n] + 1; done_k[n] = k; used[n] += 1                                                                         
                run_id = f"{a.tag}-s{idx[n]:02d}-k{k}"
                b0 = best_score(work, n)
                                                                                                                                          
                                                                                                    
                fresh = not (work / safe(n) / "state.json").exists()
                fu = ex.submit(runner, n, k, run_id, fresh, clock.agent_deadline)
                inflight[fu] = {"n": n, "k": k, "run_id": run_id, "t0": clock.now(), "b0": b0}
                log(f"row#{idx[n]:02d} session {k} starts ({len(inflight)} in flight; best {b0:.2f}"
                    + ("; blind start" if fresh and getattr(a, "blind_start", "off") == "on" else "")
                    + (f"; room priority {room_priority(b0, used[n] - 1, gains[n]):.2f}" if sched == "room" and used[n] > 1 else "") + ")")
            if not inflight:
                why = ("agent deadline" if room < a.min_session_seconds else "every row parked or at --max-sessions")
                log(f"agent stage ends: {why}")
                break
            fin, _ = fwait(list(inflight), timeout=POLL_S, return_when=FIRST_COMPLETED)
            for fu in fin:
                j = inflight.pop(fu); n = j["n"]
                try:
                    rc = fu.result()
                except Exception as e:                                                                                   
                    rc = None; log(f"row#{idx[n]:02d} session {j['k']}: runner raised {type(e).__name__}: {e}")
                toks = session_out_tokens(RUNS / j["run_id"])
                terr = session_tool_errors(RUNS / j["run_id"])
                if terr:                                                                                                           
                    log(f"WARNING row#{idx[n]:02d} session {j['k']}: tool errors {terr} (a tool the model was offered raised; see the session log)")
                is_dry = toks == 0
                dry[n] = dry[n] + 1 if is_dry else 0
                if dry[n] >= ASYNC_MAX_DRY:
                    parked.add(n)
                b1 = best_score(work, n); secs = clock.now() - j["t0"]
                gains[n].append(b1 - j["b0"])
                bl = session_blind(RUNS / j["run_id"]) if getattr(a, "blind_start", "off") == "on" else None
                if bl and (bl.get("violations") or bl.get("violations_after_reveal")):
                    log(f"row#{idx[n]:02d} session {j['k']}: blind start: {bl.get('violations')} source read(s) before the reveal, "
                        f"{bl.get('violations_after_reveal')} after (counted, not blocked)")
                with sess_path.open("a") as fh:
                    fh.write(json.dumps({"problem": n, "row": idx[n], "k": j["k"], "run_id": j["run_id"], "rc": rc, "seconds": round(secs, 1),
                                         "out_tokens": toks, "dry": is_dry, "score_before": j["b0"], "score_after": b1,
                                         "parked": n in parked, "tool_errors": terr, **({"blind": bl} if bl else {})}, ensure_ascii=False) + "\n")
                mean = statistics.mean(best_score(work, x) for x in names)
                log(f"row#{idx[n]:02d} session {j['k']} done (rc {rc}): {j['b0']:.2f} -> {b1:.2f} in {secs:.0f} s"
                    + (f"; dry ({dry[n]} in a row)" if is_dry else "") + ("; parked" if n in parked else "")
                    + f"; {len(inflight)} in flight; mean {mean:.2f}")
    finally:
        ex.shutdown(wait=True)
    return {n: {"sessions": used[n], "k": done_k[n], "dry": dry[n], "parked": n in parked, "score": best_score(work, n)} for n in names}


                                                                                                                                   
                                                                                                                 
                                                                                                                                     
                                                                                                                                
                                                                                                                             
                                                                              
                                                                                                                                       
                                                                                                                                      
BANNED = ("TECHNIQUE CARDS", "A HABIT OF THE STRONGEST", "LIBRARY LEADS", "UNVERIFIED CLAIMS", "NAMES THAT DO NOT EXIST",
          "STRUCTURAL PASS", "HEARTBEAT FIRST", "HEARTBEAT-FIRST", "LEVER REVIEW", "SCOUT RUN", "SCOUT A", "SCOUT B", "SCOUT C",
          "TERM-MODE FINISH", "HARD-TAIL", "REWRITE FIRST", "AUTOMATION FIRST", "(R3", "R3, operator", "the target to beat",
          "BLIND TARGET", "PATTERN:", "REPO AUTOMATION", "SHORT POLISH RUN", "points_left_length", "one_token_equals_heartbeats",
          "points_per_1k_heartbeats", "lean_search", "lean_mine", "[tested:", "KNOWLEDGE BRIEF", "MECHANICAL PRE-PASS", "REFUTED MOVES",
          "measured on this seed", "UPSTREAM", "git log -p", "(Tier 1)", "`•` in a lambda", "`axis` in lean_check",
          "Top-down development", "fill one hole at a time")


def audit_trajectories(run_ids: list[str]) -> dict:
    """Every harness-written message (role user: the opening, nudges, tool results), the system prompt and the tool list of each session
"""
    hits, msgs, files = [], 0, 0
    for rid in run_ids:
        for f in sorted((RUNS / rid / "trajectories").glob("*.jsonl*")):                                               
            files += 1
            raw = gzip.open(f, "rt", errors="replace").read() if f.suffix == ".gz" else f.read_text(errors="replace")
            for line in raw.splitlines():
                try:
                    r = json.loads(line)
                except ValueError:
                    continue
                if r.get("type") == "message" and r.get("role") == "user":
                    msgs += 1
                                                                                                                
                    text = re.sub(r"unknown tool \S+ in this session \(tools: [^)]*\)", "", json.dumps(r.get("content"), ensure_ascii=False))
                elif "system" in r and isinstance(r.get("tools"), list):                                                                
                    text = str(r.get("system")) + " " + " ".join(map(str, r["tools"]))
                else:
                    continue
                hits += [{"run_id": rid, "i": r.get("i"), "phrase": b} for b in BANNED if b in text]
    return {"sessions": len(run_ids), "trajectory_files": files, "user_messages": msgs, "hits": hits[:50], "n_hits": len(hits)}


                                                                                                                                     
def package_config(out: Path, with_hr: bool, frozen: Path = FROZEN) -> Path:
    """open_frozen.json (sha256 checked) as shipped: the opt-in families removed unless asked for (hr: 6f decision)."""
    raw = frozen.read_bytes()
    if hashlib.sha256(raw).hexdigest()[:16] != FROZEN_SHA16:
        raise SystemExit(f"{frozen}: not the frozen open config (sha256 {hashlib.sha256(raw).hexdigest()[:16]} != {FROZEN_SHA16})")
    cfg = json.loads(raw)
    drop = () if with_hr else OPT_IN_FAMILIES
    for f in drop:
        cfg["families"] = [x for x in cfg["families"] if x != f]
        cfg["order"] = [x for x in cfg.get("order", []) if x != f]
        (cfg.get("ops") or {}).pop(f, None); (cfg.get("ctx") or {}).pop(f, None)
        cfg["entries"] = {k: v for k, v in (cfg.get("entries") or {}).items() if not k.startswith(f + ":")}
        cfg["opt_in"] = [x for x in cfg.get("opt_in", []) if not x.startswith(f + ":")]
    cfg["name"] = "open-package" + ("" if drop else "+hr")
    cfg["_derived_from"] = {"file": str(frozen.relative_to(ROOT)), "sha256_16": FROZEN_SHA16, "removed_opt_in_families": list(drop)}
    p = out / "end_config_open.json"
    p.write_text(json.dumps(cfg, indent=1, ensure_ascii=False))
    return p


def end_input(a, names: list[str], rows: dict, hbs: dict, run: Path | None = None) -> Path:
    """The end stage's run directory (default <out>/end_input; a pipelined row has its own): rows/rKK.json, finals.json (every row's
"""
    run = Path(a.out) / "end_input" if run is None else Path(run); (run / "rows").mkdir(parents=True, exist_ok=True)
    work = Path(a.out) / "work"
    finals = {}
    for k, n in enumerate(names):
        (run / "rows" / f"r{k:02d}.json").write_text(json.dumps({"problem": n}))
        b = state_of(work, n).get("best") or {}
        if b.get("proof"):
            finals[n] = {x: b.get(x) for x in ("proof", "score", "tokens", "heartbeats", "L", "H", "Z")}
    (run / "finals.json").write_text(json.dumps(finals, ensure_ascii=False, indent=1))
    (run / "rows.jsonl").write_text("".join(json.dumps(rows[n], ensure_ascii=False) + "\n" for n in names))
    (run / "heartbeats.jsonl").write_text("".join(json.dumps(hbs[n], ensure_ascii=False) + "\n" for n in names))
    return run


def valid_end_record(r: dict) -> bool:
    """An end-stage record that may stand for a polish (review 2026-10-31, the selection lens): its input was really measured


"""
    o = r.get("out"); im = r.get("input_measured")
    return (isinstance(o, dict) and bool(o.get("proof")) and isinstance(im, dict) and im.get("ok") is True
            and isinstance(r.get("delta"), (int, float)) and r["delta"] >= 0 and (r.get("end") or {}).get("stage") != "unmeasured")


class EndPipe:
    """Eager pipelined end stage (--end-pipeline on, docs/open_end_pipeline.md section 4). The agent stage offers every idle row (no session





"""

    def __init__(self, a, rows: dict, hbs: dict, clock: Clock, launcher=None):
        self.a, self.rows, self.hbs, self.clock = a, rows, hbs, clock
        self.out = Path(a.out); self.work = self.out / "work"; self.root = self.out / "end-pipe"
        self.root.mkdir(parents=True, exist_ok=True); (self.out / "logs").mkdir(exist_ok=True)
        self.cfg = None
        self.launcher = launcher or self._run_row
        self.lock = threading.Lock()
        self.q: queue.PriorityQueue = queue.PriorityQueue(); self.seq = itertools.count()
        self.queued: dict = {}                                                                         
        self.running: set = set()                                                                                                
        self.busy: frozenset = frozenset()                                                                     
        self.closed = False
        self.threads = [threading.Thread(target=self._worker, name=f"endpipe{i}", daemon=True)
                        for i in range(max(1, int(getattr(a, "end_pipe_jobs", END_PIPE_JOBS))))]
        for t in self.threads:
            t.start()

    def stop_at(self) -> float:
        """Pipelined jobs live inside the agent stage (review 2026-10-31): they end by the agent deadline + 60 s, so the end stage at the
"""
        return self.clock.agent_deadline + 60.0

    def set_busy(self, rows) -> None:
        self.busy = frozenset(rows)

    def current_sha(self, n: str) -> str | None:
        proof = ((state_of(self.work, n).get("best") or {}).get("proof") or "").strip()
        return proof_sha(proof) if proof else None

    def polished(self, n: str, sha: str) -> bool:
        """A finished VALID polish of this best (valid_end_record)."""
        return any(r.get("problem") == n and valid_end_record(r) for r in read_jsonl_records(self.root / safe(n) / sha / "end" / "report.jsonl"))

    def attempted(self, n: str, sha: str) -> bool:
        """One attempt per (row, best), recorded on disk before launch (it holds over a restart): a polish that ended without a valid
"""
        return (self.root / safe(n) / sha / "attempted").exists()

    def covered(self, n: str) -> bool:
        """The row's CURRENT best has a finished valid polish (a running job does not count: it is stopped at the agent deadline)."""
        sha = self.current_sha(n)
        return bool(sha) and self.polished(n, sha)

    def offer(self, n: str, final: bool = False) -> bool:
        if self.closed:
            return False
        sha = self.current_sha(n)
        if not sha:
            return False
        prio = 0 if final else 1
        with self.lock:
            q = self.queued.get(n)
            if (n, sha) in self.running or (q and q[0] == sha and q[1] <= prio) or self.attempted(n, sha) or self.polished(n, sha):
                return False
            self.queued[n] = (sha, prio)                                                                                        
            self.q.put((prio, next(self.seq), n, sha))
        log(f"end pipeline: {n[:40]} best {sha} queued ({'final' if final else 'idle'})")
        return True

    def _worker(self) -> None:
        while True:
            _, _, n, sha = self.q.get()
            if n is None:
                return
            with self.lock:
                q = self.queued.get(n)
                if not q or q[0] != sha:                                                                                    
                    continue
                del self.queued[n]
                if self.closed or n in self.busy:                                                                    
                    continue
                self.running.add((n, sha))
            try:
                self.launcher(n, sha)
            except Exception as e:                                                               
                log(f"end pipeline: {n[:40]} raised {type(e).__name__}: {e}")
            finally:
                with self.lock:
                    self.running.discard((n, sha))

    def _run_row(self, n: str, sha: str):
        a, clock = self.a, self.clock
        if self.current_sha(n) != sha or self.polished(n, sha) or self.attempted(n, sha):
            return None                                                                              
        seconds = min(float(getattr(a, "end_pipe_row_s", END_PIPE_ROW_S)), clock.agent_deadline - clock.now() - 300.0)
        if seconds < 300:
            log(f"end pipeline: {n[:40]} skipped ({seconds:.0f} s left before the agent deadline)")
            return None
        if self.cfg is None:
            with self.lock:
                if self.cfg is None:
                    self.cfg = package_config(self.out, a.hr)
        d = self.root / safe(n) / sha
        d.mkdir(parents=True, exist_ok=True); (d / "attempted").write_text(time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        run = end_input(a, [n], self.rows, self.hbs, run=d / "input")
        got = (json.loads((run / "finals.json").read_text()).get(n) or {}).get("proof") or ""
        if proof_sha(got.strip()) != sha:
            return None                                                
        env = base_env(a)
        env.update(compile_slots_env(int(getattr(a, "end_pipe_slots", END_PIPE_SLOTS)), d))                                            
        env["LRA_END_STAGE_SECONDS"] = str(int(seconds))
        env["LRA_MEMGATE_RESERVE_MB"] = str(END_PIPE_RESERVE_MB)                                                               
        cmd = ["nice", "-n", str(END_PIPE_NICE), sys.executable, "harness/endstage.py", "--run-dir", str(run), "--rows", str(run / "rows.jsonl"),
               "--heartbeats", str(run / "heartbeats.jsonl"), "--out", str(d / "end"), "--config", str(self.cfg), "--jobs", "1", "--anon"]
        (d / "end").mkdir(parents=True, exist_ok=True)
        t0 = clock.now()
        rc = run_session(cmd, env, self.out / "logs" / f"endpipe.{safe(n)[:50]}.{sha}.log", min(t0 + seconds + 300.0, self.stop_at()),
                         now=clock.now)
        log(f"end pipeline: {n[:40]} best {sha} exit {rc} in {clock.now() - t0:.0f} s ({'valid polish' if self.polished(n, sha) else 'no valid polish: left to the end stage'})")
        return rc

    def close(self) -> None:
        """The agent deadline: no job starts from now; the ones running end by stop_at."""
        self.closed = True

    def join(self) -> None:
        self.closed = True
        for _ in self.threads:
            self.q.put((9, next(self.seq), None, None))
        for t in self.threads:
            t.join()


def end_stage(a, names: list[str], rows: dict, hbs: dict, clock: Clock) -> int | None:
    out = Path(a.out)
    seconds = min(clock.end_seconds, clock.left() - clock.margin - clock.norm_seconds - clock.style_seconds)
    if seconds < 300:
        log(f"end stage skipped: {seconds:.0f} s left before the export margin")
        return None
    run = end_input(a, names, rows, hbs)
    cfg = package_config(out, a.hr)
    slots = a.compile_slots or auto_slots()
    jobs = a.end_jobs or slots
    env = base_env(a)
    env.update(compile_slots_env(slots, out))
    env["LRA_END_STAGE_SECONDS"] = str(int(seconds))
    cmd = [sys.executable, "harness/endstage.py", "--run-dir", str(run), "--rows", str(run / "rows.jsonl"), "--heartbeats",
           str(run / "heartbeats.jsonl"), "--out", str(out / "end"), "--config", str(cfg), "--jobs", str(jobs), "--anon"]
    log(f"end stage: {len(names)} row(s), R5 clock {seconds:.0f} s, {slots} compile slot(s), {jobs} row(s) in flight, config {cfg.name}")
    (out / "end").mkdir(exist_ok=True)
    rc = run_session(cmd, env, out / "logs" / "end.log", clock.job_end - clock.margin - clock.norm_seconds - clock.style_seconds + 300,
                     now=clock.now)
    log(f"end stage exit {rc}")
    return rc


                                                                                                                                        
def end_outputs(out: Path) -> dict:
    """{row: out record} from the end stage's report.jsonl (the last record per row: it survives a stopped end stage), merged over the

"""
    res = {}
    work = out / "work"
    for rowdir in sorted(p for p in (out / "end-pipe").glob("*") if p.is_dir()):
        recs = {}                                                                       
        for rp in rowdir.glob("*/end/report.jsonl"):
            for r in read_jsonl_records(rp):
                if r.get("problem") and valid_end_record(r):
                    recs[rp.parent.parent.name] = (r["problem"], r["out"])
        if not recs:
            continue
        name = next(iter(recs.values()))[0]
        cur = ((state_of(work, name).get("best") or {}).get("proof") or "").strip()
        cur_sha = proof_sha(cur) if cur else None
        if cur_sha in recs:                                                                                                              
            res[name] = recs[cur_sha][1]
    for r in read_jsonl_records(out / "end" / "report.jsonl"):
        if not valid_end_record(r):                                                                                                 
            continue                                                                  
        o = r.get("out")
        if isinstance(o, dict) and o.get("proof") and r.get("problem"):
            res[r["problem"]] = o
    return res


def proof_sha(proof: str) -> str:
    return hashlib.sha256(proof.rstrip().encode()).hexdigest()[:16]


def check_forbidden_ok(proof: str) -> bool:
    from scorer.forbidden import check_forbidden
    return check_forbidden(proof) is None


def export_candidate(row: dict, end_out: dict | None, best: dict | None) -> tuple[str, dict, str]:
    """(source, record, proof) the export picks before the normalize step: the end stage's output when it passed the forbidden-pattern
"""
    from scorer.forbidden import check_forbidden
    cands = [("end", end_out or {}), ("agent", best or {}), ("seed", {"proof": row["src"], "score": 33.33})]
    for src, c in cands:
        proof = (c.get("proof") or "").rstrip()
        if proof and row["statement"].strip() in proof and (src == "seed" or check_forbidden(proof) is None):
            break
    return src, c, proof


def normalize_records(out: Path) -> dict:
    """{(row, input sha): the last normalize.jsonl line for that row and input}."""
    return {(r.get("problem"), r.get("input_sha")): r for r in read_jsonl_records(Path(out) / "normalize.jsonl")}                       


def normalized_choice(row: dict, rec: dict | None) -> str | None:
    """The normalized proof of a normalize.jsonl line when export may take it: status improved, the proof starts with the row's exact
"""
    from scorer.forbidden import check_forbidden
    from scorer.tokenize import split_declaration
    if not rec or rec.get("status") != "improved":
        return None
    proof = (rec.get("proof") or "").rstrip()
    if not proof or split_declaration(proof, row["statement"]) is None or check_forbidden(proof) is not None:
        return None
    return proof


def normalize_cmd(a, name: str, proof_file: Path, record: Path) -> list[str]:
    return [sys.executable, "harness/normalize.py", "--problem", name, "--file", str(proof_file), "--rows", str(Path(a.rows).resolve()),
            "--heartbeats", str(Path(a.heartbeats).resolve()), "--record", str(record)]


def normalize_stage(a, names: list[str], rows: dict, clock: Clock, runner=None) -> dict:
    """The lexer normalizer over every row's export candidate (module docstring, `normalize`). `runner(n, k, proof_file, record, deadline)


"""
    out = Path(a.out); nd = out / "normalize"; nd.mkdir(parents=True, exist_ok=True); (out / "logs").mkdir(exist_ok=True)
    rec_path = out / "normalize.jsonl"; work = out / "work"
    deadline = clock.normalize_deadline
    ends = end_outputs(out); prior = normalize_records(out)
    idx = {n: i for i, n in enumerate(names)}
    todo, reused = [], 0
    for n in names:
        src, _c, proof = export_candidate(rows[n], ends.get(n), state_of(work, n).get("best"))
        h = proof_sha(proof)
        old = prior.get((n, h))
        if old and old.get("status") not in NORMALIZE_RETRY:
            reused += 1
            continue
        todo.append((n, src, proof, h))
    slots = getattr(a, "compile_slots", None) or auto_slots()
    jobs = max(1, min(getattr(a, "end_jobs", None) or slots, slots))
    env = base_env(a)
    lock = threading.Lock()
    counts: dict = {}

    def write(rec: dict) -> None:
        with lock:
            counts[rec["status"]] = counts.get(rec["status"], 0) + 1
            with rec_path.open("a") as fh:
                fh.write(json.dumps(rec, ensure_ascii=False) + "\n")

    def default_runner(n, k, proof_file, record, row_deadline):
        return run_session(normalize_cmd(a, n, proof_file, record), env, out / "logs" / f"normalize.r{k:02d}.log", row_deadline, now=clock.now)
    runner = runner or default_runner

    def one(item) -> None:
        n, src, proof, h = item; k = idx[n]
        base = {"problem": n, "row": k, "source": src, "input_sha": h}
        try:
            one_row(n, k, src, proof, base)
        except Exception as e:                                                                                                       
            log(f"normalize row#{k:02d}: failed ({type(e).__name__}: {e}); the row keeps its previous choice")
            try:
                write(dict(base, status="error", reason=f"{type(e).__name__}: {e}"[:300], t=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())))
            except Exception:                
                pass

    def one_row(n, k, src, proof, base) -> None:
        left = clock.left(deadline)
        if left < NORMALIZE_MIN_START_S:
            write(dict(base, status="skipped", reason=f"{left:.0f} s left before the export margin",
                       t=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())))
            return
        bound = min(float(getattr(a, "normalize_row_seconds", NORMALIZE_ROW_SECONDS)), left)
        pf = nd / f"r{k:02d}.lean"; rf = nd / f"r{k:02d}.json"
        pf.write_text(proof + "\n"); rf.unlink(missing_ok=True)
        t0 = clock.now()
        try:
            rc = runner(n, k, pf, rf, t0 + bound)
        except Exception as e:                                                                           
            rc = -1; log(f"normalize row#{k:02d}: runner raised {type(e).__name__}: {e}")
        secs = clock.now() - t0
        try:
            r = json.loads(rf.read_text())
        except (OSError, ValueError):
            r = None
        if not isinstance(r, dict):                                    
            r = {"status": "stopped" if rc is None else "error"}
        rec = dict(base, status=r.get("status") or "error", rc=rc, seconds=round(secs, 1), bound_s=round(bound, 1),
                   **{x: r[x] for x in ("before", "after", "sites", "applied", "gain", "compiles", "tried") if x in r},
                   t=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        if rec["status"] == "improved":
            rec["proof"] = r.get("proof")
        write(rec)
        log(f"normalize row#{k:02d} ({src}): {rec['status']}" + (f" {rec.get('gain', 0):+.2f} {rec.get('applied')}" if rec["status"] == "improved" else "")
            + f" in {secs:.0f} s")

    room = clock.left(deadline)
    log(f"normalize step: {len(todo)} row(s) to run ({reused} already done), {jobs} at once, {room:.0f} s before the export margin, "
        f"row bound {float(getattr(a, 'normalize_row_seconds', NORMALIZE_ROW_SECONDS)):.0f} s")
    if todo:
        with ThreadPoolExecutor(jobs, thread_name_prefix="opk-norm") as ex:
            list(ex.map(one, todo))
    summ = {"rows": len(names), "run": len(todo), "reused": reused, "statuses": counts, "jobs": jobs,
            "seconds_left_at_start": round(room, 1)}
    log(f"normalize step done: {summ}")
    return summ


                                                                                                                                       
STYLE_RW_FROZEN = ("style_rw_wall_s", "style_rw_max_tokens", "style_rw_effort", "style_rw_exemplars")                             
STYLE_RW_OTHERS_MAX = 50                                                                                      
STYLE_RW_PREFLIGHT = ("harness.style_rw_open", "harness.endstage", "harness.goals", "harness.lean_untrunc", "harness.agent",
                      "harness.hb_tool_eval", "harness.open_config", "llm.openai_compat", "llm.junk", "scorer.compile", "scorer.forbidden",
                      "scorer.tokenize", "probe.verify_candidates")


def style_on(a) -> bool:
    return getattr(a, "style_rw", "off") == "on"


def style_args_check(a) -> str | None:
    """The style flags before anything runs: the refusal text, else None. Off: a style flag away from its default is refused (it would

"""
    if not style_on(a):
        moved = [f for f in STYLE_RW_FLAGS if getattr(a, f, None) is not None
                 and getattr(a, f) != globals()["STYLE_RW_" + f[len("style_rw_"):].upper()]]
        if moved:
            return f"{', '.join('--' + f.replace('_', '-') for f in moved)} given without --style-rw on"
        if getattr(a, "cmd", None) == "style":
            return "the style command needs --style-rw on"
        return None
    w, t, j, mt = float(a.style_rw_wall_s), float(a.style_rw_seconds), int(a.style_rw_jobs), int(a.style_rw_max_tokens)
    if not (math.isfinite(w) and w >= 300):
        return f"--style-rw-wall-s {w:g}: at least 300 s (a call, its candidates and the confirm read)"
    if not (math.isfinite(t) and t >= 0):
        return f"--style-rw-seconds {t:g}: a finite share >= 0"
    if j < 1 or mt < 1000:
        return "--style-rw-jobs >= 1 and --style-rw-max-tokens >= 1000"
    import importlib.util
    missing = []
    for m in STYLE_RW_PREFLIGHT:
        try:
            if importlib.util.find_spec(m) is None:
                missing.append(m)
        except (ImportError, ValueError) as e:
            missing.append(f"{m} ({type(e).__name__})")
    if missing:
        return f"--style-rw on: missing in this tree: {', '.join(missing)}"
    try:
        from harness import style_rw_open as SRW
        SRW.load_exemplars(a.style_rw_exemplars)
    except Exception as e:                
        return f"--style-rw on: the exemplar file is not usable ({type(e).__name__}: {str(e)[:200]})"
    return None


def style_freeze(a, out: Path) -> str | None:
    """<out>/style_rw_config.json: the step's method flags, written by the first call with --style-rw on; a later call with other values
"""
    if not style_on(a):
        return None
    p = Path(out) / "style_rw_config.json"
    cur = {f: getattr(a, f) for f in STYLE_RW_FROZEN}
    if p.exists():
        try:
            prev = json.loads(p.read_text())
        except (OSError, ValueError):
            prev = None
        if isinstance(prev, dict) and prev != cur:
            diff = sorted(k for k in set(prev) | set(cur) if prev.get(k) != cur.get(k))
            return f"{p}: this out directory's style step ran with other values ({', '.join(diff)}); use another --out"
        if isinstance(prev, dict):
            return None
    p.write_text(json.dumps(cur, indent=1))
    return None


def style_inputs(a, names: list[str], rows: dict) -> dict:
    """{row: {"source", "proof", "score"}}: exactly what export would write before the style step (export_candidate, replaced by the
"""
    out = Path(a.out); work = out / "work"; ends = end_outputs(out)
    use_norm = getattr(a, "normalize", True) and (out / "normalize.jsonl").exists()
    norm = normalize_records(out) if use_norm else {}
    res = {}
    for n in names:
        src, c, proof = export_candidate(rows[n], ends.get(n), state_of(work, n).get("best"))
        score = c.get("score")
        nr = norm.get((n, proof_sha(proof)))
        p2 = normalized_choice(rows[n], nr)
        if p2:
            src, proof, score = "normalize", p2, (nr.get("after") or {}).get("score")
        res[n] = {"source": src, "proof": proof, "score": score}
    return res


def style_others(out: Path, name: str) -> list[dict]:
    """The row's other verified proofs with a stored score (the agent best and the agent pool, when the sessions kept one), best first."""
    work = Path(out) / "work"
    cands = []
    b = state_of(work, name).get("best") or {}
    if b.get("proof") and isinstance(b.get("score"), (int, float)):
        cands.append({"proof": b["proof"], "score": float(b["score"])})
    for l in read_jsonl_records(work / safe(name) / "pool.jsonl"):
        if l.get("proof") and isinstance(l.get("score_exact"), (int, float)):
            cands.append({"proof": l["proof"], "score": float(l["score_exact"])})
    cands.sort(key=lambda c: -c["score"])
    return cands[:STYLE_RW_OTHERS_MAX]


def style_cfg(a, out: Path) -> dict:
    """The row processes' fixed arguments: the rows, the model endpoint of the sessions, the step's flags, the package's end config (the
"""
    out = Path(out)
    cfgp = out / "end_config_open.json"
    if not cfgp.exists():
        cfgp = package_config(out, getattr(a, "hr", False))
    ms = out / "end" / "meter.json"
    return {"rows": str(Path(a.rows).resolve()), "heartbeats": str(Path(a.heartbeats).resolve()), "base_url": a.base_url,
            "api_model": a.api_model or a.model, "api_key_file": a.api_key_file, "effort": a.style_rw_effort,
            "max_tokens": int(a.style_rw_max_tokens), "exemplars": a.style_rw_exemplars, "end_config": str(cfgp),
            "meter_state": str(ms) if ms.exists() else None}


def style_stage(a, names: list[str], rows: dict, clock: Clock, runner=None) -> dict:
    """The style step (module docstring, `style`) over every row's current pick, until the clock's style deadline (the export margin)."""
    from harness import style_rw_open as SRW
    out = Path(a.out)
    slots = getattr(a, "compile_slots", None) or auto_slots()
    env = base_env(a)
    env.update(compile_slots_env(slots, out))
    return SRW.run_stage(names, rows, style_inputs(a, names, rows), style_cfg(a, out), out, clock.style_deadline,
                         max(1, int(a.style_rw_jobs)), env, runner=runner, now=clock.now, log=log, wall_s=float(a.style_rw_wall_s),
                         others={n: style_others(out, n) for n in names})


def audit_proof(row: dict, proof: str, versions: list[str], seed_sorry: dict, audit=None, timeout: int = AUDIT_TIMEOUT_S,
                deadline: float | None = None) -> tuple[str, str]:
    """(clean | sorry | unknown | skipped, why) of one proof on every pin (section S): `sorry` when Lean's sorry message appears with


"""
    from scorer.compile import audit_axioms

    def tmo() -> int:
        return int(timeout if deadline is None else max(1, min(timeout, deadline - time.time())))
    aud = audit or (lambda r, p, v: audit_axioms(r, p, v, timeout=tmo()))
    if not versions:
        return "unknown", "the row lists no pin"
    unknown, skipped = [], []
    for v in versions:
        if deadline is not None and deadline - time.time() < AUDIT_MIN_PIN_S:
            unknown.append(f"{v}: the audit deadline was reached"); continue
        try:
            a = aud(row, proof, v)
        except Exception as e:                
            unknown.append(f"{v}: {type(e).__name__}: {str(e)[:80]}"); continue
        c = getattr(a, "compile", None)
        if getattr(a, "switch", False) or getattr(a, "sorry_warning", False):
            return "sorry", f"axiom audit on {v}: the declaration uses sorry (warn.sorry forced on)"
        if c is not None and getattr(c, "timed_out", False):
            unknown.append(f"{v}: the audit compile timed out"); continue
        axs = getattr(a, "axioms", None)
        if axs is not None and "sorryAx" in axs:
            if v not in seed_sorry:
                try:
                    sa = aud(row, row["src"], v)
                    seed_sorry[v] = None if getattr(sa, "axioms", None) is None else ("sorryAx" in sa.axioms or bool(getattr(sa, "sorry_warning", False)))
                except Exception:                
                    seed_sorry[v] = None
            if seed_sorry[v] is False:
                return "sorry", f"axiom audit on {v}: depends on sorryAx (the row's seed does not)"
            if not seed_sorry[v]:
                unknown.append(f"{v}: sorryAx without a sorry message and no seed verdict")
            continue
        if getattr(a, "decl_errors", None):
            unknown.append(f"{v}: the audit compile reports errors"); continue
        if getattr(a, "skipped", None):
            skipped.append(v); continue
        if axs is None:
            unknown.append(f"{v}: no #print axioms output"); continue
    if unknown:
        return "unknown", "; ".join(unknown)[:200]
    if skipped:
        return "skipped", f"sorry message check only on {', '.join(skipped)}; no sorry"
    return "clean", f"no sorry on {len(versions)} pin(s)"


def audit_export(row: dict, cands: list, audit=None, timeout: int = AUDIT_TIMEOUT_S, deadline: float | None = None) -> tuple[int, dict]:
    """Section S: index of the first candidate (in order) whose audit is not `sorry`, plus {"audit": status of the chosen one, "why",
"""
    from probe.verify_candidates import newest_first
    versions = newest_first(row["version_info"])
    seed_sorry: dict = {}; flagged = []
    for i, (src, proof) in enumerate(cands):
        if i == len(cands) - 1:
            st, why = "seed", "the row's seed is never passed over"
            if proof.rstrip() != (row["src"] or "").rstrip():
                st, why = audit_proof(row, proof, versions, seed_sorry, audit, timeout, deadline=deadline)
                if st == "sorry":
                    st, why = "unknown", "last candidate flagged; kept (" + why + ")"
            return i, {"audit": st, "why": why, "fallback": len(flagged), "flagged": flagged}
        st, why = audit_proof(row, proof, versions, seed_sorry, audit, timeout, deadline=deadline)
        if st != "sorry":
            return i, {"audit": st, "why": why, "fallback": len(flagged), "flagged": flagged}
        flagged.append(src)
        log(f"export: {safe(row['name'])[:40]}: {src} proof passed over: {why}")
    return len(cands) - 1, {"audit": "seed", "why": "all flagged", "fallback": len(flagged), "flagged": flagged}


def sorry_blind(row: dict) -> bool:
    """A pin of the row turns Lean's sorry warning off in its lakefile (PhysLib): the rows the hot path needs the guard for, audited
"""
    try:
        from scorer import compile as C
        from probe.verify_candidates import newest_first
        return row["source"] != "putnambench" and any(C._warn_sorry_off(C.lakefile_options(row["source"], v))
                                                      for v in newest_first(row["version_info"]))
    except Exception:                
        return False


def write_proofs(out: Path, recs: list) -> None:
    """proofs.jsonl written whole and renamed into place: a reader (or a stop mid-write) never sees a torn file."""
    tmp = out / "proofs.jsonl.tmp"
    tmp.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in recs))
    os.replace(tmp, out / "proofs.jsonl")


def export(a, names: list[str], rows: dict, deadline: float | None = None) -> dict:
    """proofs.jsonl + summary.json. Section S: the picks are written first, before the axiom audit (a stop during the audit leaves the


"""
    out = Path(a.out); work = out / "work"
    ends = end_outputs(out)
    use_norm = getattr(a, "normalize", True) and (out / "normalize.jsonl").exists()
    norm = normalize_records(out) if use_norm else {}
    recs, sources = [], {"end": 0, "agent": 0, "seed": 0}
    if use_norm:
        sources["normalize"] = 0
    taken_from: dict = {}; gain_sum = 0.0
    use_style = style_on(a) and (out / "style_rw.jsonl").exists()
    SRW = None
    if use_style:
        from harness import style_rw_open as SRW
    srecs = SRW.read_records(out / "style_rw.jsonl") if use_style else {}
    if use_style:
        sources["style_rw"] = 0
    pre_style: dict = {}; style_taken: dict = {}; style_gain = 0.0
    do_audit = getattr(a, "audit", True)
    audit_counts: dict = {}; audit_fallbacks = 0
    for n in names:
        row = rows[n]
        src, c, proof = export_candidate(row, ends.get(n), state_of(work, n).get("best"))
        rec = {"name": n, "proof": proof + "\n", "source": src, "stored_score": c.get("score"), "tokens": c.get("tokens"),
               "heartbeats": c.get("heartbeats")}
        nr = norm.get((n, proof_sha(proof)))
        p2 = normalized_choice(row, nr)
        if p2:
            after = nr.get("after") or {}
            rec.update(proof=p2 + "\n", source="normalize", normalized_from=src, stored_score=after.get("score"),
                       tokens=after.get("tokens"), heartbeats=after.get("heartbeats"), normalize_gain=nr.get("gain"))
            taken_from[src] = taken_from.get(src, 0) + 1; gain_sum += float(nr.get("gain") or 0)
        if use_style:                                                                                                                   
            pre = rec["proof"].rstrip()
            sr = srecs.get((n, SRW.sha16(pre)))
            p3 = SRW.choice(row, sr, pre)
            if p3:
                pre_style[len(recs)] = dict(rec)
                aft, st0 = sr.get("after") or {}, rec.get("stored_score")
                rec = dict(rec, proof=p3 + "\n", source="style_rw", style_from=rec["source"], tokens=aft.get("tokens"),
                           heartbeats=aft.get("heartbeats"), style_gain=sr.get("gain"),
                           stored_score=round(float(st0) + float(sr["gain"]), 4) if isinstance(st0, (int, float)) else aft.get("score_exact"))
                style_taken[rec["style_from"]] = style_taken.get(rec["style_from"], 0) + 1; style_gain += float(sr.get("gain") or 0)
        recs.append(rec)
    t_audit = time.time(); jobs = 0
    if do_audit:
        write_proofs(out, recs)                                                                                             

        def one(k: int):                                                                                            
            rec = recs[k]; n = rec["name"]; row = rows[n]
            cands, best = [(rec["source"], rec["proof"].rstrip())], {}
            if k in pre_style:                                                           
                cands.append((pre_style[k]["source"], pre_style[k]["proof"].rstrip()))
            try:
                best = state_of(work, n).get("best") or {}
                for s2, pr in (("end", ((ends.get(n) or {}).get("proof") or "")), ("agent", best.get("proof") or ""), ("seed", row["src"])):
                    pr = (pr or "").rstrip()                                                                                       
                    if pr and all(pr != q for _, q in cands) and (s2 == "seed" or (row["statement"].strip() in pr and check_forbidden_ok(pr))):
                        cands.append((s2, pr))
                if deadline is not None and deadline - time.time() < AUDIT_MIN_PIN_S:
                    return k, cands, best, 0, {"audit": "unaudited", "why": "the audit deadline was reached before this row", "fallback": 0,
                                               "flagged": []}
                i, info = audit_export(row, cands, deadline=deadline)
            except Exception as e:                                                                     
                i, info = 0, {"audit": "unknown", "why": f"audit error {type(e).__name__}: {str(e)[:80]}", "fallback": 0, "flagged": []}
            return k, cands, best, i, info

        try:
            order = sorted(range(len(recs)), key=lambda k: not sorry_blind(rows[recs[k]["name"]]))
            jobs = max(1, min(AUDIT_JOBS, getattr(a, "compile_slots", None) or auto_slots()))
            with ThreadPoolExecutor(jobs, thread_name_prefix="opk-audit") as ex:
                done = sorted(ex.map(one, order), key=lambda x: x[0])
        except Exception as e:                                                                               
            log(f"export: the audit failed ({type(e).__name__}: {e}); every pick kept")
            done = [(k, [], {}, 0, {"audit": "unknown", "why": f"audit error {type(e).__name__}", "fallback": 0, "flagged": []})
                    for k in range(len(recs))]
        for k, cands, best, i, info in done:
            rec = recs[k]; n = rec["name"]
            if i > 0:
                s2, pr = cands[i]
                base = rec
                if rec["source"] == "style_rw":                                                                      
                    f = rec.get("style_from")
                    style_taken[f] = style_taken.get(f, 0) - 1; style_gain -= float(rec.get("style_gain") or 0)
                    if not style_taken[f]:
                        del style_taken[f]
                    base = pre_style.get(k) or {}
                if base is not rec and base and pr == base["proof"].rstrip():                                            
                    rec = recs[k] = dict(base, audit_passed_over=info["flagged"])
                else:
                    if base.get("source") == "normalize":                                                                    
                        f = base.get("normalized_from")
                        taken_from[f] = taken_from.get(f, 0) - 1; gain_sum -= float(base.get("normalize_gain") or 0)
                        if not taken_from[f]:
                            del taken_from[f]
                    sc = {"end": (ends.get(n) or {}), "agent": best, "seed": {"score": 33.33}}.get(s2, {})
                    rec = recs[k] = {"name": n, "proof": pr + "\n", "source": s2, "stored_score": sc.get("score"), "tokens": sc.get("tokens"),
                                     "heartbeats": sc.get("heartbeats"), "audit_passed_over": info["flagged"]}
                audit_fallbacks += 1
            rec["audit"] = info["audit"]
            audit_counts[info["audit"]] = audit_counts.get(info["audit"], 0) + 1
    for rec in recs:
        sources[rec["source"]] = sources.get(rec["source"], 0) + 1
    write_proofs(out, recs)
    sc = [float(r["stored_score"]) for r in recs if r["stored_score"] is not None]
    summ = {"rows": len(recs), "sources": sources, "stored_mean": round(statistics.mean(sc), 4) if sc else None,
            "at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    if use_norm:
        summ["normalize"] = {"taken": sum(taken_from.values()), "taken_from": taken_from, "gain_sum": round(gain_sum, 2)}
    if use_style:
        summ["style_rw"] = {"taken": sum(style_taken.values()), "taken_from": style_taken, "gain_sum": round(style_gain, 4)}
    if do_audit:
        summ["audit"] = {"counts": audit_counts, "fallbacks": audit_fallbacks, "guard_env": SORRY_GUARD_ENV, "jobs": jobs,
                         "seconds": round(time.time() - t_audit, 1)}
    (out / "summary.json").write_text(json.dumps(summ, indent=1))
    log(f"export: {out / 'proofs.jsonl'}: {summ}")
    return summ


                                                                                                                                       
TOKEN_REPORT_JOIN_S = 600                                                                                       


def start_token_report(out: Path) -> threading.Thread:
    """P4 (audit section P): <out>/token_report.json ($0, measurement only), in a daemon thread started after the agent stage. Review


"""
    def work() -> None:
        try:
            from harness import open_token_report as _otr
            rep_ = _otr.report_for_out(out, RUNS)
            tmp = out / "token_report.json.tmp"
            tmp.write_text(json.dumps(rep_, indent=1)); os.replace(tmp, out / "token_report.json")
            log("token report: " + _otr.one_line(rep_))
        except Exception as e:                
            log(f"token report not written ({type(e).__name__}: {e})")
    t = threading.Thread(target=work, name="opk-token-report", daemon=True)
    t.start()
    return t


def finish_token_report(t: threading.Thread | None, clock: Clock) -> None:
    """After the export: wait for the token report at most TOKEN_REPORT_JOIN_S, and never past a minute before the job end."""
    if t is None:
        return
    t.join(timeout=max(0.1, min(TOKEN_REPORT_JOIN_S, clock.left() - 60)))
    if t.is_alive():
        log("token report not finished: not waited for (measurement only)")


                                                                                                                                     
def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("cmd", choices=["run", "agent", "end", "normalize", "export", "style"])
    ap.add_argument("--rows", required=True, help="the benchmark rows (JSONL, the warm-up file's fields)")
    ap.add_argument("--heartbeats", required=True, help="their reference heartbeats (JSONL: name, heartbeat)")
    ap.add_argument("--problems", nargs="*", help="restrict to these rows")
    ap.add_argument("--out", required=True, help="output directory (work roots, logs, end stage, proofs.jsonl)")
    ap.add_argument("--tag", default="opk", help="run id prefix")
    ap.add_argument("--base-url", default="http://127.0.0.1:8000/v1")
    ap.add_argument("--api-key-file", default=None)
    ap.add_argument("--model", default="glm-5.3-flash")
    ap.add_argument("--api-model", default=None, help="the served model name (default --model)")
    ap.add_argument("--serving-tag", default="vllm-a100-awq-w4a16")
    ap.add_argument("--reasoning-effort", default="default", help="the model template's default (GLM: max); A100 rehearsal 2026-10-30: session 1 on the warm-up rows +8.6 over low effort")
    ap.add_argument("--turns", type=int, default=60)                                              
    ap.add_argument("--max-tokens", type=int, default=6000)                         
    ap.add_argument("--max-api-retries", type=int, default=20, help="per call (20 ~ 1.5 h of server outage)")
    ap.add_argument("--no-adaptive-turns", dest="adaptive_turns", action="store_false", default=True)
    ap.add_argument("--low-turns", type=int, default=LOW_TURNS, help="agent.py --adaptive-low-turns: the turn budget of a session that starts "
                    "below 45 (2026-10-30: 90; agent.py's own default, 60, was the cap 3 of 3 sessions of the one long row ended on)")
    ap.add_argument("--agent-arg", action="append", help="extra agent.py arguments (repeatable)")
    ap.add_argument("--workers", type=int, default=8, help="sessions at once (2026-10-30: 8 streams with prefix caching on and MTP off serve 194 tok/s vs 78 on the old recipe; see docs/a100_throughput_60.md)")
    ap.add_argument("--max-sessions", type=int, default=12, help="sessions per row")
    ap.add_argument("--min-session-seconds", type=float, default=900, help="no session starts with less agent time left")
    ap.add_argument("--job-seconds", type=float, default=48 * 3600)
    ap.add_argument("--started-at", type=float, default=None, help="job start (epoch seconds; default now): setup time counts")
    ap.add_argument("--end-seconds", type=float, default=4 * 3600, help="the end stage's share of the job (R5 clock)")
    ap.add_argument("--export-margin", type=float, default=EXPORT_MARGIN_S)
    ap.add_argument("--compile-slots", type=int, default=None, help="end stage compile slots (default auto_slots())")
    ap.add_argument("--end-jobs", type=int, default=None, help="end stage rows in flight (default = compile slots)")
    ap.add_argument("--end-pipeline", choices=("off", "on"), default="off",
                    help="docs/open_end_pipeline.md: end-stage each row as soon as it can get no more agent session (during the agent stage); "
                         "the end stage at the agent deadline then covers only the rows not yet handed over")
    ap.add_argument("--end-pipe-jobs", type=int, default=END_PIPE_JOBS, help="pipelined end-stage rows at once during the agent stage")
    ap.add_argument("--end-pipe-row-s", type=float, default=END_PIPE_ROW_S, help="one pipelined row's end-stage clock (R5 seconds)")
    ap.add_argument("--end-pipe-slots", type=int, default=END_PIPE_SLOTS, help="compile slots of the pipelined end stage (its own pool)")
    ap.add_argument("--blind-start", choices=("off", "on"), default="off",
                    help="2026-10-31 (operator; docs/open_blind_start.md): each row's FIRST session (the --fresh one) starts blind: the statement "
                         "with a `sorry` body and a facts sheet of the reference (names and numbers, no proof text); the reference stays the banked "
                         "best and is shown after a third of the session's turns if nothing of the session's own is banked; later sessions unchanged")
    ap.add_argument("--hr", action="store_true", help="also run the opt-in family hr")
    ap.add_argument("--no-normalize", dest="normalize", action="store_false", default=True,
                    help="no lexer-normalizer step after the end stage (and no time reserved for it); export ignores normalize.jsonl")
    ap.add_argument("--normalize-seconds", type=float, default=NORMALIZE_SECONDS,
                    help="the normalize step's share of the job, reserved after the end stage (the agent deadline moves earlier by it)")
    ap.add_argument("--normalize-row-seconds", type=float, default=NORMALIZE_ROW_SECONDS, help="wall bound of one row's normalize step")
    ap.add_argument("--keep-local-ref", action="store_true", help="keep the local reference-heartbeat table (dev rows only)")
                                                                                        
    ap.add_argument("--no-compact-tool-json", dest="compact_tool_json", action="store_false", default=True,
                    help="P1 off: tool results as spaced, \\u-escaped JSON as before (default: agent.py --compact-tool-json)")
    ap.add_argument("--no-skeleton-combinator-holes", dest="skeleton_combinator_holes", action="store_false", default=True,
                    help="P2 off: lean_skeleton's default hole reading (default: agent.py --skeleton-combinator-holes)")
    ap.add_argument("--connect-budget-seconds", type=float, default=CONNECT_BUDGET_S,
                    help="P3: per model call, how long a refused / failed connection waits for the server without using an attempt")
    ap.add_argument("--no-audit", dest="audit", action="store_false", default=True,
                    help="section S off: no axiom audit at export (the guard env stays); default: every row's proof audited on every pin")
                                                                                
    ap.add_argument("--style-rw", choices=("off", "on"), default="off",
                    help="the accept-only style rewrite after the normalize step, with the package's own model (default off)")
    ap.add_argument("--style-rw-seconds", type=float, default=STYLE_RW_SECONDS,
                    help="the step's share of the job, reserved before the end stage (the agent deadline moves earlier by it)")
    ap.add_argument("--style-rw-wall-s", type=float, default=STYLE_RW_WALL_S, help="the hard wall per row (frozen per out directory)")
    ap.add_argument("--style-rw-jobs", type=int, default=STYLE_RW_JOBS, help="rows at once")
    ap.add_argument("--style-rw-max-tokens", type=int, default=STYLE_RW_MAX_TOKENS, help="max_tokens per call (frozen)")
    ap.add_argument("--style-rw-effort", default=STYLE_RW_EFFORT, choices=("default", "low", "high", "max"),
                    help="the step's calls: default = thinking off (enable_thinking false); low / high / max = thinking on with that reasoning_effort (frozen)")
    ap.add_argument("--style-rw-exemplars", default=STYLE_RW_EXEMPLARS,
                    help="sha16 of harness/style_rw_open_exemplars.json (frozen; the step refuses to start on another file)")
    ap.add_argument("--schedule", choices=SCHEDULES, default=DEFAULT_SCHEDULE,
                    help="P5: agent-stage order after every row's first session: room (default: most (100 - best) / (sessions + 1) first, "
                         "x0.3 after 3 flat sessions in a row) or ladder (fewest sessions, then row order; the order before 2026-10-28)")
    return ap


def main(argv=None) -> int:
    os.environ.update(SORRY_GUARD_ENV)                                                                                          
    a = build_parser().parse_args(argv)
    if a.compile_slots is not None and a.compile_slots < 1:
        raise SystemExit("--compile-slots must be >= 1")
    if a.cmd == "normalize" and not a.normalize:
        raise SystemExit("normalize with --no-normalize")
    bad = style_args_check(a)                                                    
    if bad:
        raise SystemExit(bad)
    names, rows, hbs = load_rows(a.rows, a.heartbeats)
    if a.problems:
        unknown = [p for p in a.problems if p not in rows]
        if unknown:
            raise SystemExit(f"--problems: not in the rows file: {unknown}")
        names = [n for n in names if n in set(a.problems)]
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); (out / "logs").mkdir(exist_ok=True)
    clk_p = out / "clock.json"
    if a.started_at is None and clk_p.exists():                                           
        a.started_at = json.loads(clk_p.read_text())["started_at"]
    a.started_at = time.time() if a.started_at is None else a.started_at
    norm_s = a.normalize_seconds if a.normalize else 0.0
    style_s = float(a.style_rw_seconds) if style_on(a) else 0.0
    bad = style_freeze(a, out)
    if bad:
        raise SystemExit(bad)
    clk_p.write_text(json.dumps({"started_at": a.started_at, "job_seconds": a.job_seconds, "end_seconds": a.end_seconds,
                                 "normalize_seconds": norm_s, **({"style_rw_seconds": style_s} if style_on(a) else {})}))
    clock = Clock(a.started_at, a.job_seconds, a.end_seconds, a.export_margin, norm_seconds=norm_s, style_seconds=style_s)
    log(f"open package {a.cmd}: {len(names)} row(s), job end in {clock.left() / 3600:.2f} h, out {out}")
    rep_t = None
    pipe = EndPipe(a, rows, hbs, clock) if a.cmd == "run" and getattr(a, "end_pipeline", "off") == "on" else None
    if a.cmd in ("run", "agent"):
                                                                                                            
        res = agent_stage(a, names, clock, on_idle=pipe.offer, set_busy=pipe.set_busy) if pipe else agent_stage(a, names, clock)
        (out / "agent_stage.json").write_text(json.dumps(res, indent=1, ensure_ascii=False))
        sp = out / "agent_sessions.jsonl"
        aud = audit_trajectories([l["run_id"] for l in read_jsonl(sp)] if sp.exists() else [])
        (out / "prompt_audit.json").write_text(json.dumps(aud, indent=1))
        log(f"prompt audit: {aud['user_messages']} harness message(s) in {aud['trajectory_files']} trajectory file(s), {aud['n_hits']} banned phrase(s)")
        rep_t = start_token_report(out)                                                                                                   
    if a.cmd in ("run", "end"):
        if pipe:
                                                                                                                                     
                                                                                                                                        
                                                                                                              
            pipe.join()
        left = [n for n in names if not (pipe and pipe.covered(n))]
        if pipe:
            log(f"end pipeline: the current best of {len(names) - len(left)} row(s) polished (or being polished) during the agent stage; "
                f"the end stage takes the other {len(left)}")
        if left:
            end_stage(a, left, rows, hbs, clock)
    if a.cmd in ("run", "end", "normalize") and a.normalize:                                                        
        try:                                                                                                      
            res = normalize_stage(a, names, rows, clock)
        except Exception as e:                
            log(f"normalize step failed ({type(e).__name__}: {e}); export takes only the rows it recorded as improved")
            res = {"error": f"{type(e).__name__}: {e}"[:500]}
        try:
            (out / "normalize_stage.json").write_text(json.dumps(res, indent=1))
        except OSError as e:
            log(f"normalize_stage.json not written: {e}")
    if a.cmd in ("run", "end", "normalize", "style") and style_on(a):                                                              
        try:
            res = style_stage(a, names, rows, clock)
        except Exception as e:                
            log(f"style step failed ({type(e).__name__}: {e}); export takes only the rows it recorded as improved")
            res = {"error": f"{type(e).__name__}: {e}"[:500]}
        try:
            (out / "style_rw_stage.json").write_text(json.dumps(res, indent=1))
        except OSError as e:
            log(f"style_rw_stage.json not written: {e}")
    if a.cmd in ("run", "end", "normalize", "export", "style"):                                                                            
        export(a, names, rows, deadline=max(clock.job_end - AUDIT_WRITE_S, time.time() + AUDIT_MIN_S))
    finish_token_report(rep_t, clock)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
