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
                                                                                                                                          
                                                                                                                                           
                                                                                                                                         
                                                                                                                                           
                                                                                                                                 
                                                                                                                        
                                                                                 
                                                                                                                                       
                                                                                                                                     
                                                                                                                                         
END_PIPE_R10 = "on"
END_PIPE_R10_CONFIG = ROOT / "probe/open_package/end_r10.json"
END_PIPE_R10_SHA16 = "9ddb2a6cf3e791e5"                                                                                 
END_PIPE_R10_JOBS = 3                                                                                           
END_PIPE_R10_SLOTS = 1                                                                                                            
END_PIPE_R10_ROW_S = 7200.0                                                                                                
END_PIPE_R10_SHARE1 = 0.6
END_PIPE_R10_PHASE = 0.4                                                                                                                        
END_PIPE_R10_MIN_S = 600.0                                                        
END_PIPE_R10_ALTS = 5                                                                                                                  
R10_ROUNDS = ("r10", "r10b")
                                                                                                                                         
                                                                                                                                         
                                                                                                                                            
DIALECT_STAGE = "dial"
DEFAULT_DIALECT = "on"                                                                                                          
DIALECT_ROW_SECONDS = 600.0                                                                                                                 
DIALECT_MARGIN_S = 300.0                                                                                                         
DIALECT_MIN_S = 180.0                                                                            
DIALECT_SLOTS = 1                                                                                                     
DIALECT_SECONDS = 900.0                                                                                                                       
                                                                                                                                                 
PIPE_STAGES = ("end",) + R10_ROUNDS + (DIALECT_STAGE,)                                                                                               
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


def git_trust(env) -> None:
    """rc3 (2026-11-01, rc2's box smoke): Lake runs git inside the env checkouts (.lake/packages/*), and git refuses a repository owned by


"""
    n = int(env.get("GIT_CONFIG_COUNT") or 0)
    if any(env.get(f"GIT_CONFIG_KEY_{i}") == "safe.directory" and env.get(f"GIT_CONFIG_VALUE_{i}") == "*" for i in range(n)):
        return
    env[f"GIT_CONFIG_KEY_{n}"] = "safe.directory"; env[f"GIT_CONFIG_VALUE_{n}"] = "*"; env["GIT_CONFIG_COUNT"] = str(n + 1)
AUDIT_TIMEOUT_S = 600                                                        
AUDIT_WRITE_S = 60                                                                                                                      
AUDIT_MIN_S = 120                                                                                                         
AUDIT_MIN_PIN_S = 5                                                                                        
AUDIT_JOBS = 4                                                                                                                        
                                                                                            
DEFAULT_SCHEDULE = "room"
                                                                                                                                           
                                                                                                                                         
                                                                                                                                          
                                                              
LOW_TURNS = 90
                                                                                                                                           
                                                                                                                                      
                                                                                                                                          
                                                                                                                                                
                                                                                                                               
                                                                                                                                          
                                                                                                                                              
                                                                                                                                         
                                                                                                                                            
                                                                                                                                        
DEFAULT_WORKERS = 11
DEFAULT_SESSION_MAX_CONTEXT = 200_000
DEFAULT_FIRST_WAVE_STAGGER = 120.0
DEFAULT_MAX_SESSIONS = 12
DEFAULT_END_SECONDS = 7200.0
DEFAULT_END_PIPELINE = "on"
                                                                                                                                               
                                                                                                                                             
                                                                                                    
DEFAULT_END_PIPE_WRITEBACK = "on"
WRITEBACK_EPS = 0.005
                                                                                                                                 
                                                                                                                                          
                                                                                                                                         
                                                                                                                                           
                                                                                                                                         
                                                                                                                         
                                                                                                                 
AUTO_CARD = ROOT / "harness/open_card_automation.md"
AUTO_CARD_SHA16 = "5d1b11bd2e6c6db4"
DEFAULT_AUTO_CARD = "off"
DEFAULT_AUTO_CARD_MIN_REF_TOKENS = 0
                                                                                                                                       
                                                                                                                                        
                                                                                                                         
                                                                                                                                       
                                                    
DEFAULT_FUNIND = "on"
METHOD_FLAGS = ("end_pipe_writeback", "automation_card", "automation_card_min_ref_tokens", "funind")                                                       
                                                                                                                                       
                                                                                                     
METHOD_FLAGS_ADDED_OFF = {"automation_card": "off", "automation_card_min_ref_tokens": 0, "automation_card_sha16": None, "funind": "off"}
                                                                                                                                      
                                                                                                                                      
                                                                                                                                          
                                                                                
METHOD_FLAGS_RETIRED_OFF = ("off", None)
                                                                                                                                       
                                                                                                                                        
                                                                                                                                             
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
                 norm_seconds: float = 0.0, dial_seconds: float = 0.0):
        self.t0, self.job_end, self.now = float(started_at), float(started_at) + float(job_seconds), now
        self.end_seconds, self.margin, self.norm_seconds = float(end_seconds), float(export_margin), float(norm_seconds)
        self.dial_seconds = max(0.0, min(float(dial_seconds), self.end_seconds))

    @property
    def agent_deadline(self) -> float:
        return self.job_end - self.end_seconds - self.norm_seconds - self.margin

    @property
    def dialect_deadline(self) -> float:
        """The end of the end stage's window (before rc2: the end stage's stop): the dialect step's stop; normalize starts here."""
        return self.job_end - self.margin - self.norm_seconds

    @property
    def end_stop(self) -> float:
        """The end stage's stop: its window less the dialect step's reserved share (rc2 adjustment (3))."""
        return self.dialect_deadline - self.dial_seconds

    @property
    def normalize_deadline(self) -> float:
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
    git_trust(env)                                                                 
    return env


                                                                                                                                       
def state_of(work: Path, name: str) -> dict:
    try:
        return json.loads((work / safe(name) / "state.json").read_text())
    except (OSError, ValueError):
        return {}


def best_score(work: Path, name: str) -> float:
    return float(((state_of(work, name).get("best") or {}).get("score")) or 33.33)


def automation_card_for(a, name: str) -> bool:
    """--automation-card on and row `name`'s reference proof_length >= --automation-card-min-ref-tokens (0: every row). The lengths are the

"""
    if getattr(a, "automation_card", DEFAULT_AUTO_CARD) != "on":
        return False
    need = int(getattr(a, "automation_card_min_ref_tokens", DEFAULT_AUTO_CARD_MIN_REF_TOKENS) or 0)
    if need <= 0:
        return True
    have = (getattr(a, "ref_tokens", None) or {}).get(name)
    return have is not None and int(have) >= need


def session_cmd(a, name: str, run_id: str, fresh: bool) -> list[str]:
    cmd = [sys.executable, "harness/agent.py", "--open-package", "--endpoint", "openai", "--base-url", a.base_url, "--model", a.model,
           "--api-model", a.api_model or a.model, "--serving-tag", a.serving_tag, "--problems", name, "--workers", "1",
           "--turns", str(a.turns), "--max-tokens", str(a.max_tokens), "--reasoning-effort", a.reasoning_effort,
           "--work-root", str(Path(a.out).resolve() / "work"), "--run-id", run_id, "--rows", str(Path(a.rows).resolve()),
           "--heartbeats", str(Path(a.heartbeats).resolve()), "--max-api-retries", str(a.max_api_retries)]
    if fresh:
        cmd.append("--fresh")
    if a.api_key_file:
        cmd += ["--api-key-file", a.api_key_file]
    if not a.adaptive_turns:
        cmd.append("--no-adaptive-turns")
    cmd += ["--adaptive-low-turns", str(int(getattr(a, "low_turns", LOW_TURNS)))]                                                           
    if getattr(a, "compact_tool_json", True):                                                                     
        cmd.append("--compact-tool-json")
    if getattr(a, "skeleton_combinator_holes", True):                                                                            
        cmd.append("--skeleton-combinator-holes")
    if automation_card_for(a, name):                                                                                            
        cmd += ["--open-card", str(AUTO_CARD)]
    if getattr(a, "kv_shed", "off") == "on":                                                                                                
        cmd += ["--stop-file", str(shed_stop_path(a.out, run_id))]
    if int(getattr(a, "session_max_context", 0) or 0) > 0:                                                               
        cmd += ["--max-context-tokens", str(int(a.session_max_context))]
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


def run_session(cmd: list[str], env: dict, log_path: Path, deadline: float, now=time.time, why: str = "job deadline") -> int | None:
    """One agent.py (end stage, normalize.py) process; stopped at `deadline` (SIGTERM, then SIGKILL after STOP_GRACE_S). Returns its exit

"""
    tag = f"{os.getpid()}-{time.time_ns()}-{threading.get_ident()}"
    with open(log_path, "a") as fh:
        fh.write(f"[open_package] command: {shlex.join(map(str, cmd))}\n"); fh.flush()                                                 
        p = subprocess.Popen(cmd, cwd=ROOT, env=dict(env, **{REAP_ENV: tag}), stdout=fh, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            return _wait_session(p, fh, deadline, now, why)
        finally:
            left = reap_tagged(tag)
            if left:
                fh.write(f"\n[open_package] {len(left)} process(es) left behind by the session killed: {left[:20]}\n"); fh.flush()


def _wait_session(p, fh, deadline: float, now, why: str = "job deadline") -> int | None:
    """run_session's wait: the exit code, or None once stopped at `deadline` (SIGTERM, then SIGKILL)."""
    while True:
        try:
            return p.wait(timeout=max(1.0, min(POLL_S, deadline - now())))
        except subprocess.TimeoutExpired:
            if now() < deadline:
                continue
        fh.write(f"\n[open_package] {why}: stopping the session\n"); fh.flush()
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


                                                                                                                                       
                                                                                                                                         
                                                                                                                                  
                                                                                                                                         
                                                                                                                                         
                                                                                                                                      
                                                                                                                                          
                                                                                                                                         
                                                                                                                                       
                                                                                                                                   
                                                                                                                                         
                                                                                                                                       
                                                                                                                                    
                                                                                    
KV_GUARD_HOLD = 0.90                                                        
KV_GUARD_RELEASE = 0.85                                                                                                  
KV_GUARD_PREEMPT_S = 180.0                                                                                
KV_GUARD_RECHECK_S = 20.0                                                                                                               
KV_GUARD_STALE_S = 60.0                                                                                                                          
KV_GUARD_FLOOR_GAP = 4                                                                                                      
KV_GUARD_MAX_HOLD_S = 1800.0                                                                                        
KV_GUARD_TIMEOUT_S = 5.0                                                                                                        
                                                                                                                                       
                                                                                                                                       
                                                                                                                          
KV_GUARD_MAX_BYTES = 8 << 20                                                                               
KV_GUARD_NOTE_S = 600.0                                                   
KV_GUARD_SAY_S = 1800.0                                                                                               
KV_GUARD_LOG = "kv_guard.jsonl"
DEFAULT_KV_GUARD = "on"
_VLLM_METRIC = re.compile(r"^vllm:(kv_cache_usage_perc|gpu_cache_usage_perc|num_requests_running|num_requests_waiting|num_preemptions_total)"
                          r"(?:\{[^}]*\})?\s+(\S+)")


def metrics_url(base_url: str) -> str:
    """vLLM's Prometheus endpoint on the server of an OpenAI-compatible base URL: http://h:8000/v1 -> http://h:8000/metrics."""
    return re.sub(r"/v1$", "", str(base_url).rstrip("/")) + "/metrics"


def _url_for_log(url: str) -> str:
    return re.sub(r"//[^/@]*@", "//", url)                                             


def parse_vllm_metrics(text: str) -> dict | None:
    """{kv, running, waiting, preempt} from a vLLM /metrics page: the KV cache use (vllm:kv_cache_usage_perc, 0..1; older servers'



"""
    v: dict = {}
    for line in str(text).splitlines():
        m = _VLLM_METRIC.match(line)
        if not m:
            continue
        try:
            x = float(m.group(2))
        except ValueError:
            continue
        if not math.isfinite(x):
            continue
        k = m.group(1)
        v[k] = max(v.get(k, x), x) if k.endswith("_perc") else v.get(k, 0.0) + x
    kv = v.get("kv_cache_usage_perc", v.get("gpu_cache_usage_perc"))
    if kv is None or not 0.0 <= kv <= 1.0:
        return None
    return {"kv": kv, "running": v.get("num_requests_running", 0.0), "waiting": v.get("num_requests_waiting", 0.0),
            "preempt": v.get("num_preemptions_total")}


class _NoReading(ValueError):
    """No reading for a reason the guard itself names (its text is logged; other exceptions are logged by their type only)."""


def _bearer(api_key_file) -> str:
    """The sessions' own token (agent.py --endpoint openai: the key file's text, "EMPTY" without one). Never logged."""
    try:
        kp = Path(api_key_file).expanduser() if api_key_file else None
        return kp.read_text().strip() if kp and kp.exists() else "EMPTY"
    except OSError:
        return "EMPTY"


class KVGuard:
    """The agent stage's admission gate (the section comment above). admit(inflight, want) -> how many of `want` starts may go now; it




"""

    def __init__(self, base_url: str, api_key_file, workers: int, out=None, now=time.time, getter=None):
        self.url = metrics_url(base_url)
        self._key = _bearer(api_key_file)
        self.workers = int(workers)
        self.floor = max(1, self.workers - KV_GUARD_FLOOR_GAP)
        self.now = now
        self.get = getter or self._http_get
        self.path = Path(out) / KV_GUARD_LOG if out else None
        self.hist: list = []                                                       
        self.last: dict | None = None                                             
        self.last_try: float | None = None
        self.failing = False; self.fail_said = False; self.said_t: float | None = None
        self.hold_t0: float | None = None; self.bound_t0: float | None = None; self.noted_t: float | None = None
        self.holds = 0; self.held_s = 0.0; self.forced = 0; self.reads = 0; self.read_errors = 0; self.broken = False
        self._reader: threading.Thread | None = None                                          

    def describe(self) -> str:
        return (f"kv guard on: vLLM metrics {_url_for_log(self.url)} every {KV_GUARD_RECHECK_S:.0f} s; a start is held while the KV cache use "
                f">= {KV_GUARD_HOLD:.2f} (until < {KV_GUARD_RELEASE:.2f}) or requests wait while preemptions rose within {KV_GUARD_PREEMPT_S:.0f} s; "
                f"never below {self.floor} of {self.workers} sessions in flight; one start per {KV_GUARD_MAX_HOLD_S / 60:.0f} min of a hold; "
                f"no readable metrics = no gate")

    def _http_get(self) -> str:
        """One read with a wall-clock bound: _fetch in a daemon thread, waited for at most 2 * KV_GUARD_TIMEOUT_S (requests' timeout bounds

"""
        t = self._reader
        if t is not None and t.is_alive():
            raise _NoReading("the previous /metrics read is still running")
        box: dict = {}

        def run():
            try:
                box["text"] = self._fetch()
            except Exception as e:                                                     
                box["error"] = e
        wall = 2 * KV_GUARD_TIMEOUT_S
        t = threading.Thread(target=run, name="kv-guard-read", daemon=True)
        self._reader = t
        t.start()
        t.join(wall)
        if t.is_alive():
            raise _NoReading(f"/metrics read not done within {wall:g} s")
        if "error" in box:
            raise box["error"]
        if "text" not in box:
            raise _NoReading("/metrics read ended without a page")
        return box["text"]

    def _fetch(self) -> str:
        import requests                                                                                                 
        with requests.get(self.url, headers={"Authorization": f"Bearer {self._key}"}, timeout=KV_GUARD_TIMEOUT_S, stream=True) as r:
            r.raise_for_status()
            buf = bytearray()
            for chunk in r.iter_content(65536):
                buf += chunk
                if len(buf) > KV_GUARD_MAX_BYTES:
                    raise _NoReading(f"/metrics body larger than {KV_GUARD_MAX_BYTES} bytes")
            return buf.decode("utf-8", errors="replace")

    def _event(self, now: float, event: str, **kw) -> None:
        if self.path is None:
            return
        try:
            with self.path.open("a") as fh:
                fh.write(json.dumps({"t": round(now, 1), "utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now)), "event": event,
                                     **kw}) + "\n")
        except OSError:
            pass

    def sample(self, now: float) -> None:
        """One read. A failure keeps the last good reading (it ages out after KV_GUARD_STALE_S); the first failure is said, again only after
"""
        self.last_try = now; self.reads += 1
        try:
            r = parse_vllm_metrics(self.get())
            if r is None:
                raise _NoReading("no vLLM KV cache use (0..1) on the page")
        except Exception as e:                                                           
            self.read_errors += 1
            if not self.failing:
                self.failing = True
                if self.said_t is None or not 0 <= now - self.said_t < KV_GUARD_SAY_S:
                    self.said_t = now; self.fail_said = True
                    what = str(e) if isinstance(e, _NoReading) else type(e).__name__                                               
                    log(f"kv guard: vLLM metrics unreadable at {_url_for_log(self.url)} ({what}): no gate while there is no "
                        f"reading (sessions start as without the guard)")
                    self._event(now, "unreadable", error=what)
            return
        if self.failing and self.fail_said:
            log(f"kv guard: vLLM metrics readable again (KV {r['kv']:.2f}, {r['waiting']:.0f} waiting)")
            self._event(now, "readable", kv=round(r["kv"], 4))
        self.failing = False; self.fail_said = False
        r["t"] = now; self.last = r
        pr = r.get("preempt")
        if pr is not None:
            if self.hist and (pr < self.hist[-1][1] or now < self.hist[-1][0]):
                self.hist = []                                                                            
            self.hist.append((now, pr))
            keep = KV_GUARD_PREEMPT_S + 4 * KV_GUARD_RECHECK_S
            while len(self.hist) > 2 and now - self.hist[1][0] > keep:
                self.hist.pop(0)

    def preempt_rise(self, now: float) -> float:
        """The preemption counter's rise over the last KV_GUARD_PREEMPT_S: the newest reading minus the newest one at or before the window's
"""
        if not self.hist:
            return 0.0
        base = self.hist[0]
        for s in self.hist:
            if s[0] <= now - KV_GUARD_PREEMPT_S:
                base = s
            else:
                break
        return max(0.0, self.hist[-1][1] - base[1])

    def reading(self, now: float):
        """(the last good reading, the preemption counter's rise) while that reading is fresh, else None; a read first when one is due.
"""
        if self.last_try is None or not 0 <= now - self.last_try < KV_GUARD_RECHECK_S:                                  
            self.sample(now)
        r = self.last
        if r is None or not 0 <= now - r["t"] <= KV_GUARD_STALE_S:                                               
            return None
        return r, self.preempt_rise(now)

    def pressure(self, now: float):
        """None (no fresh reading: no gate), or (reasons, reading, rise); reasons empty = healthy."""
        rd = self.reading(now)
        if rd is None:
            return None
        r, rise = rd
        thr = KV_GUARD_RELEASE if self.hold_t0 is not None else KV_GUARD_HOLD
        why = []
        if r["kv"] >= thr:
            why.append(f"KV {r['kv']:.2f} >= {thr:.2f}")
        if r["waiting"] > 0 and rise > 0:
            why.append(f"{r['waiting']:.0f} waiting, preemptions +{rise:.0f} within {KV_GUARD_PREEMPT_S:.0f} s")
        return why, r, rise

    def _numbers(self, r: dict | None, rise: float | None) -> dict:
        if not r:
            return {}
        return {"kv": round(r["kv"], 4), "waiting": r["waiting"], "running": r["running"], "preempt_rise": rise}

    def _release(self, now: float, reason: str, p) -> None:
        dur = max(0.0, now - self.hold_t0)                             
        self.held_s += dur
        r, rise = (p[1], p[2]) if p else (None, None)
        log(f"kv guard: release after {dur / 60:.1f} min ({reason}"
            + (f"; KV {r['kv']:.2f}, {r['waiting']:.0f} waiting, preemptions +{rise:.0f}" if r else "") + ")")
        self._event(now, "release", reason=reason, held_s=round(dur, 1), **self._numbers(r, rise))
        self.hold_t0 = self.bound_t0 = self.noted_t = None

    def admit(self, inflight: int, want: int) -> int:
        """How many of `want` session starts may go now (want when the server is healthy or unread). No harm on failure: a guard that
"""
        try:
            return self._admit(inflight, want)
        except Exception as e:                
            if not self.broken:
                self.broken = True
                log(f"kv guard: raised {type(e).__name__}: {e}; no gate from now on (sessions start as without the guard)")
            self.hold_t0 = self.bound_t0 = self.noted_t = None
            return max(0, want)

    def _admit(self, inflight: int, want: int) -> int:
        if self.broken:
            return max(0, want)
        now = self.now()
        p = self.pressure(now)
        if want <= 0:
            if self.hold_t0 is not None:
                self._release(now, "no start pending", p)
            return max(0, want)
        if p is None or not p[0]:
            if self.hold_t0 is not None:
                self._release(now, "metrics unreadable" if p is None else "healthy", p)
            return want
        why, r, rise = p
        fill = max(0, self.floor - int(inflight))                                     
        if fill >= want:
            return want
        held = want - fill
        if self.hold_t0 is None:
            self.hold_t0 = self.bound_t0 = self.noted_t = now; self.holds += 1
            log(f"kv guard: hold {held} start(s) ({'; '.join(why)}; {r['running']:.0f} running in vLLM; {inflight} session(s) in flight, "
                f"floor {self.floor}" + (f", {fill} start(s) up to the floor" if fill else "") + f"); re-check every {KV_GUARD_RECHECK_S:.0f} s")
            self._event(now, "hold", reasons=why, inflight=int(inflight), want=int(want), floor=self.floor, **self._numbers(r, rise))
        elif not 0 <= now - self.bound_t0 < KV_GUARD_MAX_HOLD_S:                                                      
            self.bound_t0 = now; self.forced += 1; fill = max(fill, 1)
            log(f"kv guard: hold bound ({KV_GUARD_MAX_HOLD_S / 60:.0f} min): one start goes ({'; '.join(why)}; {inflight} in flight)")
            self._event(now, "forced", reasons=why, inflight=int(inflight), **self._numbers(r, rise))
        elif not 0 <= now - self.noted_t < KV_GUARD_NOTE_S:
            self.noted_t = now
            log(f"kv guard: still holding {held} start(s) after {max(0.0, now - self.hold_t0) / 60:.0f} min ({'; '.join(why)}; {inflight} in flight)")
        return min(want, fill)

    def close(self) -> None:
        """The agent stage is over: an open hold ends; one summary line when the guard did anything or could not read."""
        try:
            self._close()
        except Exception as e:                
            log(f"kv guard: closing raised {type(e).__name__}: {e}")

    def _close(self) -> None:
        now = self.now()
        if self.hold_t0 is not None:
            self._release(now, "agent stage over", None)
        if self.holds or self.read_errors:
            log(f"kv guard: {self.holds} hold(s), {self.held_s / 60:.1f} min held in all, {self.forced} forced start(s); metrics read "
                f"{self.reads} time(s), {self.read_errors} unreadable")


def kv_guard_for(a, clock) -> KVGuard | None:
    """The stage's guard: None with --kv-guard off, or for an args object without the flag (tests, wrappers built before 2026-11-01)."""
    if getattr(a, "kv_guard", "off") != "on" or not getattr(a, "base_url", None):
        return None
    try:
        return KVGuard(a.base_url, getattr(a, "api_key_file", None), a.workers, out=a.out, now=clock.now)
    except Exception as e:                                                                       
        log(f"kv guard: not started ({type(e).__name__}: {e}); sessions start as without the guard")
        return None


                                                                                                                                       
                                                                                                                                   
                                                                                                                            
                                                                                                                                      
                                                                                                                                         
                                                                                                                                      
                                                                                                                                           
                                                                                                                                        
                                                                                                                      
                                                                                                          
                                                                                                                                        
                                                                                                                                            
                                                                                                                                       
                                                                                                                                          
                                                                                                                                           
                                                                                                                                         
                                                                                                                                         
                                                                                                                                
                                                                                                                                     
                                                                                          
                                                                                                                                         
                                                                                                                                          
                                                                                                                             
SHED_KV = 0.95                                                                                           
SHED_S = 180.0                                                                                                   
SHED_COOLDOWN_S = 600.0                                        
SHED_MIN_AGE_S = 900.0                                                                                                    
SHED_NOTE_S = 600.0                                                                                                       
SHED_DIR = "shed"                                                                                                                           
SHED_TAIL = (1 << 18, 1 << 21, 1 << 24)                                                                                        
DEFAULT_KV_SHED = "off"


def shed_stop_path(out, run_id: str) -> Path:
    """Session run_id's stop file (agent.py --stop-file): <out>/shed/<run id>.stop, absolute (the session runs from ROOT). A run id is
"""
    return Path(out).resolve() / SHED_DIR / f"{run_id}.stop"


def trajectory_files(run_dir: Path) -> list[Path]:
    """A session's trajectory files, one per stem: <stem>.jsonl.gz when it exists, else <stem>.jsonl. agent.py appends to the plain file

"""
    by: dict = {}
    try:
        for f in sorted((Path(run_dir) / "trajectories").iterdir()):
            if f.name.endswith(".jsonl.gz"):
                by[f.name[:-len(".jsonl.gz")]] = f
            elif f.name.endswith(".jsonl"):
                by.setdefault(f.name[:-len(".jsonl")], f)
    except OSError:
        return []
    return [by[k] for k in sorted(by)]


def _turn_out_tokens(f: Path) -> tuple[int, bool]:
    """(output_tokens summed over one trajectory file's 'turn' records, whether the file read to its end): a .gz cut short by a stop
"""
    tot, ok = 0, True
    try:
        with (gzip.open(f, "rt", errors="replace") if f.name.endswith(".gz") else open(f, errors="replace")) as fh:
            for line in fh:
                try:
                    r = json.loads(line)
                    if isinstance(r, dict) and r.get("type") == "turn":
                        tot += max(0, int(r.get("output_tokens") or 0))
                except (ValueError, TypeError):
                    continue
    except Exception:                                                                                           
        ok = False
    return tot, ok


def trajectory_out_tokens(run_dir: Path) -> int:
    """Model output tokens on record in a session's trajectories (the 'turn' records' output_tokens; trajectory_files: the .gz preferred
"""
    tot = 0
    try:
        for f in trajectory_files(run_dir):
            n, ok = _turn_out_tokens(f)
            if not ok and f.name.endswith(".gz") and f.with_name(f.name[:-3]).exists():
                n = max(n, _turn_out_tokens(f.with_name(f.name[:-3]))[0])
            tot += n
    except Exception:                
        pass
    return tot


def _tail_turn_input(f: Path) -> int:
    """input_tokens of the last 'turn' record in a plain trajectory file, read from its tail (SHED_TAIL windows, the first that holds a

"""
    size = f.stat().st_size
    for w in SHED_TAIL:
        off = max(0, size - w)
        with open(f, "rb") as fh:
            fh.seek(off); lines = fh.read(w).split(b"\n")
        if off > 0:
            lines = lines[1:]                              
        last = None
        for raw in reversed(lines):
            if b'"type": "turn"' not in raw and b'"type": "budget_forcing"' not in raw:
                continue
            try:
                r = json.loads(raw)
            except ValueError:
                continue
            if not isinstance(r, dict):
                continue
            if last is None:
                if r.get("type") == "turn":
                    last = r
            elif r.get("type") == "turn":
                break
            elif r.get("type") == "budget_forcing" and r.get("turn") == last.get("turn"):
                return max(0, int(last.get("input_tokens") or 0)) // 2
        if last is not None:
            return max(0, int(last.get("input_tokens") or 0))
        if off == 0:
            return 0
    return 0


def last_turn_context(run_dir: Path) -> int:
    """A running session's last prompt: input_tokens of the last 'turn' record of its plain trajectory (agent.py appends to

"""
    best = 0
    for f in trajectory_files(run_dir):
        if f.name.endswith(".jsonl"):
            try:
                best = max(best, _tail_turn_input(f))
            except Exception:                
                continue
    return best


class ShedGuard:
    """--kv-shed on (the section comment above). tick(sessions) every pass of the stage loop, sessions = the in-flight ones, each




"""

    def __init__(self, reader, workers: int, out, now=time.time, ctx=None, own_reader: bool = False):
        self.reader, self.own_reader = reader, own_reader
        self.workers = int(workers)
        self.floor = max(1, self.workers - KV_GUARD_FLOOR_GAP)                                                     
        self.out = Path(out); self.dir = self.out.resolve() / SHED_DIR
        self.now = now
        self.ctx = ctx or (lambda run_id: last_turn_context(RUNS / run_id))
        self.seen_t: float | None = None                                                             
        self.kv_t0: float | None = None; self.wp_t0: float | None = None                                                        
        self.spell = False; self.spells = 0
        self.pending: dict | None = None                                                                
        self.last_t: float | None = None; self.last_row: str | None = None
        self.sheds = 0; self.consumed = 0; self.unneeded = 0
        self.noted: dict = {}
        self.broken = False
        self.dir.mkdir(parents=True, exist_ok=True)
        for f in self.dir.glob("*.stop*"):                                                                     
            try:
                f.unlink()
            except OSError:
                pass

    def describe(self) -> str:
        return (f"kv shed on: under sustained pressure (KV >= {SHED_KV:.2f}, or requests waiting while preemptions rose within "
                f"{KV_GUARD_PREEMPT_S:.0f} s, in every reading for {SHED_S:.0f} s) with more than {self.floor} of {self.workers} sessions in "
                f"flight, the session with the largest last prompt (>= {SHED_MIN_AGE_S / 60:.0f} min old, not of the row shed last) is asked "
                f"to end at its next turn boundary (agent.py --stop-file {self.dir}/<run id>.stop); one per {SHED_COOLDOWN_S / 60:.0f} min, "
                f"none while one is pending; never a signal")

    def _event(self, now: float, event: str, **kw) -> None:
        self.reader._event(now, event, **kw)                                                        

    def _note(self, now: float, key: str, msg: str, **kw) -> None:
        t = self.noted.get(key)
        if t is None or not 0 <= now - t < SHED_NOTE_S:
            self.noted[key] = now
            log(f"kv shed: {msg}")
            self._event(now, "shed_blocked", reason=key, **kw)

    def _spell_over(self, now: float, reason: str) -> None:
        self.spell = False
        log(f"kv shed: pressure no longer sustained ({reason})")
        self._event(now, "pressure_over", reason=reason)

    def tick(self, sessions: list) -> str | None:
        try:
            return self._tick(sessions)
        except Exception as e:                
            if not self.broken:
                self.broken = True
                log(f"kv shed: raised {type(e).__name__}: {e}; no shed from now on (running sessions are never stopped by it)")
            return None

    def _tick(self, sessions: list) -> str | None:
        if self.broken:
            return None
        now = self.now()
        rd = self.reader.reading(now)
        if rd is None:                                                                                      
            self.kv_t0 = self.wp_t0 = None
            if self.spell:
                self._spell_over(now, "no fresh metrics reading")
            return None
        r, rise = rd
        t = r["t"]
        if t != self.seen_t:                                                                                                     
            self.seen_t = t
            kv_hi, wp = r["kv"] >= SHED_KV, r["waiting"] > 0 and rise > 0
            self.kv_t0 = (self.kv_t0 if self.kv_t0 is not None and 0 <= t - self.kv_t0 else t) if kv_hi else None                       
            self.wp_t0 = (self.wp_t0 if self.wp_t0 is not None and 0 <= t - self.wp_t0 else t) if wp else None                   
        why = []
        if self.kv_t0 is not None and t - self.kv_t0 >= SHED_S:
            why.append(f"KV {r['kv']:.2f} >= {SHED_KV:.2f} for {t - self.kv_t0:.0f} s")
        if self.wp_t0 is not None and t - self.wp_t0 >= SHED_S:
            why.append(f"{r['waiting']:.0f} waiting while preemptions rose (+{rise:.0f} within {KV_GUARD_PREEMPT_S:.0f} s) for "
                       f"{t - self.wp_t0:.0f} s")
        if not why:
            if self.spell:
                self._spell_over(now, f"KV {r['kv']:.2f}, {r['waiting']:.0f} waiting")
            return None
        nums = {"kv": round(r["kv"], 4), "waiting": r["waiting"], "running": r["running"], "preempt_rise": rise, "inflight": len(sessions)}
        if not self.spell:
            self.spell = True; self.spells += 1; self.noted = {}
            log(f"kv shed: sustained pressure ({'; '.join(why)}; {r['running']:.0f} running in vLLM; {len(sessions)} session(s) in flight, "
                f"floor {self.floor})")
            self._event(now, "pressure", reasons=why, floor=self.floor, **nums)
        if self.pending is not None:
            p = self.pending
            self._note(now, "pending", f"row#{p['row']:02d} session {p['k']} was asked to end {max(0.0, now - p['t']) / 60:.0f} min ago and "
                                       f"has not ended yet: no other shed", **nums)
            return None
        if self.last_t is not None and 0 <= now - self.last_t < SHED_COOLDOWN_S:
            self._note(now, "cooldown", f"the last shed was {(now - self.last_t) / 60:.1f} min ago (at most one per "
                                        f"{SHED_COOLDOWN_S / 60:.0f} min)", **nums)
            return None
        if len(sessions) <= self.floor:
            self._note(now, "floor", f"{len(sessions)} session(s) in flight, not above the floor {self.floor}: no shed", **nums)
            return None
        old = [s for s in sessions if now - s["t0"] >= SHED_MIN_AGE_S]                                                    
        cands = [s for s in old if s["n"] != self.last_row]
        size = {s["run_id"]: max(0, int(self.ctx(s["run_id"]) or 0)) for s in cands}
        cands = [s for s in cands if size[s["run_id"]] > 0]
        if not cands:
            self._note(now, "no candidate", f"no session to ask: {len(sessions)} in flight, {len(old)} at least {SHED_MIN_AGE_S / 60:.0f} min "
                                            f"old" + (", the row shed last excluded" if self.last_row is not None else "")
                                            + ", none with a turn on record among the rest", **nums)
            return None
        pick = max(cands, key=lambda s: (size[s["run_id"]], -s["t0"]))                                                       
        path = shed_stop_path(self.out, pick["run_id"])
        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            tmp = path.with_name(path.name + ".tmp")                                                           
            tmp.write_text(json.dumps({"run_id": pick["run_id"], "why": "kv shed", "utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now)),
                                       "prompt_tokens": size[pick["run_id"]], "reasons": why}) + "\n")
            os.replace(tmp, path)
        except OSError as e:
            self._note(now, "write", f"stop file {path} not written ({type(e).__name__}: {e}): no shed", **nums)
            return None
        self.pending = {"run_id": pick["run_id"], "n": pick["n"], "row": pick["row"], "k": pick["k"], "t": now, "path": str(path)}
        self.last_t, self.last_row = now, pick["n"]; self.sheds += 1
        nxt = sorted((size[s["run_id"]] for s in cands if s is not pick), reverse=True)[:4]
        log(f"kv shed: row#{pick['row']:02d} session {pick['k']} asked to end at its next turn boundary (last prompt {size[pick['run_id']]} "
            f"tokens, the largest of {len(cands)} eligible" + (f"; next {nxt}" if nxt else "") + f"; {'; '.join(why)}; {len(sessions)} in "
            f"flight, floor {self.floor})")
        self._event(now, "shed", run_id=pick["run_id"], row=pick["row"], k=pick["k"], prompt_tokens=size[pick["run_id"]],
                    age_s=round(now - pick["t0"], 1), eligible=len(cands), reasons=why, **nums)
        return pick["run_id"]

    def ended(self, run_id: str) -> str | None:
        try:
            return self._ended(run_id)
        except Exception as e:                
            log(f"kv shed: session end bookkeeping raised {type(e).__name__}: {e}")
            if self.pending is not None and self.pending.get("run_id") == run_id:
                self.pending = None
            return None

    def _ended(self, run_id: str) -> str | None:
        path = shed_stop_path(self.out, run_id)
        left = path.exists()
        if left:                                                                                  
            try:
                path.unlink()
            except OSError:
                pass
        p = self.pending
        if p is None or p["run_id"] != run_id:
            return None
        self.pending = None
        now = self.now(); dur = max(0.0, now - p["t"])
        self._event(now, "shed_end", run_id=run_id, row=p["row"], k=p["k"], taken=not left, after_s=round(dur, 1))
        if left:
            self.unneeded += 1
            log(f"kv shed: row#{p['row']:02d} session {p['k']} ended {dur:.0f} s after the ask without taking its stop file (removed)")
            return "unneeded"
        self.consumed += 1
        log(f"kv shed: row#{p['row']:02d} session {p['k']} ended at a turn boundary {dur:.0f} s after the ask")
        return "consumed"

    def close(self) -> None:
        """The agent stage is over: an open ask is withdrawn (its file removed), an open spell ends, one summary line when anything
"""
        try:
            now = self.now()
            if self.pending is not None:
                try:
                    Path(self.pending["path"]).unlink()
                except OSError:
                    pass
                self.pending = None
            if self.spell:
                self._spell_over(now, "agent stage over")
            if self.sheds or self.spells:
                log(f"kv shed: {self.spells} sustained-pressure spell(s), {self.sheds} shed(s): {self.consumed} ended at a turn boundary, "
                    f"{self.unneeded} ended before taking the stop file")
            if self.own_reader:
                self.reader.close()
        except Exception as e:                
            log(f"kv shed: closing raised {type(e).__name__}: {e}")


def shed_guard_for(a, clock, guard) -> ShedGuard | None:
    """The stage's shed guard: None with --kv-shed off (the default), or for an args object without the flag. Its readings are the KV
"""
    if getattr(a, "kv_shed", "off") != "on" or not getattr(a, "base_url", None):
        return None
    try:
        reader = guard if guard is not None else KVGuard(a.base_url, getattr(a, "api_key_file", None), a.workers, out=a.out, now=clock.now)
        return ShedGuard(reader, a.workers, a.out, now=clock.now, own_reader=guard is None)
    except Exception as e:                                                                        
        log(f"kv shed: not started ({type(e).__name__}: {e}); no session is asked to end")
        return None


def session_stop_why(run_dir: Path) -> str | None:
    """Why agent.py ended a session at a turn boundary (summary.json "why": "kv shed" / "context cap", b105); None otherwise."""
    try:
        for r in json.loads((run_dir / "summary.json").read_text()):
            if isinstance(r, dict) and isinstance(r.get("why"), str):
                return r["why"]
    except Exception:                
        pass
    return None


def _nonneg_seconds(x: str) -> float:
    v = float(x)
    if not (math.isfinite(v) and v >= 0):
        raise argparse.ArgumentTypeError(f"{x}: seconds >= 0 (0 = off)")
    return v


def _nonneg_int(x: str) -> int:
    try:
        v = int(x)
    except ValueError:
        raise argparse.ArgumentTypeError(f"{x}: an integer >= 0 (0 = off)") from None
    if v < 0:
        raise argparse.ArgumentTypeError(f"{x}: an integer >= 0 (0 = off)")
    return v


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


def session_out_tokens(run_dir: Path) -> int:
    """Model output tokens of a finished session (agent.py's summary.json); 0 when it produced none (a server outage). b105 (2026-11-01;


"""
    try:
        res = json.loads((run_dir / "summary.json").read_text())
        return sum(int(r.get("out_tokens") or 0) for r in res if isinstance(r, dict))
    except (OSError, ValueError, TypeError):
        return trajectory_out_tokens(run_dir)


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


def agent_stage(a, names: list[str], clock: Clock, runner=None, on_idle=None, set_busy=None, before_start=None) -> dict:
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
        kw = {"why": "session wall cap"} if deadline < clock.agent_deadline else {}                                                    
        return run_session(session_cmd(a, n, run_id, fresh), env, out / "logs" / f"s{idx[n]:02d}.k{k}.log", deadline, now=clock.now, **kw)
    runner = runner or default_runner
    log(f"agent stage: {a.workers} worker(s) over {len(names)} row(s), at most {a.max_sessions} session(s) per row, deadline in "
        f"{clock.left(clock.agent_deadline) / 3600:.2f} h, schedule {sched}")
    guard = kv_guard_for(a, clock)                                                                                    
    if guard is not None:
        log(guard.describe())
    wall = float(getattr(a, "session_max_seconds", 0) or 0)                                           
    if wall > 0:
        log(f"session wall cap: a session still running {wall:.0f} s after its start is stopped (SIGTERM; its banked best stays)")
    shed = shed_guard_for(a, clock, guard)                                                               
    if shed is not None:
        log(shed.describe())
    ctx_cap = int(getattr(a, "session_max_context", 0) or 0)                                                
    if ctx_cap > 0:
        log(f"context cap: a session ends after a turn whose prompt was >= {ctx_cap} tokens (agent.py --max-context-tokens; at the turn "
            f"boundary, as after its last turn; its banked best stays)")
    stagger = float(getattr(a, "first_wave_stagger", 0) or 0)                                               
    wave, wave_t = stagger > 0, None                                                                        
    if wave:
        log(f"first wave: one session start per {stagger:g} s until {a.workers} are in flight or a session ends (then the async ladder "
            f"as before)")
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
            want = min(len(ready), max(0, a.workers - len(inflight)))
            go = guard.admit(len(inflight), want) if guard is not None else want
            if wave and go > 0:                                                                                                          
                go = 1 if wave_t is None or not 0 <= clock.now() - wave_t < stagger else 0
            for n in ready[:go]:
                k = done_k[n] + 1; done_k[n] = k; used[n] += 1                                                                         
                run_id = f"{a.tag}-s{idx[n]:02d}-k{k}"
                if before_start is not None:                                                                                    
                    try:
                        before_start(n, k)
                    except Exception as e:                                                        
                        log(f"row#{idx[n]:02d} session {k}: before-start hook raised {type(e).__name__}: {e}")
                b0 = best_score(work, n)
                                                                                                                                          
                                                                                                    
                fresh = not (work / safe(n) / "state.json").exists()
                dl = min(clock.agent_deadline, clock.now() + wall) if wall > 0 else clock.agent_deadline
                fu = ex.submit(runner, n, k, run_id, fresh, dl)
                inflight[fu] = {"n": n, "k": k, "run_id": run_id, "t0": clock.now(), "b0": b0, "dl": dl}
                log(f"row#{idx[n]:02d} session {k} starts ({len(inflight)} in flight; best {b0:.2f}"
                    + (f"; room priority {room_priority(b0, used[n] - 1, gains[n]):.2f}" if sched == "room" and used[n] > 1 else "") + ")")
                if wave:
                    wave_t = clock.now()
            if wave and len(inflight) >= a.workers:
                wave = False
                log(f"first wave: {len(inflight)} sessions in flight; the async ladder from now on")
            if shed is not None and inflight:                                                                                        
                shed.tick([{"n": j["n"], "row": idx[j["n"]], "k": j["k"], "run_id": j["run_id"], "t0": j["t0"]} for j in inflight.values()])
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
                if wave:                                                  
                    wave = False
                    log(f"first wave: row#{idx[n]:02d} session {j['k']} ended; the async ladder from now on")
                shed_end = shed.ended(j["run_id"]) if shed is not None else None                                         
                stop_why = session_stop_why(RUNS / j["run_id"]) if (shed is not None or ctx_cap > 0) else None
                toks = session_out_tokens(RUNS / j["run_id"])
                terr = session_tool_errors(RUNS / j["run_id"])
                if terr:                                                                                                           
                    log(f"WARNING row#{idx[n]:02d} session {j['k']}: tool errors {terr} (a tool the model was offered raised; see the session log)")
                is_dry = toks == 0 and shed_end != "consumed"                                                                       
                dry[n] = dry[n] + 1 if is_dry else 0
                if dry[n] >= ASYNC_MAX_DRY:
                    parked.add(n)
                b1 = best_score(work, n); secs = clock.now() - j["t0"]
                gains[n].append(b1 - j["b0"])
                with sess_path.open("a") as fh:
                    fh.write(json.dumps({"problem": n, "row": idx[n], "k": j["k"], "run_id": j["run_id"], "rc": rc, "seconds": round(secs, 1),
                                         "out_tokens": toks, "dry": is_dry, "score_before": j["b0"], "score_after": b1,
                                         "parked": n in parked, "tool_errors": terr,
                                         **({"stop": stop_why} if stop_why else {}), **({"shed": shed_end} if shed_end else {})},
                                        ensure_ascii=False) + "\n")
                mean = statistics.mean(best_score(work, x) for x in names)
                log(f"row#{idx[n]:02d} session {j['k']} done (rc {rc}): {j['b0']:.2f} -> {b1:.2f} in {secs:.0f} s"
                    + (f"; dry ({dry[n]} in a row)" if is_dry else "") + ("; parked" if n in parked else "")
                    + ("; stopped at the session wall cap" if rc is None and j["dl"] < clock.agent_deadline else "")
                    + (f"; ended at a turn boundary ({stop_why})" if stop_why else "; asked to end (kv shed)" if shed_end == "consumed" else "")
                    + f"; {len(inflight)} in flight; mean {mean:.2f}")
    finally:
        ex.shutdown(wait=True)
        if shed is not None:
            shed.close()
        if guard is not None:
            guard.close()
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
    p = out / "end_config_open.json"
    p.write_text(json.dumps(package_config_dict(with_hr, frozen), indent=1, ensure_ascii=False))
    return p


def package_config_dict(with_hr: bool, frozen: Path = FROZEN) -> dict:
    """package_config's body (rc2: also read by dialect_open_args, which writes its own copy, so the shared file is never rewritten
"""
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
    return cfg


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

    def __init__(self, a, rows: dict, hbs: dict, clock: Clock, launcher=None, r10_launcher=None, dial_launcher=None):
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
        self.final_rows: set = set()                                                                                 
        self.closed = False
        self.threads = [threading.Thread(target=self._worker, name=f"endpipe{i}", daemon=True)
                        for i in range(max(1, int(getattr(a, "end_pipe_jobs", END_PIPE_JOBS))))]
                                                                                                                          
        self.r10_on = getattr(a, "end_pipe_r10", END_PIPE_R10) == "on"
        self.r10_launcher = r10_launcher or self._run_r10
        self.r10_cfg = None
        self.rq: queue.PriorityQueue = queue.PriorityQueue()
        self.r10_queued: dict = {}                            
        self.r10_running: set = set()             
                                                                                                                                      
                                                               
        self.dial_on = dialect_on(a)
        self.dial_launcher = dial_launcher or self._run_dial
        if self.r10_on:
            self.threads += [threading.Thread(target=self._r10_worker, name=f"endpipe-r10-{i}", daemon=True)
                             for i in range(max(1, int(getattr(a, "end_pipe_r10_jobs", END_PIPE_R10_JOBS))))]
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
            if final:
                self.final_rows.add(n)
            q = self.queued.get(n)
            blocked = bool((n, sha) in self.running or (q and q[0] == sha and q[1] <= prio) or self.attempted(n, sha) or self.polished(n, sha))
            if not blocked:
                self.queued[n] = (sha, prio)                                                                                        
                self.q.put((prio, next(self.seq), n, sha))
        if blocked:                                                                                                                         
            return (n, sha) not in self.running and self.offer_r10(n, sha, prio)
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
            if self.polished(n, sha) and n not in self.busy:                                                                                
                if self.r10_on:
                    self.offer_r10(n, sha, 0 if n in self.final_rows else 1)
                else:                                                                                     
                    self.dial_after(n, sha)

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
        for t in self.threads:
            (self.rq if t.name.startswith("endpipe-r10") else self.q).put((9, next(self.seq), None, None))
        for t in self.threads:
            t.join()

                                                                                                                                  
    def record(self, n: str, sha: str, stage: str) -> dict | None:
        """The last VALID record (valid_end_record) of one stage ("end", "r10", "r10b") of this best, else None."""
        recs = [r for r in read_jsonl_records(self.root / safe(n) / sha / stage / "report.jsonl") if r.get("problem") == n and valid_end_record(r)]
        return recs[-1] if recs else None

    def r10_attempted(self, n: str, sha: str) -> bool:
        return (self.root / safe(n) / sha / "r10_attempted").exists()

    def r10_pending(self, n: str, sha: str) -> bool:
        """The r10 rounds of this best are queued or running (rc1-open, the b94b x b94a merge): the write-back waits for them, since
"""
        with self.lock:
            q = self.r10_queued.get(n)
            return (n, sha) in self.r10_running or bool(q and q[0] == sha)

    def offer_r10(self, n: str, sha: str, prio: int = 1) -> bool:
        """Queue the r10 rounds of this best: on, not closed, its open polish valid, never attempted, not queued / running."""
        if not self.r10_on or self.closed or not self.polished(n, sha) or self.r10_attempted(n, sha):
            return False
        with self.lock:
            q = self.r10_queued.get(n)
            if (n, sha) in self.r10_running or (q and q[0] == sha and q[1] <= prio):
                return False
            self.r10_queued[n] = (sha, prio)
            self.rq.put((prio, next(self.seq), n, sha))
        log(f"end pipeline: {n[:40]} best {sha} queued for the r10 rounds")
        return True

    def _r10_worker(self) -> None:
        while True:
            _, _, n, sha = self.rq.get()
            if n is None:
                return
            with self.lock:
                q = self.r10_queued.get(n)
                if not q or q[0] != sha:
                    continue
                del self.r10_queued[n]
                if self.closed or n in self.busy:                                                    
                    continue
                self.r10_running.add((n, sha))
            try:
                try:
                    self.r10_launcher(n, sha)
                except (Exception, SystemExit) as e:                                                                               
                    log(f"end pipeline r10: {n[:40]} raised {type(e).__name__}: {e}")
                self.dial_after(n, sha)                                                                                                    
            finally:
                with self.lock:
                    self.r10_running.discard((n, sha))

                                                                                                                                   
    def dial_after(self, n: str, sha: str):
        """The dialect pass of this best when --dialect on; whatever it raises is logged (the chain's earlier output stands)."""
        if not self.dial_on:
            return None
        try:
            return self.dial_launcher(n, sha)
        except (Exception, SystemExit) as e:                
            log(f"end pipeline dial: {n[:40]} raised {type(e).__name__}: {e}")
            return None

    def dial_attempted(self, n: str, sha: str) -> bool:
        return (self.root / safe(n) / sha / "dial_attempted").exists()

    def _run_dial(self, n: str, sha: str):
        """Stage `dial` (b98, section 8): harness/dialect.py on pipe_choice's output of this best so far (open polish / r10 / r10b),


"""
        a, clock = self.a, self.clock
        d = self.root / safe(n) / sha
        if self.closed or self.current_sha(n) != sha or self.dial_attempted(n, sha):
            return None
        pre = pipe_choice(d, dial=False)
        if not pre or not (pre[1].get("proof") or "").strip():
            return None
        secs = min(dialect_row_seconds(a), self.stop_at() - 60.0 - clock.now() - DIALECT_MARGIN_S)
        if secs < DIALECT_MIN_S:
            log(f"end pipeline dial: {n[:40]} best {sha} not started ({secs:.0f} s of tool phase left before the agent deadline)")
            return None
        (d / "dial_attempted").write_text(time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        t0 = clock.now()
        rc = run_dialect_row(a, n, self.rows, self.hbs, pre[1], d / "dial_input", d / DIALECT_STAGE, secs,
                             min(t0 + secs + DIALECT_MARGIN_S, self.stop_at()), self.out / "logs" / f"endpipe-dial.{safe(n)[:50]}.{sha}.log",
                             meters=[d / "end" / "meter.json"], pipelined=True, now=clock.now)
        rec = self.record(n, sha, DIALECT_STAGE)
        changed = bool(rec) and _es_sha(rec["out"]["proof"]) != _es_sha(pre[1]["proof"])
        log(f"end pipeline dial: {n[:40]} best {sha} exit {rc} in {clock.now() - t0:.0f} s ("
            + (f"valid, {'changed' if changed else 'unchanged'}, paired delta {rec['delta']}" if rec else "no valid record") + ")")
        return rc

    def known_proofs(self, n: str, skip_outputs_of: str | None = None) -> list[dict]:
        """Every verified proof of the row this pipeline holds: each best it was offered (<sha>/input/finals.json) and every valid stage

"""
        row, seen = self.rows[n], {}
        for d in sorted(p for p in (self.root / safe(n)).glob("*") if p.is_dir()):
            items = []
            try:
                items.append((json.loads((d / "input" / "finals.json").read_text()) or {}).get(n) or {})
            except (OSError, ValueError):
                pass
            for st in (() if d.name == skip_outputs_of else PIPE_STAGES):
                r = self.record(n, d.name, st)
                if r:
                    items.append(r["out"])
            if d.name != skip_outputs_of:                                                                                          
                nr = self.norm_record(n, d.name)
                if nr:
                    items.append(nr)
            for it in items:
                pr = (it.get("proof") or "").strip()
                sc = it.get("score")
                if not pr or not isinstance(sc, (int, float)) or row["statement"].strip() not in pr or not check_forbidden_ok(pr):
                    continue
                h = proof_sha(pr)
                if h not in seen or float(sc) > seen[h]["score"]:
                    seen[h] = {"proof": pr, "score": float(sc)}
        return sorted(seen.values(), key=lambda c: -c["score"])

    def norm_record(self, n: str, sha: str) -> dict | None:
        """{proof, score} of the normalizer's improved output of this best (<sha>/norm/record.json; normalized_choice), else None."""
        try:
            rec = json.loads((self.root / safe(n) / sha / "norm" / "record.json").read_text())
        except (OSError, ValueError):
            return None
        pr = normalized_choice(self.rows[n], rec) if n in self.rows else None
        sc = (rec.get("after") or {}).get("score")
        return {"proof": pr, "score": float(sc)} if pr and isinstance(sc, (int, float)) else None

    def _run_norm(self, n: str, sha: str, raw: dict) -> int | None:
        """The package's lexer normalizer (harness/normalize.py, the export's normalize step) on the agent best itself, once per best, its
"""
        a, clock = self.a, self.clock
        nd = self.root / safe(n) / sha / "norm"
        if (nd / "record.json").exists():
            return 0
        nd.mkdir(parents=True, exist_ok=True)
        pf = nd / "input.lean"; pf.write_text(raw["proof"].rstrip() + "\n")
        env = base_env(a)
        env.update(compile_slots_env(int(getattr(a, "end_pipe_r10_slots", END_PIPE_R10_SLOTS)), nd))
        env["LRA_MEMGATE_RESERVE_MB"] = str(END_PIPE_RESERVE_MB)
        cmd = ["nice", "-n", str(END_PIPE_NICE)] + normalize_cmd(a, n, pf, nd / "record.json")
        return run_session(cmd, env, self.out / "logs" / f"endpipe-norm.{safe(n)[:50]}.{sha}.log",
                           min(clock.now() + NORMALIZE_ROW_SECONDS, self.stop_at()), now=clock.now)

    def r10_input(self, n: str, prev: dict, run: Path, skip_outputs_of: str | None = None) -> Path:
        """One round's run directory: finals = `prev` (the round's input; a measured output keeps its reading so the round can reuse it),

"""
        (run / "rows").mkdir(parents=True, exist_ok=True)
        ps = proof_sha((prev.get("proof") or "").strip())
        alts = [c for c in self.known_proofs(n, skip_outputs_of) if c["proof"] and proof_sha(c["proof"]) != ps][:END_PIPE_R10_ALTS]
        steps = {f"alt{k}": {"item": {"proof": c["proof"].rstrip() + "\n", "score": c["score"], "verified": True}}
                 for k, c in enumerate(sorted(alts, key=lambda c: c["score"]))}
        (run / "rows" / "r00.json").write_text(json.dumps({"problem": n, "steps": steps}, ensure_ascii=False))
        (run / "finals.json").write_text(json.dumps({n: dict(prev, proof=prev["proof"].rstrip() + "\n")}, ensure_ascii=False, indent=1))
        (run / "rows.jsonl").write_text(json.dumps(self.rows[n], ensure_ascii=False) + "\n")
        (run / "heartbeats.jsonl").write_text(json.dumps(self.hbs[n], ensure_ascii=False) + "\n")
        return run

    def r10_config(self, path: Path, seconds: float) -> Path:
        """The shipped r10 config (sha256 checked) with its sweep and tool phase wall budgets scaled to a round's clock."""
        if self.r10_cfg is None:
            raw = END_PIPE_R10_CONFIG.read_bytes()
            if hashlib.sha256(raw).hexdigest()[:16] != END_PIPE_R10_SHA16:
                raise SystemExit(f"{END_PIPE_R10_CONFIG}: not the shipped r10 config (sha256 {hashlib.sha256(raw).hexdigest()[:16]} != {END_PIPE_R10_SHA16})")
            self.r10_cfg = json.loads(raw)
        cfg = json.loads(json.dumps(self.r10_cfg))
        ph = int(max(120.0, END_PIPE_R10_PHASE * float(seconds)))
        for k in ("sweep", "tools"):
            b = cfg["budgets"][k]
            b["seconds"] = min(int(b.get("seconds") or ph), ph)
        cfg["_derived_from"] = {"file": str(END_PIPE_R10_CONFIG.relative_to(ROOT)), "sha256_16": END_PIPE_R10_SHA16, "round_seconds": int(seconds)}
        path.write_text(json.dumps(cfg, indent=1, ensure_ascii=False))
        return path

    def _run_r10(self, n: str, sha: str):
        """The r10 rounds of one best (section 7), in the squeeze's shape: round 1 (r10) on the agent best itself, BESIDE the open polish




"""
        a, clock = self.a, self.clock
        first = self.record(n, sha, "end")
        if self.current_sha(n) != sha or not first or self.r10_attempted(n, sha):
            return None
        d = self.root / safe(n) / sha
        try:
            raw = (json.loads((d / "input" / "finals.json").read_text()) or {}).get(n) or {}
        except (OSError, ValueError):
            raw = {}
        if not raw.get("proof") or proof_sha(raw["proof"].strip()) != sha:
            return None                                                                                                   
        total = min(float(getattr(a, "end_pipe_r10_row_s", END_PIPE_R10_ROW_S)), self.stop_at() - 60.0 - clock.now() - 300.0)
        if total < END_PIPE_R10_MIN_S:
            log(f"end pipeline r10: {n[:40]} skipped ({total:.0f} s left before the agent deadline)")
            return None
        (d / "r10_attempted").write_text(time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        t_end, rc = clock.now() + total, None
        for k, rnd in enumerate(R10_ROUNDS):
            if k == 0:
                prev, skip = {"proof": raw["proof"], "score": raw.get("score")}, sha
            else:
                if not self.closed and self.current_sha(n) == sha:
                    try:
                        self._run_norm(n, sha, raw)                                                                           
                    except Exception as e:                                                                       
                        log(f"end pipeline r10: {n[:40]} normalize raised {type(e).__name__}: {e}")
                outs = [r["out"] for r in (first, self.record(n, sha, "r10")) if r]
                if all(proof_sha(o["proof"].strip()) == sha for o in outs) and not self.norm_record(n, sha):
                    break                                                                                                              
                prev, skip = max(outs, key=_out_score), None
            left = min(t_end, self.stop_at() - 60.0) - clock.now()
            secs = left * (END_PIPE_R10_SHARE1 if k == 0 else 1.0)
            if secs < END_PIPE_R10_MIN_S or self.closed or self.current_sha(n) != sha:
                log(f"end pipeline r10: {n[:40]} best {sha} round {rnd} not started ("
                    + ("closed" if self.closed else "the best moved" if self.current_sha(n) != sha else f"{secs:.0f} s left") + ")")
                break
            run = self.r10_input(n, prev, d / f"{rnd}_input", skip_outputs_of=skip)
            cfg = self.r10_config(run / "end_r10.json", secs)
            env = base_env(a)
            env.update(compile_slots_env(int(getattr(a, "end_pipe_r10_slots", END_PIPE_R10_SLOTS)), d / rnd))
            env["LRA_MEMGATE_RESERVE_MB"] = str(END_PIPE_RESERVE_MB)
            cmd = ["nice", "-n", str(END_PIPE_NICE), sys.executable, "harness/endstage_r10.py", "--run-dir", str(run), "--rows",
                   str(run / "rows.jsonl"), "--heartbeats", str(run / "heartbeats.jsonl"), "--out", str(d / rnd), "--config", str(cfg),
                   "--jobs", "1", "--anon"]
            (d / rnd).mkdir(parents=True, exist_ok=True)
            t0 = clock.now()
            rc = run_session(cmd, env, self.out / "logs" / f"endpipe-{rnd}.{safe(n)[:50]}.{sha}.log", min(t0 + secs + 600.0, self.stop_at()),
                             now=clock.now)
            rec = self.record(n, sha, rnd)
            changed = bool(rec) and proof_sha(rec["out"]["proof"].strip()) != proof_sha(prev["proof"].strip())
            log(f"end pipeline r10: {n[:40]} best {sha} round {rnd} exit {rc} in {clock.now() - t0:.0f} s ("
                + (f"valid, {'changed' if changed else 'unchanged'}, paired delta {rec['delta']}" if rec else "no valid record") + ")")
        return rc


                                                                                                                                           
                                                                                                                                           
                                                                                                                                          
                                                                                                                                        
                                                                                                                                      
                                                                                                                                         
                                                                                                                                            
                                                                                                                                             
                                                                                                                                           
                                                                 
WRITEBACK_LOG = "writeback.jsonl"


def atomic_write(p: Path, text: str) -> None:
    """Write via a temporary file and rename: a reader (an EndPipe job, a starting session) never sees a torn file."""
    p = Path(p)
    tmp = p.with_name(p.name + ".opk-tmp")
    tmp.write_text(text)
    os.replace(tmp, p)


def _r10b_input_record(shadir: Path, n: str) -> dict | None:
    """The valid end / r10 record whose output was round 2's input (<shadir>/r10b_input/finals.json, written by _run_r10: the better of
"""
    try:
        prev = ((json.loads((shadir / "r10b_input" / "finals.json").read_text()) or {}).get(n) or {}).get("proof") or ""
    except (OSError, ValueError, AttributeError):
        return None
    if not prev.strip():
        return None
    ph = proof_sha(prev.strip())
    cands = []
    for st in ("end", "r10"):
        recs = [r for r in read_jsonl_records(shadir / st / "report.jsonl") if r.get("problem") == n and valid_end_record(r)]
        if recs and proof_sha(recs[-1]["out"]["proof"].strip()) == ph:
            cands.append(recs[-1])
    return max(cands, key=lambda r: _out_score(r["out"])) if cands else None


def writeback_candidate(out: Path, n: str, row: dict, pipe=None) -> tuple[dict, dict, dict] | None:
    """(current best, new best, report record) when the eager pipeline's output of the row's CURRENT agent best beats it, else None. The











"""
    out = Path(out)
    cur = state_of(out / "work", n).get("best") or {}
    proof = (cur.get("proof") or "").strip()
    if not proof:
        return None
    sha = proof_sha(proof)
    if pipe is not None and pipe.r10_pending(n, sha):
        log(f"write-back {n[:40]}: waits, the r10 rounds of best {sha} are queued or running")
        return None
    shadir = out / "end-pipe" / safe(n) / sha
    ch = pipe_choice_record(shadir, dial=False)                                                                                  
    if not ch or ch[1].get("problem") != n:
        return None
    rnd, r = ch; o = r["out"]
    new = (o.get("proof") or "").rstrip()
    if not new or proof_sha(new) == sha or o.get("verified") is False or not isinstance(r.get("delta"), (int, float)):
        return None
    delta = float(r["delta"])
    if rnd == "r10b":                                                                                                          
        base = _r10b_input_record(shadir, n)
        if base is None:
            return None
        delta += float(base["delta"])
    if not delta > 0:
        return None
    try:
        s_new, s_cur = float(o["score"]), float(cur.get("score") if cur.get("score") is not None else 33.33)
    except (KeyError, TypeError, ValueError):
        return None
    if not (math.isfinite(s_new) and s_new > s_cur + WRITEBACK_EPS):
        return None
    if row["statement"].strip() not in new or not check_forbidden_ok(new):
        return None
    compat = o.get("compat") if isinstance(o.get("compat"), dict) else None
    if compat is None and isinstance(o.get("Z"), (int, float)) and o["Z"] >= 100:                                          
        from probe.verify_candidates import newest_first
        compat = {v: True for v in newest_first(row["version_info"])}
    nb = {"score": s_new, "proof": new, "tokens": o.get("tokens"), "heartbeats": o.get("heartbeats"), "L": o.get("L"), "H": o.get("H"),
          "Z": o.get("Z"), "compat": compat}
    if isinstance(o.get("score_exact"), (int, float)):
        nb["score_exact"] = o["score_exact"]
    nb["writeback"] = {"from_sha": sha, "to_sha": proof_sha(new), "from_score": cur.get("score"), "delta": delta,
                       "polish": f"end-pipe/{safe(n)}/{sha}", "round": rnd, "stage": o.get("stage"),
                       "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    return cur, nb, r


def _writeback_logged(out: Path, n: str, to_sha: str) -> bool:
    return any(l.get("problem") == n and (l.get("to") or {}).get("sha") == to_sha for l in read_jsonl_records(Path(out) / WRITEBACK_LOG))


def _writeback_line(n: str, k, best: dict, wb: dict, recovered: bool = False) -> dict:
    return {"problem": n, "k": k, "from": {"sha": wb.get("from_sha"), "score": wb.get("from_score")},
            "to": {"sha": wb.get("to_sha"), **{x: best.get(x) for x in ("score", "tokens", "heartbeats", "L", "H", "Z")}},
            "delta": wb.get("delta"), "polish": wb.get("polish"), "round": wb.get("round", "end"), "stage": wb.get("stage"), "t": wb.get("t"),
            **({"recovered": True} if recovered else {})}


def writeback_reconcile(out: Path, n: str) -> bool:
    """A driver stopped between a write-back's state write and its log line: the row's best still carries its "writeback" record, so the
"""
    out = Path(out)
    b = state_of(out / "work", n).get("best") or {}
    wb = b.get("writeback")
    if not (isinstance(wb, dict) and wb.get("to_sha") and b.get("proof")) or proof_sha(b["proof"].strip()) != wb["to_sha"]:
        return False
    if _writeback_logged(out, n, wb["to_sha"]):
        return False
    with (out / WRITEBACK_LOG).open("a") as fh:
        fh.write(json.dumps(_writeback_line(n, None, b, wb, recovered=True), ensure_ascii=False) + "\n")
    return True


def writeback_row(out: Path, n: str, row: dict, k=None, pipe=None) -> dict | None:
    """The write-back (module docstring): the caller guarantees no session of row n is in flight. Order: state.json (atomic, with the



"""
    out = Path(out)
    writeback_reconcile(out, n)
    got = writeback_candidate(out, n, row, pipe=pipe) if pipe is not None else writeback_candidate(out, n, row)
    if not got:
        return None
    cur, nb, _r = got
    st = out / "work" / safe(n) / "state.json"
    raw = st.read_text()
    s = json.loads(raw)
    if proof_sha(((s.get("best") or {}).get("proof") or "").strip()) != nb["writeback"]["from_sha"]:
        return None                                                                                                                  
    s["best"] = nb
    (st.parent / "state.json.before-writeback").write_text(raw)
    atomic_write(st, json.dumps(s, ensure_ascii=False, indent=1))
    atomic_write(st.parent / "best.lean", nb["proof"].rstrip() + "\n")
    line = _writeback_line(n, k, nb, nb["writeback"])
    if not _writeback_logged(out, n, nb["writeback"]["to_sha"]):
        with (out / WRITEBACK_LOG).open("a") as fh:
            fh.write(json.dumps(line, ensure_ascii=False) + "\n")
    log(f"write-back {n[:40]}: agent best {cur.get('score')} -> {nb['score']} (end-pipe {nb['writeback']['round']} of {nb['writeback']['from_sha']}, "
        f"paired delta {nb['writeback']['delta']:+.4f}){'' if k is None else f'; session {k} starts from it'}")
    return line


                                                                                                                                        
def automation_card_check(a) -> str | None:
    """--automation-card on, before anything runs: the minimum is >= 0, the shipped card exists, its sha is AUTO_CARD_SHA16 and it holds
"""
    if int(getattr(a, "automation_card_min_ref_tokens", 0) or 0) < 0:
        return "--automation-card-min-ref-tokens must be >= 0"
    if getattr(a, "automation_card", DEFAULT_AUTO_CARD) != "on":
        return None
    try:
        raw = AUTO_CARD.read_bytes()
    except OSError as e:
        return f"--automation-card on: {AUTO_CARD} not readable ({type(e).__name__})"
    h = hashlib.sha256(raw).hexdigest()[:16]
    if h != AUTO_CARD_SHA16:
        return f"--automation-card on: {AUTO_CARD} is not the pinned card (sha256 {h} != {AUTO_CARD_SHA16})"
    hit = [b for b in BANNED if b in raw.decode("utf-8", "replace")]
    if hit:
        return f"--automation-card on: the card holds banned phrase(s) {hit}"
    return None


def method_flags(a) -> dict:
    """The frozen flags: --end-pipe-writeback as given; the automation card (a namespace without it: off), its minimum (0 while the card
"""
    cur = {f: getattr(a, f, None) for f in METHOD_FLAGS}
    on = getattr(a, "automation_card", DEFAULT_AUTO_CARD) == "on"
    cur["automation_card"] = "on" if on else "off"
    cur["automation_card_min_ref_tokens"] = int(getattr(a, "automation_card_min_ref_tokens", 0) or 0) if on else 0
    cur["automation_card_sha16"] = AUTO_CARD_SHA16 if on else None
    cur["funind"] = "on" if funind_on(a) else "off"                                             
    return cur


def method_freeze(a, out: Path) -> str | None:
    """<out>/method_flags.json: --end-pipe-writeback and the automation card (method_flags) as the first `run` / `agent` call gave them; a



"""
    if getattr(a, "cmd", "run") not in ("run", "agent"):
        return None
    p = Path(out) / "method_flags.json"
    cur = method_flags(a)
    if p.exists():
        try:
            prev = json.loads(p.read_text())
        except (OSError, ValueError):
            prev = None
        if isinstance(prev, dict):
            prev = {k: v for k, v in prev.items() if k in METHOD_FLAGS or k in METHOD_FLAGS_ADDED_OFF or v not in METHOD_FLAGS_RETIRED_OFF}
            for k, v in METHOD_FLAGS_ADDED_OFF.items():                                                                    
                prev.setdefault(k, v)
            diff = sorted(k for k in set(prev) | set(cur) if prev.get(k) != cur.get(k))
            if diff:
                return (f"{p}: this out directory ran with " + ", ".join(f"{k}={prev.get(k)}" for k in diff) + "; this command gives "
                        + ", ".join(f"{k}={cur.get(k)}" for k in diff) + " (resume with the run's own flags, or use another --out)")
            return None
    atomic_write(p, json.dumps(cur, indent=1))
    return None


def end_stage(a, names: list[str], rows: dict, hbs: dict, clock: Clock) -> int | None:
    out = Path(a.out)
                                                                                                                                   
    seconds = min(clock.end_seconds - clock.dial_seconds, clock.left(clock.end_stop))
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
    rc = run_session(cmd, env, out / "logs" / "end.log", clock.end_stop + 300, now=clock.now)
    log(f"end stage exit {rc}")
    return rc


                                                                                                                                        
def dialect_on(a) -> bool:
    """--dialect on. The CLI default is DEFAULT_DIALECT; an args object built without the flag (tests and tools that wrap the stages, as
"""
    return getattr(a, "dialect", "off") == "on"


def funind_on(a) -> bool:
    """--funind on (open run 3). The CLI default is DEFAULT_FUNIND; an args object built without the flag reads off (as dialect_on)."""
    return getattr(a, "funind", "off") == "on"


def dialect_row_seconds(a) -> float:
    return float(getattr(a, "dialect_row_seconds", None) or DIALECT_ROW_SECONDS)


def _es_sha(text: str) -> str:
    """harness/endstage.sha (sha256 of the STRIPPED text, 16 hex digits): what the end stage's records carry (input_measured.sha)."""
    return hashlib.sha256((text or "").strip().encode()).hexdigest()[:16]


def seed_meter(dst: Path, sources) -> str | None:
    """Reuse this run's end-stage meter decision for a dialect process (b98): the first readable meter.json among `sources` with the direct


"""
    dst = Path(dst)
    if (dst / "meter.json").exists():
        return None
    for src in sources or ():
        try:
            m = json.loads(Path(src).read_text())
        except (OSError, ValueError):
            continue
        if isinstance(m, dict) and m.get("prefer", "direct") == "direct" and isinstance(m.get("tests"), dict) and m["tests"]:
            dst.mkdir(parents=True, exist_ok=True)
            (dst / "meter.json").write_text(json.dumps({"fallback": m.get("fallback"), "tests": m["tests"], "prefer": "direct",
                                                         "seeded_from": str(src)}, indent=1))
            return str(src)
    return None


def dialect_input(n: str, rows: dict, hbs: dict, prev: dict, run: Path) -> Path:
    """One dialect run directory: rows/r00.json ({problem}), finals.json (the input proof with its stored numbers only: the output then
"""
    run = Path(run); (run / "rows").mkdir(parents=True, exist_ok=True)
    fin = {k: prev.get(k) for k in ("score", "tokens", "heartbeats", "L", "H", "Z", "compat") if prev.get(k) is not None}
    (run / "rows" / "r00.json").write_text(json.dumps({"problem": n}))
    (run / "finals.json").write_text(json.dumps({n: dict(fin, proof=prev["proof"].rstrip() + "\n")}, ensure_ascii=False, indent=1))
    (run / "rows.jsonl").write_text(json.dumps(rows[n], ensure_ascii=False) + "\n")
    (run / "heartbeats.jsonl").write_text(json.dumps(hbs[n], ensure_ascii=False) + "\n")
    return run


def dialect_cmd(run: Path, out_dir: Path, seconds: float, extra=()) -> list[str]:
    return [sys.executable, "harness/dialect.py", "--run-dir", str(run), "--rows", str(Path(run) / "rows.jsonl"), "--heartbeats",
            str(Path(run) / "heartbeats.jsonl"), "--out", str(out_dir), "--jobs", "1", "--anon", "--seconds", str(int(seconds))] + list(extra)


def dialect_open_args(a, run: Path) -> list[str]:
    """rc2 (the operator-approved b98 adjustments (1) and (2)): the dialect pass under the open frozen config like the package's other




"""
    try:
        cfg = package_config_dict(bool(getattr(a, "hr", False)))
    except (SystemExit, OSError, ValueError) as e:
        raise RuntimeError(f"the open end config is not readable ({e})") from None
    if not isinstance(cfg.get("accept"), dict) or not cfg["accept"]:
        raise RuntimeError("the open end config has no accept block")
    p = Path(run) / "end_config_open.json"; p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(cfg, indent=1, ensure_ascii=False))
    args = ["--accept-config", str(p), "--funind", "on" if funind_on(a) else "off"]                                             
    if "t4" in (cfg.get("families") or ()):
        ops = [o for o in ((cfg.get("ops") or {}).get("t4") or ()) if isinstance(o, str) and o.strip()]
        if ops:
            args += ["--ops", "t4=" + ",".join(ops)]
    else:
        args += ["--t4", "off"]
    return args


def run_dialect_row(a, n: str, rows: dict, hbs: dict, prev: dict, run: Path, out_dir: Path, seconds: float, deadline: float, log_path: Path,
                    meters=(), pipelined: bool = False, now=time.time) -> int | None:
    """One row's dialect pass (harness/dialect.py) on `prev` (a record with its proof) in its own process: the run directory, the reused



"""
    dialect_input(n, rows, hbs, prev, run)
    extra = dialect_open_args(a, run)
    Path(out_dir).mkdir(parents=True, exist_ok=True)
    seed_meter(out_dir, meters)
    env = base_env(a)
    env.update(compile_slots_env(DIALECT_SLOTS, out_dir))
    cmd = dialect_cmd(run, out_dir, seconds, extra)
    if pipelined:
        env["LRA_MEMGATE_RESERVE_MB"] = str(END_PIPE_RESERVE_MB)
        cmd = ["nice", "-n", str(END_PIPE_NICE)] + cmd
    return run_session(cmd, env, log_path, deadline, now=now)


def dialect_done(out: Path) -> dict:
    """{row: set of endstage shas} the dialect pass already covers: the input and the output of every valid dialect record (the pipeline's
"""
    out = Path(out); done: dict = {}
    files = list((out / "end-pipe").glob(f"*/*/{DIALECT_STAGE}/report.jsonl")) + list((out / "dialect").glob("*/*/report.jsonl"))
    for f in files:
        for r in read_jsonl_records(f):
            n = r.get("problem")
            if n and valid_end_record(r):
                s_ = done.setdefault(n, set())
                s_.add((r.get("input_measured") or {}).get("sha"))
                s_.add(_es_sha(r["out"]["proof"]))
    return done


def dialect_stage(a, names: list[str], rows: dict, hbs: dict, clock: Clock, runner=None) -> dict:
    """The dialect step after the end stage (b98, section 8): every row whose pick so far (export_candidate over end_outputs, never the







"""
    out = Path(a.out); work = out / "work"; root = out / "dialect"; root.mkdir(parents=True, exist_ok=True); (out / "logs").mkdir(exist_ok=True)
    stop = clock.dialect_deadline
    ends = end_outputs(out); done = dialect_done(out)
    idx = {n: i for i, n in enumerate(names)}
    todo, counts = [], {"covered": 0, "seed": 0}
    for n in names:
        src, c, proof = export_candidate(rows[n], ends.get(n), state_of(work, n).get("best"))
        if src == "seed":
            counts["seed"] += 1
            continue
        h = _es_sha(proof)
        if h in done.get(n, ()):
            counts["covered"] += 1
            continue
        todo.append((n, src, dict(c, proof=proof), h))
    slots = getattr(a, "compile_slots", None) or auto_slots()
    jobs = max(1, min(getattr(a, "dialect_jobs", None) or slots, slots))
    lock = threading.Lock()

    def default_runner(n, prev, d, seconds, deadline):
        return run_dialect_row(a, n, rows, hbs, prev, d / "input", d, seconds, deadline, out / "logs" / f"dialect.r{idx[n]:02d}.log",
                               meters=[out / "end" / "meter.json"] + sorted((out / "end-pipe" / safe(n)).glob("*/end/meter.json")),
                               now=clock.now)
    runner = runner or default_runner

    def one(item) -> None:
        n, src, prev, h = item
        st = "error"
        try:
            secs = min(dialect_row_seconds(a), stop - clock.now() - DIALECT_MARGIN_S)
            if secs < DIALECT_MIN_S:
                st = "skipped"
                return
            d = root / safe(n) / h
            t0 = clock.now()
            rc = runner(n, prev, d, secs, min(t0 + secs + DIALECT_MARGIN_S, stop))
            recs = [r for r in read_jsonl_records(d / "report.jsonl") if r.get("problem") == n and valid_end_record(r)]
            if not recs:
                st = "stopped" if rc is None else "no_record"
            else:
                st = "improved" if _es_sha(recs[-1]["out"]["proof"]) != h else "unchanged"
            log(f"dialect row#{idx[n]:02d} ({src}): {st}" + (f", paired delta {recs[-1]['delta']}" if recs else "") + f" in {clock.now() - t0:.0f} s")
        except Exception as e:                                                                                  
            log(f"dialect row#{idx[n]:02d}: failed ({type(e).__name__}: {e}); the row keeps its pick")
        finally:
            with lock:
                counts[st] = counts.get(st, 0) + 1
    room = stop - clock.now()
    log(f"dialect step: {len(todo)} row(s) to run ({counts['covered']} already through it, {counts['seed']} on the seed), {jobs} at once, "
        f"{room:.0f} s before its stop (the end of the end stage's window; reserved share {clock.dial_seconds:.0f} s), row tool phase "
        f"{dialect_row_seconds(a):.0f} s")
    if todo and room - DIALECT_MARGIN_S >= DIALECT_MIN_S:
        with ThreadPoolExecutor(jobs, thread_name_prefix="opk-dial") as ex:
            list(ex.map(one, todo))
    elif todo:
        counts["skipped"] = counts.get("skipped", 0) + len(todo)
    summ = {"rows": len(names), "run": len(todo), "jobs": jobs, "statuses": counts, "seconds_left_at_start": round(room, 1)}
    log(f"dialect step done: {summ}")
    return summ


                                                                                                                                        
def _out_score(o: dict) -> float:
    v = o.get("score_exact", o.get("score"))
    return float(v) if isinstance(v, (int, float)) else float("-inf")


def pipe_choice_record(shadir: Path, dial: bool = False) -> tuple[str, dict] | None:
    """(stage, report record) a pipelined best stands for (b94a, section 7): the second round's valid record when there is one (its input




"""
    recs = {}
    for st in PIPE_STAGES:
        for r in read_jsonl_records(shadir / st / "report.jsonl"):
            if r.get("problem") and valid_end_record(r):
                recs[st] = r
    if "r10b" in recs:
        st = "r10b"
    elif "end" in recs or "r10" in recs:
        st = max((st for st in ("end", "r10") if st in recs), key=lambda st: (_out_score(recs[st]["out"]), st == "end"))
    else:
        return None
    dr = recs.get(DIALECT_STAGE) if dial else None
    if dr and dr["problem"] == recs[st]["problem"] and (dr.get("input_measured") or {}).get("sha") == _es_sha(recs[st]["out"]["proof"]):
        st = DIALECT_STAGE
    return st, recs[st]


def pipe_choice(shadir: Path, dial: bool = True) -> tuple[str, dict] | None:
    """(row, out record) of pipe_choice_record (the export's pick: with the dialect stage's output, b98); dial=False: the choice before
"""
    ch = pipe_choice_record(shadir, dial=dial)
    return (ch[1]["problem"], ch[1]["out"]) if ch else None


def end_outputs(out: Path) -> dict:
    """{row: out record} from the end stage's report.jsonl (the last record per row: it survives a stopped end stage), merged over the


"""
    res = {}
    work = out / "work"
    for rowdir in sorted(p for p in (out / "end-pipe").glob("*") if p.is_dir()):
        recs = {}                                                                       
        for shadir in sorted(p for p in rowdir.glob("*") if p.is_dir()):
            ch = pipe_choice(shadir)                                                                         
            if ch:
                recs[shadir.name] = ch
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
                                                                                                                                     
                                                                                                                                        
                                                                                                                                       
                                                                                                                                      
                                                                                                                                      
                                                                                            
    base: dict = {}
    take: dict = {}
    files = ([(f, f.parent.name) for f in sorted((out / "dialect").glob("*/*/report.jsonl"))]
             + [(f, None) for f in sorted((out / "end-pipe").glob(f"*/*/{DIALECT_STAGE}/report.jsonl"))])
    for f, dir_sha in files:
        last = None
        for r in read_jsonl_records(f):
            n = r.get("problem")
            if not n or not valid_end_record(r):
                continue
            if n not in base:
                base[n] = ((res.get(n) or {}).get("proof") or ((state_of(work, n).get("best") or {}).get("proof")) or "").strip()
            h = (r.get("input_measured") or {}).get("sha")
            if base[n] and h == _es_sha(base[n]) and (dir_sha is None or h == dir_sha):
                last = r
        if last is not None and (last["problem"] not in take or _out_score(last["out"]) > _out_score(take[last["problem"]])):
            take[last["problem"]] = last["out"]
    res.update(take)
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
        recs.append(rec)
    t_audit = time.time(); jobs = 0
    if do_audit:
        write_proofs(out, recs)                                                                                             

        def one(k: int):                                                                                            
            rec = recs[k]; n = rec["name"]; row = rows[n]
            cands, best = [(rec["source"], rec["proof"].rstrip())], {}
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
                if rec.get("source") == "normalize":                                                                    
                    f = rec.get("normalized_from")
                    taken_from[f] = taken_from.get(f, 0) - 1; gain_sum -= float(rec.get("normalize_gain") or 0)
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
    ap.add_argument("cmd", choices=["run", "agent", "end", "normalize", "export"])
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
    ap.add_argument("--workers", type=int, default=DEFAULT_WORKERS,
                    help="sessions at once (default 11: the official run 2 recipe, 2026-11-01)")
    ap.add_argument("--max-sessions", type=int, default=DEFAULT_MAX_SESSIONS,
                    help="sessions per row (default 12: the 48 h deadline and the room schedule decide how many each row gets)")
    ap.add_argument("--min-session-seconds", type=float, default=900, help="no session starts with less agent time left")
    ap.add_argument("--kv-guard", choices=("off", "on"), default=DEFAULT_KV_GUARD,
                    help="2026-11-01 (default on; docs/open_kv_guard.md): before a session starts, read vLLM's /metrics on --base-url's server "
                         f"(the sessions' key) and hold the start while the KV cache use >= {KV_GUARD_HOLD} (until < {KV_GUARD_RELEASE}) or requests "
                         f"wait while preemptions rose within {KV_GUARD_PREEMPT_S:.0f} s; re-checked every {KV_GUARD_RECHECK_S:.0f} s, never below "
                         f"--workers - {KV_GUARD_FLOOR_GAP} sessions in flight (at least 1), one start per {KV_GUARD_MAX_HOLD_S / 60:.0f} min of a "
                         f"hold; unreadable metrics (or no page within {2 * KV_GUARD_TIMEOUT_S:.0f} s): no gate (as off). Running sessions are never stopped")
    ap.add_argument("--session-max-seconds", type=_nonneg_seconds, default=0.0,
                    help="per-session wall cap (default 0 = off): a session still running this long after its start is stopped as at the "
                         "agent deadline (SIGTERM, then SIGKILL; its banked best stays)")
    ap.add_argument("--kv-shed", choices=("off", "on"), default=DEFAULT_KV_SHED,
                    help=f"b105 (2026-11-01, default {DEFAULT_KV_SHED}; docs/open_kv_guard.md section 6): under SUSTAINED KV pressure (KV >= "
                         f"{SHED_KV} in every reading for {SHED_S:.0f} s, or requests waiting while preemptions rose within "
                         f"{KV_GUARD_PREEMPT_S:.0f} s for {SHED_S:.0f} s; the KV guard's /metrics reads) with more than --workers - "
                         f"{KV_GUARD_FLOOR_GAP} sessions in flight, ask ONE session to end at its next turn boundary: the one with the largest "
                         f"last prompt, >= {SHED_MIN_AGE_S / 60:.0f} min old, not of the row shed last (a stop file <out>/{SHED_DIR}/<run id>.stop, "
                         f"agent.py --stop-file in every session; it ends as after its last turn, never dry); one per "
                         f"{SHED_COOLDOWN_S / 60:.0f} min, none while one is pending; never a signal")
    ap.add_argument("--session-max-context", type=_nonneg_int, default=DEFAULT_SESSION_MAX_CONTEXT, metavar="TOKENS",
                    help=f"b105 (default {DEFAULT_SESSION_MAX_CONTEXT}; 0 = off): agent.py --max-context-tokens TOKENS in every session: a session ends after a turn whose "
                         "prompt was >= TOKENS (at the turn boundary, as after its last turn; its banked best stays, the row's next session "
                         "starts with a fresh context)")
    ap.add_argument("--first-wave-stagger", type=_nonneg_seconds, default=DEFAULT_FIRST_WAVE_STAGGER, metavar="SECONDS",
                    help=f"b105 (default {DEFAULT_FIRST_WAVE_STAGGER:g}; 0 = off): at the agent stage's start, one session start per SECONDS (at the stage's 5 s passes) "
                         "until --workers are in flight or a session has ended, then the async ladder as before (the first wave's contexts "
                         "then do not grow in lockstep)")
    ap.add_argument("--job-seconds", type=float, default=48 * 3600)
    ap.add_argument("--started-at", type=float, default=None, help="job start (epoch seconds; default now): setup time counts")
    ap.add_argument("--end-seconds", type=float, default=DEFAULT_END_SECONDS,
                    help="the end stage's share of the job at the agent deadline (R5 clock; default 7200 s, 2026-10-31; was 14400)")
    ap.add_argument("--export-margin", type=float, default=EXPORT_MARGIN_S)
    ap.add_argument("--compile-slots", type=int, default=None, help="end stage compile slots (default auto_slots())")
    ap.add_argument("--end-jobs", type=int, default=None, help="end stage rows in flight (default = compile slots)")
    ap.add_argument("--end-pipeline", choices=("off", "on"), default=DEFAULT_END_PIPELINE,
                    help="docs/open_end_pipeline.md (default on since 2026-10-31; off restores the old timeline): polish every idle row's current "
                         "best with the end stage during the agent stage; the end stage at the agent deadline then covers only the rows "
                         "whose current best has no finished polish")
    ap.add_argument("--end-pipe-jobs", type=int, default=END_PIPE_JOBS, help="pipelined end-stage rows at once during the agent stage")
    ap.add_argument("--end-pipe-row-s", type=float, default=END_PIPE_ROW_S, help="one pipelined row's end-stage clock (R5 seconds)")
    ap.add_argument("--end-pipe-slots", type=int, default=END_PIPE_SLOTS, help="compile slots of the pipelined end stage (its own pool)")
    ap.add_argument("--end-pipe-r10", choices=("off", "on"), default=END_PIPE_R10,
                    help="docs/open_end_pipeline.md section 7 (default on, b94a): after a pipelined row's open polish, the closed final's r10 end "
                         "stage ($0) on it, then a second round on an improved output; accept-gated, the export takes the last valid round")
    ap.add_argument("--end-pipe-r10-jobs", type=int, default=END_PIPE_R10_JOBS, help="rows in the r10 rounds at once (their own pool)")
    ap.add_argument("--end-pipe-r10-row-s", type=float, default=END_PIPE_R10_ROW_S, help="one row's clock for both r10 rounds (seconds)")
    ap.add_argument("--end-pipe-r10-slots", type=int, default=END_PIPE_R10_SLOTS, help="compile slots per r10 job (its own pool)")
    ap.add_argument("--end-pipe-writeback", choices=("off", "on"), default=DEFAULT_END_PIPE_WRITEBACK,
                    help="b94b (default on; acts only with --end-pipeline on): right before a row's next session, the pipeline's valid polish of the "
                         "row's current agent best becomes its agent best when it beats it (paired delta > 0 on the all-pin meter, stored score "
                         f"+ more than {WRITEBACK_EPS}); <out>/writeback.jsonl; frozen per out directory")
    ap.add_argument("--automation-card", choices=("off", "on"), default=DEFAULT_AUTO_CARD,
                    help="open run 3 (default off): the opening of every session of a row that qualifies (--automation-card-min-ref-tokens) gets "
                         "the shipped automation card (harness/open_card_automation.md, sha pinned; agent.py --open-card); frozen per out directory")
    ap.add_argument("--automation-card-min-ref-tokens", type=int, default=DEFAULT_AUTO_CARD_MIN_REF_TOKENS, metavar="N",
                    help="with --automation-card on: only rows whose reference proof_length (rows file) is at least N get the card (default 0: "
                         "every row); frozen per out directory with the card")
    ap.add_argument("--hr", action="store_true", help="also run the opt-in family hr")
    ap.add_argument("--no-normalize", dest="normalize", action="store_false", default=True,
                    help="no lexer-normalizer step after the end stage (and no time reserved for it); export ignores normalize.jsonl")
    ap.add_argument("--no-end-stages", action="store_true",
                    help="skip the end stage, the dialect step and normalize after the agent stage; the job clock does not change (post_fast/CHANGE.md)")
    ap.add_argument("--normalize-seconds", type=float, default=NORMALIZE_SECONDS,
                    help="the normalize step's share of the job, reserved after the end stage (the agent deadline moves earlier by it)")
    ap.add_argument("--normalize-row-seconds", type=float, default=NORMALIZE_ROW_SECONDS, help="wall bound of one row's normalize step")
    ap.add_argument("--dialect", choices=("off", "on"), default=DEFAULT_DIALECT,
                    help="b98 (docs/open_end_pipeline.md section 8): the model-free dialect pass (harness/dialect.py, accept-gated by the end "
                         "stage) as the eager pipeline's last stage after the r10 rounds and after the end stage on rows not yet through it, "
                         f"inside the end stage's window (default {DEFAULT_DIALECT})")
    ap.add_argument("--funind", choices=("off", "on"), default=DEFAULT_FUNIND,
                    help="open run 3 (default on; acts only with --dialect on): the funind family (harness/funind.py: deterministic "
                         "fun_induction rewrites of an induction block, probe-checked, accept-gated like every family) first in the dialect "
                         "pass's tool phase; frozen per out directory")
    ap.add_argument("--dialect-row-seconds", type=float, default=DIALECT_ROW_SECONDS,
                    help="the dialect pass's tool-phase wall per row (its process stops DIALECT_MARGIN_S later)")
    ap.add_argument("--dialect-jobs", type=int, default=None, help="rows in the dialect step at once after the end stage (default: the compile slots)")
    ap.add_argument("--dialect-seconds", type=float, default=DIALECT_SECONDS,
                    help="rc2: the dialect step's reserved share after the end stage, taken from the end stage's window (--end-seconds; the "
                         f"end stage stops this much earlier, the agent deadline does not move; at most --end-seconds; default {DIALECT_SECONDS:.0f})")
    ap.add_argument("--keep-local-ref", action="store_true", help="keep the local reference-heartbeat table (dev rows only)")
                                                                                        
    ap.add_argument("--no-compact-tool-json", dest="compact_tool_json", action="store_false", default=True,
                    help="P1 off: tool results as spaced, \\u-escaped JSON as before (default: agent.py --compact-tool-json)")
    ap.add_argument("--no-skeleton-combinator-holes", dest="skeleton_combinator_holes", action="store_false", default=True,
                    help="P2 off: lean_skeleton's default hole reading (default: agent.py --skeleton-combinator-holes)")
    ap.add_argument("--connect-budget-seconds", type=float, default=CONNECT_BUDGET_S,
                    help="P3: per model call, how long a refused / failed connection waits for the server without using an attempt")
    ap.add_argument("--no-audit", dest="audit", action="store_false", default=True,
                    help="section S off: no axiom audit at export (the guard env stays); default: every row's proof audited on every pin")
    ap.add_argument("--schedule", choices=SCHEDULES, default=DEFAULT_SCHEDULE,
                    help="P5: agent-stage order after every row's first session: room (default: most (100 - best) / (sessions + 1) first, "
                         "x0.3 after 3 flat sessions in a row) or ladder (fewest sessions, then row order; the order before 2026-10-28)")
    return ap


def main(argv=None) -> int:
    os.environ.update(SORRY_GUARD_ENV)                                                                                          
    git_trust(os.environ)                                                                                                
    a = build_parser().parse_args(argv)
    if a.compile_slots is not None and a.compile_slots < 1:
        raise SystemExit("--compile-slots must be >= 1")
    if a.cmd == "normalize" and not a.normalize:
        raise SystemExit("normalize with --no-normalize")
    if getattr(a, "dialect_seconds", 0.0) < 0:
        raise SystemExit("--dialect-seconds must be >= 0")
    bad = automation_card_check(a)                         
    if bad:
        raise SystemExit(bad)
    names, rows, hbs = load_rows(a.rows, a.heartbeats)
    a.ref_tokens = {n: int(rows[n]["proof_length"]) for n in rows}                                                             
    if a.problems:
        unknown = [p for p in a.problems if p not in rows]
        if unknown:
            raise SystemExit(f"--problems: not in the rows file: {unknown}")
        names = [n for n in names if n in set(a.problems)]
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True); (out / "logs").mkdir(exist_ok=True)
    clk_p = out / "clock.json"
    if a.started_at is None and clk_p.exists():                                           
        a.started_at = json.loads(clk_p.read_text())["started_at"]
                                                                                                                                       
                                                                                                                                               
    try:
        prev_end = float(json.loads(clk_p.read_text())["end_seconds"]) if clk_p.exists() else None
    except (OSError, ValueError, TypeError, KeyError):
        prev_end = None
    if prev_end is not None and prev_end != float(a.end_seconds):
        log(f"resume: {clk_p} has --end-seconds {prev_end:.0f}, this command {float(a.end_seconds):.0f}: the agent deadline moves by "
            f"{prev_end - float(a.end_seconds):+.0f} s (pass the run's own flags to resume it unchanged)")
    a.started_at = time.time() if a.started_at is None else a.started_at
    norm_s = a.normalize_seconds if a.normalize else 0.0
    dial_s = min(float(getattr(a, "dialect_seconds", DIALECT_SECONDS)), float(a.end_seconds)) if dialect_on(a) else 0.0            
    bad = method_freeze(a, out)
    if bad:
        raise SystemExit(bad)
    clk_p.write_text(json.dumps({"started_at": a.started_at, "job_seconds": a.job_seconds, "end_seconds": a.end_seconds,
                                 "normalize_seconds": norm_s}))
    clock = Clock(a.started_at, a.job_seconds, a.end_seconds, a.export_margin, norm_seconds=norm_s,
                  dial_seconds=dial_s)                                                                        
    log(f"open package {a.cmd}: {len(names)} row(s), job end in {clock.left() / 3600:.2f} h, out {out}")
    if a.cmd in ("run", "agent"):
        if getattr(a, "automation_card", DEFAULT_AUTO_CARD) == "on":
            k = sum(1 for n in names if automation_card_for(a, n))
            log(f"automation card on (sha {AUTO_CARD_SHA16}, reference proof_length >= {int(a.automation_card_min_ref_tokens or 0)}): "
                f"{k} of {len(names)} row(s) get it")
        elif int(getattr(a, "automation_card_min_ref_tokens", 0) or 0) > 0:
            log("--automation-card-min-ref-tokens without --automation-card on: no row gets the card")
        if funind_on(a):
            log("funind on: the dialect pass runs the fun_induction family first (accept-gated)" if dialect_on(a) else
                "--funind on without --dialect on: the funind family does not run")
    if dial_s > 0 and a.cmd in ("run", "end"):
        log(f"dialect share: the last {dial_s:.0f} s of the end stage's {float(a.end_seconds):.0f} s window are the dialect step's "
            f"(end stage stop in {clock.left(clock.end_stop) / 3600:.2f} h, the step's stop in {clock.left(clock.dialect_deadline) / 3600:.2f} h)")
    rep_t = None
    pipe = EndPipe(a, rows, hbs, clock) if a.cmd == "run" and getattr(a, "end_pipeline", "off") == "on" else None
    if a.cmd in ("run", "agent"):
                                                                                                            
        wb = None
        if pipe and getattr(a, "end_pipe_writeback", DEFAULT_END_PIPE_WRITEBACK) == "on":
            for n in names:                                                                                         
                try:
                    if writeback_reconcile(out, n):
                        log(f"write-back {n[:40]}: log line recovered from the row's best")
                except Exception as e:                
                    log(f"write-back {n[:40]}: reconcile raised {type(e).__name__}: {e}")
            wb = lambda n, k: writeback_row(out, n, rows[n], k, pipe=pipe)              
        if pipe:
            res = (agent_stage(a, names, clock, on_idle=pipe.offer, set_busy=pipe.set_busy, before_start=wb) if wb else
                   agent_stage(a, names, clock, on_idle=pipe.offer, set_busy=pipe.set_busy))
        else:
            res = agent_stage(a, names, clock)
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
        if left and not a.no_end_stages:
            end_stage(a, left, rows, hbs, clock)
        if dialect_on(a) and not a.no_end_stages:                                                                                                               
            try:
                res = dialect_stage(a, names, rows, hbs, clock)
            except Exception as e:                
                log(f"dialect step failed ({type(e).__name__}: {e}); every row keeps its pick")
                res = {"error": f"{type(e).__name__}: {e}"[:500]}
            try:
                (out / "dialect_stage.json").write_text(json.dumps(res, indent=1))
            except OSError as e:
                log(f"dialect_stage.json not written: {e}")
    if a.cmd in ("run", "end", "normalize") and a.normalize and not a.no_end_stages:                                                        
        try:                                                                                                      
            res = normalize_stage(a, names, rows, clock)
        except Exception as e:                
            log(f"normalize step failed ({type(e).__name__}: {e}); export takes only the rows it recorded as improved")
            res = {"error": f"{type(e).__name__}: {e}"[:500]}
        try:
            (out / "normalize_stage.json").write_text(json.dumps(res, indent=1))
        except OSError as e:
            log(f"normalize_stage.json not written: {e}")
    if a.cmd in ("run", "end", "normalize", "export"):                                                                            
        export(a, names, rows, deadline=max(clock.job_end - AUDIT_WRITE_S, time.time() + AUDIT_MIN_S))
    finish_token_report(rep_t, clock)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
