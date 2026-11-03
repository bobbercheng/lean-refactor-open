"""Memory admission gate for every Lean compile (operator 2026-10-07: "Before you launch each heavy lean program you need to check













"""
from __future__ import annotations

import errno, fcntl, json, os, signal, subprocess, sys, threading, time
from contextlib import contextmanager
from pathlib import Path

LOCK = Path(os.environ.get("LRA_MEMGATE_DIR", "/tmp")) / "lra-memgate.lock"
LEDGER = LOCK.with_suffix(".json")
RAMP_S = 60
POLL_S = 5
RELAX_S = int(os.environ.get("LRA_MEMGATE_RELAX_S", "600"))
MAX_WAIT_S = int(os.environ.get("LRA_MEMGATE_MAX_WAIT_S", "1800"))


                                                                                                                                        
                                                                                                                                     
_NO_FLOCK = {errno.ENOSYS, errno.ENOLCK, errno.EOPNOTSUPP, errno.EINVAL, getattr(errno, "ENOTSUP", errno.EOPNOTSUPP)}
_FALLBACK = threading.Lock()
_FALLBACK_WARNED = []


@contextmanager
def _locked(path: Path):
    """The gate's exclusive lock: flock on `path`, or the in-process fallback when the filesystem has no flock."""
    with open(path) as lk:
        try:
            fcntl.flock(lk, fcntl.LOCK_EX)
        except OSError as e:
            if e.errno not in _NO_FLOCK:
                raise
            if not _FALLBACK_WARNED:
                _FALLBACK_WARNED.append(1)
                print(f"[memgate] flock unavailable on {path} ({e}); the gate's lock falls back to this process only", file=sys.stderr, flush=True)
            with _FALLBACK:
                yield
            return
        yield


def _working_set(current: int, stat: str) -> int:
    """Bytes of a cgroup's memory.current that a new compile cannot get back: current minus the reclaimable file cache.


"""
    f = {}
    for line in stat.splitlines():
        k, _, v = line.partition(" ")
        if k in ("inactive_file", "file", "file_mapped") and v.strip().isdigit():
            f[k] = int(v)
    reclaim = max(f.get("inactive_file", 0), f.get("file", 0) - f.get("file_mapped", 0))
    return max(0, current - max(0, reclaim))


def _cgroup_avail_mb() -> int | None:
    """Room left inside this process's own cgroup (cgroup v2 memory.max - memory.current), or None when unlimited.

"""
    try:
        rel = [l.split(":", 2)[2].strip() for l in open("/proc/self/cgroup") if l.startswith("0::")][0]
        base = Path("/sys/fs/cgroup") / rel.lstrip("/")
        best = None
        for d in [base, *base.parents]:                                                      
            mx = d / "memory.max"; cur = d / "memory.current"
            if mx.exists() and cur.exists():
                m = mx.read_text().strip()
                if m != "max":
                    st = d / "memory.stat"
                    used = _working_set(int(cur.read_text().strip()), st.read_text() if st.exists() else "")
                    room = (int(m) - used) // (1024 * 1024)
                    best = room if best is None else min(best, room)
            if str(d) == "/sys/fs/cgroup":
                break
        if best is None and os.environ.get("LRA_MEMGATE_CGROUP_V1") == "1":
            return _cgroup_v1_avail_mb()
        return best
    except Exception:                                                       
        return _cgroup_v1_avail_mb() if os.environ.get("LRA_MEMGATE_CGROUP_V1") == "1" else None


def _cgroup_v1_avail_mb(proc_cgroup: str = "/proc/self/cgroup", root: str = "/sys/fs/cgroup") -> int | None:
    """cgroup v1 (opt-in, LRA_MEMGATE_CGROUP_V1=1, set by run.sh for the organizers' server; 2026-10-31): room left under the tightest

"""
    try:
        with open(proc_cgroup) as fh:
            rel = next((l.split(":", 2)[2].strip() for l in fh if "memory" in l.split(":", 2)[1].split(",")), None)
        if rel is None:
            return None
        base = Path(root) / "memory" / rel.lstrip("/")
        best = None
        for d in [base, *base.parents]:
            lim, use = d / "memory.limit_in_bytes", d / "memory.usage_in_bytes"
            if lim.exists() and use.exists():
                m = int(lim.read_text().strip())
                if m < (1 << 60):                                                         
                    st = (d / "memory.stat").read_text() if (d / "memory.stat").exists() else ""
                    f = {k: int(v) for k, _, v in (l.partition(" ") for l in st.splitlines()) if v.strip().isdigit()}
                    reclaim = f.get("total_inactive_file", f.get("inactive_file", 0))
                    room = (m - max(0, int(use.read_text().strip()) - reclaim)) // (1024 * 1024)
                    best = room if best is None else min(best, room)
            if str(d) == str(Path(root) / "memory"):
                break
        return best
    except Exception:                
        return None


def _global_avail_mb() -> int:
    with open("/proc/meminfo") as f:
        for line in f:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) // 1024
    return 0


def _my_cgroup() -> str:
    try:
        return [l.split(":", 2)[2].strip() for l in open("/proc/self/cgroup") if l.startswith("0::")][0]
    except Exception:                
        return ""


def _avail_mb(grants: list[dict] | None = None, now: float = 0.0) -> int:
    """Room for one more compile: min(machine MemAvailable - every ramping grant, own cgroup room - ramping grants IN THIS cgroup).

"""
    grants = grants or []
    ramp = [g for g in grants if now - g["t"] < RAMP_S]
    left = _global_avail_mb() - sum(g["mb"] for g in ramp)
    cg = _cgroup_avail_mb()
    if cg is not None:
        me = _my_cgroup()
        left = min(left, cg - sum(g["mb"] for g in ramp if g.get("cg") == me))
    return left


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
        return True
    except OSError:
        return False


def _load() -> list[dict]:
    try:
        grants = json.loads(LEDGER.read_text())
    except Exception:                
        return []
    return [g for g in grants if _alive(g.get("pid", -1))]


def _save(grants: list[dict]) -> None:
    tmp = LEDGER.with_suffix(".tmp")
    tmp.write_text(json.dumps(grants))
    tmp.replace(LEDGER)


def acquire(need_mb: int | None = None, reserve_mb: int | None = None, label: str = "") -> str:
                                                                                                                              
                                                                                                                                 
                                                                                                                        
    need = int(need_mb or os.environ.get("LRA_MEMGATE_CLAIM_MB", "8000"))
    reserve = int(reserve_mb or os.environ.get("LRA_MEMGATE_RESERVE_MB", "8000"))
    token = f"{os.getpid()}-{time.time_ns()}"
    waited, last_log = 0.0, 0.0
    LOCK.touch(exist_ok=True)
    while True:
        with _locked(LOCK):
            grants = _load()
            now = time.time()
            ramping = sum(g["mb"] for g in grants if now - g["t"] < RAMP_S)
            left = _avail_mb(grants, now)
            relaxed = waited >= RELAX_S
            if left >= need + (0 if relaxed else reserve):
                grants.append({"token": token, "pid": os.getpid(), "mb": need, "t": now, "label": label[:60], "cg": _my_cgroup()})
                _save(grants)
                if waited:
                    print(f"[memgate] admitted after {waited:.0f}s hold ({left} MB free after ramping grants"
                          f"{'; reserve waived after the relax limit' if relaxed and left < need + reserve else ''})", file=sys.stderr, flush=True)
                return token
        if waited >= MAX_WAIT_S:
            print(f"[memgate] GIVE UP {label[:40]} after {waited:.0f}s: need {need} MB, have {left} MB; reported as a timed-out compile",
                  file=sys.stderr, flush=True)
            raise subprocess.TimeoutExpired(label or "lean", waited)
        if waited - last_log >= 60 or waited == 0:
            print(f"[memgate] HOLD {label[:40]}: need {need}+{reserve} MB, have {left} MB "
                  f"({ramping} MB granted to compiles still ramping up; same-cgroup grants count against MemoryMax)", file=sys.stderr, flush=True)
            last_log = waited
        time.sleep(POLL_S)
        waited += POLL_S


def release(token: str) -> None:
    LOCK.touch(exist_ok=True)
    with _locked(LOCK):
        _save([g for g in _load() if g.get("token") != token])


def run_lean(cmd, **kw):
    """subprocess.run for a Lean compile, admitted by the memory gate first."""
    token = acquire(label=" ".join(str(c) for c in cmd[-1:]))
    try:
                                                                                                                        
                                                                                                                    
        timeout = kw.pop("timeout", None)
        capture = kw.pop("capture_output", False)
        if capture:
            kw.setdefault("stdout", subprocess.PIPE); kw.setdefault("stderr", subprocess.PIPE)
        with subprocess.Popen(cmd, start_new_session=True, **kw) as proc:
            try:
                out, err = proc.communicate(timeout=timeout)
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                proc.communicate()
                raise
            return subprocess.CompletedProcess(proc.args, proc.returncode, out, err)
    finally:
        release(token)
