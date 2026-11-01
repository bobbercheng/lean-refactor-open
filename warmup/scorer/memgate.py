"""Memory admission gate for every Lean compile (2026-10-07): before each heavy Lean program starts, check
available memory; when there is not enough, hold the program until enough memory is available.

`run_lean(cmd, **kw)` is a drop-in for `subprocess.run(cmd, **kw)` on `lake env lean …` commands:
  1. under an exclusive file lock (so concurrent harness processes cannot all pass the check at once), read MemAvailable;
  2. subtract the memory already granted to compiles that started in the last RAMP_S seconds (a Lean process takes up to ~a minute
     to reach its working size, so MemAvailable does not yet reflect it);
  3. launch only if what is left >= need (the compile's own -M cap, LRA_LEAN_MEMORY_MB) + reserve (LRA_MEMGATE_RESERVE_MB);
     otherwise release the lock, wait POLL_S seconds and retry, logging to stderr once a minute while held;
  4. record the grant in a small ledger (pid, MB, start time) and remove it when the compile ends (success, error or timeout).
The wait does not count against the compile's own timeout.
"""
from __future__ import annotations

import fcntl, json, os, subprocess, sys, time
from pathlib import Path

LOCK = Path(os.environ.get("LRA_MEMGATE_DIR", "/tmp")) / "lra-memgate.lock"
LEDGER = LOCK.with_suffix(".json")
RAMP_S = 60
POLL_S = 5


def _cgroup_avail_mb() -> int | None:
    """Room left inside this process's own cgroup (cgroup v2 memory.max - memory.current), or None when unlimited.
    Needed because a systemd service's MemoryMax is far below the machine's MemAvailable: on 2026-10-07 19:42 the gate admitted
    compiles on 64 GB of global headroom while lra-mine (MemoryMax 36 G) had none, and the cgroup OOM killer took two of them."""
    try:
        rel = [l.split(":", 2)[2].strip() for l in open("/proc/self/cgroup") if l.startswith("0::")][0]
        base = Path("/sys/fs/cgroup") / rel.lstrip("/")
        best = None
        for d in [base, *base.parents]:      # the tightest limit on the way up the hierarchy
            mx = d / "memory.max"; cur = d / "memory.current"
            if mx.exists() and cur.exists():
                m = mx.read_text().strip()
                if m != "max":
                    used = int(cur.read_text().strip())
                    st = d / "memory.stat"   # working set = current - inactive file cache (reclaimable; mmapped .olean pages)
                    if st.exists():
                        for line in st.read_text().splitlines():
                            if line.startswith("inactive_file "):
                                used -= int(line.split()[1]); break
                    room = (int(m) - used) // (1024 * 1024)
                    best = room if best is None else min(best, room)
            if str(d) == "/sys/fs/cgroup":
                break
        return best
    except Exception:  # noqa: BLE001
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
    except Exception:  # noqa: BLE001
        return ""


def _avail_mb(grants: list[dict] | None = None, now: float = 0.0) -> int:
    """Room for one more compile: min(machine MemAvailable - every ramping grant, own cgroup room - ramping grants IN THIS cgroup).
    A compile still ramping up in another service does not use this service's MemoryMax, so counting it against the cgroup term
    held the LR-eval scorer for up to 650 s with 86 GB free (2026-10-07 20:45)."""
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
    except Exception:  # noqa: BLE001
        return []
    return [g for g in grants if _alive(g.get("pid", -1))]


def _save(grants: list[dict]) -> None:
    tmp = LEDGER.with_suffix(".tmp")
    tmp.write_text(json.dumps(grants))
    tmp.replace(LEDGER)


def acquire(need_mb: int | None = None, reserve_mb: int | None = None, label: str = "") -> str:
    # Claim per compile (not the hard cap): measured 2026-10-07, the heaviest legitimate compile (PutnamBench references, full
    # Mathlib) peaks at 6.1 GB RSS; ArkLib ~4 GB; Strata/CSLib/PhysLib <= 2 GB. The hard per-process cap stays LRA_LEAN_MEMORY_MB
    # (16 GB, Lean -M); the claim + LRA_MEMGATE_RESERVE_MB (8 GB) covers a compile growing past its claim up to the cap.
    need = int(need_mb or os.environ.get("LRA_MEMGATE_CLAIM_MB", "8000"))
    reserve = int(reserve_mb or os.environ.get("LRA_MEMGATE_RESERVE_MB", "8000"))
    token = f"{os.getpid()}-{time.time_ns()}"
    waited, last_log = 0.0, 0.0
    LOCK.touch(exist_ok=True)
    while True:
        with open(LOCK) as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)
            grants = _load()
            now = time.time()
            ramping = sum(g["mb"] for g in grants if now - g["t"] < RAMP_S)
            left = _avail_mb(grants, now)
            if left >= need + reserve:
                grants.append({"token": token, "pid": os.getpid(), "mb": need, "t": now, "label": label[:60], "cg": _my_cgroup()})
                _save(grants)
                if waited:
                    print(f"[memgate] admitted after {waited:.0f}s hold ({left} MB free after ramping grants)", file=sys.stderr, flush=True)
                return token
            fcntl.flock(lk, fcntl.LOCK_UN)
        if waited - last_log >= 60 or waited == 0:
            print(f"[memgate] HOLD {label[:40]}: need {need}+{reserve} MB, have {left} MB "
                  f"({ramping} MB granted to compiles still ramping up; same-cgroup grants count against MemoryMax)", file=sys.stderr, flush=True)
            last_log = waited
        time.sleep(POLL_S)
        waited += POLL_S


def release(token: str) -> None:
    LOCK.touch(exist_ok=True)
    with open(LOCK) as lk:
        fcntl.flock(lk, fcntl.LOCK_EX)
        _save([g for g in _load() if g.get("token") != token])


def run_lean(cmd, **kw):
    """subprocess.run for a Lean compile, admitted by the memory gate first."""
    token = acquire(label=" ".join(str(c) for c in cmd[-1:]))
    try:
        return subprocess.run(cmd, **kw)
    finally:
        release(token)
