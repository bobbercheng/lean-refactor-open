#!/usr/bin/env python3
"""Small helpers of setup.sh / run.sh on the organizers' server (2026-10-31; README.md). Standard library only (the self-check imports












"""
from __future__ import annotations

import argparse, fcntl, hashlib, json, os, re, shlex, shutil, signal, subprocess, sys, time, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
JOB_MAX_S = 48 * 3600
PKG_WORKERS = 14                                                                                                     
WORKERS_FLOOR = 4
CPU_RESERVE = 8                                                                                                   
SLOTS_MIN, SLOTS_MAX, SLOT_GB = 3, 32, 8                                           


def kv(**pairs) -> str:
    return "\n".join(f"{k}={shlex.quote('' if v is None else str(v))}" for k, v in pairs.items())


                                                                                                                                       
def usable_cpus() -> int:
    try:
        return len(os.sched_getaffinity(0))                                                       
    except (AttributeError, OSError):
        return os.cpu_count() or 4


def cgroup_limit_bytes(proc_cgroup: str = "/proc/self/cgroup", root: str = "/sys/fs/cgroup") -> int | None:
    """The tightest cgroup memory limit of this process (v2 memory.max, else v1 memory.limit_in_bytes), None when unlimited."""
    best = None
    try:
        lines = Path(proc_cgroup).read_text().splitlines()
    except OSError:
        return None
    for l in lines:
        parts = l.split(":", 2)
        if len(parts) != 3:
            continue
        hid, ctrls, rel = parts
        if hid == "0" and ctrls == "":
            base, files = Path(root) / rel.lstrip("/"), ("memory.max",)
            stop = Path(root)
        elif "memory" in ctrls.split(","):
            base, files = Path(root) / "memory" / rel.lstrip("/"), ("memory.limit_in_bytes",)
            stop = Path(root) / "memory"
        else:
            continue
        for d in [base, *base.parents]:
            for f in files:
                try:
                    v = (d / f).read_text().strip()
                except OSError:
                    continue
                if v.isdigit() and int(v) < (1 << 60):
                    best = int(v) if best is None else min(best, int(v))
            if d == stop or str(d) == "/":
                break
    return best


def mem_available_gb(meminfo: str = "/proc/meminfo") -> float:
    try:
        kb = next(int(l.split()[1]) for l in Path(meminfo).read_text().splitlines() if l.startswith("MemAvailable:"))
        return kb / 1024 / 1024
    except (OSError, StopIteration, ValueError):
        return 48.0


def sizing(cpus: int, node_cpus: int, mem_gb: float, limit_gb: float | None) -> dict:
    """WORKERS: the package default (14, not passed) unless the allocation has fewer than 14 + CPU_RESERVE CPUs, then cpus - 8, at least 4.


"""
    workers = None
    if cpus < PKG_WORKERS + CPU_RESERVE:
        workers = max(WORKERS_FLOOR, min(PKG_WORKERS, cpus - CPU_RESERVE))
    slots = None
    eff_mem = min(mem_gb, limit_gb) if limit_gb else mem_gb
    if cpus < node_cpus or (limit_gb and limit_gb < mem_gb):
        slots = max(SLOTS_MIN, min(SLOTS_MAX, cpus // 3, int(eff_mem // SLOT_GB)))
    return {"WORKERS": workers, "SLOTS": slots, "CPUS": cpus, "NODE_CPUS": node_cpus, "MEM_AVAIL_GB": round(mem_gb, 1),
            "CGROUP_LIMIT_GB": round(limit_gb, 1) if limit_gb else None}


def cmd_sizing(a) -> int:
    lim = cgroup_limit_bytes()
    print(kv(**sizing(usable_cpus(), os.cpu_count() or usable_cpus(), mem_available_gb(), lim / 2**30 if lim else None)))
    return 0


                                                                                                                                       
def slurm_times(job_id: str | None = None, runner=subprocess.run) -> tuple[float | None, float | None]:
    """(start, end) epoch seconds of the Slurm job from squeue, (None, None) outside Slurm or when unknown."""
    job_id = job_id or os.environ.get("SLURM_JOB_ID")
    if not job_id or not shutil.which("squeue"):
        return None, None
    try:
        out = runner(["squeue", "-h", "-j", str(job_id), "-o", "%S %e"], capture_output=True, text=True, timeout=30).stdout.split()
    except (OSError, subprocess.SubprocessError):
        return None, None
    res = []
    for s in (out + [None, None])[:2]:
        try:
            res.append(time.mktime(time.strptime(s, "%Y-%m-%dT%H:%M:%S")) if s else None)
        except (ValueError, TypeError):
            res.append(None)
    return res[0], res[1]


STAMP = "orgjob.json"                                                                                                    
JOB_ID_VARS = ("LRA_JOB_ID", "SLURM_JOB_ID", "PBS_JOBID", "LSB_JOBID", "FLUX_JOB_ID")
SHORT_LEFT_S = 1200                                                                                                               


def current_job_id(env=None) -> str:
    """The scheduler's job id of this process (Slurm, PBS, LSF, Flux; LRA_JOB_ID overrides), "" outside a scheduler."""
    env = os.environ if env is None else env
    return next((str(env[v]) for v in JOB_ID_VARS if env.get(v)), "")


def _read_json(p: Path) -> dict:
    try:
        d = json.loads(Path(p).read_text())
        return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def _utc(t: float) -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t))


def job_clock(out: Path, now: float, start: float | None = None, job: float | None = None, safety: float = 600.0,
              slurm=(None, None), job_id: str = "", resume: bool = False, rows: str = "") -> dict:
    """The job clock (review 2026-11-01: an old runs/final/clock.json must never cut a new job short).







"""
    out = Path(out)
    clk, stamp = _read_json(out / "clock.json"), _read_json(out / STAMP)
    prev = clk.get("started_at") or stamp.get("started_at")
    prev = float(prev) if prev else None
    s_start, s_end = slurm
    stamp_job = str(stamp.get("job_id") or "")
    same_job = bool(job_id) and stamp_job == job_id and (not clk.get("started_at") or not stamp.get("started_at")
                                                          or int(float(clk["started_at"])) == int(float(stamp["started_at"])))
    notes = []
    if same_job and (stamp.get("job_arg") != (None if job is None else float(job)) or (rows and stamp.get("rows", rows) != rows)):
        same_job = False                                                                                                  
        notes.append(f"the same job {job_id} but another command (LRA_JOB_SECONDS or the rows file differ): a new run")
    if start is not None:
        source, st = "LRA_START", float(start)
        own = prev is not None and (resume or same_job or int(prev) == int(st))
    elif prev is not None and (same_job or resume):
        source, st, own = ("resumed (same job " + job_id + ")" if same_job else "resumed (LRA_RESUME=1)"), prev, True
    elif s_start and s_start <= now:
        source, st, own = "slurm", float(s_start), False
    else:
        source, st, own = "now", float(now), False
    if job is not None:
        jb = float(job)
    elif source.startswith("resumed"):
        jb = float(clk.get("job_seconds") or stamp.get("job_seconds") or (JOB_MAX_S - safety))
    else:
        jb = JOB_MAX_S - safety
    end = st + jb
    if s_end and s_end - safety < end:
        end = s_end - safety
        notes.append(f"capped at the Slurm job's end {_utc(s_end)} - {safety:.0f} s")
    if prev is None:
        action = "fresh"
    elif own:
        action = "resume"
    else:
        action = "set-aside"
        notes.append(f"{out} holds another run's state (clock started {_utc(prev)}"
                     + (f", job {stamp_job}" if stamp_job else ", no job id") + f"; this job: {job_id or 'no job id'}): "
                     "it is set aside, never resumed (LRA_RESUME=1 resumes it instead)")
    left = end - now
    if left <= 0 and not resume:
        action = "refuse"
        notes.append(f"the clock ({source}) ended {_utc(end)}, {-left:.0f} s ago: nothing to run (LRA_RESUME=1 runs on it anyway: the "
                     f"end stage and the export of what {out} saved; or LRA_START / LRA_OUT for a new clock)")
    elif left < SHORT_LEFT_S:
        notes.append(f"only {left:.0f} s left on this clock")
    return {"START": int(st), "JOB": int(end - st), "SOURCE": source, "JOB_END": int(end), "ACTION": action,
            "PREV_START": int(prev) if prev is not None else "", "NOTE": "; ".join(notes)}


def set_aside(out: Path, prev_start: int | str) -> Path:
    """Move a previous run's OUT to OUT.prev-<its start>[-n] (same filesystem: a rename) and leave OUT absent."""
    out = Path(out)
    base = f"{out.name}.prev-{prev_start or 'unknown'}"
    for k in range(100):
        dst = out.with_name(base if k == 0 else f"{base}-{k}")
        if not dst.exists():
            os.rename(out, dst)
            return dst
    raise OSError(f"no free name for {out} beside {base}")


def owner_alive(out: Path, me: int | None = None) -> int | None:
    """The pid of another run.sh still running on OUT (stamped by clock --apply on this host), else None."""
    st = _read_json(Path(out) / STAMP)
    try:
        pid = int(st.get("pid") or 0)
    except (TypeError, ValueError):
        return None
    if not pid or pid == me or st.get("host") != os.uname().nodename or not _alive(pid):
        return None
    try:
        cmd = Path(f"/proc/{pid}/cmdline").read_bytes().replace(b"\0", b" ").decode(errors="replace")
    except OSError:
        return None
    return pid if "run.sh" in cmd else None


def cmd_clock(a) -> int:
    out, now = Path(a.out), float(a.now) if a.now else time.time()
    resume = a.resume or os.environ.get("LRA_RESUME", "0") == "1"
    job_id = a.job_id if a.job_id is not None else current_job_id()
    pid = owner_alive(out, me=a.pid)
    if pid:
        print(kv(ACTION="refuse", NOTE=f"run.sh (pid {pid}) is still running on {out}", START="", JOB="", JOB_END="", SOURCE=""))
        return 3
    rec = job_clock(out, now, a.start, a.job, a.safety, slurm_times(), job_id=job_id, resume=resume, rows=a.rows or "")
    rec["SET_ASIDE"] = ""
    if a.apply and rec["ACTION"] == "set-aside":
        try:
            rec["SET_ASIDE"] = str(set_aside(out, rec["PREV_START"]))
        except OSError as e:
            rec["ACTION"], rec["NOTE"] = "refuse", rec["NOTE"] + f"; could not set it aside ({e}): move it yourself or set LRA_OUT"
    if a.apply and rec["ACTION"] != "refuse":
        out.mkdir(parents=True, exist_ok=True)
        old = _read_json(out / STAMP) if rec["ACTION"] == "resume" else {}
        stamp = {"job_id": job_id, "started_at": rec["START"], "job_seconds": rec["JOB"], "job_end": rec["JOB_END"], "source": rec["SOURCE"],
                 "job_arg": a.job, "rows": a.rows or "", "host": os.uname().nodename, "pid": a.pid or os.getppid(), "written_at": int(now),
                 "starts": int(old.get("starts", 0)) + 1}
        tmp = out / f".{STAMP}.{os.getpid()}"
        tmp.write_text(json.dumps(stamp) + "\n")
        os.replace(tmp, out / STAMP)
    print(kv(**rec))
    return 3 if rec["ACTION"] == "refuse" else 0


                                                                                                                                      
def flock_ok(d: Path) -> bool:
    try:
        d.mkdir(parents=True, exist_ok=True)
        p = d / f".flocktest-{os.getpid()}"
        with open(p, "a") as fh:
            fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
            fcntl.flock(fh, fcntl.LOCK_UN)
        p.unlink(missing_ok=True)
        return True
    except OSError:
        return False


def pick_fast_dir(candidates: list[str], tag: str) -> Path | None:
    """The first candidate (a writable directory where flock works) with a per-user, per-job subdirectory."""
    for c in candidates:
        if not c:
            continue
        base = Path(c)
        if not base.is_dir() or not os.access(base, os.W_OK | os.X_OK):
            continue
        d = base / tag
        if flock_ok(d):
            return d
    return None


def cmd_fastdir(a) -> int:
    user = os.environ.get("USER") or str(os.getuid())
    tag = f"lra-{re.sub(r'[^A-Za-z0-9_.-]', '_', user)}-{os.environ.get('SLURM_JOB_ID') or a.tag}"
    cands = [os.environ.get("LRA_FAST_DIR", ""), "/dev/shm", os.environ.get("TMPDIR", ""), "/tmp"]
    d = pick_fast_dir(cands, tag)
    if d is None:
        print("no directory with working flock among: " + " ".join(c for c in cands if c), file=sys.stderr)
        return 1
    print(d)
    return 0


def cmd_flocktest(a) -> int:
    ok = flock_ok(Path(a.dir))
    print(f"flock {'ok' if ok else 'NOT available'} in {a.dir}")
    return 0 if ok else 1


                                                                                                                                       
def models_ok(url: str, timeout: float = 5.0) -> bool:
    try:
        with urllib.request.urlopen(url.rstrip("/") + "/models", timeout=timeout) as r:
            return r.status == 200
    except (OSError, ValueError):
        return False


def cmd_ready(a) -> int:
    t_end = time.time() + a.timeout
    while time.time() < t_end:
        if models_ok(a.url):
            print(f"ready: {a.url}")
            return 0
        if a.pidfile and not _alive_file(a.pidfile):
            print(f"not ready: the server process ({a.pidfile}) is gone", file=sys.stderr)
            return 2
        time.sleep(a.poll)
    print(f"not ready after {a.timeout:.0f} s: {a.url}", file=sys.stderr)
    return 1


def _alive_file(pidfile: str) -> bool:
    try:
        os.kill(int(Path(pidfile).read_text().split()[0]), 0)
        return True
    except (OSError, ValueError, IndexError):
        return False


def tagged_pids(tag: str, proc_root: Path = Path("/proc")) -> list[int]:
    needle, me, out = f"LRA_ORG_JOB={tag}".encode(), os.getpid(), []
    for d in proc_root.iterdir():
        if not d.name.isdigit() or int(d.name) == me:
            continue
        try:
            if needle in (d / "environ").read_bytes().split(b"\0"):
                out.append(int(d.name))
        except OSError:
            continue
    return out


def cmd_reap(a) -> int:
    pids = tagged_pids(a.tag)
    for sig, wait_s in ((signal.SIGTERM, a.grace), (signal.SIGKILL, 0)):
        for p in pids:
            try:
                os.kill(p, sig)
            except OSError:
                pass
        t_end = time.time() + wait_s
        while wait_s and time.time() < t_end and any(_alive(p) for p in pids):
            time.sleep(1)
        pids = [p for p in pids if _alive(p)]
        if not pids:
            break
    print(f"reap {a.tag}: done")
    return 0


def _alive(pid: int) -> bool:
    try:
        os.kill(pid, 0)
    except OSError:
        return False
    try:                            
        return Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[0] != "Z"
    except (OSError, IndexError):
        return True


                                                                                                                                       
def promote(out: Path) -> str:
    """OUT/interim/proofs.jsonl becomes OUT/proofs.jsonl only if the latter does not exist (link: atomic, never over the export)."""
    src, dst = out / "interim" / "proofs.jsonl", out / "proofs.jsonl"
    if dst.exists():
        return "kept: proofs.jsonl exists (the export ran)"
    if not src.exists():
        return "nothing: no interim proofs.jsonl"
    tmp = out / f".proofs.interim.{os.getpid()}"
    shutil.copyfile(src, tmp)
    try:
        os.link(tmp, dst)
        res = f"promoted: {src} -> {dst}"
    except FileExistsError:
        res = "kept: proofs.jsonl appeared meanwhile (the export ran)"
    finally:
        tmp.unlink(missing_ok=True)
    return res


def cmd_promote(a) -> int:
    print(promote(Path(a.out)))
    return 0


                                                                                                                                       
TC_RE = re.compile(r"version (\d+\.\d+\.\d+(?:-rc\d+)?)")


def toolchain_name(d: Path, runner=subprocess.run) -> str | None:
    """elan's directory name for a toolchain directory: its own name when it is one (leanprover--lean4---v4.30.0), else from
"""
    if not (d / "bin" / "lean").exists():
        return None
    if d.name.startswith("leanprover--lean4---"):
        return d.name
    try:
        v = runner([str(d / "bin" / "lean"), "--version"], capture_output=True, text=True, timeout=60).stdout
    except (OSError, subprocess.SubprocessError):
        return None
    m = TC_RE.search(v or "")
    return f"leanprover--lean4---v{m.group(1)}" if m else None


def elan_link(eh: Path, dirs: list[Path], runner=subprocess.run) -> list[str]:
    """Symlink every toolchain found in `dirs` (each a toolchain, or a directory of toolchains) into eh/toolchains; existing names kept."""
    tcs = eh / "toolchains"; tcs.mkdir(parents=True, exist_ok=True)
    done = []
    for base in dirs:
        base = Path(base)
        if not base.is_dir():
            continue
        cands = [base] if (base / "bin" / "lean").exists() else sorted(p for p in base.iterdir() if p.is_dir())
        for d in cands:
            name = toolchain_name(d, runner)
            if not name:
                continue
            dst = tcs / name
            if dst.exists() or dst.is_symlink():
                continue
            if d.resolve() == dst.resolve():
                continue
            dst.symlink_to(d.resolve(), target_is_directory=True)
            done.append(f"{name} -> {d.resolve()}")
    return done


def cmd_elan_link(a) -> int:
    for l in elan_link(Path(a.elan_home), [Path(x) for x in a.dirs]):
        print("linked " + l)
    return 0


                                                                                                                                       
def cmd_selfcheck(a) -> int:
    """One real compile of the first --n rows' seeds on their newest pin through scorer.compile (the agent sessions' path), twice."""
    sys.path.insert(0, str(ROOT))
    from probe.verify_candidates import newest_first
    from scorer import compile as C
    rows = [json.loads(l) for l in Path(a.rows).read_text().splitlines() if l.strip()][: a.n]
    bad = 0
    for r in rows:
        ver = newest_first(r["version_info"])[0]
        times = []
        for label in ("cold", "warm"):
            t0 = time.time()
            if r["source"] == "putnambench":
                res = C.compile_putnam(r["header"], r["src"], ver, timeout=a.timeout)
            else:
                res = C.compile_project(r, r["src"], ver, timeout=a.timeout)
            times.append(time.time() - t0)
            if not res.ok:
                bad += 1
                print(f"selfcheck FAILED: row {rows.index(r)} ({r['source']} {ver}) {label}: {(res.errors or ['?'])[0][:300]}")
                break
        else:
            print(f"selfcheck ok: row {rows.index(r)} ({r['source']} {ver}) heartbeats {res.heartbeats}, {times[0]:.1f} s cold, {times[1]:.1f} s warm")
        wd = C.env_dir(ver) if r["source"] == "putnambench" else C.project_env_dir(r["source"], ver)
        if shutil.which("rg"):
            t0 = time.time()
            n = subprocess.run(["rg", "-L", "--files", "-g", "*.lean", str(wd)], capture_output=True, text=True, timeout=600).stdout.count("\n")
            print(f"rg over {wd.name}: {n} .lean files listed in {time.time() - t0:.1f} s")
    return 1 if bad else 0


                                                                                                                                       
def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("sizing")
    p = sub.add_parser("clock"); p.add_argument("--out", required=True); p.add_argument("--start", type=float)
    p.add_argument("--job", type=float); p.add_argument("--safety", type=float, default=600.0); p.add_argument("--now", type=float)
    p.add_argument("--job-id"); p.add_argument("--resume", action="store_true"); p.add_argument("--pid", type=int); p.add_argument("--rows")
    p.add_argument("--apply", action="store_true", help="set a previous run's OUT aside and stamp OUT with this job (run.sh, not check / dry)")
    p = sub.add_parser("fastdir"); p.add_argument("--tag", default=hashlib.sha256(str(ROOT).encode()).hexdigest()[:8])
    p = sub.add_parser("flocktest"); p.add_argument("dir")
    p = sub.add_parser("ready"); p.add_argument("url"); p.add_argument("--timeout", type=float, default=5400)
    p.add_argument("--poll", type=float, default=10); p.add_argument("--pidfile")
    p = sub.add_parser("reap"); p.add_argument("tag"); p.add_argument("--grace", type=float, default=20)
    p = sub.add_parser("promote"); p.add_argument("out")
    p = sub.add_parser("elan-link"); p.add_argument("elan_home"); p.add_argument("dirs", nargs="+")
    p = sub.add_parser("selfcheck"); p.add_argument("--rows", required=True); p.add_argument("--n", type=int, default=1)
    p.add_argument("--timeout", type=int, default=900)
    a = ap.parse_args(argv)
    return {"sizing": cmd_sizing, "clock": cmd_clock, "fastdir": cmd_fastdir, "flocktest": cmd_flocktest, "ready": cmd_ready,
            "reap": cmd_reap, "promote": cmd_promote, "elan-link": cmd_elan_link, "selfcheck": cmd_selfcheck}[a.cmd](a)


if __name__ == "__main__":
    raise SystemExit(main())
