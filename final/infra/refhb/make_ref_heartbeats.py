#!/usr/bin/env python3
"""Reference heartbeats for a benchmark rows file when the official heartbeats file is not available (b100, 2026-11-01).











































"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import socket
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

OFFSET_DEFAULT = 2
BASIS = ("direct path (harness/hb_tool_eval.Evaluator._compile, newest pin) + offset: on the warm-up 15, official - direct has "
         "median +2 kHB and direct+2 is within 0.71 % of the official reference on every row (docs/b100_refhb.md)")
WARMUP_ROWS = ROOT / "data/benchmark_warmup.jsonl"
WARMUP_HBS = ROOT / "data/benchmark_heartbeats.jsonl"
REUSE_KEYS = ("source", "statement", "src", "header", "file_path")


def log(msg: str) -> None:
    print(f"[refhb {time.strftime('%H:%M:%S')}] {msg}", file=sys.stderr, flush=True)


def load_jsonl(path) -> list[dict]:
    out = []
    for i, line in enumerate(Path(path).read_text(encoding="utf-8").splitlines(), 1):
        if line.strip():
            r = json.loads(line)
            if not isinstance(r, dict):
                raise ValueError(f"{path}:{i}: not a JSON object")
            out.append(r)
    return out


def newest_pin(row: dict) -> tuple[str, str]:
    """(toolchain, commit) of the row's newest pin: the toolchain the official reference is measured on."""
    from probe.verify_candidates import newest_first
    v = newest_first(row["version_info"])[0]
    commit = next((str(c) for vi in row["version_info"] if isinstance(vi, dict) for t, c in vi.items() if t == v), "")
    return v, commit


def src_sha(row: dict) -> str:
    return hashlib.sha256("\0".join(str(row.get(k)) for k in REUSE_KEYS).encode()).hexdigest()[:16]


def warmup_reuse() -> dict:
    """{name: (warm-up row, official heartbeats)} from the repo's warm-up data files, {} when either is missing."""
    if not (WARMUP_ROWS.exists() and WARMUP_HBS.exists()):
        return {}
    hbs = {h["name"]: h["heartbeat"] for h in load_jsonl(WARMUP_HBS)
           if isinstance(h.get("heartbeat"), (int, float)) and h["heartbeat"] > 0}
    return {r["name"]: (r, int(hbs[r["name"]])) for r in load_jsonl(WARMUP_ROWS) if r.get("name") in hbs}


def reuse_value(row: dict, table: dict) -> int | None:
    hit = table.get(row["name"])
    if not hit:
        return None
    w, hb = hit
    if any(row.get(k) != w.get(k) for k in REUSE_KEYS):
        return None
    try:
        return hb if newest_pin(row) == newest_pin(w) else None
    except (KeyError, ValueError, TypeError):
        return None


def env_dir(row: dict, version: str) -> Path:
    from scorer import compile as compiler
    return (compiler.env_dir(version) if row["source"] == "putnambench"
            else compiler.project_env_dir(row["source"], version))


def git_head() -> str | None:
    try:
        p = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, capture_output=True, text=True, timeout=20)
        return p.stdout.strip() or None
    except (OSError, subprocess.SubprocessError):
        return None


_ENV_COMMITS: dict = {}
_ENV_LOCK = threading.Lock()


def env_commit(wd: Path) -> dict:
    """{"commit", "where", "dirty"} of a built environment: its git HEAD (tracked files modified: dirty), else the commit envs/manifest.json
"""
    key = str(wd)
    with _ENV_LOCK:
        if key in _ENV_COMMITS:
            return _ENV_COMMITS[key]
        out = {"commit": None, "where": "unknown", "dirty": None}
        if (wd / ".git").exists():
            env = dict(os.environ, GIT_OPTIONAL_LOCKS="0")
            try:
                p = subprocess.run(["git", "-c", "safe.directory=*", "-C", str(wd), "rev-parse", "HEAD"], capture_output=True,
                                   text=True, timeout=60, env=env)
                if p.returncode == 0 and p.stdout.strip():
                    out.update(commit=p.stdout.strip(), where="git")
                    q = subprocess.run(["git", "-c", "safe.directory=*", "-C", str(wd), "status", "--porcelain", "--untracked-files=no"],
                                       capture_output=True, text=True, timeout=300, env=env)
                    out["dirty"] = bool(q.stdout.strip()) if q.returncode == 0 else None
            except (OSError, subprocess.SubprocessError):
                pass
        if out["commit"] is None:
            for m in dict.fromkeys((wd.parent / "manifest.json", wd.resolve().parent / "manifest.json")):
                try:
                    rec = json.loads(m.read_text()).get(wd.name)
                except (OSError, ValueError, AttributeError):
                    continue
                if isinstance(rec, dict) and rec.get("commit"):
                    out.update(commit=str(rec["commit"]), where=f"manifest {m}")
                    break
        _ENV_COMMITS[key] = out
        return out


def pin_check(wd: Path, commit: str) -> str | None:
    """None when the environment at `wd` is at the row's pin `commit` (or either commit is unknown), else the warning text."""
    e = env_commit(wd)
    probs = []
    if e["commit"] and commit and not (e["commit"].startswith(commit) or commit.startswith(e["commit"])):
        probs.append(f"environment {wd.name} is at {e['commit'][:12]} ({e['where'].split(' ')[0]}), the row pins {commit[:12]}")
    if e["dirty"]:
        probs.append(f"environment {wd.name} has modified tracked files")
    return "; ".join(probs) or None


def mem_available_gb() -> float:
    try:
        for line in open("/proc/meminfo"):
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / 1024 / 1024
    except OSError:
        pass
    return 16.0


def default_jobs() -> int:
    return max(1, min(8, (os.cpu_count() or 4) // 4, int(mem_available_gb() // 8)))


def atomic_write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    tmp.write_text(text, encoding="utf-8")
    os.replace(tmp, path)


def hb_lines(values: dict) -> str:
    """The official file's format: one {"name", "heartbeat"} object per line, UTF-8 (not escaped), sorted by name."""
    return "".join(json.dumps({"name": n, "heartbeat": int(values[n])}, ensure_ascii=False) + "\n" for n in sorted(values))


                                                                                                                              
class Meter:
    """One Evaluator per worker thread (its own scratch SCRATCH/w<k>, so its compile slots are its own; no environment variable is

"""

    def __init__(self, jobs: int, timeout: int, scratch: Path, toolchains=None):
        self.scratch, self.timeout, self.toolchains = Path(scratch), timeout, toolchains
        gate_dir = Path(os.environ["LRA_MEMGATE_DIR"]) if os.environ.get("LRA_MEMGATE_DIR") else self.scratch
        gate_dir.mkdir(parents=True, exist_ok=True)
        self.gate_lock = gate_dir / "lra-memgate.lock"
        self._local, self._lock, self._n = threading.local(), threading.Lock(), 0

    def _ev(self):
        ev = getattr(self._local, "ev", None)
        if ev is None:
            from harness.hb_tool_eval import Evaluator
            with self._lock:
                k, self._n = self._n, self._n + 1
            ev = Evaluator({}, {}, max_compiles=1 << 30, scratch_root=self.scratch / f"w{k}", toolchains=self.toolchains,
                           timeout=self.timeout)
            ev._gate.LOCK, ev._gate.LEDGER = self.gate_lock, self.gate_lock.with_suffix(".json")
            self._local.ev = ev
        return ev

    def direct(self, row: dict, version: str, timeout: int | None = None) -> dict:
        t0 = time.monotonic()
        ev = self._ev()                                                                            
        ev.timeout = int(timeout or self.timeout)
        try:
            res = ev._compile(row, row["src"], version)
        except (OSError, ValueError, KeyError) as e:
            return {"ok": False, "hb": None, "error": f"{type(e).__name__}: {e}"[:400], "seconds": round(time.monotonic() - t0, 1)}
        finally:
            ev.timeout = self.timeout
        err = None if res.ok else ((res.errors or ["failed"])[0])[:400]
        if res.ok and (res.heartbeats is None or res.hb_blind):
            err = "compiled but arena_measure could not run in this file (hb_blind)"
        return {"ok": bool(res.ok and res.heartbeats is not None and not res.hb_blind), "hb": res.heartbeats,
                "hb_blind": bool(res.hb_blind), "timed_out": bool(res.timed_out), "error": err,
                "seconds": round(res.seconds, 1)}

    def scorer(self, row: dict, version: str, timeout: int | None = None) -> dict:
        from scorer.compile import compile_project, compile_putnam
        t0 = time.monotonic()
        timeout = int(timeout or self.timeout)
        try:
            res = (compile_putnam(row["header"], row["src"], version, timeout=timeout) if row["source"] == "putnambench"
                   else compile_project(row, row["src"], version, timeout=timeout))
        except (OSError, ValueError, KeyError, subprocess.SubprocessError) as e:
            return {"ok": False, "hb": None, "error": f"{type(e).__name__}: {e}"[:400], "seconds": round(time.monotonic() - t0, 1)}
        err = None if res.ok else ((res.errors or ["failed"])[0])[:400]
        return {"ok": bool(res.ok and res.heartbeats is not None and not res.hb_blind), "hb": res.heartbeats,
                "hb_blind": bool(res.hb_blind), "timed_out": bool(res.timed_out), "error": err, "seconds": round(res.seconds, 1)}


def measure_row(k: int, row: dict, meter: Meter, args, reuse: dict) -> dict:
    tag = f"row#{k:02d}"
    rec = {"pin": None, "method": None, "heartbeat": None, "hb_direct": None, "hb_scorer": None, "seconds": 0.0,
           "ok": False, "hb_blind": False, "error": None, "src_sha": src_sha(row), "offset": args.offset}
    try:
        version, commit = newest_pin(row)
    except (KeyError, ValueError, TypeError, IndexError) as e:
        rec["error"] = f"version_info unreadable: {e}"
        log(f"{tag}: FAILED ({rec['error']})")
        return rec
    rec["pin"] = version
    rec["commit"] = commit
    hb = reuse_value(row, reuse) if reuse else None
    if hb is not None:
        rec.update(method="warmup-official", heartbeat=hb, ok=True)
        log(f"{tag}: warm-up row, official value reused ({version})")
        return rec
    try:
        wd = env_dir(row, version)
    except (KeyError, NotImplementedError) as e:
        rec["error"] = f"unknown source {row.get('source')!r} ({type(e).__name__}: {e})"
        log(f"{tag}: FAILED ({rec['error']})")
        return rec
    if not wd.is_dir():
        rec["error"] = f"environment missing: {wd.name} (build it first)"
        log(f"{tag}: FAILED ({rec['error']})")
        return rec
    e = env_commit(wd)
    rec["env_commit"], rec["env_commit_from"] = e["commit"], e["where"].split(" ")[0]
    warn = pin_check(wd, commit)
    if warn:
        rec["env_warning"] = warn
        if getattr(args, "strict", False):
            rec["error"] = f"--strict: {warn}"
            log(f"{tag}: FAILED ({rec['error']})")
            return rec
        log(f"{tag}: WARNING {warn} (measured anyway; --strict refuses)")
    d = s = None
    if args.method in ("direct", "both"):
        d = meter.direct(row, version)
        rec["hb_direct"], rec["hb_blind"] = d["hb"], d.get("hb_blind", False)
        rec["seconds"] += d["seconds"]
        rec["direct_error"] = d["error"]
        if d["ok"] and args.repeat > 1:                                                                                 
            reads = [d["hb"]]
            for _ in range(args.repeat - 1):
                again = meter.direct(row, version)
                rec["seconds"] += again["seconds"]
                if again["ok"]:
                    reads.append(again["hb"])
            reads.sort()
            d["hb"] = rec["hb_direct"] = reads[(len(reads) - 1) // 2]
            rec["hb_direct_reads"] = reads
    fallback = args.method == "direct" and not d["ok"] and not args.no_fallback
    if fallback and d.get("timed_out"):                                                                       
        fallback = False
        rec["scorer_error"] = "not tried: the direct compile timed out"
    if args.method in ("scorer", "both") or fallback:
        s = meter.scorer(row, version, timeout=None if args.method != "direct" else
                         min(meter.timeout, max(600, int(2 * d["seconds"]) + 300)))
        rec["hb_scorer"] = s["hb"]
        rec["seconds"] += s["seconds"]
        rec["scorer_error"] = s["error"]
    if d is not None and d["ok"]:
        rec.update(method=f"direct+{args.offset}", heartbeat=int(d["hb"]) + args.offset, ok=True)
    elif s is not None and s["ok"]:
        rec.update(method="scorer", heartbeat=int(s["hb"]), ok=True,
                   note="scorer path (lake env lean): reads 0-3 % above the official meter on some libraries")
    else:
        rec["error"] = (d or {}).get("error") or (s or {}).get("error") or "no reading"
    rec["seconds"] = round(rec["seconds"], 1)
    log(f"{tag}: {version} {rec['method'] or 'FAILED'} hb={rec['heartbeat']} direct={rec['hb_direct']} scorer={rec['hb_scorer']} "
        f"({rec['seconds']}s){'' if rec['ok'] else ' error: ' + str(rec['error'])[:160]}")
    return rec


def fill_placeholders(rows: list[dict], results: dict, meter: Meter, args) -> dict:
    """--allow-missing: a flagged stand-in for each row of `rows` without a reading in `results` ({name: record}); the records are

"""
    from probe.verify_candidates import newest_first
    by = {r["name"]: r for r in rows}

    def tokens(r):
        try:
            return int(r.get("proof_length") or 0)
        except (TypeError, ValueError):
            return 0
    got = {n: rec["heartbeat"] for n, rec in results.items() if rec.get("ok") and rec.get("heartbeat") and tokens(by.get(n, {})) > 0}
    filled = {}
    for r in rows:
        rec = results.setdefault(r["name"], {"ok": False, "heartbeat": None, "error": "not measured"})
        if rec.get("ok") and rec.get("heartbeat"):
            continue
        kind = val = None
        if "timed out" not in str(rec.get("scorer_error")) and rec.get("error") != "timeout":
            try:
                older = newest_first(r["version_info"])[1:3]
            except (KeyError, ValueError, TypeError, IndexError):
                older = []
            for v in older:
                try:
                    wd = env_dir(r, v)
                except (KeyError, NotImplementedError):
                    break
                if not wd.is_dir():
                    continue
                c = next((str(c) for vi in r["version_info"] if isinstance(vi, dict) for t, c in vi.items() if t == v), "")
                if getattr(args, "strict", False) and pin_check(wd, c):
                    continue
                d = meter.direct(r, v, timeout=min(meter.timeout, 900))
                rec["seconds"] = round(float(rec.get("seconds") or 0) + d["seconds"], 1)
                if d["ok"]:
                    kind, val = f"older-pin {v}", int(d["hb"]) + args.offset
                    break
        scaled = None
        if tokens(r) > 0 and got:
            same = [got[n] / tokens(by[n]) for n in got if by[n].get("source") == r.get("source")]
            ratios = sorted(same if len(same) >= 2 else [got[n] / tokens(by[n]) for n in got])
            scaled = max(1, round(ratios[(len(ratios) - 1) // 2] * tokens(r)))
        if val is None:
            reading = (int(rec["hb_direct"]) + args.offset if rec.get("hb_direct") is not None
                       else int(rec["hb_scorer"]) if rec.get("hb_scorer") is not None else None)
            if reading is not None and (scaled is None or reading >= scaled / 4):
                kind, val = "despite-error", reading
            elif reading is not None:
                rec["placeholder_rejected"] = f"despite-error reading {reading} < 1/4 of the length-scaled {scaled}"
        if val is None and scaled is not None:
            kind, val = "length-scaled", scaled
        if val is None:
            continue
        rec.update(method=f"placeholder-{kind.split(' ')[0]}", placeholder=kind, heartbeat=int(val), ok=False)
        filled[r["name"]] = kind
        log(f"PLACEHOLDER {r['name'][:60]}: {kind} heartbeat={val} (no reading: {str(rec.get('error'))[:120]})")
    return filled


def measure_rows(rows: list[dict], *, jobs: int = 0, offset: int = OFFSET_DEFAULT, method: str = "direct", timeout: int = 1800,
                 reuse: bool = True, repeat: int = 1, no_fallback: bool = False, scratch=None, toolchains=None,
                 allow_missing: bool = False, strict: bool = False) -> dict:
    """{name: record} for `rows` (the CLI's per-row records; record["heartbeat"] is the value when record["ok"], or, with

"""
    args = argparse.Namespace(offset=offset, method=method, no_fallback=no_fallback, repeat=max(1, repeat), strict=strict)
    table = warmup_reuse() if reuse else {}
    jobs = jobs or default_jobs()
    meter = Meter(jobs, timeout, Path(scratch).resolve() if scratch else ROOT / "probe/refhb/.scratch", toolchains)
    order = sorted(range(len(rows)), key=lambda k: -int(rows[k].get("proof_length") or 0))
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        recs = dict(zip(order, ex.map(lambda k: measure_row(k, rows[k], meter, args, table), order)))
    out = {rows[k]["name"]: recs[k] for k in range(len(rows))}
    if allow_missing:
        fill_placeholders(rows, out, meter, args)
    return out


def make(args) -> int:
    rows = load_jsonl(args.rows)
    names = [r.get("name") for r in rows]
    if not rows or any(not isinstance(n, str) or not n for n in names) or len(set(names)) != len(names):
        log("rows refused: empty file, a row without a name, or a duplicate name")
        return 2
    if args.names:
        want = {n.strip() for n in args.names.split(",") if n.strip()}
        rows = [r for r in rows if r["name"] in want]
        if not rows:
            log("--names matches no row")
            return 2
    out = Path(args.out)
    meta_path = out.with_name(out.name + ".meta.json")
    direct_path = out.with_name((out.name[:-6] if out.name.endswith(".jsonl") else out.name) + ".direct.json")
    partial = out.with_name(out.name + ".partial")
    reuse = {} if args.no_reuse else warmup_reuse()
                                                                                                   
    need_env = [r for r in rows if not (reuse and reuse_value(r, reuse) is not None)]
    if need_env:
        have = 0
        for r in need_env:
            try:
                have += env_dir(r, newest_pin(r)[0]).is_dir()
            except Exception:                
                pass
        if not have and len(need_env) == len(rows):
            log(f"no built environment for any of the {len(need_env)} row(s) to measure (envs/<source>-<toolchain>, putnambench: "
                "envs/mathlib-<toolchain>)")
            return 2
    prev = {}
    if args.resume and meta_path.exists():
        try:
            prev = json.loads(meta_path.read_text()).get("rows", {})
        except (OSError, ValueError):
            prev = {}
    t_start = time.time()
    scratch = Path(args.scratch).resolve() if args.scratch else ROOT / "probe/refhb/.scratch"
    jobs = args.jobs or default_jobs()
    log(f"{len(rows)} row(s), jobs {jobs}, method {args.method}, offset {args.offset}, reuse {'on' if reuse else 'off'}, "
        f"timeout {args.timeout}s, scratch {scratch}")
    meter = Meter(jobs, args.timeout, scratch, args.toolchains)
    results: dict = {}
    lock = threading.Lock()
    todo = []
    for k, r in enumerate(rows):
        p = prev.get(r["name"])
        try:
            pin_now = newest_pin(r)[0]
        except (KeyError, ValueError, TypeError, IndexError):
            pin_now = None
        if p and p.get("ok") and p.get("src_sha") == src_sha(r) and p.get("offset") == args.offset \
                and p.get("pin") == pin_now and (p.get("method") != "warmup-official" or reuse) \
                and (p.get("method") != f"direct+{args.offset}" or len(p.get("hb_direct_reads") or [p.get("hb_direct")]) >= args.repeat):
            results[r["name"]] = dict(p, resumed=True)
        else:
            todo.append((k, r))
    if len(todo) < len(rows):
        log(f"--resume: {len(rows) - len(todo)} row(s) kept from {meta_path.name}")
                                                                                                  
    todo.sort(key=lambda kr: -int(kr[1].get("proof_length") or 0))

    def job(kr):
        k, r = kr
        rec = measure_row(k, r, meter, args, reuse)
        with lock:
            results[r["name"]] = rec
            write_meta(meta_path, rows, results, args, jobs, t_start, final=False)
        return rec
    with ThreadPoolExecutor(max_workers=jobs) as ex:
        list(ex.map(job, todo))
    placeholders = fill_placeholders(rows, results, meter, args) if args.allow_missing else {}
    write_meta(meta_path, rows, results, args, jobs, t_start, final=True)
    values = {n: rec["heartbeat"] for n, rec in results.items() if (rec.get("ok") or rec.get("placeholder")) and rec.get("heartbeat")}
    direct = {n: rec["hb_direct"] for n, rec in results.items() if rec.get("hb_direct") is not None}
    atomic_write(direct_path, json.dumps({"_meta": {"what": "reference heartbeats on the direct path (no offset), "
                                                    "infra/refhb/make_ref_heartbeats.py", "rows": str(Path(args.rows).resolve()),
                                                    "at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}, **direct},
                                         ensure_ascii=False, indent=1) + "\n")
    missing = [k for k, r in enumerate(rows) if r["name"] not in values]
    counts = {}
    for rec in results.values():
        if rec.get("ok"):
            m = rec["method"] if not rec["method"].startswith("direct+") else "direct"
            counts[m] = counts.get(m, 0) + 1
    warns = {n: rec["env_warning"] for n, rec in results.items() if rec.get("env_warning")}
    summary = (f"{len(values)}/{len(rows)} (warmup {counts.get('warmup-official', 0)} / direct {counts.get('direct', 0)} / "
               f"scorer {counts.get('scorer', 0)}" + (f" / PLACEHOLDER {len(placeholders)}" if placeholders else "")
               + f"), {time.time() - t_start:.0f}s wall" + (f"; env pin WARNINGS {len(warns)}" if warns else ""))
    if missing:
        atomic_write(partial, hb_lines(values))
        if out.exists():                                                               
            os.replace(out, out.with_name(out.name + ".prev"))
            log(f"moved the existing {out.name} aside to {out.name}.prev")
        log(f"REFHB INCOMPLETE {summary}; no reading for {len(missing)} row(s): "
            + ", ".join(f"row#{k:02d} ({str(results.get(rows[k]['name'], {}).get('error'))[:120]})" for k in missing[:12])
            + f"; wrote {partial.name} (not {out.name})")
        return 1
    atomic_write(out, hb_lines(values))
    partial.unlink(missing_ok=True)
    if placeholders:
        log(f"REFHB PLACEHOLDERS {len(placeholders)} row(s) without a reading got a flagged stand-in (--allow-missing): "
            + ", ".join(f"row#{k:02d} ({placeholders[r['name']]})" for k, r in enumerate(rows) if r["name"] in placeholders)[:600])
    for n, w in sorted(warns.items())[:12]:
        log(f"WARNING env pin: {n[:60]}: {w}")
    log(f"REFHB OK {summary} -> {out}")
    return 0


def write_meta(path: Path, rows, results, args, jobs, t_start, final: bool) -> None:
    rec = {"tool": "infra/refhb/make_ref_heartbeats.py", "rows_file": str(Path(args.rows).resolve()),
           "rows_sha256": hashlib.sha256(Path(args.rows).read_bytes()).hexdigest(), "n_rows": len(rows),
           "offset": args.offset, "method": args.method, "reuse_warmup": not args.no_reuse, "basis": BASIS,
           "allow_missing": bool(getattr(args, "allow_missing", False)), "strict": bool(getattr(args, "strict", False)),
           "placeholders": {n: r["placeholder"] for n, r in sorted(results.items()) if r.get("placeholder")},
           "env_warnings": {n: r["env_warning"] for n, r in sorted(results.items()) if r.get("env_warning")},
           "commit": git_head(), "host": socket.gethostname(), "nproc": os.cpu_count(), "jobs": jobs,
           "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(t_start)),
           "finished": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()) if final else None,
           "wall_s": round(time.time() - t_start, 1), "rows": {n: results[n] for n in sorted(results)}}
    atomic_write(path, json.dumps(rec, ensure_ascii=False, indent=1) + "\n")


                                                                                                                             
def parse_worker(path) -> dict:
    """{name: (L, y, Z)} from a scored submission's per-row table (submit/results/*.worker.json rows:
"""
    out = {}
    for r in json.loads(Path(path).read_text()):
        if len(r) < 8 or str(r[1]).lower() != "compiled":
            continue
        try:
            L = float(str(r[4]).rstrip("%"))
            y = int(str(r[5]).split(" of ")[0].replace(",", ""))
            k, n = (int(x) for x in str(r[7]).split("/"))
            out[r[0]] = (L, y, 100.0 * k / n)
        except (ValueError, IndexError):
            continue
    return out


def check(args) -> int:
    est = {h["name"]: h["heartbeat"] for h in load_jsonl(args.check)}
    off = {h["name"]: h["heartbeat"] for h in load_jsonl(args.official)}
    meta_path = Path(args.check).with_name(Path(args.check).name + ".meta.json")
    meta = json.loads(meta_path.read_text()).get("rows", {}) if meta_path.exists() else {}
    alts = {"estimate": est}
    scorer_vals = {n: m["hb_scorer"] for n, m in meta.items() if m.get("hb_scorer")}
    if scorer_vals:
        alts["scorer-path"] = scorer_vals
    common = sorted(set(est) & set(off))
    print(f"rows: estimate {len(est)}, official {len(off)}, common {len(common)}")
    print(f"{'row':58s} {'official':>9s} {'estimate':>9s} {'err%':>7s} {'method':>16s}" + ("  scorer err%" if scorer_vals else ""))
    errs = []
    for n in common:
        e = (est[n] - off[n]) / off[n] * 100
        errs.append(e)
        extra = f"  {(scorer_vals[n] - off[n]) / off[n] * 100:+8.3f}" if n in scorer_vals else ""
        print(f"{n[:58]:58s} {off[n]:9d} {est[n]:9d} {e:+7.3f} {str(meta.get(n, {}).get('method', '')):>16s}{extra}")
    if errs:
        print(f"estimate vs official: mean abs {sum(map(abs, errs)) / len(errs):.3f} %, max abs {max(map(abs, errs)):.3f} %, "
              f"mean signed {sum(errs) / len(errs):+.3f} %")
    if scorer_vals:
        se = [(scorer_vals[n] - off[n]) / off[n] * 100 for n in common if n in scorer_vals]
        print(f"scorer path vs official: mean abs {sum(map(abs, se)) / len(se):.3f} %, max abs {max(map(abs, se)):.3f} %")
    for w in args.worker or []:
        rows = parse_worker(w)
        print(f"\nscore error on {Path(w).name} (worker heartbeats y held fixed; score = (L + H + Z)/3, H = (R - y)/R*100)")
        for label, ref in alts.items():
            ds = []
            for n, (L, y, Z) in rows.items():
                if n in off and n in ref and ref[n]:
                    s_off = (L + (off[n] - y) / off[n] * 100 + Z) / 3
                    s_est = (L + (ref[n] - y) / ref[n] * 100 + Z) / 3
                    ds.append((s_est - s_off, n))
            if ds:
                worst = max(ds, key=lambda d: abs(d[0]))
                print(f"  {label:12s} rows {len(ds):3d}  mean score error {sum(d for d, _ in ds) / len(ds):+.4f}  "
                      f"max row {abs(worst[0]):.3f} ({worst[1][:40]})")
    return 0


def git_trust(env) -> None:
    """rc3: safe.directory=* for lake's git calls in env checkouts owned by another user (same rule as harness/open_package.git_trust)."""
    n = int(env.get("GIT_CONFIG_COUNT") or 0)
    if any(env.get(f"GIT_CONFIG_KEY_{i}") == "safe.directory" and env.get(f"GIT_CONFIG_VALUE_{i}") == "*" for i in range(n)):
        return
    env[f"GIT_CONFIG_KEY_{n}"] = "safe.directory"; env[f"GIT_CONFIG_VALUE_{n}"] = "*"; env["GIT_CONFIG_COUNT"] = str(n + 1)


def main() -> int:
    git_trust(os.environ)
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rows"); ap.add_argument("--out")
    ap.add_argument("--jobs", type=int, default=0, help="rows measured at once (default min(8, nproc/4, MemAvailable GB/8))")
    ap.add_argument("--offset", type=int, default=OFFSET_DEFAULT, help="added to a direct-path reading (default 2)")
    ap.add_argument("--method", choices=["direct", "scorer", "both"], default="direct",
                    help="direct (default; scorer path as fallback), scorer, or both (direct value, scorer reading recorded)")
    ap.add_argument("--no-reuse", action="store_true", help="measure warm-up rows too (default: reuse their official values)")
    ap.add_argument("--no-fallback", action="store_true", help="direct: no scorer-path fallback")
    ap.add_argument("--timeout", type=int, default=1800, help="seconds per compile")
    ap.add_argument("--repeat", type=int, default=1, help="direct readings per row, the median kept (default 1)")
    ap.add_argument("--names", help="comma-separated subset of row names")
    ap.add_argument("--resume", action="store_true", help="keep rows already measured ok in OUT.meta.json")
    ap.add_argument("--scratch", help="scratch directory inside this checkout (default probe/refhb/.scratch)")
    ap.add_argument("--toolchains", help="an Elan toolchains directory (default: $ELAN_HOME, ~/.elan, the envs' parents)")
    ap.add_argument("--allow-missing", action="store_true",
                    help="a row without a reading gets a FLAGGED placeholder (despite-error / older-pin / length-scaled) and OUT is "
                         "written (exit 0) instead of OUT.partial (exit 1); for an unattended release")
    ap.add_argument("--strict", action="store_true",
                    help="an environment not at the row's pin commit (or with modified tracked files) is an error, not a warning")
    ap.add_argument("--check", metavar="HB.jsonl", help="compare an estimate with --official (and --worker score tables)")
    ap.add_argument("--official"); ap.add_argument("--worker", nargs="*")
    a = ap.parse_args()
    if a.check:
        if not a.official:
            ap.error("--check needs --official")
        return check(a)
    if not (a.rows and a.out):
        ap.error("--rows and --out are required")
    return make(a)


if __name__ == "__main__":
    sys.exit(main())
