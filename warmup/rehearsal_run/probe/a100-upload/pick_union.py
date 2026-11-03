#!/usr/bin/env python3
"""Union pick for the OPEN warm-up 15 (p85e plan wf_5a596588-311 rank 8, 2026-10-31 ~22:00 UTC; untracked, wraps the tracked
probe/a100/warmup_upload_measure.py without editing it).

The base is the watch88 pick: warmup_upload_measure.candidates() over the p85 / p85b exports + agent bests + end-pipe finals, the squeeze
output and the blind lineage. The union ADDS every verified candidate in runs/*/verified.jsonl under an explicit allowlist of OPEN-LINE roots
(the A100 GLM-5.3-Flash lineage on the vast boxes: p85, p85b, their box backups, the blind lineage, the p85e mirror). A union proof replaces a
row's pick only after the official all-pin meter (probe/calib/eval_official.py --all-pins, on the GB10) scores it STRICTLY above the current
pick measured on the same meter in the same way.

  pick     (no Lean, seconds) base pick + the accepted union rows from the measure cache; writes <dir>/candidate.jsonl ({name, proof}, warm-up
           order), <dir>/pick.json, <dir>/pending.json. Line 1 = "pick-union: stored mean X ..." (the 88 watcher greps "stored mean").
           stored = the base pick's stored score; an accepted row adds its measured official gain (union - pick, same meter, same host).
  measure  (Lean; refuses unless its own cgroup has a memory cap, i.e. inside a systemd unit) measures the pending NEW per-row winners (the top
           --per-row union proofs not already among the base candidates with stored > pick stored - --alt-gap) and the current pick of those
           rows; --all also measures every row's base pick and union pick and writes <dir>/pred.json (submit/candidates/*.pred.json format)
           with the measured official means of both. Appends <cache>/measure.jsonl (keyed by proof sha, never re-measured); then re-picks.
  launch   starts `measure` in the capped unit lra-union-measure (MemoryMax 24G, OOMPolicy continue, CPUWeight 20, RuntimeMaxSec 1800,
           2 jobs x 2 compile slots; b94 keeps priority) when something is pending and the unit is not running; returns at once.

Every source is checked against the allowlist and the run-id / model / path guards below; anything outside fails the whole command (exit 2).
Nothing is uploaded here (the coordinator asks the operator). Absolute end: --end (default 2026-11-01 12:30 UTC) for measure / launch.

    python3 probe/a100-upload/pick_union.py pick --dir probe/a100-upload/watch88
    python3 probe/a100-upload/pick_union.py launch --dir probe/a100-upload/watch88
    python3 probe/a100-upload/pick_union.py launch --dir probe/a100-upload/watch88 --all     # full measured means + pred.json
"""
from __future__ import annotations

import argparse, calendar, fcntl, glob, hashlib, importlib.util, json, os, re, statistics, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]                     # the lra-a100 checkout
_spec = importlib.util.spec_from_file_location("warmup_upload_measure", ROOT / "probe/a100/warmup_upload_measure.py")
wum = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(wum)   # read-only reuse: candidates / pick / valid / eval_official

# ---- the allowlist (relative to ROOT; glob patterns) ----
BASE_RUNS = ["probe/a100-reh-p85/out", "probe/a100-reh-p85b/out", "probe/a100-upload/squeeze-out", "probe/a100-reh-p85b-blind/out"]
BASE_ALLOW = BASE_RUNS + ["probe/a100-reh-p85e*", "probe/a100-reh-p85e*/*"]
VERIFIED_ROOTS = ["probe/a100-reh-p85", "probe/a100-reh-p85b", "probe/a100-reh-p85b-blind", "probe/a100-backup-*", "probe/a100-reh-p85e*"]
VERIFIED_GLOBS = ["runs/*/verified.jsonl", "*/runs/*/verified.jsonl", "lra__probe__runs/*/verified.jsonl", "*/lra__probe__runs/*/verified.jsonl"]
RUN_ID_RE = re.compile(r"^p85[be]?-[a-z]*-?\d+-k\d+$")           # p85-sNN-kK, p85b-sNN-kK, p85b-blind-NN-kK, p85b-cNN-kK / -tNN-kK (p85e)
MODEL_RE = re.compile(r"^glm-5\.3-flash-vllm-a100")              # the open model on the A100 box
DENY_RE = re.compile(r"ccline|cxline|(^|[-_])hx-|oline|fresh|zai|poc2|agent-flash|opus|sonnet|haiku|astra|argon|fable|terra|carbon|closed|"
                     r"gapdash|^b62$|seed\.unused|^sol($|-)", re.I)
FORBIDDEN_TREES = [ROOT / "probe/runs", Path("/home/bobber/source/lean-refactor/probe/runs"), Path("/home/bobber/source/lean-refactor/probe/b62")]
EXCLUDE_RE = re.compile(r"^seed\.unused")
UNIT = "lra-union-measure"
END_DEFAULT = "2026-11-01T12:30:00Z"


class OutsideAllowlist(Exception):
    pass


def sha(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def _expand(patterns: list[str]) -> list[Path]:
    out = []
    for pat in patterns:
        out += [Path(p) for p in sorted(glob.glob(str(ROOT / pat))) if Path(p).is_dir()]
    return out


def guard_path(p: Path, roots: list[Path], what: str) -> None:
    """Fail unless p (symlinks resolved) is inside one of the allowlisted roots, outside every forbidden tree, with no denied component."""
    rp = p.resolve()
    if not any(rp == r.resolve() or r.resolve() in rp.parents for r in roots):
        raise OutsideAllowlist(f"{what} {p} -> {rp}: outside the open-line allowlist")
    for t in FORBIDDEN_TREES:
        if rp == t.resolve() or t.resolve() in rp.parents:
            raise OutsideAllowlist(f"{what} {p} -> {rp}: inside the forbidden tree {t}")
    rel = rp.relative_to(ROOT.resolve()) if ROOT.resolve() in rp.parents else rp
    bad = [c for c in rel.parts if DENY_RE.search(c)]
    if bad:
        raise OutsideAllowlist(f"{what} {p}: denied path component(s) {bad}")


def collect_union(rows: list[dict]) -> tuple[dict, dict]:
    """{row: [cand]} from verified.jsonl under the allowlisted roots (deduped by proof sha, max stored kept), and a stats dict."""
    names = {r["name"]: r for r in rows}
    roots = _expand(VERIFIED_ROOTS)
    by: dict = {n: {} for n in names}
    st = {"roots": {}, "files": 0, "entries": 0, "kept": 0, "rejected": {}, "skipped_run_ids": [], "excluded": []}
    seen_files = set()
    for root in roots:
        guard_path(root, roots, "root")
        nf = 0
        for g in VERIFIED_GLOBS:
            for f in sorted(root.glob(g)):
                rf = f.resolve()
                if rf in seen_files:
                    continue
                seen_files.add(rf)
                if any(EXCLUDE_RE.search(c) for c in f.relative_to(root).parts):   # seed.unused-* inside an allowed root: excluded, not read
                    st["excluded"].append(str(f.relative_to(ROOT))); continue
                guard_path(f, roots, "source")
                rid = f.parent.name
                if not RUN_ID_RE.match(rid) or DENY_RE.search(rid):
                    st["skipped_run_ids"].append(str(f.relative_to(ROOT)))
                    continue
                nf += 1
                for e in wum.read_jsonl(f):
                    st["entries"] += 1
                    n, proof = e.get("problem"), e.get("proof") or ""
                    prov = e.get("provenance") or {}
                    if not MODEL_RE.match(str(prov.get("model") or "")):
                        raise OutsideAllowlist(f"{f}: entry for {n} has model {prov.get('model')!r}, not the open A100 model")
                    if prov.get("run_id") not in (None, rid):
                        raise OutsideAllowlist(f"{f}: entry run_id {prov.get('run_id')!r} != directory {rid!r}")
                    if n not in names or e.get("score") is None:
                        continue
                    why = None if float(e.get("Z") or 0) >= 100 else "Z < 100"
                    why = why or wum.valid(names[n], proof)
                    if why:
                        st["rejected"][why] = st["rejected"].get(why, 0) + 1
                        continue
                    s = sha(proof); stored = float(e["score"])
                    src = f"union:{root.relative_to(ROOT / 'probe')}/{f.parent.parent.relative_to(root)}:{rid}".replace("/.:", ":")
                    c = by[n].get(s)
                    if c is None or stored > c["stored"]:
                        by[n][s] = {"proof": proof.rstrip() + "\n", "stored": stored, "src": src, "sha": s,
                                    "n_src": (c["n_src"] + 1) if c else 1}
                    else:
                        c["n_src"] += 1
        st["roots"][str(root.relative_to(ROOT))] = nf
        st["files"] += nf
    out = {n: sorted(v.values(), key=lambda c: -c["stored"]) for n, v in by.items()}
    st["kept"] = sum(len(v) for v in out.values())
    return out, st


def load_cache(cache: Path) -> dict:
    m = {}
    if cache.exists():
        for r in wum.read_jsonl(cache):
            if r.get("sha"):
                m[r["sha"]] = r
    return m


def clean(rec: dict | None) -> float | None:
    """The measured official score when the measurement is clean (ok, Z 100 on every pin), else None."""
    if rec and rec.get("ok") and rec.get("score_pred") is not None and float(rec.get("Z") or 0) >= 100:
        return float(rec["score_pred"])
    return None


def decide(a, rows: list[dict]) -> dict:
    base_runs = [Path(ROOT / x) if not Path(x).is_absolute() else Path(x) for x in a.runs]
    base_roots = _expand(BASE_ALLOW)
    for r in base_runs:
        guard_path(r, base_roots, "base run")
    by = wum.candidates(rows, base_runs)
    chosen, rep = wum.pick(rows, by)
    union, ust = collect_union(rows)
    cache = load_cache(Path(a.cache))
    res = {"rows": {}, "pending": [], "union_stats": ust}
    for r, cur in zip(rows, chosen):
        n = r["name"]; cs = sha(cur["proof"])
        base_shas = {sha(c["proof"]) for c in by[n]}
        new = [u for u in union[n] if u["sha"] not in base_shas]
        targets = [u for u in new if u["stored"] > cur["stored"] - a.alt_gap][:a.per_row]
        cur_off = clean(cache.get(cs))
        pend = []
        if targets and cs not in cache:
            pend.append({"name": n, "role": "pick", "src": cur["src"], "sha": cs, "proof": cur["proof"]})
        pend += [{"name": n, "role": "union", "src": u["src"], "sha": u["sha"], "proof": u["proof"]} for u in targets if u["sha"] not in cache]
        measured = [(clean(cache.get(u["sha"])), u) for u in new if clean(cache.get(u["sha"])) is not None]
        best = max(measured, key=lambda x: x[0]) if measured else None
        accept = bool(best and cur_off is not None and best[0] > cur_off)
        row = {"base_src": cur["src"], "base_stored": cur["stored"], "base_sha": cs, "base_official_gb10": cur_off,
               "union_new": len(new), "union_top_stored": new[0]["stored"] if new else None, "targets": [(u["src"], u["stored"]) for u in targets],
               "best_union_official_gb10": best[0] if best else None, "best_union_src": best[1]["src"] if best else None, "accepted": accept}
        if accept:
            gain = best[0] - cur_off
            row.update({"proof": best[1]["proof"], "src": best[1]["src"], "stored": round(cur["stored"] + gain, 4), "gain": round(gain, 4),
                        "sha": best[1]["sha"]})
        else:
            row.update({"proof": cur["proof"], "src": cur["src"], "stored": cur["stored"], "gain": 0.0, "sha": cs})
        res["rows"][n] = row
        res["pending"] += pend
    res["stored_mean"] = statistics.mean(v["stored"] for v in res["rows"].values())
    res["base_stored_mean"] = statistics.mean(v["base_stored"] for v in res["rows"].values())
    return res


def write_pick(a, rows: list[dict], res: dict) -> None:
    d = Path(a.dir); d.mkdir(parents=True, exist_ok=True)
    acc = [n for n, v in res["rows"].items() if v["accepted"]]
    print(f"pick-union: stored mean {res['stored_mean']:.3f} (base {res['base_stored_mean']:.3f}; union rows {len(acc)} "
          f"+{res['stored_mean'] - res['base_stored_mean']:.3f}; pending {len(res['pending'])} measurements)")
    for r in rows:
        v = res["rows"][r["name"]]
        tag = f"UNION +{v['gain']:.3f} vs pick {v['base_official_gb10']}" if v["accepted"] else (
            f"union top {v['union_top_stored']} ({v['union_new']} new)" if v["union_new"] else "no new union proof")
        print(f"  {r['name'][:58]:58s} {v['stored']:7.2f}  {v['src'][:60]:60s} {tag}")
    tmp = d / "candidate.jsonl.tmp"
    tmp.write_text("".join(json.dumps({"name": r["name"], "proof": res["rows"][r["name"]]["proof"]}, ensure_ascii=False) + "\n" for r in rows))
    os.replace(tmp, d / "candidate.jsonl")
    meta = {"stored_mean": round(res["stored_mean"], 4), "base_stored_mean": round(res["base_stored_mean"], 4), "runs": a.runs,
            "tool": "probe/a100-upload/pick_union.py", "allow": {"base": BASE_ALLOW, "verified_roots": VERIFIED_ROOTS, "verified_globs": VERIFIED_GLOBS,
            "run_id_re": RUN_ID_RE.pattern, "model_re": MODEL_RE.pattern}, "union_stats": res["union_stats"], "cache": a.cache,
            "at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "rows": {n: {k: v[k] for k in v if k != "proof"} for n, v in res["rows"].items()}}
    tmp = d / "pick.json.tmp"; tmp.write_text(json.dumps(meta, indent=1, ensure_ascii=False)); os.replace(tmp, d / "pick.json")
    tmp = d / "pending.json.tmp"
    tmp.write_text(json.dumps([{k: p[k] for k in ("name", "role", "src", "sha")} for p in res["pending"]], indent=1, ensure_ascii=False))
    os.replace(tmp, d / "pending.json")


def capped() -> str | None:
    """None when this process runs in a cgroup with a memory cap (a systemd unit with MemoryMax), else why not."""
    try:
        cg = Path("/proc/self/cgroup").read_text().strip().splitlines()[-1].split(":", 2)[2]
        mm = (Path("/sys/fs/cgroup") / cg.lstrip("/") / "memory.max").read_text().strip()
    except (OSError, IndexError) as e:
        return f"cannot read the cgroup memory cap ({e})"
    return None if mm != "max" and int(mm) <= 48 * 2**30 else f"cgroup {cg} memory.max={mm} (run via `launch`, a capped unit)"


def measure(a, rows: list[dict]) -> int:
    why = capped()
    if why:
        print(f"REFUSED: {why}", file=sys.stderr); return 2
    d = Path(a.dir); cache = Path(a.cache); cache.parent.mkdir(parents=True, exist_ok=True); d.mkdir(parents=True, exist_ok=True)
    lock = open(cache.parent / "measure.lock", "w")
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        print("another measure holds the lock; exit"); return 0
    (cache.parent / "measure.pid").write_text(str(os.getpid()))
    res = decide(a, rows)
    jobs, seen = [], set()
    for p in res["pending"]:
        if p["sha"] not in seen:
            seen.add(p["sha"]); jobs.append(p)
    if a.all:
        names = {r["name"] for r in rows}
        by = wum.candidates(rows, [ROOT / x for x in a.runs]); chosen, _ = wum.pick(rows, by)
        known = load_cache(cache)
        for c in chosen:
            s = sha(c["proof"])
            if s not in known and s not in seen and c["name"] in names:
                seen.add(s); jobs.append({"name": c["name"], "role": "pick", "src": c["src"], "sha": s, "proof": c["proof"]})
        for n, v in res["rows"].items():
            if v["sha"] not in known and v["sha"] not in seen:
                seen.add(v["sha"]); jobs.append({"name": n, "role": "union", "src": v["src"], "sha": v["sha"], "proof": v["proof"]})
    jobs = jobs[:a.max_jobs]
    print(f"{time.strftime('%H:%M:%S', time.gmtime())} measure: {len(jobs)} proofs ({len(res['pending'])} pending, all={a.all})", flush=True)
    scratch = cache.parent / "scratch"; scratch.mkdir(exist_ok=True)
    with ThreadPoolExecutor(max(1, a.jobs)) as ex, cache.open("a") as fh:
        for j, m in zip(jobs, ex.map(lambda j: wum.eval_official(j["name"], j["proof"], scratch), jobs)):
            rec = {"sha": j["sha"], "name": j["name"], "role": j["role"], "src": j["src"],
                   **{k: m.get(k) for k in ("ok", "tokens_official", "hb_direct", "hb_official_pred", "L", "H", "Z", "score_pred", "error", "seconds")},
                   "host": os.uname().nodename, "at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n"); fh.flush()
            print(f"  {j['role']:5s} {j['name'][:50]:50s} {rec.get('score_pred')}  Z {rec.get('Z')}  {j['src'][:60]}", flush=True)
    res = decide(a, rows)
    write_pick(a, rows, res)
    if a.all:
        known = load_cache(cache)
        by = wum.candidates(rows, [ROOT / x for x in a.runs]); chosen, _ = wum.pick(rows, by)
        base_m = [clean(known.get(sha(c["proof"]))) for c in chosen]
        uni_m = [clean(known.get(res["rows"][r["name"]]["sha"])) for r in rows]
        pred = {}
        for r, um in zip(rows, uni_m):
            v = res["rows"][r["name"]]; rec = known.get(v["sha"]) or {}
            pred[r["name"]] = {"score": um, "source": f"open A100 from-seed lineage {v['src']} (eval_official --all-pins, GB10)",
                               "L": rec.get("L"), "H": rec.get("H"), "Z": rec.get("Z")}
        bm = statistics.mean(base_m) if all(x is not None for x in base_m) else None
        um = statistics.mean(uni_m) if all(x is not None for x in uni_m) else None
        pred["_meta"] = {"predicted_mean": um, "base_measured_mean": bm, "measured_rows": sum(x is not None for x in uni_m), "runs": a.runs,
                         "tool": "probe/a100-upload/pick_union.py measure --all", "at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        (d / "pred.json").write_text(json.dumps(pred, indent=1, ensure_ascii=False))
        print(f"measured official (GB10 all-pin): union pick {um if um is None else round(um, 3)}  base pick {bm if bm is None else round(bm, 3)}  "
              f"-> {d}/pred.json")
    return 0


def launch(a, rows: list[dict]) -> int:
    env = dict(os.environ, XDG_RUNTIME_DIR=f"/run/user/{os.getuid()}", DBUS_SESSION_BUS_ADDRESS=f"unix:path=/run/user/{os.getuid()}/bus")
    if subprocess.run(["systemctl", "--user", "is-active", "--quiet", UNIT], env=env).returncode == 0:
        print(f"{UNIT} already running"); return 0
    res = decide(a, rows); write_pick(a, rows, res)
    if not res["pending"] and not a.all:
        print("nothing pending"); return 0
    log = Path(a.cache).parent / "measure.log"; log.parent.mkdir(parents=True, exist_ok=True)
    rt = max(60, min(1800, int(a.end_epoch - time.time())))
    cmd = ["systemd-run", "--user", "--unit", UNIT, "--collect", "-p", "MemoryMax=24G", "-p", "OOMPolicy=continue", "-p", "CPUWeight=20",
           "-p", f"RuntimeMaxSec={rt}", f"--working-directory={ROOT}",
           "-E", f"PATH={Path.home()}/.elan/bin:{Path(sys.executable).parent}:/usr/bin:/bin", "-E", f"HOME={Path.home()}",
           "-E", "PYTHONUNBUFFERED=1", "-E", "LRA_FORCE_WARN_SORRY=1", "-E", "LRA_HBTOOL_SLOTS=2",
           "-p", f"StandardOutput=append:{log}", "-p", f"StandardError=append:{log}",
           sys.executable, str(Path(__file__).resolve()), "measure", "--dir", str(Path(a.dir).resolve()), "--cache", str(Path(a.cache).resolve()),
           "--per-row", str(a.per_row), "--alt-gap", str(a.alt_gap), "--jobs", str(a.jobs), "--max-jobs", str(a.max_jobs), "--end", a.end,
           "--runs", *a.runs] + (["--all"] if a.all else [])
    p = subprocess.run(cmd, env=env, capture_output=True, text=True)
    print(f"launch {UNIT}: rc {p.returncode} {(p.stderr or p.stdout).strip()[-200:]}")
    return 0 if p.returncode == 0 else 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("cmd", choices=["pick", "measure", "launch"])
    ap.add_argument("--runs", nargs="+", default=BASE_RUNS, help="base --runs (the watch88 set; each must be in BASE_ALLOW)")
    ap.add_argument("--dir", default=str(ROOT / "probe/a100-upload/watch88"))
    ap.add_argument("--cache", default=str(ROOT / "probe/a100-upload/union/measure.jsonl"))
    ap.add_argument("--rows", default=str(wum.WARMUP))
    ap.add_argument("--per-row", type=int, default=2)
    ap.add_argument("--alt-gap", type=float, default=0.3)
    ap.add_argument("--jobs", type=int, default=2)
    ap.add_argument("--max-jobs", type=int, default=40)
    ap.add_argument("--all", action="store_true", help="measure: also every row's base and union pick; writes pred.json")
    ap.add_argument("--end", default=END_DEFAULT)
    a = ap.parse_args()
    a.end_epoch = calendar.timegm(time.strptime(a.end, "%Y-%m-%dT%H:%M:%SZ"))
    rows = wum.read_jsonl(Path(a.rows))
    assert len(rows) == 15, f"{a.rows}: {len(rows)} rows, expected the warm-up 15"
    try:
        if a.cmd in ("measure", "launch") and time.time() > a.end_epoch:
            print(f"past --end {a.end}: no {a.cmd}"); return 0
        if a.cmd == "pick":
            write_pick(a, rows, decide(a, rows)); return 0
        return measure(a, rows) if a.cmd == "measure" else launch(a, rows)
    except OutsideAllowlist as e:
        print(f"ALLOWLIST VIOLATION: {e}", file=sys.stderr); return 2


if __name__ == "__main__":
    raise SystemExit(main())
