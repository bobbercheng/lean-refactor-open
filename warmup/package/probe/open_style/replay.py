#!/usr/bin/env python3
"""Replay of the open style step (docs/open_style_step.md section 5): harness/style_rw_open.py on the finals of a finished package run,
















"""
from __future__ import annotations

import argparse, hashlib, json, os, statistics, sys, time, types
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness import open_package as OP              
from harness import style_rw_open as SRW              

READS = ("proofs.jsonl", "summary.json", "end/meter.json", "end_config_open.json", "end/report.jsonl", "normalize.jsonl")


def fingerprint(src: Path, names: list[str]) -> dict:
    """sha256[:16] of every file of the source out/ directory the replay reads (missing: None)."""
    out = {}
    for rel in list(READS) + [f"work/{OP.safe(n)}/{f}" for n in names for f in ("state.json", "pool.jsonl")]:
        p = src / rel
        try:
            out[rel] = hashlib.sha256(p.read_bytes()).hexdigest()[:16]
        except OSError:
            out[rel] = None
    return out


def load_inputs(a, names: list[str], rows: dict) -> dict:
    """{row: {"source", "proof", "score"}} from the input proofs.jsonl (the export's picks)."""
    pf = Path(a.proofs) if a.proofs else Path(a.src_out) / "proofs.jsonl"
    recs = {r.get("name"): r for r in OP.read_jsonl_records(pf)}
    out = {}
    for n in names:
        r = recs.get(n)
        if not r or not (r.get("proof") or "").strip():
            raise SystemExit(f"{pf}: no proof for {n}")
        out[n] = {"source": r.get("source"), "proof": r["proof"].rstrip(), "score": r.get("stored_score")}
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--src-out", help="a finished package out/ directory (read only)")
    ap.add_argument("--proofs", help="a proofs.jsonl to rewrite instead of <src-out>/proofs.jsonl")
    ap.add_argument("--rows", required=True); ap.add_argument("--heartbeats", required=True)
    ap.add_argument("--problems", nargs="*", help="restrict to these rows")
    ap.add_argument("--names-from", help="restrict to the rows named in this JSONL file (e.g. data/benchmark_warmup.jsonl: the warm-up 15)")
    ap.add_argument("--dest", required=True, help="the replay's own directory (never inside --src-out)")
    ap.add_argument("--base-url", required=True); ap.add_argument("--api-model", default="glm-5.3-flash")
    ap.add_argument("--api-key-file", default=None)
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--wall-s", type=float, default=SRW.WALL_S)
    ap.add_argument("--total-s", type=float, default=6000.0)
    ap.add_argument("--effort", default=SRW.EFFORT, choices=SRW.EFFORTS)
    ap.add_argument("--max-tokens", type=int, default=SRW.MAX_TOKENS)
    ap.add_argument("--exemplars", default=SRW.EXEMPLARS_SHA16)
    ap.add_argument("--compile-slots", type=int, default=None, help="default open_package.auto_slots()")
    ap.add_argument("--no-polish", action="store_true", help="skip the $0 end-stage polish of the best candidate")
    a = ap.parse_args(argv)
    if not (a.src_out or a.proofs):
        ap.error("--src-out or --proofs")
    dest = Path(a.dest).resolve()
    src = Path(a.src_out).resolve() if a.src_out else None
    if src is not None and (dest == src or src in dest.parents):
        ap.error("--dest must not be inside --src-out (the source is never written)")
    os.environ.update(OP.SORRY_GUARD_ENV)
    names, rows, _hbs = OP.load_rows(a.rows, a.heartbeats)
    if a.problems:
        unknown = [p for p in a.problems if p not in rows]
        if unknown:
            raise SystemExit(f"--problems: not in the rows file: {unknown}")
        names = [n for n in names if n in set(a.problems)]
    if a.names_from:
        keep = {r.get("name") for r in OP.read_jsonl_records(Path(a.names_from))}
        names = [n for n in names if n in keep]
        if not names:
            raise SystemExit(f"--names-from {a.names_from}: no row of the rows file is named there")
    SRW.load_exemplars(a.exemplars)                                                       
    inputs = load_inputs(a, names, rows)
    dest.mkdir(parents=True, exist_ok=True)
    fp0 = fingerprint(src, names) if src else {}
    t0 = time.time(); deadline = t0 + float(a.total_s)
    ns = types.SimpleNamespace(rows=a.rows, heartbeats=a.heartbeats, keep_local_ref=False, connect_budget_seconds=OP.CONNECT_BUDGET_S)
    env = OP.base_env(ns)
    slots = a.compile_slots or OP.auto_slots()
    env.update(OP.compile_slots_env(slots, dest))
    cfgp = (src / "end_config_open.json") if src and (src / "end_config_open.json").exists() else OP.package_config(dest, False)
    ms = (src / "end" / "meter.json") if src and (src / "end" / "meter.json").exists() else None
    cfg = {"rows": str(Path(a.rows).resolve()), "heartbeats": str(Path(a.heartbeats).resolve()), "base_url": a.base_url,
           "api_model": a.api_model, "api_key_file": a.api_key_file, "effort": a.effort, "max_tokens": a.max_tokens,
           "exemplars": a.exemplars, "end_config": None if a.no_polish else str(cfgp), "meter_state": str(ms) if ms else None}
    others = {n: OP.style_others(src, n) for n in names} if src else {}
    OP.log(f"style replay: {len(names)} row(s), {a.jobs} at once, wall {a.wall_s:.0f} s per row, bound {a.total_s:.0f} s, "
           f"{slots} compile slot(s), endpoint {a.base_url} ({a.api_model}), exemplars {a.exemplars}, dest {dest}")
    summ = SRW.run_stage(names, rows, inputs, cfg, dest, deadline, a.jobs, env, log=OP.log, wall_s=a.wall_s, others=others)
    lines = SRW.read_records(dest / "style_rw.jsonl")
    per, out_recs = [], []
    for k, n in enumerate(names):
        inp = inputs[n]
        ln = lines.get((n, SRW.sha16(inp["proof"]))) or {}
        try:
            rec = json.loads((dest / "style_rw" / f"r{k:02d}.json").read_text())
        except (OSError, ValueError):
            rec = {}
        acc = SRW.choice(rows[n], ln, inp["proof"])
        per.append({"row": k, "name": n, "source": inp["source"], "input_score": inp["score"], "status": ln.get("status"),
                    "accepted": bool(acc), "gain": ln.get("gain") if acc else 0.0, "before": ln.get("before"), "after": ln.get("after") if acc else None,
                    "wall_s": ln.get("seconds"), "bound_s": ln.get("bound_s"), "calls": rec.get("calls"), "cands": rec.get("cands"),
                    "compiled": rec.get("compiled"), "why": ln.get("why"),
                    "noop_calls": sum(1 for c in rec.get("call_records") or [] if c.get("noop")),
                    "polish_gain": ((rec.get("polish") or {}).get("gain") if acc and (rec.get("candidate") or {}).get("polished") else None),
                    "exemplars_shown": len(((rec.get("exemplars") or {}).get("shown")) or [])})
        out_recs.append({"name": n, "proof": (acc if acc else inp["proof"]) + "\n", "source": "style_rw" if acc else inp["source"],
                         "stored_score": (round(float(inp["score"]) + float(ln["gain"]), 4) if acc and isinstance(inp["score"], (int, float))
                                          else inp["score"]), **({"style_from": inp["source"], "style_gain": ln.get("gain")} if acc else {})})
    fp1 = fingerprint(src, names) if src else {}
    run = [p for p in per if p["status"] in ("improved", "kept")]
    res = {"config": {k: v for k, v in vars(a).items()}, "started": t0, "seconds": round(time.time() - t0, 1), "stage": summ,
           "rows": len(per), "run": len(run), "accepted": sum(p["accepted"] for p in per),
           "gain_sum": round(sum(p["gain"] or 0 for p in per), 4),
           "mean_gain_all_rows": round(statistics.mean([p["gain"] or 0 for p in per]), 4) if per else None,
           "statuses": {s: sum(1 for p in per if p["status"] == s) for s in sorted({str(p["status"]) for p in per})},
           "wall_max_s": max([p["wall_s"] or 0 for p in per] or [0]), "noop_calls": sum(p["noop_calls"] for p in per),
           "calls": sum(int(p["calls"] or 0) for p in per), "polish_gain_sum": round(sum(p["polish_gain"] or 0 for p in per), 4),
           "source_untouched": fp0 == fp1, "source_fingerprint": fp0, "per_row": per}
    res["trajectories_gzipped"] = (summ.get("trajectories_gzipped") or 0) + SRW.gzip_trajectories(dest / "style_rw" / "trajectories")
    (dest / "replay.json").write_text(json.dumps(res, indent=1, ensure_ascii=False, default=str))
    tmp = dest / "proofs.jsonl.tmp"
    tmp.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in out_recs)); os.replace(tmp, dest / "proofs.jsonl")
    OP.log(f"style replay done in {res['seconds']:.0f} s: {res['accepted']} of {res['rows']} accepted, gain sum {res['gain_sum']:+.4f}, "
           f"mean over all rows {res['mean_gain_all_rows']}, statuses {res['statuses']}, calls {res['calls']} ({res['noop_calls']} no-op), "
           f"source untouched {res['source_untouched']}; {dest / 'replay.json'}")
    return 0 if res["source_untouched"] else 3


if __name__ == "__main__":
    raise SystemExit(main())
