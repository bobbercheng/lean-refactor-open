"""Compile probe candidates (PutnamBench header+decl, or project rows in place), measure heartbeats on


"""
from __future__ import annotations

import argparse, json, sys, time
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scorer.compile import compile_putnam, compile_project              
from scorer.score import len_pct, hb_pct_local, compat_pct, problem_score              


def newest_first(version_info: list[dict]) -> list[str]:
    def key(v: str):
        core = v.lstrip("v").split("-")[0]
        nums = tuple(int(x) for x in core.split("."))
        return (nums, 0 if "-rc" in v else 1)                            
    vs = [v for pair in version_info for v in pair]
    return sorted(vs, key=key, reverse=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("run_id")
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--timeout", type=int, default=600)
    args = ap.parse_args()
    rows = {json.loads(l)["name"]: json.loads(l) for l in (ROOT / "data/benchmark_warmup.jsonl").open() if l.strip()}
    hbs = {json.loads(l)["name"]: json.loads(l)["heartbeat"] for l in (ROOT / "data/benchmark_heartbeats.jsonl").open() if l.strip()}
    run_dir = ROOT / "probe/runs" / args.run_id
    cands = [json.loads(l) for l in (run_dir / "candidates.jsonl").open() if l.strip()]
    done = set()
    res_path = run_dir / "verified.jsonl"
    if res_path.exists():
        done = {json.loads(l)["sha256"] for l in res_path.open() if l.strip()}
    todo = [c for c in cands if c["sha256"] not in done]
    print(f"{len(todo)} candidates to verify (of {len(cands)})", flush=True)
    out = res_path.open("a")

    def one(c: dict) -> dict:
        row = rows[c["problem"]]
        versions = newest_first(row["version_info"])
        primary = versions[0]
        def comp(version: str, count: bool = True):
            if row["source"] == "putnambench":
                return compile_putnam(row["header"], c["proof"], version, count=count, timeout=args.timeout)
            return compile_project(row, c["proof"], version, count=count, timeout=args.timeout)
        r = comp(primary)
        rec = dict(c)
        rec.update({"primary": primary, "primary_ok": r.ok, "heartbeats": r.heartbeats,
                    "compile_seconds": round(r.seconds, 1), "errors": r.errors[:5], "compat": {primary: r.ok}})
        if r.ok:
            for v in versions[1:]:
                rv = comp(v, count=False)
                rec["compat"][v] = rv.ok
                if not rv.ok:
                    rec.setdefault("compat_errors", {})[v] = rv.errors[:3]
        L = len_pct(row["proof_length"], c["tokens"])
        H = hb_pct_local(c["problem"], r.heartbeats, hbs.get(c["problem"])) if r.ok else 0.0
        Z = compat_pct(rec["compat"]) if r.ok else 0.0
        rec.update({"L": round(L, 2), "H": round(H, 2), "Z": round(Z, 2), "score": problem_score(r.ok, L, H, Z)})
        return rec

    t0 = time.time()
    with ThreadPoolExecutor(args.workers) as ex:
        futs = {ex.submit(one, c): c for c in todo}
        for fut in as_completed(futs):
            c = futs[fut]
            try:
                rec = fut.result()
            except Exception as e:                
                rec = dict(c, primary_ok=False, errors=[f"verifier error: {e}"], score=0.0)
            out.write(json.dumps(rec, ensure_ascii=False) + "\n"); out.flush()
            print(f"[{time.time()-t0:5.0f}s] {rec['problem'][:20]} {rec['sha256']} ok={rec.get('primary_ok')} "
                  f"tok={rec.get('tokens')} hb={rec.get('heartbeats')} L={rec.get('L')} H={rec.get('H')} Z={rec.get('Z')} "
                  f"score={rec.get('score')} {('ERR ' + rec['errors'][0][:120]) if rec.get('errors') else ''}", flush=True)


if __name__ == "__main__":
    main()
