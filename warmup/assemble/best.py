"""Assemble a submission JSONL: per problem the best eligible bank record by
score (ties: fewer tokens); reference proof as fallback (33.33). With
--include-dev-only, API-derived records are allowed (for local ceiling
estimates ONLY; never submit such a file)."""
from __future__ import annotations

import argparse, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from bank.store import load_all, eligible  # noqa: E402
from scorer.score import aggregate  # noqa: E402


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=None)
    ap.add_argument("--include-dev-only", action="store_true")
    ap.add_argument("--only-run-prefix", default=None, help="restrict to records whose provenance.run_id starts with this (e.g. fresh-or-)")
    ap.add_argument("--only-model", default=None, help="restrict to records whose provenance.model starts with this (e.g. glm-5.3-flash)")
    ap.add_argument("--only-mode", default=None, help="restrict to records whose provenance.mode equals this (e.g. agent)")
    args = ap.parse_args()
    rows = {json.loads(l)["name"]: json.loads(l) for l in (ROOT / "data/benchmark_warmup.jsonl").open() if l.strip()}
    recs = load_all()
    chosen, per = {}, {}
    for name, row in rows.items():
        cands = [r for r in recs if r["problem"] == name and (eligible(r) or (args.include_dev_only and r.get("primary_ok")))]
        if args.only_model:
            # a filter without "@" matches the model name exactly (so glm-5.3-flash does not pull in glm-5.3-flash-nvfp4@openrouter)
            cands = [r for r in cands if (str((r.get("provenance") or {}).get("model", "")).split("@")[0] == args.only_model if "@" not in args.only_model
                                          else str((r.get("provenance") or {}).get("model", "")).startswith(args.only_model))]
        if args.only_run_prefix:
            cands = [r for r in cands if str((r.get("provenance") or {}).get("run_id", "")).startswith(args.only_run_prefix)]
        if args.only_mode:
            cands = [r for r in cands if (r.get("provenance") or {}).get("mode") == args.only_mode]
        best = max(cands, key=lambda r: (r.get("score", 0.0), -r.get("tokens", 10**9)), default=None)
        if best and best.get("score", 0.0) > 33.33:
            chosen[name] = best["proof"]; per[name] = best["score"]
        else:
            chosen[name] = row["src"]; per[name] = 33.33
    total = aggregate(per, list(rows))
    tag = " (INCLUDES DEV-ONLY RECORDS — not submittable)" if args.include_dev_only else ""
    if args.only_model or args.only_mode or args.only_run_prefix:
        tag += f" [filter: model={args.only_model or '*'} mode={args.only_mode or '*'} run={args.only_run_prefix or '*'}]"
    print(f"assembled score: {total}{tag}")
    for n in rows:
        print(f"  {per[n]:6.2f}  {n}")
    if args.out:
        with open(args.out, "w") as f:
            for n, p in chosen.items():
                f.write(json.dumps({"name": n, "proof": p}, ensure_ascii=False) + "\n")
        print("wrote", args.out)


if __name__ == "__main__":
    main()
