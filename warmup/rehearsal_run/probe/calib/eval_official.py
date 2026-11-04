#!/usr/bin/env python3
"""Predict the OFFICIAL worker score of one candidate proof (2026-10-20, docs/board_gap_sub07.md).

    python3 probe/calib/eval_official.py ROW PROOF_FILE [--all-pins] [--scratch DIR]

Heartbeats on the direct lean path (harness/hb_tool_eval.Evaluator, read-only import), predicted worker count
y = h * R_off / R_direct + 2 (leave-one-upload-out error of a 15-row mean about 0.007); tokens with the worker's observed `:=` + line
break rule (+1); Z from every listed pin with --all-pins. Prints one JSON line. Run ONLY inside a memory-capped systemd user unit:
    systemd-run --user --wait --pipe --unit lra-eval-<x> -p MemoryMax=24G -p RuntimeMaxSec=3600 \
      --working-directory=/home/bobber/source/lean-refactor python3 probe/calib/eval_official.py ROW FILE --all-pins
"""
import argparse, json, re, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.hb_tool_eval import Evaluator, load_dataset  # noqa: E402

ap = argparse.ArgumentParser(); ap.add_argument("row"); ap.add_argument("proof_file"); ap.add_argument("--all-pins", action="store_true")
ap.add_argument("--scratch", default=None)
a = ap.parse_args()
rows, hbs = load_dataset(ROOT / "data/benchmark_warmup.jsonl", ROOT / "data/benchmark_heartbeats.jsonl")
R_direct = json.loads((ROOT / "probe/calib/ref_direct.json").read_text())
row = rows[a.row]; proof = Path(a.proof_file).read_text()
scratch = Path(a.scratch) if a.scratch else ROOT / f"probe/calib/.evalscratch_{re.sub(r'[^A-Za-z0-9]', '_', a.row)[:40]}"
ev = Evaluator(rows, hbs, max_compiles=100, scratch_root=scratch)
t0 = time.time()
res = ev.evaluate(a.row, proof, full=a.all_pins)
out = {"row": a.row, "ok": bool(res.get("ok")), "tokens": res.get("tokens"), "hb_direct": res.get("heartbeats"),
       "error": (res.get("error") or "")[:400], "seconds": round(time.time() - t0, 1)}
if out["ok"] and out["tokens"] is not None and out["hb_direct"] is not None:
    ref_tok, R_off = row["proof_length"], hbs[a.row]
    st = row["statement"].strip(); i = proof.find(st)
    body_nl = bool(re.match(r"\s*:=[ \t]*\n", proof[i + len(st):])) if i >= 0 else False
    tok = out["tokens"] + (1 if body_nl else 0)
    y = out["hb_direct"] * R_off / R_direct[a.row] + 2
    L = round((ref_tok - tok) / ref_tok * 100, 2); H = round((R_off - y) / R_off * 100, 2)
    compat = res.get("compat") or res.get("versions") or {}
    Z = round(100 * sum(1 for v in compat.values() if v) / len(compat), 2) if (a.all_pins and compat) else None
    out.update({"tokens_official": tok, "colon_eq_newline": body_nl, "hb_official_pred": round(y, 1), "L": L, "H": H, "Z": Z,
                "compat": compat, "score_pred": round((L + H + (Z if Z is not None else 100.0)) / 3, 3),
                "note": "" if a.all_pins else "Z assumed 100 (primary pin only); rerun with --all-pins before using"})
print(json.dumps(out, ensure_ascii=False))
