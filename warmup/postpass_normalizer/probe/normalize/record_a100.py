#!/usr/bin/env python3
"""Record the lexer normalizer's improved A100 bests through the standard checker (2026-10-12: run the normalizer on the A100 line's
best results and update the score tracker when it improves a best; the official worker accepted the rewrites on sub05, 69.08 vs
69.11 predicted, token counts identical on all 15 rows).

Reads probe/normalize/a100<tag>.jsonl (harness/normalize.py --bests a100), re-checks every improved proof with harness.leantools.
lean_check (byte-identical statement, forbidden constructs, primary compile, toolchain compatibility, strictly better than the line's
best) under the A100 line's own provenance, marked `normalized`, exactly like agent.py --normalize does after a session. Records go
to probe/runs/fresh-a100-normalize1/verified.jsonl; bank/import_verified.py banks them and the tracker counts them toward the
flash-a100-w4a16 line. The line's state files (harness/work_fresh-a100) are NOT modified: each check gets a copy.
Compiles: run inside a memory-capped unit.   python3 probe/normalize/record_a100.py --tag -v2
"""
import argparse, copy, json, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]; sys.path.insert(0, str(ROOT))
from harness.leantools import lean_check  # noqa: E402

ap = argparse.ArgumentParser(); ap.add_argument("--tag", default=""); a = ap.parse_args()
res = [json.loads(l) for l in (ROOT / f"probe/normalize/a100{a.tag}.jsonl").open() if l.strip()]
states = {}
for p in (ROOT / "harness/work_fresh-a100").glob("*/state.json"):
    s = json.loads(p.read_text()); states[s["problem"]] = s
out = ROOT / "probe/runs/fresh-a100-normalize1"; out.mkdir(parents=True, exist_ok=True)
sha = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
for r in res:
    if r.get("status") != "improved":
        continue
    st = copy.deepcopy(states[r["problem"]]); before = (st.get("best") or {}).get("score")
    prov = {"kind": "api-dev-only", "model": "glm-5.3-flash-vllm-a100-awq-w4a16@openai", "run_id": "fresh-a100-normalize1", "mode": "agent",
            "normalized": r.get("applied"), "normalizer": f"harness/normalize.py@{sha}"}
    t = lean_check(r["problem"], r["proof"], st, prov, out / "verified.jsonl")
    after = (st.get("best") or {}).get("score")
    print(f"{r["problem"][:44]:44s} ok={t.get('ok')} tok {t.get('tokens')} hb {t.get('heartbeats')} Z {t.get('Z')} score {before} -> {after}"
          f"{'  RECORDED' if after and before and after > before else '  (not better: not recorded)'}", flush=True)
