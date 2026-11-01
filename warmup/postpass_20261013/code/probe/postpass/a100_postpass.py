#!/usr/bin/env python3
"""$0 CPU post-passes on the open-weight A100 line (2026-10-13: try every method, especially the non-LLM ones, which cost almost
nothing; the open replication repo updated like the closed one). The line's own work root (harness/work_fresh-a100)
is never modified: the passes run on a copy, and only strict gains are recorded back under the line's own provenance, exactly as
probe/normalize/record_a100.py recorded the lexer normalizer (82.03 -> 82.29).
  prepare   copy harness/work_fresh-a100 to harness/hwork/a100-postpass (row folders without snapshots) and install, per row, the best
            of its stored best and its normalizer record (probe/runs/fresh-a100-normalize1/verified.jsonl) as the copy's best
  record    re-check every copy best that beats that starting point with harness.leantools.lean_check (byte-identical statement, forbidden
            constructs, primary compile, every listed toolchain, strictly better) under the A100 line's provenance, marked `postpass`;
            records go to probe/runs/fresh-a100-postpass1/verified.jsonl (bank/import_verified.py banks them; the tracker counts them toward
            flash-a100-w4a16). The passes' own records (transfer@cpu, hb-polish@cpu, hb-rewrite@cpu: closed-dev-only) never reach the bank.
Compiles: run inside a memory-capped unit.   python3 probe/postpass/a100_postpass.py prepare|record"""
import copy, json, shutil, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]; sys.path.insert(0, str(ROOT))
LINE = ROOT / "harness/work_fresh-a100"; COPY = ROOT / "harness/hwork/a100-postpass"
NORM = ROOT / "probe/runs/fresh-a100-normalize1/verified.jsonl"; OUT = ROOT / "probe/runs/fresh-a100-postpass1"
MODEL = "glm-5.3-flash-vllm-a100-awq-w4a16@openai"


def start_bests() -> dict:
    """Per problem: the line's starting best for the passes (stored best, or its normalizer record when higher), as a best dict."""
    out = {}
    for sp in LINE.glob("*/state.json"):
        s = json.loads(sp.read_text()); out[s["problem"]] = s.get("best") or {}
    for l in NORM.open():
        r = json.loads(l)
        if r.get("primary_ok") and float(r.get("score") or 0) > float(out.get(r["problem"], {}).get("score") or 0):
            out[r["problem"]] = {k: r.get(k) for k in ("score", "proof", "tokens", "heartbeats", "L", "H", "Z", "compat")}
    return out


def prepare() -> None:
    if COPY.exists():
        sys.exit(f"{COPY} exists: refusing to overwrite")
    sb = start_bests(); n = 0
    for d in sorted(p for p in LINE.iterdir() if (p / "state.json").exists()):
        dst = COPY / d.name
        shutil.copytree(d, dst, ignore=shutil.ignore_patterns("snapshots", "*.bak", "*.lock", ".state.lock"))
        s = json.loads((dst / "state.json").read_text()); b = sb[s["problem"]]
        if float(b.get("score") or 0) > float((s.get("best") or {}).get("score") or 0):
            s["best"] = b; n += 1
        (dst / "state.json").write_text(json.dumps(s, ensure_ascii=False, indent=1)); (dst / "best.lean").write_text(s["best"]["proof"].rstrip() + "\n")
    print(f"copied {len(sb)} rows to {COPY.relative_to(ROOT)}; normalizer bests installed on {n}")


def record() -> None:
    from harness.leantools import lean_check
    sb = start_bests(); OUT.mkdir(parents=True, exist_ok=True)
    sha = subprocess.run(["git", "rev-parse", "--short", "HEAD"], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    states = {json.loads(p.read_text())["problem"]: json.loads(p.read_text()) for p in LINE.glob("*/state.json")}
    gain = 0.0; k = 0
    for sp in sorted(COPY.glob("*/state.json")):
        c = json.loads(sp.read_text()); n = c["problem"]; cb = c.get("best") or {}; b0 = sb[n]
        if float(cb.get("score") or 0) <= float(b0.get("score") or 0) + 1e-9:
            continue
        st = copy.deepcopy(states[n]); st["best"] = dict(b0)   # strictly better than the starting point, never re-recording it
        runs = sorted({str(a.get("run_id")) for a in c.get("attempts") or [] if str(a.get("run_id", "")).startswith("a100-postpass-")})
        prov = {"kind": "api-dev-only", "model": MODEL, "run_id": "fresh-a100-postpass1", "mode": "agent", "postpass": runs,
                "postpass_code": f"harness@{sha}"}
        t = lean_check(n, cb["proof"], st, prov, OUT / "verified.jsonl")
        after = (st.get("best") or {}).get("score"); ok = bool(after and after > float(b0.get("score") or 0))
        gain += (after - float(b0["score"])) if ok else 0.0; k += ok
        print(f"row {sorted(states).index(n) + 1:2d} ok={t.get('ok')} Z={t.get('Z')} score {b0.get('score')} -> {after}"
              f"{'  RECORDED' if ok else '  (not better: not recorded)'}", flush=True)
    print(f"a100 postpass: {k} row(s) recorded, summed gain {gain:+.2f} = {gain / 15:+.3f} on the 15-row line")


{"prepare": prepare, "record": record}[sys.argv[1]]()
