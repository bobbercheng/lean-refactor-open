#!/usr/bin/env python3
"""Rows and conclusion for infra/vast/scale_test.sh (docs/a100_scale_test.md).
  scale_report.py --row <run_id> <workers> <minutes>   one markdown table row for a finished phase
  scale_report.py                                      conclusion over all scale-a100-w* phases found
"""
from __future__ import annotations

import glob, gzip, json, re, statistics, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def phase(run: str) -> dict:
    out: dict = {"run": run}
    met = []
    for line in (ROOT / "probe" / f"{run}.metrics").read_text().splitlines() if (ROOT / "probe" / f"{run}.metrics").exists() else []:
        try:
            t, r, w, g = (float(x) for x in line.split())
            met.append((t, r, w, g))
        except ValueError:
            pass
    if len(met) >= 2:
        out["tok_s"] = (met[-1][3] - met[0][3]) / max(1.0, met[-1][0] - met[0][0])
        out["running"] = statistics.mean(m[1] for m in met)
        out["waiting"] = statistics.mean(m[2] for m in met)
    tj = ROOT / "probe" / "runs" / run / "turns.jsonl"
    out["turns"] = sum(1 for _ in tj.open()) if tj.exists() else 0
    secs = []
    for f in glob.glob(str(ROOT / "probe" / "runs" / run / "trajectories" / "*")):
        try:
            lines = gzip.open(f, "rt").read().splitlines()
        except OSError:
            lines = open(f).read().splitlines()
        for l in lines:
            try:
                m = json.loads(l)
            except ValueError:
                continue
            if m.get("type") == "turn" and m.get("seconds"):
                secs.append(float(m["seconds"]))
    out["p50_s"] = statistics.median(secs) if secs else None
    log = ROOT / "probe" / f"{run}.log"
    out["holds"] = len(re.findall(r"\[memgate\] HOLD", log.read_text(errors="replace"))) if log.exists() else 0
    out["api_errors"] = len(re.findall(r"api error", log.read_text(errors="replace"))) if log.exists() else 0
    return out


def fmt(x, spec):
    return "-" if x is None else format(x, spec)


def main() -> None:
    if len(sys.argv) >= 5 and sys.argv[1] == "--row":
        run, w, m = sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
        p = phase(run)
        print(f"| {w} | {m} | {p['turns']} | {p['turns'] / m:.1f} | {fmt(p.get('tok_s'), '.0f')} | {fmt(p.get('running'), '.1f')} | "
              f"{fmt(p.get('waiting'), '.1f')} | {fmt(p.get('p50_s'), '.0f')} | {p['holds']} |"
              + (f" ({p['api_errors']} api errors)" if p["api_errors"] else ""))
        return
    rows = []
    for log in sorted(glob.glob(str(ROOT / "probe" / "scale-a100-w*.log"))):
        run = Path(log).stem
        w = int(run.rsplit("w", 1)[1])
        rows.append((w, phase(run)))
    rows.sort()
    if not rows:
        print("no phases found"); return
    print("\n## Conclusion (generated)\n")
    base = rows[0]
    for w, p in rows:
        rel = (p.get("tok_s") or 0) / max(1e-9, base[1].get("tok_s") or 1e-9)
        print(f"- {w} workers: {fmt(p.get('tok_s'), '.0f')} tok/s ({rel:.2f}x the {base[0]}-worker phase), mean {fmt(p.get('running'), '.1f')} requests running, "
              f"{fmt(p.get('waiting'), '.1f')} waiting, p50 {fmt(p.get('p50_s'), '.0f')} s per turn, {p['holds']} memgate holds, {p['api_errors']} API errors")
    best = max(rows, key=lambda r: r[1].get("tok_s") or 0)
    print(f"\nHighest aggregate throughput: **{best[0]} workers**. Queueing (waiting > 0) means more workers than max-num-seqs (16) can serve; "
          "memgate holds mean the GB10's Lean compiles, not the A100, were the limit in that phase.")


if __name__ == "__main__":
    main()
