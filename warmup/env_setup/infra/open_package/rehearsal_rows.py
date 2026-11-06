#!/usr/bin/env python3
"""The rows of the A100 rehearsal (docs/a100_rehearsal.md): the 15 warm-up rows plus PICK non-sealed LeanPool dev rows
(data/leanpool_dev/rows.jsonl, branch b63-leanpool 2026-10-25; every row pins leanpool v4.35.0-rc3 @ edbe5bd5), with their reference
heartbeats, in the format harness/open_package.py takes (--rows / --heartbeats). Writes into OUT:
  rows.jsonl, heartbeats.jsonl          the combined files (names unique, warm-up first, then the LeanPool picks in file order)
  harness_envs.leanpool.json            the LeanPool environment alone (infra/open_package/envs_from_rows.py over the picks): the build on
                                        the instance runs harness_setup.sh with ENVS_JSON=<this file> so the 15 restored envs are not rebuilt
  harness_envs.run.json                 the 16 environments of the run (the committed 15 + LeanPool): the run's and the restore check's list
PICK rows: --names N1 N2 ... or the --pick smallest-heartbeat rows of distinct projects (default 3; deterministic).
    python3 infra/open_package/rehearsal_rows.py --out probe/a100-reh/rows [--pick 3 | --names ...]"""
from __future__ import annotations

import argparse, json, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "infra/open_package"))
import envs_from_rows as E  # noqa: E402


def jsonl(p: Path) -> list[dict]:
    return [json.loads(l) for l in p.read_text().splitlines() if l.strip()]


def pick_rows(rows: list[dict], hbs: dict, n: int, names: list[str] | None) -> list[dict]:
    if names:
        by = {r["name"]: r for r in rows}
        miss = [x for x in names if x not in by]
        if miss:
            raise SystemExit(f"--names not in the LeanPool rows: {miss}")
        return [by[x] for x in names]
    out, projects = [], set()
    if n <= 0:   # ROWS_PICK=0: the warm-up rows alone (verify 2026-10-28: the loop below took every project before)
        return out
    for r in sorted(rows, key=lambda r: (hbs[r["name"]], r["name"])):   # smallest reference heartbeats first: short rehearsal compiles
        proj = r["file_path"].split("/")[1] if r["file_path"].startswith("LeanPool/") else r["file_path"]
        if proj in projects:
            continue
        projects.add(proj); out.append(r)
        if len(out) == n:
            break
    return out


def build(warm: list[dict], warm_hbs: list[dict], lp: list[dict], lp_hbs: list[dict], n: int, names: list[str] | None):
    hb = {h["name"]: h["heartbeat"] for h in lp_hbs}
    picks = pick_rows(lp, hb, n, names)
    rows = warm + picks
    seen = [r["name"] for r in rows]
    if len(set(seen)) != len(seen):
        raise SystemExit("duplicate row names")
    whb = {h["name"]: h for h in warm_hbs}
    hbs = [whb[r["name"]] for r in warm] + [{"name": r["name"], "heartbeat": hb[r["name"]]} for r in picks]
    for r in rows:
        if r["name"] not in {h["name"] for h in hbs}:
            raise SystemExit(f"no heartbeats for {r['name']}")
    lp_envs = E.envs(picks, E.URLS, E.NO_CACHE)
    return rows, hbs, picks, lp_envs


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--out", required=True)
    ap.add_argument("--warmup", default=str(ROOT / "data/benchmark_warmup.jsonl"))
    ap.add_argument("--warmup-hbs", default=str(ROOT / "data/benchmark_heartbeats.jsonl"))
    ap.add_argument("--leanpool", default=str(ROOT / "data/leanpool_dev/rows.jsonl"))
    ap.add_argument("--leanpool-hbs", default=str(ROOT / "data/leanpool_dev/heartbeats.jsonl"))
    ap.add_argument("--envs-json", default=str(ROOT / "infra/vast/harness_envs.json"), help="the committed 15-env list")
    ap.add_argument("--pick", type=int, default=3)
    ap.add_argument("--names", nargs="*")
    ap.add_argument("--no-warmup", action="store_true", help="LeanPool picks only (tests)")
    a = ap.parse_args()
    warm = [] if a.no_warmup else jsonl(Path(a.warmup)); warm_hbs = [] if a.no_warmup else jsonl(Path(a.warmup_hbs))
    rows, hbs, picks, lp_envs = build(warm, warm_hbs, jsonl(Path(a.leanpool)), jsonl(Path(a.leanpool_hbs)), a.pick, a.names)
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    (out / "rows.jsonl").write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in rows))
    (out / "heartbeats.jsonl").write_text("".join(json.dumps(h, ensure_ascii=False) + "\n" for h in hbs))
    (out / "harness_envs.leanpool.json").write_text(json.dumps(lp_envs, indent=1) + "\n")
    base = json.loads(Path(a.envs_json).read_text())
    for k in lp_envs:
        if k in base and base[k]["commit"] != lp_envs[k]["commit"]:
            raise SystemExit(f"{k}: the committed env list pins another commit")
    merged = dict(base); merged.update(lp_envs)
    (out / "harness_envs.run.json").write_text(json.dumps(merged, indent=1) + "\n")
    print(f"{len(rows)} rows ({len(warm)} warm-up + {len(picks)} LeanPool: {[p['name'] for p in picks]}); envs: {len(lp_envs)} LeanPool, "
          f"{len(merged)} in the run -> {out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
