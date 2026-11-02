#!/usr/bin/env python3
"""Rows -> environments preflight (review 2026-10-28, finding 11: a row whose environment is missing failed only at the first compile,
after the model session had started). For every row and every pin: the environment directory exists (envs/<project>-<toolchain>, or
envs/mathlib-<toolchain> for PutnamBench), its lean-toolchain names the pinned toolchain, the toolchain is installed in ~/.elan, and
for a project row the module's .olean is built (.lake/build/lib/lean/<Module/Path>.olean). Prints one line per problem and exits 1 on
any problem; "envs ok" and exit 0 otherwise.
    python3 infra/open_package/check_envs.py --rows ROWS.jsonl [--root .] [--elan ~/.elan]"""
from __future__ import annotations

import argparse, json, os, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PROJECT_DIRS = {"strata": "strata", "cslib": "cslib", "physlib": "physlib", "arklib": "arklib", "leanpool": "leanpool", "putnambench": "mathlib"}


def check(rows: list[dict], root: Path, elan: Path) -> list[str]:
    bad = []
    for r in rows:
        src = r["source"]
        if src not in PROJECT_DIRS:
            bad.append(f"{r['name']}: unknown source {src!r}"); continue
        for vi in r["version_info"]:
            for ver in vi:
                env = root / "envs" / f"{PROJECT_DIRS[src]}-{ver}"
                if not env.is_dir():
                    bad.append(f"{r['name']}: no environment {env.relative_to(root) if env.is_relative_to(root) else env}"); continue
                tc = (env / "lean-toolchain").read_text().strip() if (env / "lean-toolchain").exists() else ""
                if not tc.endswith(":" + ver):
                    bad.append(f"{r['name']}: {env.name}/lean-toolchain is {tc!r}, pin {ver}")
                tcdir = elan / "toolchains" / tc.replace("/", "--").replace(":", "---")
                if not (tcdir / "bin" / "lean").exists():
                    bad.append(f"{r['name']}: toolchain {tc} not installed ({tcdir})")
                if src != "putnambench":
                    olean = env / ".lake/build/lib/lean" / Path(r["file_path"]).with_suffix(".olean")
                    if not olean.exists():
                        bad.append(f"{r['name']}: module not built: {olean.relative_to(env)} in {env.name}")
                elif not (env / ".lake/build/lib/lean/Mathlib.olean").exists() and not (env / ".lake/build/lib/lean/Mathlib").is_dir():
                    bad.append(f"{r['name']}: Mathlib not built in {env.name}")
    return bad


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--rows", required=True)
    ap.add_argument("--root", default=str(ROOT))
    ap.add_argument("--elan", default=os.environ.get("ELAN_HOME") or str(Path.home() / ".elan"))
    a = ap.parse_args()
    rows = [json.loads(l) for l in Path(a.rows).read_text().splitlines() if l.strip()]
    bad = check(rows, Path(a.root).resolve(), Path(a.elan).expanduser())
    for b in bad:
        print("MISSING " + b)
    print(f"envs {'FAILED: ' + str(len(bad)) + ' problem(s)' if bad else 'ok'}: {len(rows)} rows")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
