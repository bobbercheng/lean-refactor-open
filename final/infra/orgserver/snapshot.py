#!/usr/bin/env python3
"""Interim proofs file of a running job (2026-10-31; README.md "If the job is cut short"). harness/open_package.py writes







"""
from __future__ import annotations

import argparse, contextlib, io, os, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
SKIP = {"interim", "proofs.jsonl", "proofs.jsonl.tmp", "summary.json"}


def shadow(out: Path) -> Path:
    """<out>/interim with one symlink per entry of <out> (refreshed: new entries appear as the run goes on)."""
    sh = out / "interim"
    sh.mkdir(parents=True, exist_ok=True)
    for p in out.iterdir():
        if p.name in SKIP or p.name.startswith("."):
            continue
        link = sh / p.name
        if link.is_symlink() or link.exists():
            if link.is_symlink() and os.readlink(link) == str(p.resolve()):
                continue
            if link.is_symlink():
                link.unlink()
            else:
                continue
        link.symlink_to(p.resolve(), target_is_directory=p.is_dir())
    return sh


def snapshot(rows: str, hbs: str, out: Path, extra: list[str]) -> dict:
    from harness import open_package as OP
    sh = shadow(out)
    a = OP.build_parser().parse_args(["export", "--rows", rows, "--heartbeats", hbs, "--out", str(sh), *extra, "--no-audit"])
    names, rows_d, _ = OP.load_rows(a.rows, a.heartbeats)
    if a.problems:
        names = [n for n in names if n in set(a.problems)]
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):                                                      
        summ = OP.export(a, names, rows_d)
    return summ


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    extra = []
    if "--" in argv:
        i = argv.index("--"); argv, extra = argv[:i], argv[i + 1:]
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--rows", required=True)
    ap.add_argument("--heartbeats", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--promote", action="store_true", help="also copy it to <out>/proofs.jsonl when that does not exist")
    a = ap.parse_args(argv)
    out = Path(a.out)
    stamp = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    if not out.is_dir():
        print(f"[{stamp}] snapshot: {out} does not exist yet")
        return 1
    rc = 0
    try:
        summ = snapshot(a.rows, a.heartbeats, out, extra)
        print(f"[{stamp}] snapshot: {out / 'interim' / 'proofs.jsonl'}: {summ.get('rows')} rows, sources {summ.get('sources')}, "
              f"stored mean {summ.get('stored_mean')}")
    except Exception as e:                                       
        print(f"[{stamp}] snapshot failed: {type(e).__name__}: {e}")
        rc = 1
    if a.promote:                                                                                
        from infra.orgserver import orgtools
        print(f"[{stamp}] snapshot: {orgtools.promote(out)}")
    return rc


if __name__ == "__main__":
    raise SystemExit(main())
