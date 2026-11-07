"""The `... in` chain edit for a row whose reference proof fails the measured compile (setup step `envfix`, 2026-11-01; the same code as













"""
from __future__ import annotations

import json
import re
import shutil
from pathlib import Path

CHAIN = re.compile(r"(open|omit|set_option|include|unseal|variable)\b.*\bin$")


def chain_edit(prefix: str) -> tuple[list[str], list[tuple[int, str, str]]]:
    """(the prefix's lines with the chain's trailing ` in` removed, [(1-based line, old, new)]). Walks up from the declaration over
"""
    lines = prefix.split("\n"); i = len(lines) - 2; changed = []
    while i >= 0:
        s = lines[i].strip()
        if s.endswith("-/"):
            while i >= 0 and not lines[i].lstrip().startswith("/-"):
                i -= 1
            i -= 1
            continue
        if CHAIN.match(s):
            new = re.sub(r"\s+in\s*$", "", lines[i]); changed.append((i + 1, lines[i], new)); lines[i] = new; i -= 1
            continue
        if s.startswith("@[") or s == "":
            i -= 1
            continue
        break
    return lines, sorted(changed)


def pins(row: dict) -> list[str]:
    return [next(iter(d)) for d in row.get("version_info") or []]


def plan(row: dict) -> list[dict]:
    """One entry per pin whose file has a chain to edit: {"pin", "path", "changes"}. Pins without the file or the declaration are skipped."""
    from scorer import compile as C
    out = []
    for pin in pins(row):
        f = C.project_env_dir(row["source"], pin) / row["file_path"]
        if not f.exists():
            continue
        try:
            prefix = C.file_prefix(row, pin)
        except (OSError, ValueError):
            continue
        _, changes = chain_edit(prefix)
        if changes:
            out.append({"pin": pin, "path": f, "changes": changes})
    return out


def relevant(row: dict) -> bool:
    """The chain can change validity (scorer.compile._ATTACHED_IN on the newest pin's core: omit / include / unseal / variable /
"""
    from scorer import compile as C
    pins_ = pins(row)
    if not pins_:
        return False
    try:
        core, _ = C.split_modifiers(C.file_prefix(row, pins_[0]))
    except (OSError, ValueError):
        return False
    return bool(C._ATTACHED_IN.search(core))


def apply(row: dict, entries: list[dict], backup: Path) -> list[dict]:
    """Make the edits of `entries` (from plan()), one per distinct real file (two pins resolving to one file are edited once). Each file
"""
    from scorer import compile as C
    done, seen = [], set()
    for e in entries:
        f = Path(e["path"]); real = f.resolve()
        if real in seen:
            continue
        seen.add(real)
        b = backup / str(real).lstrip("/").replace("/", "__")
        b.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(real, b)
        prefix = C.file_prefix(row, e["pin"]); text = real.read_text()
        if not text.startswith(prefix):
            continue
        lines, changes = chain_edit(prefix)
        real.write_text("\n".join(lines) + text[len(prefix):])
        done.append(dict(e, path=real, backup=b, changes=changes, row_source=row["source"]))
        _mark(C.project_env_dir(row["source"], e["pin"]), real, [ln for ln, _, _ in changes])
    return done


MARKER = ".lra_envfix.json"                                                                                                     


def _mark(env_dir, real: Path, lines, remove: bool = False) -> None:
    try:
        root = Path(env_dir).resolve(); rel = str(real.resolve().relative_to(root)); m = root / MARKER
        d = json.loads(m.read_text()) if m.exists() else {}
        if remove:
            d.pop(rel, None)
        else:
            d[rel] = lines
        if d:
            m.write_text(json.dumps(d, indent=1))
        elif m.exists():
            m.unlink()
    except (OSError, ValueError):
        pass


def restore(entries: list[dict]) -> None:
    """Undo exactly the recorded lines (new -> old), so another row's edit in the same file or a later change elsewhere is kept; a line
"""
    for e in reversed(entries):
        f = Path(e["path"])
        try:
            lines = f.read_text().split("\n")
        except OSError:
            continue
        for ln, old, new in e["changes"]:
            if 0 < ln <= len(lines) and lines[ln - 1] == new:
                lines[ln - 1] = old
        f.write_text("\n".join(lines))
        try:
            from scorer import compile as C
            _mark(C.project_env_dir(e["row_source"], e["pin"]), f, [], remove=True) if e.get("row_source") else None
        except Exception:                
            pass


def check_reference(row: dict, timeout: int = 1800) -> dict:
    """The row's reference proof on its newest pin through the scorer's MEASURED compile (the path every candidate is scored on)."""
    from scorer import compile as C
    pin = pins(row)[0]
    try:
        r = C.compile_project(row, row["src"], pin, timeout=timeout)
    except Exception as e:                
        return {"ok": False, "error": f"{type(e).__name__}: {e}"[:300], "timed_out": False}
    return {"ok": bool(r.ok and r.heartbeats is not None and not r.hb_blind), "error": ((r.errors or [""])[0])[:300],
            "timed_out": bool(getattr(r, "timed_out", False)), "heartbeats": r.heartbeats}


def main(argv=None) -> int:
    """Standalone step (independent of the heartbeats file, so it also runs when official references are supplied): every



"""
    import argparse, sys, time
    from concurrent.futures import ThreadPoolExecutor
    ap = argparse.ArgumentParser(description=main.__doc__.split("\n")[0])
    ap.add_argument("--rows", required=True); ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--backup", default=None, help="backup directory (default: <rows>.envfix/)"); ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    rows = [json.loads(l) for l in open(a.rows) if l.strip()]
    backup = Path(a.backup) if a.backup else Path(a.rows).with_name(Path(a.rows).name + ".envfix")
    log = lambda m: print(f"[envfix {time.strftime('%H:%M:%S')}] {m}", flush=True)
    files = {}
    for r in rows:
        if r.get("source") != "putnambench":
            for pin in pins(r):
                files.setdefault((r.get("source"), pin, r.get("file_path")), []).append(r["name"])
    cand = []
    for r in rows:                                                                                                    
        if r.get("source") == "putnambench" or not relevant(r) or not plan(r):
            continue
        if any(n != r["name"] for pin in pins(r) for n in files.get((r.get("source"), pin, r.get("file_path")), [])):
            log(f"{r['name']}: `... in` chain above the declaration, but its file is shared with another row: left alone"); continue
        cand.append(r)
    log(f"{len(rows)} row(s); {len(cand)} with a validity-relevant chain in an unshared file: checking their references")
    with ThreadPoolExecutor(max_workers=max(1, a.jobs)) as ex:
        first = dict(zip([r["name"] for r in cand], ex.map(check_reference, cand)))
    fixed, kept, failed = [], [], []
    for r in cand:
        c = first[r["name"]]
        if c["ok"]:
            kept.append(r["name"]); continue
        _e = (c["error"] or "").lower()
        if c["timed_out"] or ("timed out" in _e and "deterministic" not in _e):                                                               
            log(f"{r['name']}: reference timed out: not edited ({c['error'][:120]})"); failed.append(r["name"]); continue
        if a.dry_run:
            log(f"{r['name']}: reference fails the measured compile ({c['error'][:120]}): WOULD edit"); continue
        applied = []
        try:
            applied = apply(r, plan(r), backup)
            again = check_reference(r)
        except Exception as e:                
            if applied:
                restore(applied)
            log(f"{r['name']}: edit failed ({type(e).__name__}: {e}); restored"); failed.append(r["name"]); continue
        if again["ok"]:
            fixed.append(r["name"])
            log(f"{r['name']}: reference failed ({c['error'][:100]}); chain edit on {len(applied)} file(s) -> compiles, {again['heartbeats']} hb")
        else:
            restore(applied); failed.append(r["name"])
            log(f"{r['name']}: still failing after the chain edit ({again['error'][:100]}); restored")
    log(f"ENVFIX DONE fixed {len(fixed)}, unchanged (reference ok) {len(kept)}, not fixed {len(failed)}"
        + (f"; backups in {backup}; setup.sh restores the marked files before it rebuilds an environment" if fixed else ""))
    return 0


if __name__ == "__main__":
    import sys as _sys
    _sys.path.insert(0, str(Path(__file__).resolve().parents[2]))
    raise SystemExit(main())
