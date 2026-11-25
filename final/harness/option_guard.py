#!/usr/bin/env python3
"""Option guard: this package accepts, keeps and writes no proof that sets a `debug.*` option.

Debug options are not allowed in benchmark proofs. The guard rejects every `set_option debug.<name>` (any name, any spacing, a
comment between the words, `«debug»`, inside a chain of `set_option .. in` / `open .. in` lines). Other options, such as
`smartUnfolding`, `maxRecDepth` or `backward.isDefEq.*`, are not rejected.

The rule that carries this is at the level of one token and reads no comment and no string: an option name is one identifier, which
holds no space and no comment, so a text sets a debug option only if it holds the name `debug.` (or `«debug».`) at the start of an
identifier. Every such text is rejected, wherever the name stands. The price is that a proof which uses a local name `debug` with a
projection (`debug.1`), or which holds `debug.` in a comment or a string, is rejected too; none of the 60 released reference proofs
does. One more rule reads the text as it is and with its comments removed the scorer's way: `set_option` followed by `debug.` in any
letter case. Every rule takes time linear in the text.

  debug_option(text)       THE predicate: the reason (one line) when `text` sets a debug option, else None
  check_forbidden(code)    the Arena's forbidden list (scorer/forbidden.check_forbidden, an exact copy of the Arena's) followed by the
                           predicate. Every gate of the package imports check_forbidden from here, so a candidate with a debug option
                           is handled exactly like one that fails the Arena's list: it is not compiled, not banked, not adopted, and
                           the model reads `forbidden construct: <the reason>`
  debug_rows(recs)         the names of the records ({"name", "proof"}) whose proof sets a debug option
  assert_clean(recs, where)  raises DebugOptionError naming the rows; every writer of a proofs file calls it
  check_input(recs, rows, mode, where)  an input file's records: mode "fail" (the default) raises DebugOptionError naming the
                           rows; mode "reference" replaces each such record by the row's reference proof from the rows file (the
                           record a row has before any work: source "seed", stored score 33.33). No older proof is searched for.

    python3 harness/option_guard.py PROOFS.jsonl --rows ROWS.jsonl [--debug-rows fail|reference]
exit 0: no row sets a debug option (with `reference`: the rows named on stdout were replaced, PROOFS.jsonl was rewritten by rename and
its first content kept beside it as PROOFS.jsonl.debug-rows); exit 2: rows named on stderr, nothing written (also for a file with a
line that is not JSON, when its text holds a debug option); exit 1: the file or the rows file cannot be read as JSONL."""
from __future__ import annotations

import json, os, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scorer.forbidden import check_forbidden as arena_check_forbidden, strip_lean_comments  # noqa: E402

REASON = "set_option debug.* (debug options are not allowed in benchmark proofs)"
MODES = ("fail", "reference")
SEED_SCORE = 33.33   # a reference proof's score (L 0, H 0, Z 100), as harness/open_package.export writes it for a seed row
# the name `debug.` at the start of an identifier: not after a character that continues an identifier or a name (`x.debug.y`,
# `trace.debug.z` and `mydebug.w` are other names); `«debug».` is the same name, whatever stands before the guillemet
_DEBUG_NAME = re.compile(r"(?<![\w.'!?])«?debug»?\.")
_SET_DEBUG = re.compile(r"set_option\s+debug\s*\.", re.IGNORECASE)


class DebugOptionError(ValueError):
    """A proof that sets a debug option reached a place where it must not be kept or written."""


def _views(text: str):
    """`text` as it is and with its comments removed the scorer's way (strings kept), for the rule that reads letter case
    loosely. Guillemets go in both views (`«debug».x` is `debug.x`). Both views take linear time."""
    for v in (text, strip_lean_comments(text)):
        yield v.replace("«", "").replace("»", "")


def debug_option(text: str | None) -> str | None:
    """The reason (one line) when `text` sets a debug option, else None."""
    if not text:
        return None
    if "debug" not in text.lower():   # every rejected form holds the word: nothing more to read
        return None
    if _DEBUG_NAME.search(text):   # the token-level rule: no comment, quote or line break between other words can hide the name
        return REASON
    for v in _views(text):
        if _SET_DEBUG.search(v):
            return REASON
    return None


def check_forbidden(code: str) -> str | None:
    """The label of the first hit: the Arena's forbidden list first (its labels unchanged), then the option guard; None when clean."""
    return arena_check_forbidden(code) or debug_option(code)


def debug_rows(recs) -> list:
    """The names of the records whose proof sets a debug option, in order."""
    return [r.get("name") for r in recs if isinstance(r, dict) and debug_option(r.get("proof"))]


def assert_clean(recs, where: str) -> None:
    bad = debug_rows(recs)
    if bad:
        raise DebugOptionError(f"{where}: {len(bad)} row(s) carry a `set_option debug.*` option, which is not allowed in benchmark "
                               f"proofs: {', '.join(map(str, bad))}. Nothing was written.")


def reference_record(name: str, row: dict) -> dict:
    """The record of a row before any work: its reference proof from the rows file, as the export writes a seed row."""
    return {"name": name, "proof": (row.get("src") or "").rstrip() + "\n", "source": "seed", "stored_score": SEED_SCORE, "tokens": None,
            "heartbeats": None, "option_guard": "the input proof set a debug option; replaced by the reference proof"}


def check_input(recs: list, rows: dict, mode: str = "fail", where: str = "input") -> tuple[list, list]:
    """(records, indices replaced). mode "fail": DebugOptionError naming every row whose proof sets a debug option. mode "reference":
    those records become reference_record(); a row that is not in `rows`, or whose reference proof sets a debug option too, raises."""
    if mode not in MODES:
        raise ValueError(f"--debug-rows must be one of {MODES}, not {mode!r}")
    bad = [k for k, r in enumerate(recs) if isinstance(r, dict) and debug_option(r.get("proof"))]
    if not bad:
        return recs, []
    names = ", ".join(str(recs[k].get("name")) for k in bad)
    if mode == "fail":
        raise DebugOptionError(f"{where}: {len(bad)} row(s) carry a `set_option debug.*` option, which is not allowed in benchmark "
                               f"proofs: {names}. Such a proof is not kept. Remove these rows from the input, or "
                               f"pass --debug-rows reference (LRA_DEBUG_ROWS=reference for run.sh and post_fast/post_stage.sh) to "
                               f"replace each of them by the benchmark's reference proof before the stage starts.")
    out = list(recs)
    for k in bad:
        name = recs[k].get("name")
        row = rows.get(name)
        if row is None or not (row.get("src") or "").strip() or debug_option(row.get("src")):
            raise DebugOptionError(f"{where}: row {name} carries a `set_option debug.*` option and the rows file has no usable reference "
                                   f"proof for it (missing, or it sets a debug option itself). Nothing was written.")
        out[k] = reference_record(name, row)
    return out, bad


def read_jsonl(path) -> list:
    return [json.loads(l) for l in Path(path).read_text().splitlines() if l.strip()]


def check_file(path, rows_path, mode: str = "fail") -> list:
    """check_input() on a proofs file, in place: the names replaced ([] when the file was clean and left untouched). With replacements
    the file is rewritten by rename; its first content is kept once as <path>.debug-rows (never overwritten)."""
    path = Path(path)
    recs = read_jsonl(path)
    rows = {r["name"]: r for r in read_jsonl(rows_path)}
    out, bad = check_input(recs, rows, mode, str(path))
    if not bad:
        return []
    keep = path.with_name(path.name + ".debug-rows")
    if not keep.exists():
        keep.write_bytes(path.read_bytes())
    tmp = path.with_name(f"{path.name}.{os.getpid()}.guard.tmp")
    tmp.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in out))
    os.replace(tmp, path)
    return [recs[k].get("name") for k in bad]


def main(argv=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("proofs", help="a proofs file (JSONL: name, proof, ...)")
    ap.add_argument("--rows", required=True, help="the benchmark rows (JSONL; `src` is the reference proof)")
    ap.add_argument("--debug-rows", choices=MODES, default="fail",
                    help="fail (default): name the rows whose proof sets a debug option and exit 2; reference: replace each of them by "
                         "the benchmark's reference proof, in place")
    a = ap.parse_args(argv)
    try:
        done = check_file(a.proofs, a.rows, a.debug_rows)
    except DebugOptionError as e:
        print(f"option guard: {e}", file=sys.stderr)
        return 2
    except (OSError, ValueError) as e:   # not readable as JSONL: read as one text, so that a broken file is never taken for a clean one
        try:
            hit = debug_option(Path(a.proofs).read_text(errors="replace"))
        except OSError:
            hit = None
        if hit:
            print(f"option guard: {a.proofs}: a line does not parse as JSON and the text holds a `set_option debug.*` option, which "
                  f"is not allowed in benchmark proofs. Nothing was written.", file=sys.stderr)
            return 2
        print(f"option guard: {a.proofs}: not checked, the file or the rows file cannot be read as JSONL ({type(e).__name__}: {e})",
              file=sys.stderr)
        return 1
    if done:
        print(f"option guard: {a.proofs}: {len(done)} row(s) set a debug option and were replaced by the reference proof (stored score "
              f"{SEED_SCORE}): {', '.join(map(str, done))}; the file as it was: {a.proofs}.debug-rows")
    else:
        print(f"option guard: {a.proofs}: no row sets a debug option")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
