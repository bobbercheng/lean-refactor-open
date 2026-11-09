#!/usr/bin/env python3
"""Op `sonnet_lintdrop` (gap lane sonnet, surface / lexer): delete the simp arguments that Lean's OWN linter reports as unused.

Lean (>= 4.27, on by default) emits `linter.unusedSimpArgs` warnings ("This simp argument is unused: ... Omit it from the simp argument
list") with the exact source range of every `simp [..]` / `simp only [..]` / `simpa` / `simp_all` / `dsimp` argument that never fired.
An open proof that carries many such arguments (long `simp only [...]` lists written by a model that never ran a ddmin on a slow row)
saves 2 tokens per argument and, because the simp set shrinks, often heartbeats too. This is the cheap sibling of `sonnet_listdrop`
(which finds the same units by compiling every single deletion: 20-40 compiles per row): here ONE compile of the proof (plus a `#eval 0`
marker that tells where the proof starts in the file) yields the whole set of deletable arguments, and the gate verifies the result.

Rule (pure text surgery driven by Lean's feedback; no table, no row name, no proof text):
  1. query(): compile `proof + "\\n#eval 0"` on the primary pin; the marker message tells the proof's first line; every
     `linter.unusedSimpArgs` message's pos / endPos is converted to an offset in the proof and accepted only when it is EXACTLY one item
     of a bracket list `[a, b, c]` found by bracket pairing (comments and strings masked);
  2. candidates(): (a) all reported items removed at once, (b) the lists one by one (largest token saving first). An item run at the end of
     a list takes the comma before it; a list whose items are all unused loses its brackets (`simp only [a, b]` -> `simp only`).
The gate keeps a candidate only if it compiles on every pin and scores higher; arguments unused on the primary pin but used on another
pin make the union fail there, so the per-list fallbacks matter.
"""
from __future__ import annotations

# provenance: research lane gaplane-sonnet (worktree lra-gl-sonnet), commit 0024646, ported unchanged into open-post-v3 (2026-11-04)

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post.sonnet_listdrop import _split_items  # noqa: E402
from scorer.tokenize import count_tokens  # noqa: E402

FAMILY = "sonnet_lintdrop"
KINDS = ("linter.unusedSimpArgs",)
MARK = "#eval 0"


def _line_starts(text: str) -> list[int]:
    out, p = [], 0
    for ln in text.split("\n"):
        out.append(p)
        p += len(ln) + 1
    return out


def _offset(starts: list[int], line0: int, line: int, col: int) -> int | None:
    """Offset in the proof of Lean position (1-based line, 0-based column) when the proof's first line is file line `line0`."""
    i = line - line0
    if i < 0 or i >= len(starts):
        return None
    return starts[i] + col


def marker_line(messages) -> int | None:
    """File line of the `#eval 0` marker (the last information message "0" at column 0)."""
    best = None
    for m in messages or []:
        if not isinstance(m, dict) or m.get("severity") != "information":
            continue
        if K.msg_text(m).strip() != "0":
            continue
        pos = m.get("pos") or {}
        if pos.get("column") == 0 and isinstance(pos.get("line"), int):
            best = pos["line"]
    return best


def reported_ranges(proof: str, messages) -> list[tuple[int, int]]:
    """(start, end) offsets in `proof` of every argument the linter reports unused (needs the marker to be present in `messages`)."""
    ml = marker_line(messages)
    if ml is None:
        return []
    n = proof.count("\n") + 1
    line0 = ml - n
    if line0 < 1:
        return []
    starts = _line_starts(proof)
    out = []
    for m in messages or []:
        if not isinstance(m, dict) or m.get("kind") not in KINDS or m.get("severity") != "warning":
            continue
        p, q = m.get("pos") or {}, m.get("endPos") or {}
        try:
            a = _offset(starts, line0, p["line"], p["column"])
            b = _offset(starts, line0, q["line"], q["column"])
        except Exception:  # noqa: BLE001
            continue
        if a is None or b is None or not (0 <= a < b <= len(proof)):
            continue
        out.append((a, b))
    return sorted(set(out))


def lists(body: str):
    """[(open, close, items)] for every bracket list of the body, items = [(start, end)] depth-0 comma items (blanks trimmed)."""
    mask = _mask(body)
    res = []
    for o, c in sorted(_pairs(body, mask).items()):
        if body[o] != "[" or mask[o] or mask[c]:
            continue
        res.append((o, c, _split_items(body, mask, o + 1, c)))
    return res


def plan(body: str, ranges: list[tuple[int, int]]):
    """Group the reported ranges (offsets in BODY) by the bracket list that has exactly that item. Returns [(open, close, items, removed)]
    where removed is the sorted list of item indices; ranges that are not exactly one item are dropped (position mismatch = no edit)."""
    out = []
    for o, c, items in lists(body):
        rem = []
        for k, (a, b) in enumerate(items):
            if a < b and (a, b) in ranges:
                rem.append(k)
        if rem:
            out.append((o, c, items, rem))
    return out


def _spans(body: str, o: int, c: int, items, rem) -> list[tuple[int, int]]:
    n = len(items)
    if len(rem) == n:
        s = o
        while s > 0 and body[s - 1] in " \t":
            s -= 1
        return [(s, c + 1)]
    spans, k = [], 0
    while k < len(rem):
        j = k
        while j + 1 < len(rem) and rem[j + 1] == rem[j] + 1:
            j += 1
        i0, i1 = rem[k], rem[j]
        if i1 < n - 1:
            spans.append((items[i0][0], items[i1 + 1][0]))
        else:
            spans.append((items[i0 - 1][1], items[i1][1]))
        k = j + 1
    return spans


def apply_plan(body: str, groups) -> str:
    spans = []
    for o, c, items, rem in groups:
        spans += _spans(body, o, c, items, rem)
    spans.sort()
    out, last = [], 0
    for s, e in spans:
        if s < last:
            return body
        out.append(body[last:s])
        last = e
    out.append(body[last:])
    return "".join(out)


def query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None):
    """One compile of the proof with the end marker; returns {"ranges": [(start, end)]} in BODY coordinates, or None."""
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return None
        head, body = hb
        full = proof.rstrip()
        if not full.startswith(head.rstrip()) and not (head + body).startswith(full[:20]):
            return None
        r = run(full + "\n" + MARK, None)
        msgs = getattr(r, "messages", None)
        rng = reported_ranges(full, msgs)
        off = len(head)
        body_rng = [(a - off, b - off) for a, b in rng if a >= off]
        if stats is not None:
            stats[FAMILY] = {"reported": len(rng)}
        return {"ranges": body_rng}
    except Exception as e:  # noqa: BLE001
        if e.__class__.__name__ == "_Stop":
            raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:160]}")
        return None


def has_sites(proof: str, statement: str) -> bool:
    """Pure pre-check: some simp-family bracket list exists (the linter can only speak about those)."""
    hb = K.head_body(proof, statement)
    if hb is None:
        return False
    return bool(re.search(r"\b(simp|simp_all|simpa|dsimp|simp_arith|norm_num|field_simp)\b[^\n\[]*\[", hb[1]))


def candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None):
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return []
        head, body = hb
        rng = (ctx or {}).get("ranges")
        if not rng:
            return []
        groups = plan(body, [tuple(x) for x in rng])
        if not groups:
            return []
        em = K.Emitter(proof, statement, head, body, int(max_per_op or 8))

        def saved(g):
            return count_tokens(body) - count_tokens(apply_plan(body, [g]))

        total = len(groups)
        nitems = sum(len(g[3]) for g in groups)
        em.add(f"{FAMILY}:all", apply_plan(body, groups), f"all {nitems} unused simp args ({total} lists) dropped")
        if total > 1:
            for g in sorted(groups, key=lambda g: -saved(g))[:max(1, em.cap - 1)]:
                em.add(f"{FAMILY}:list", apply_plan(body, [g]), f"{len(g[3])} unused simp args of one list dropped")
        return em.out
    except Exception:  # noqa: BLE001
        return []
