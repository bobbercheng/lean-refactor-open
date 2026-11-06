#!/usr/bin/env python3
"""Kernel-skip op "kskip" of the open post-step (harness/open_post.py; 2026-11-03 ~12:15 UTC, "Trio + Q5 kernel-skip"):
a proof whose closer is a `decide` with the `+kernel` flag makes the kernel re-check the decision in an auxiliary theorem; Lean's option
`debug.skipKernelTC` (not on the Arena's forbidden list; scorer/forbidden.py unchanged) set around that closer skips that re-check.

  site      the proof's LAST tactic (after its last `;`, `<;>` or `by` on the last code line, comments and strings masked) is
            `decide` with `+kernel` among its `+flag` / `-flag` options (never `+native`), and is not already prefixed by the option.
  generate  (every candidate costs tokens; the caller's gate prices them)
    kskip:inplace  that closer C -> `set_option debug.skipKernelTC true in C`, the rest of the proof unchanged
    kskip:unfold   the whole body -> ` by` / `unfold P` / `set_option debug.skipKernelTC true in C` (one tactic per line), P the head
                   predicate of the statement's conclusion: as written in the statement (after its binders and leading Pi binders
                   `(x : T) →` / `∀ x, `), and the head constant Lean reports for it when the implied family's env query answered for
                   this exact proof (ctx "implied_query"), when that name differs
Pure text: no compile, no table, no row name; P and C come from the statement and the proof. Nothing here decides anything: the
caller measures every candidate and keeps it only when it compiles on every pin and scores higher (harness/open_post.py)."""
from __future__ import annotations

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post.d4_implied import DECL_RE  # noqa: E402

FAMILY = "kskip"
OPS = ("kskip:inplace", "kskip:unfold")
SKIP = "set_option debug.skipKernelTC true in"
CLOSER_RE = re.compile(r"^decide(?:[ \t]+[+-][A-Za-z][\w.]*)*$")
SEP_RE = re.compile(r"<;>|;|(?:(?<![\w.'])|(?<=[^\w.']'))by(?![\w'])")   # d4_implied.closer's split (`∘'by`: the prime ends a token)
OPEN_B, CLOSE_B = "([{⦃", ")]}⦄"
HEAD_STOP = frozenset({"fun", "λ", "if", "then", "else", "match", "let", "have", "show", "by", "do", "Type", "Sort", "Prop", "True",
                       "False", "not"})
MAX_PER_OP = 4


def closer_span(body: str) -> tuple[int, int, str] | None:
    """(start, end, closer text whitespace-normalised) of the kernel-checked decide closer ending the body (module docstring, "site"),
    else None."""
    mask = _mask(body)
    clean = "".join(" " if mask[i] and body[i] != "\n" else body[i] for i in range(len(body)))
    end = len(clean.rstrip())
    if end == 0:
        return None
    ls = clean.rfind("\n", 0, end) + 1
    line = clean[ls:end]
    cuts = [m.end() for m in SEP_RE.finditer(line)]
    seg0 = cuts[-1] if cuts else 0
    seg = line[seg0:]
    lo = ls + seg0 + (len(seg) - len(seg.lstrip()))
    c = re.sub(r"\s+", " ", seg.strip())
    if not CLOSER_RE.match(c) or "+kernel" not in c.split() or "native" in c:
        return None
    if clean[:lo].rstrip().endswith(" in") and re.search(r"debug\.skipKernelTC\s+true\s+in\s*$", clean[:lo]):
        return None
    return lo, end, c


def statement_head(statement: str) -> str | None:
    """The head identifier of the statement's conclusion as written (module docstring, kskip:unfold), else None."""
    m = DECL_RE.match(statement)
    if not m:
        return None
    rest = statement[m.end():]
    mask = _mask(rest)
    pairs = _pairs(rest, mask)
    i, n = 0, len(rest)
    while True:   # the binders before the type's colon
        while i < n and rest[i].isspace():
            i += 1
        if i < n and rest[i] in OPEN_B and i in pairs:
            i = pairs[i] + 1
            continue
        break
    if i >= n or rest[i] != ":" or rest[i:i + 2] == ":=":
        return None
    ty, j = rest, i + 1
    while True:   # leading Pi binders of the conclusion
        while j < n and ty[j].isspace():
            j += 1
        if j < n and ty[j] in OPEN_B and j in pairs:
            k = pairs[j] + 1
            while k < n and ty[k].isspace():
                k += 1
            if ty.startswith("→", k):
                j = k + 1
                continue
            if ty.startswith("->", k):
                j = k + 2
                continue
            return None   # a parenthesised conclusion: no plain head
        if ty.startswith("∀", j) or ty.startswith("Π", j):
            depth, k = 0, j + 1
            while k < n:
                ch = ty[k]
                if not mask[k]:
                    if ch in OPEN_B:
                        depth += 1
                    elif ch in CLOSE_B:
                        depth -= 1
                    elif ch == "," and depth == 0:
                        break
                k += 1
            if k >= n:
                return None
            j = k + 1
            continue
        break
    mh = re.match(K.IDENT, ty[j:])
    if not mh:
        return None
    h = mh.group(0)
    if h in HEAD_STOP or h.split(".")[-1] in HEAD_STOP:
        return None
    return h


def heads(statement: str, ctx: dict | None, proof: str) -> list[str]:
    """kskip:unfold's predicates: the written head, then Lean's name for it (the implied query's answer for this exact proof)."""
    out = []
    h = statement_head(statement)
    if h:
        out.append(h)
    q = (ctx or {}).get("implied_query") or {}
    if q.get("answered") and (ctx or {}).get("implied_query_for") == K.proof_key(proof):
        lh = q.get("head")
        if isinstance(lh, str) and K.IDENT_RE.match(lh) and lh not in out and h is not None:
            out.append(lh)   # only when the statement has a plain head (the reported head is that head's full name)
    return out


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int | None = None,
               ctx: dict | None = None) -> list[dict]:
    hb = K.head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    sp = closer_span(body)
    if sp is None:
        return []
    lo, hi, c = sp
    em = K.Emitter(proof, statement, head, body, int(max_per_op) if max_per_op else MAX_PER_OP)
    em.add("kskip:inplace", body[:lo] + f"{SKIP} {body[lo:hi]}" + body[hi:], f"`{c}` -> `{SKIP} {c}`", save=False)
    for P in heads(statement, ctx, proof):
        em.add("kskip:unfold", f" by\n  unfold {P}\n  {SKIP} {c}", f"unfold {P}; {SKIP} {c}", save=False)
    return em.out
