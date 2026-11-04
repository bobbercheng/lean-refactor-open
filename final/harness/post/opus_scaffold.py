#!/usr/bin/env python3
"""Structural op "opus_scaffold" of the open post-step (gap lane opus, 2026-11-03): remove scaffolding `have` / `obtain` steps.

  site      a tactic step `have NAME ... :=` / `have : T :=` (name `this`) / `obtain PAT := e` / `have ⟨..⟩ := e`, with all its
            continuation lines (single- or multi-line, also the first step of a `·` bullet), whose bound names are never written
            again in the rest of its block (only automation could read them: omega, linarith, simp_all, assumption, ...), or are
            written ONLY as items of automation hint lists `[..]` (then the items go too).
            Comments / strings: a step whose text holds a comment is skipped.
  generate  scaffold:joint  every site removed at once
            scaffold:del    one site removed (largest saving first); a bullet-line site hands its bullet to the next step
  screen    query(): all candidates in ONE d4_measure file (the incumbent the control); only the ones predicted to read higher are
            proposed (Lean decides whether the remaining automation still closes the goal without the step).
Pure text plus the row's own environment (the screen compile). No row name, table or proof text."""
from __future__ import annotations

# provenance: research lane gaplane-opus (worktree lra-gl-opus), commit ef7dde5, ported unchanged into open-post-v3 (2026-11-04)

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from harness.post import opus_screen as SC  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "opus_scaffold"
MAX_PER_OP = 16
BULLET = "·"
STEP_RE = re.compile(r"^(?P<kw>have|haveI|obtain)\b(?P<rest>.*)$", re.S)
IDENT = re.compile(r"(?<![\w'.₀-₉])[A-Za-z_Ͱ-Ͽἀ-῿][\w'!?₀-₉ₐ-ₜͰ-Ͽ]*")
HINT_TAC = re.compile(r"\b(?:simp|simp_all|simpa|linarith|nlinarith|positivity|grind|norm_num|field_simp|aesop|omega|polyrith)\b[^\n\[]*\[")
KEYWORDS = {"have", "haveI", "obtain", "fun", "by", "at", "with", "using", "only", "rfl", "_", "show", "from", "this"}


def _indent(ln: str) -> int:
    return len(ln) - len(ln.lstrip(" "))


def _names(kw: str, rest: str) -> set[str] | None:
    """Names bound by the step (None: not understood)."""
    head = rest.split(":=", 1)[0]
    if kw in ("have", "haveI"):
        h = head.strip()
        if not h or h.startswith(":"):
            return {"this"}
        if h.startswith("⟨"):
            pat = h[:h.rfind("⟩") + 1] if "⟩" in h else None
            return None if pat is None else {t for t in IDENT.findall(pat) if t not in KEYWORDS}
        m = IDENT.match(h)
        return {m.group(0)} if m else None
    # obtain PAT (: T)? := e
    h = head.strip()
    if "|" in h:
        return None
    pat = h.split(":", 1)[0] if not h.startswith("⟨") else h[:h.rfind("⟩") + 1]
    return {t for t in IDENT.findall(pat) if t not in KEYWORDS} or None


def sites(body: str) -> list[dict]:
    mask = _mask(body)
    L = body.split("\n")
    offs, o = [], 0
    for ln in L:
        offs.append(o)
        o += len(ln) + 1
    out = []
    for i, ln in enumerate(L):
        s = ln.lstrip(" ")
        bullet = s.startswith(BULLET)
        if bullet:
            s2 = s[len(BULLET):]
            col = _indent(ln) + len(BULLET) + (len(s2) - len(s2.lstrip(" ")))
            s = s2.lstrip(" ")
        else:
            col = _indent(ln)
        m = STEP_RE.match(s)
        if not m or ":=" not in body[offs[i]:]:
            continue
        j = i + 1
        while j < len(L) and (not L[j].strip() or _indent(L[j]) > col):
            j += 1
        while j > i + 1 and not L[j - 1].strip():
            j -= 1
        a, b = offs[i], offs[j - 1] + len(L[j - 1])
        if any(mask[a:b]):
            continue
        step = "\n".join(L[i:j])
        if ":=" not in step and not re.search(r"\bfrom\b", step):
            continue
        if re.search(r"(?<![\w'])rfl(?![\w'])", m.group("rest").split(":=", 1)[0]):
            continue   # an `rfl` pattern substitutes: not scaffolding
        names = _names(m.group("kw"), m.group("rest"))
        if not names:
            continue
        # the scope: the rest of the enclosing block (lines at column >= col until a line at a smaller column)
        k = j
        while k < len(L) and (not L[k].strip() or _indent(L[k]) >= col or
                              (L[k].lstrip(" ").startswith(BULLET) and _indent(L[k]) >= col)):
            k += 1
        if j >= len(L) or k == j:
            continue   # the step is its block's last: nothing after it to close the goal
        scope_a, scope_b = offs[j], (offs[k - 1] + len(L[k - 1])) if k > j else offs[j]
        scope = body[scope_a:scope_b]
        if not scope.strip():
            continue   # nothing after the step in its block
        refs = [mm for mm in IDENT.finditer(scope) if mm.group(0) in names and not mask[scope_a + mm.start()]]
        hint_edits = []
        ok = True
        for mm in refs:
            e = _hint_item(body, scope_a + mm.start(), scope_a + mm.end())
            if e is None:
                ok = False
                break
            hint_edits.append(e)
        if not ok:
            continue
        out.append({"line": i, "end_line": j, "start": a, "end": b, "bullet": bullet, "col": col, "names": names,
                    "hints": hint_edits, "next_line": j if j < len(L) else None})
    return out


def _hint_item(body: str, a: int, b: int):
    """(start, end) of the hint-list item that is exactly the name at [a, b) (with its comma), else None."""
    # walk back to `[` or `,` on the same bracket level
    i = a - 1
    while i >= 0 and body[i] in " \n":
        i -= 1
    if i < 0 or body[i] not in "[,":
        return None
    j = b
    while j < len(body) and body[j] in " \n":
        j += 1
    if j >= len(body) or body[j] not in ",]":
        return None
    k = body.rfind("[", 0, a)
    if k < 0 or "]" in body[k:a]:
        return None
    lk = body.rfind("\n", 0, k) + 1
    if not HINT_TAC.search(body[lk:k + 1]):
        return None   # the list must belong to an automation tactic on the line of its `[`
    if body[i] == "," and body[j] == "]":
        return (i, b)                  # `, h]` -> `]`
    if body[i] == "[" and body[j] == ",":
        jj = j + 1
        while jj < len(body) and body[jj] == " ":
            jj += 1
        return (a, jj)                 # `[h, x` -> `[x`
    if body[i] == "," and body[j] == ",":
        return (i, b)                  # `, h,` -> `,`
    return ("all", k, j + 1)           # `[h]`: the whole list goes


def _apply(body: str, sel: list[dict]) -> str | None:
    L = body.split("\n")
    edits = []
    offs, o = [], 0
    for ln in L:
        offs.append(o)
        o += len(ln) + 1
    for s in sel:
        a = offs[s["line"]]
        b = offs[s["end_line"]] if s["end_line"] < len(L) else len(body)
        if s["bullet"]:
            nl = s["end_line"]
            if nl >= len(L) or _indent(L[nl]) != s["col"] or L[nl].lstrip(" ").startswith(BULLET):
                return None
            first = L[s["line"]]
            prefix = first[:len(first) - len(first.lstrip(" "))] + BULLET + " "
            edits.append((a, offs[nl] + s["col"], prefix))
        else:
            edits.append((a, b, ""))
        for h in s["hints"]:
            if h[0] == "all":
                k, e = h[1], h[2]
                st = k
                while st > 0 and body[st - 1] == " ":
                    st -= 1
                edits.append((st, e, ""))
            else:
                edits.append((h[0], h[1], ""))
    edits.sort()
    for x, y in zip(edits, edits[1:]):
        if x[1] > y[0]:
            return None
    out = body
    for a, b, t in sorted(edits, reverse=True):
        out = out[:a] + t + out[b:]
    return out


def raw_candidates(body: str) -> list[tuple[str, str, str]]:
    if SC.unchecked(body):
        return []
    ss = sites(body)
    t0 = count_tokens(body)
    out = []
    singles = []
    for s in ss:
        nb = _apply(body, [s])
        if nb is not None and count_tokens(nb) < t0:
            singles.append((t0 - count_tokens(nb), s, nb))
    singles.sort(key=lambda x: -x[0])
    if len(singles) >= 2:
        sel = []
        for _, s, _ in singles:   # greedy: the largest savings first, a step that overlaps a chosen one is left out
            if _apply(body, sel + [s]) is not None:
                sel.append(s)
        nb = _apply(body, sel) if len(sel) >= 2 else None
        if nb is not None:
            out.append(("joint", nb, f"{len(sel)} scaffolding steps removed"))
    for d, s, nb in singles:
        out.append(("del", nb, f"step at line {s['line'] + 1} ({', '.join(sorted(s['names']))}) removed, -{d} tokens"))
    return out


def has_sites(proof: str, statement: str) -> bool:
    try:
        body = split_declaration(proof, statement)
        return bool(body) and bool(raw_candidates(body))
    except Exception:
        return False


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return []
        head, body = hb
        em = K.Emitter(proof, statement, head, body, int(max_per_op or MAX_PER_OP))
        raws = raw_candidates(body)
        scr = (ctx or {}).get("scaffold_screen") if (ctx or {}).get("scaffold_key") == K.proof_key(proof) else None
        if scr is not None:
            up = dict(scr.get("up", []))
            uns = set(scr.get("unscreened", []))
            raws = sorted([r for r in raws if r[1] in up], key=lambda r: -up[r[1]]) + [r for r in raws if r[1] in uns]
        for var, nb, note in raws:
            em.add(f"{FAMILY}:{var}", nb, note)
        return em.out
    except Exception:
        return []


def query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None) -> dict | None:
    """One screen file (harness/post/opus_screen.py: measured, else plain) over the candidates; {} when nothing to screen."""
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return {}
        _, body = hb
        raws = raw_candidates(body)
        if len(raws) <= 1:
            return {}
        got = SC.screen(statement, body, [r[1] for r in raws], run, ctx, log=log, tag=FAMILY, max_files=1)
        if got is None:
            return {}
        return {"scaffold_key": K.proof_key(proof), "scaffold_screen": got}
    except Exception as e:  # never raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:200]}")
        return {}
