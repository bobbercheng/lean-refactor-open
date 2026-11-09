#!/usr/bin/env python3
"""v5_deferhave (post-step v5, branch open-post-v5-v5deferhave, 2026-11-04): a typed `have` proved by a tactic block, whose name is
written exactly once later in its scope as a bare argument of a term step, is deferred to a `?_` goal: the `have` step goes, the use
becomes `?_`, and the have's tactic block (re-indented to the use step's block column) closes that goal. The type T is no longer
written (nor elaborated on its own).

    has_sites(proof, statement) -> bool                                           (pure)
    query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None) -> dict
    candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None) -> [{"op", "decl", "note"}]   (pure)

  site      `have h : T := by` + a block on the following lines (deeper than the `have`), or `have h : T := by tac` on one line;
            also `have : T := by ..` (the name `this`; no other anonymous `have` / `suffices` before its use). The header (`have` ..
            `by`) has no comment; between the name and `:` only explicit binders (`x`, `(x y : X)`; v2), not `haveI`. The step is a
            step of a tactic block (a bullet line, a line after a line ending in `by`, a sibling of a tactic-only step, or a sibling
            of the use's exact / refine / apply step); the proof has no kernel-unchecked closer (debug.skipKernelTC: no site).
  use       the name written exactly once in the rest of its block (identifier boundaries, comments and strings ignored), as a bare
            argument (not a dot head `h.x`, not applied `h a`, not before `▸` / `:=`, not after `@`), inside the term of a tactic step
            whose head is exact / refine / refine' / apply (final kind) or have / let / use / specialize / calc / obtain (mid kind),
            the step starting at or after the have's column (a step of the same block or of a nested one), possibly on a
            continuation line of a multi-line term. Not a site: the use inside a lemma list `[..]`, inside a nested `by` / `match`
            or a `·` function in the term (consumed by automation / a pattern); under a `fun` / `λ` binder whose name the moved
            block writes (capture); a step whose text does not close its own brackets (a nested `(by ..)` block's last line).
  rewrite   the have step's lines go (a bullet on its line passes to the next step); the use becomes `?_`; final kind: `exact` ->
            `refine` and the block goes right after the step (in the order of the `?_`s when several haves defer into one step);
            `exact h` / `refine h` alone: the step is replaced by the block ("whole"). Mid kind (`have x := f ?_` is refine_lift:
            the main goal comes first): the block goes at the end of the step's block ("end"); variant "after": right after the
            step; final kind with other `?_`s in the step or `apply`: variant "end" too; `exact`: variant "apply" (`apply f ?_`, the
            block after: implicit arguments that h's type fixed become goals Lean may still unify). Binder haves (v2): a bare use
            -> `?_` with `intro <binders>` before the block; a use applied to exactly its binders (atoms) -> `?_`, the binder names
            substituted by the arguments in the block (`(h a)` -> `?_`). Variant "typed" (no binders): the use becomes `(?_ : T)`
            at the first placement (a token or two saved; the implicit arguments T fixed stay fixed). Joint: every non-conflicting
            site of the proof at once (their first placements).
  screen    query(): ONE measured batch file (harness/post/d4_measure.py's `#eval` heartbeat sandwich per copy) with the incumbent
            as the control, the joint variant and the single-site variants (MAX_SINGLES at most, largest token saving first),
            each copy built with v4_rescreen's context-keeping copy (the dotted name's namespace prefix, `private`, the file's
            attached `... in` lines repeated before every copy: vendored below, unchanged in substance) so screen-blind rows still
            read; parsed with opus_screen.measured_parse (an error or a sorry warning before a copy's reading fails it). The
            variants that read clean and are predicted > 0 at the row's exchange rate are kept. A second file (at most 2 compiles
            per row and round): the rest when they did not fit one file; the "rejoint" (the union of the singles that read up,
            when the joint did not, 2+ sites) when they did; or the plain marker screen (fixed copies, no heartbeats:
            a clean compile of a shorter variant is kept) when the measured control does not read. A statement no copy can be
            built for (not a theorem / lemma, universe parameters, `_root_`): the joint (else the best single) and the next single
            are proposed unscreened (the gate reads them).
  output    the kept variants: the joint / rejoint first, then the singles by predicted gain; MAX_CANDS at most (= READS). The gate is
            unchanged. Every fault is caught (no candidates); a budget stop propagates.

Model-free and deterministic; reads only the proof, the statement and the row's own file prefix (no row name, table or proof text)."""
from __future__ import annotations

import re, sys, threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from harness.post import opus_screen as SC  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "v5_deferhave"
MAX_SINGLES = 12      # single-site variants in the screen at most (the joint and the control besides)
MAX_CANDS = 4         # proposals per round (= READS["v5_deferhave"])
UNSCREENED = 2        # proposals when no screen copy can be built
BULLET = "·"
FINAL_HEADS = ("exact", "refine", "refine'", "apply")
MID_HEADS = ("have", "let", "use", "specialize", "calc", "obtain")
HEADS = FINAL_HEADS + MID_HEADS
IDC = r"\w'₀-₉ₐ-ₜ!?"
NAME_RE = re.compile(r"[^\W\d][\w'₀-₉ₐ-ₜ]*")
HAVE_RE = re.compile(r"have(?![\w'])")
OPEN, CLOSE = "([{⟨", ")]}⟩"
ANON_RE = re.compile(r"(?<![\w'.])(?:have|haveI|suffices)\s*:")
# tactic words that tell a tactic block from a term-mode `have` chain (any step of the block starting with one of them)
TACTICS = set(HEADS) | {"intro", "intros", "rintro", "simp", "simp_all", "simpa", "rw", "rewrite", "rwa", "omega", "linarith", "nlinarith",
                        "constructor", "rcases", "cases", "induction", "exacts", "norm_num", "ring", "field_simp", "unfold", "dsimp",
                        "aesop", "grind", "decide", "positivity", "gcongr", "by_cases", "by_contra", "split", "subst", "ext",
                        "funext", "congr", "show", "change", "trivial", "rfl", "assumption", "contradiction", "exfalso", "left",
                        "right", "refine_lift", "next", "case", "all_goals", "any_goals", "repeat", "first", "try", "unhygienic",
                        "set", "generalize", "specialize", "replace", "nth_rewrite", "nth_rw", "conv", "filter_upwards", "choose",
                        "lift", "push_neg", "contrapose", "tauto", "itauto", "fin_cases", "interval_cases", "norm_cast",
                        "exact_mod_cast", "push_cast", "symm", "trans", "calc", "match", "fun_induction", "clear", "revert"}
TACTIC_ONLY = TACTICS - {"have", "let", "show", "calc", "match", "suffices", "fun", "trans", "symm"}


def _indent(ln: str) -> int:
    return len(ln) - len(ln.lstrip(" "))


def _lead(ln: str) -> tuple[int, bool]:
    """(the column of the line's first token after an optional `·` bullet, whether it has the bullet)."""
    s = ln.lstrip(" ")
    if s.startswith(BULLET):
        r = s[len(BULLET):]
        return _indent(ln) + len(BULLET) + (len(r) - len(r.lstrip(" "))), True
    return _indent(ln), False


def _word(s: str) -> str:
    m = re.match(r"[A-Za-z_][\w'?]*", s)
    return m.group(0) if m else ""


class _Text:
    """The body as lines with their offsets and the comment / string mask."""

    def __init__(self, body: str):
        self.body = body
        self.L = body.split("\n")
        self.mask = _mask(body)
        self.offs, o = [], 0
        for ln in self.L:
            self.offs.append(o)
            o += len(ln) + 1

    def off(self, line: int, col: int) -> int:
        return self.offs[line] + col

    def masked(self, a: int, b: int) -> bool:
        return any(self.mask[a:b])

    def nonempty(self, i: int) -> bool:
        return bool(self.L[i].strip())


def _depth_scan(text: str, mask: list[bool], start: int, end: int) -> tuple[int, bool]:
    """(the bracket depth at `end` relative to `start`, whether it ever went below 0)."""
    d, neg = 0, False
    for k in range(start, end):
        if mask[k]:
            continue
        ch = text[k]
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
            if d < 0:
                neg = True
    return d, neg


def _block_end(T: _Text, first: int, col: int) -> int:
    """The last non-empty line of the block of a step at column `col` that starts at line `first` (lines at column >= col)."""
    k, last = first, first
    while k < len(T.L):
        if T.nonempty(k):
            if _indent(T.L[k]) < col:
                break
            last = k
        k += 1
    return last


def _step_end(T: _Text, q: int, qcol: int) -> int:
    """The last line of the step starting on line q at column qcol (its continuation lines are deeper)."""
    e = q
    k = q + 1
    while k < len(T.L):
        if T.nonempty(k):
            if _indent(T.L[k]) <= qcol:
                break
            e = k
        k += 1
    return e


def _is_tactic_block(T: _Text, i: int, col: int, bullet: bool) -> bool:
    """The step on line i at column col is a step of a tactic block (not a term-mode `have` chain): a bullet line; a sibling step
    (same column) that starts with a tactic-only word; the block's opening line (the nearest shallower one) ending in `by`; the top
    block of a `by` body."""
    if bullet:
        return True
    for k in range(i - 1, -1, -1):
        if not T.nonempty(k):
            continue
        lc, _b = _lead(T.L[k])
        if _indent(T.L[k]) <= col and lc == col:
            if _b or _word(T.L[k][lc:]) in TACTIC_ONLY:
                return True   # a bullet sibling, or a tactic-only sibling
            continue
        if _indent(T.L[k]) < col:
            r = T.L[k].rstrip()
            if re.search(r"(?<![\w'.])by$", r) or (_b and lc == col):
                return True
            break
        # a deeper line: a continuation or a nested block of an earlier sibling
    else:
        if T.body.lstrip().startswith("by"):
            return True
    e = _block_end(T, i, col)
    for k in range(i + 1, e + 1):
        if T.nonempty(k) and _lead(T.L[k])[0] == col and _indent(T.L[k]) <= col and _word(T.L[k][col:].lstrip(BULLET + " ")) in TACTIC_ONLY:
            return True
    return False


# ------------------------------------------------------------------------------------------------------------------------------ sites
def _have_header(T: _Text, i: int):
    """The have step on line i: {"name", "col", "bullet", "end" (its last line), "by_line", "same" (tactic text after `by` on its
    line, '' when the block is on the next lines), "block" (lines relative to the block column), "save"} or None."""
    ln = T.L[i]
    col, bullet = _lead(ln)
    s = ln[col:]
    if not HAVE_RE.match(s):
        return None
    if ln[:col].strip() not in ("", BULLET):
        return None
    rest = s[4:]
    r2 = rest.lstrip(" ")
    bnd: list = []
    if r2.startswith(":") and not r2.startswith(":="):
        name = "this"
    else:
        m = NAME_RE.match(r2)
        if not m or not rest.startswith(" "):
            return None
        name = m.group(0)
        if name == "_":
            return None
        bnd = _binders(r2[m.end():])
        if bnd is None:
            return None   # implicit / instance binders, `:=` with no type, a pattern
    e = _step_end(T, i, col)
    # the header's `:=` at depth 0 (from the type's colon on)
    a = T.off(i, col) + 4
    end_off = T.off(e, len(T.L[e]))
    d, k, assign = 0, a, None
    while k < end_off:
        if not T.mask[k]:
            ch = T.body[k]
            if ch in OPEN:
                d += 1
            elif ch in CLOSE:
                d -= 1
                if d < 0:
                    return None
            elif d == 0 and T.body.startswith(":=", k):
                assign = k
                break
        k += 1
    if assign is None:
        return None
    m = re.match(r":=[ \t]*by(?![\w'])", T.body[assign:])
    if not m:
        return None
    by_end = assign + m.end()
    if T.masked(T.off(i, 0), by_end):
        return None   # a comment / string in the header
    by_line = T.body.count("\n", 0, by_end)
    tail = T.body[by_end:T.offs[by_line] + len(T.L[by_line])]
    if T.masked(by_end, by_end + len(tail)):
        return None
    same = tail.strip()
    if same:
        if e != by_line:
            return None   # a same-line block with continuation lines: not handled
        block = [same]
    else:
        lines = T.L[by_line + 1:e + 1]
        ne = [x for x in lines if x.strip()]
        if not ne:
            return None
        bcol = _indent(ne[0])
        if bcol <= col or any(_indent(x) < bcol for x in ne):
            return None
        block = [x[bcol:] if x.strip() else "" for x in lines]
    head_text = T.body[T.off(i, col):by_end]
    # the type's text (the first depth-0 `:` after the name / binders up to the `:=`), on one line: the "typed" placement's ascription
    ty, d, k = None, 0, T.off(i, col) + 4
    while k < assign:
        ch = T.body[k]
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
        elif ch == ":" and d == 0 and not T.body.startswith(":=", k):
            ty = " ".join(T.body[k + 1:assign].split())
            break
        k += 1
    return {"name": name, "binders": bnd, "line": i, "col": col, "bullet": bullet, "end": e, "by_line": by_line, "same": same, "block": block,
            "save": count_tokens(head_text), "type": ty}


def _binders(text: str) -> list[str] | None:
    """The explicit binder names between a have's name and its type's `:` (`x y`, `(x y : X)`, `(x)`), [] for none; None when the
    text has other binders (`{x}`, `[inst]`, `⦃x⦄`, a pattern) or no type colon."""
    names: list = []
    k = 0
    while k < len(text):
        ch = text[k]
        if ch == " ":
            k += 1
            continue
        if ch == ":":
            return None if text.startswith(":=", k) else names
        if ch == "(":
            d, j = 0, k
            while j < len(text):
                if text[j] in OPEN:
                    d += 1
                elif text[j] in CLOSE:
                    d -= 1
                    if d == 0:
                        break
                j += 1
            if j >= len(text):
                return None
            inner = text[k + 1:j].split(":", 1)[0]
            ns = inner.split()
            if not ns or not all(NAME_RE.fullmatch(x) for x in ns):
                return None
            names += ns
            k = j + 1
            continue
        m = NAME_RE.match(text, k)
        if not m or m.group(0) == "_":
            return None
        names.append(m.group(0))
        k = m.end()
    return None


def _atoms(text: str, n: int) -> tuple[list[str], int] | None:
    """The first n argument atoms of `text` (identifiers, numerals, one bracket group each), then a terminator (end of line, `)`,
    `⟩`, `,`, `}`): (atoms, the length consumed up to the last atom), or None."""
    out, k = [], 0
    while len(out) < n:
        while k < len(text) and text[k] == " ":
            k += 1
        if k >= len(text) or text[k] == "\n":
            return None
        ch = text[k]
        if ch in "(⟨":
            d, j = 0, k
            while j < len(text) and text[j] != "\n":
                if text[j] in OPEN:
                    d += 1
                elif text[j] in CLOSE:
                    d -= 1
                    if d == 0:
                        break
                j += 1
            if j >= len(text) or text[j] == "\n":
                return None
            out.append(text[k:j + 1])
            k = j + 1
            continue
        m = re.compile(r"[^\W\d][\w'₀-₉ₐ-ₜ]*(?:\.[^\W\d][\w'₀-₉ₐ-ₜ]*|\.\d+)*|\d+").match(text, k)
        if not m or m.group(0) in ("fun", "by", "at", "with", "using", "from", "then", "else", "do"):
            return None
        out.append(m.group(0))
        k = m.end()
    rest = text[k:].split("\n", 1)[0].lstrip(" ")
    if rest and rest[0] not in ")⟩,}":
        return None
    return out, k


def _subst(block: list[str], binders: list[str], args: list[str]) -> list[str] | None:
    """The block's lines with each binder name (identifier occurrences outside comments and strings, not after `.`) replaced by its
    argument atom (Lean decides whether the block still closes the instantiated goal)."""
    text = "\n".join(block)
    mask = _mask(text)
    for b, a in zip(binders, args):
        if a == b:
            continue
        pat = re.compile(r"(?<![\w'.₀-₉ₐ-ₜ])" + re.escape(b) + r"(?![\w'₀-₉ₐ-ₜ])")
        out, last = [], 0
        for m in pat.finditer(text):
            if mask[m.start()]:
                continue
            out.append(text[last:m.start()])
            out.append(a)
            last = m.end()
        out.append(text[last:])
        text = "".join(out)
        mask = _mask(text)
    return text.split("\n")


def _occurrences(T: _Text, name: str, a: int, b: int) -> list[int]:
    out = []
    for m in re.finditer(r"(?<![\w'.₀-₉ₐ-ₜ])" + re.escape(name) + r"(?![\w'₀-₉ₐ-ₜ])", T.body[a:b]):
        if not T.mask[a + m.start()]:
            out.append(a + m.start())
    return out


def _find_step(T: _Text, u: int, lo: int, col_min: int):
    """(q, qcol, head) of the tactic step whose text holds line u: the nearest line q in [lo, u] whose first token (after a bullet)
    is a step head and below which every line up to u is deeper; None when there is none."""
    for q in range(u, lo - 1, -1):
        if not T.nonempty(q):
            continue
        qcol, _b = _lead(T.L[q])
        if qcol < col_min:
            return None
        w = _word(T.L[q][qcol:])
        if q < u and any(T.nonempty(r) and _indent(T.L[r]) <= qcol for r in range(q + 1, u + 1)):
            continue
        if w in HEADS:
            return q, qcol, w
    return None


def _kw(body: str, k: int, w: str) -> bool:
    """The keyword w starts at offset k (identifier boundaries)."""
    return body.startswith(w, k) and (k == 0 or not re.match(r"[\w'.]", body[k - 1])) and not re.match(r"[\w'!?]", body[k + len(w):k + len(w) + 1])


def _scan_use(T: _Text, a: int, use: int, name_len: int):
    """Context of the use at offset `use` inside the step text starting at offset `a` (the head word's end): None when the use is
    not deferrable (in a lemma list, under a nested `by` / `match` / `·` function, applied, a dot head, ...), else {"binders": names
    bound by enclosing `fun` / `λ`}."""
    stack: list = []          # open brackets
    scopes: list = []         # (kind, depth, names)
    d = 0
    body, mask = T.body, T.mask
    for k in range(a, use):
        if mask[k]:
            continue
        ch = body[k]
        if ch in OPEN:
            d += 1
            stack.append(ch)
        elif ch in CLOSE:
            d -= 1
            if stack:
                stack.pop()
            scopes = [x for x in scopes if x[1] <= d]
        elif _kw(body, k, "by"):
            scopes.append(("by", d, ()))
        elif _kw(body, k, "match"):
            scopes.append(("match", d, ()))
        elif _kw(body, k, "fun") or ch == "λ":
            j = k + (1 if ch == "λ" else 3)
            mm = re.compile(r"=>|↦").search(body, j, use)
            scopes.append(("fun", d, tuple(NAME_RE.findall(body[j:mm.start()])) if mm else ()))
        elif ch == BULLET and stack and stack[-1] == "(":
            scopes.append(("cdot", d, ()))
    if any(x[0] in ("by", "match", "cdot") for x in scopes):
        return None
    if stack and stack[-1] == "[":
        return None
    pre = body[a:use].rstrip()
    prev = pre[-1:]
    if prev == "@":
        return None
    nxt = body[use + name_len:]
    line_rest = nxt.split("\n", 1)[0]
    r = line_rest.lstrip(" ")
    if nxt.startswith(".") or r.startswith("▸") or r.startswith(":=") or r.startswith("|>."):
        return None   # a dot head, a rewrite by the name, a named argument
    head_pos = (not prev) or pre.endswith("<|") or pre.endswith(":=") or not re.match(r"[\w'₀-₉ₐ-ₜ)\]}⟩_.!?]", prev)
    applied = False
    if head_pos and (r.startswith("$") or r.startswith("<|")):
        return None   # the name is applied to an argument (`h $ x`, `h <| x`)
    if head_pos and r and (re.match(r"[\w'(⟨@_?]", r[:1]) or r[:1].isdigit()) \
            and not re.match(r"(?:at|using|with|from|then|else|in|generalizing)(?![\w'])", r):
        applied = True   # the name is applied to arguments (a binder have may take exactly its binders)
    return {"binders": tuple(n for x in scopes if x[0] == "fun" for n in x[2]), "applied": applied, "head_pos": head_pos}


def sites(body: str) -> list[dict]:
    """The deferrable haves of `body` (the text after the statement's `:=`), in line order."""
    if SC.unchecked(body):
        return []
    T = _Text(body)
    out = []
    for i in range(len(T.L)):
        try:
            h = _have_header(T, i)
        except Exception:  # noqa: BLE001
            h = None
        if h is None:
            continue
        col, e = h["col"], h["end"]
        j = e + 1
        if j >= len(T.L):
            continue
        k_end = _block_end(T, j, col) if any(T.nonempty(x) for x in range(j, len(T.L))) else e
        # the scope: lines j .. k_end (the rest of the have's block)
        a = T.offs[j]
        b = T.offs[k_end] + len(T.L[k_end]) if k_end >= j else a
        if b <= a:
            continue
        occ = _occurrences(T, h["name"], a, b)
        if len(occ) != 1:
            continue
        use = occ[0]
        if h["name"] == "this" and ANON_RE.search(T.body[a:use]):
            continue
        u = T.body.count("\n", 0, use)
        st = _find_step(T, u, j, col)
        if st is None:
            continue
        q, qcol, head = st
        q_tac = head in TACTIC_ONLY or _is_tactic_block(T, q, qcol, _lead(T.L[q])[1])
        if not q_tac:
            continue
        if not (_is_tactic_block(T, i, col, h["bullet"]) or (qcol == col and head in TACTIC_ONLY)):
            continue
        se = _step_end(T, q, qcol)
        sa, sb = T.off(q, qcol), T.offs[se] + len(T.L[se])
        dd, neg = _depth_scan(T.body, T.mask, sa, sb)
        if dd != 0 or neg:
            continue
        ctx = _scan_use(T, sa + len(head), use, len(h["name"]))
        if ctx is None:
            continue
        span, block = len(h["name"]), list(h["block"])
        if h["binders"]:
            if ctx["applied"]:   # v2: `h a1 .. an` with exactly the have's binders -> `?_`, the block with the binders substituted
                at = _atoms(T.body[use + len(h["name"]):], len(h["binders"]))
                if at is None:
                    continue
                span = len(h["name"]) + at[1]
                block = _subst(block, h["binders"], at[0])
            else:                # v2: a bare use of a binder have -> `?_`, the block after `intro <binders>`
                block = ["intro " + " ".join(h["binders"])] + block
        elif ctx["applied"]:
            continue
        ua, ub = use, use + span
        if ua > 0 and T.body[ua - 1] == "(" and T.body[ub:ub + 1] == ")" and not T.mask[ua - 1]:
            ua, ub = ua - 1, ub + 1   # `(h a)` -> `?_`
        moved = "\n".join(block)
        if ctx["binders"] and any(re.search(r"(?<![\w'.])" + re.escape(n) + r"(?![\w'])", moved) for n in ctx["binders"]):
            continue
        term = T.body[sa + len(head):sb].strip()
        whole = term == T.body[ua:ub].strip() and q == se and head in ("exact", "refine", "refine'")
        if not (sa <= use < sb):
            continue
        if head == "obtain" and ":=" not in T.body[sa:use]:
            continue   # the use must be in the `obtain`'s source term
        if head in ("have", "let") and ":=" not in T.body[sa:use]:
            continue   # the use must be in the value, not the type
        other_holes = any(not T.mask[sa + m.start()] for m in re.finditer(r"\?_", T.body[sa:sb]))
        blk_end = _block_end(T, q, qcol)
        ba, bb = T.off(q, qcol), T.offs[blk_end] + len(T.L[blk_end])
        d2, neg2 = _depth_scan(T.body, T.mask, ba, bb)
        end_ok = d2 == 0 and not neg2
        if head in FINAL_HEADS:
            places = ["after"] + (["end"] if (other_holes or head == "apply") and end_ok and blk_end > se else [])
            if head == "exact":
                places.append("apply")   # `exact f h` -> `apply f ?_`: implicit arguments h's type fixed may become goals and unify later
        else:
            places = (["end"] if end_ok else []) + ["after"]
        if whole:
            places = ["whole"]
        elif not h["binders"] and h.get("type"):
            places.append("typed")   # `(?_ : T)`: the type kept as an ascription (implicit arguments it fixed stay fixed)
        out.append(dict(h, block=block, ua=ua, ub=ub, use=use, use_line=u, step=q, step_col=qcol, head=head, step_end=se, block_end=blk_end, places=places,
                        whole=whole, kind="final" if head in FINAL_HEADS else "mid"))
    return out


# ------------------------------------------------------------------------------------------------------------------------------ rewrite
def _moved_lines(s: dict, tc: int) -> list[str]:
    return [(" " * tc + x) if x.strip() else "" for x in s["block"]]


def _apply(body: str, sel: list[tuple[dict, str]]) -> str | None:
    """The body with every (site, placement) in `sel` applied, or None on a conflict."""
    T = _Text(body)
    n = len(T.L)
    deleted: set = set()
    inline: dict = {}       # line -> [(col_a, col_b, text)]
    inserts: dict = {}      # line -> [(key, [lines])]  (after that line)
    whole_sub: dict = {}    # line -> [lines] (replaces the line)
    bullet_to: dict = {}    # line -> prefix (the deleted have's bullet prefix)
    touched: list = []
    refined: set = set()
    for s, place in sel:
        hr = set(range(s["line"], s["end"] + 1))
        if hr & deleted:
            return None
        rng = set(range(s["step"], s["step_end"] + 1))
        for (a, b, kind, who) in touched:
            if hr & set(range(a, b + 1)):
                return None
            if kind == "have" and rng & set(range(a, b + 1)):
                return None
            if kind == "whole" and rng & set(range(a, b + 1)):
                return None
        if place == "whole" and any(k == "step" and set(range(a, b + 1)) & rng for a, b, k, _w in touched):
            return None
        deleted |= hr
        touched.append((s["line"], s["end"], "have", id(s)))
        touched.append((s["step"], s["step_end"], "whole" if place == "whole" else "step", id(s)))
        if s["bullet"]:
            nl = s["end"] + 1
            while nl < n and not T.nonempty(nl):
                nl += 1
            if nl >= n or _indent(T.L[nl]) != s["col"] or _lead(T.L[nl])[1] or nl in deleted:
                return None
            bullet_to[nl] = T.L[s["line"]][:s["col"]]
        u = s["use_line"]
        ucol = s["ua"] - T.offs[u]
        tc = s["step_col"]
        if place == "whole":
            first = T.L[s["step"]][:tc]
            ml = _moved_lines(s, tc)
            ml[0] = first + ml[0][tc:] if ml and ml[0] else ml[0]
            whole_sub[s["step"]] = ml
            continue
        if T.body.count("\n", s["ua"], s["ub"]):
            return None
        inline.setdefault(u, []).append((ucol, ucol + s["ub"] - s["ua"], f"(?_ : {s['type']})" if place == "typed" else "?_"))
        if s["head"] == "exact" and s["step"] not in refined:
            refined.add(s["step"])
            inline.setdefault(s["step"], []).append((tc, tc + len("exact"), "apply" if place == "apply" else "refine"))
        elif s["head"] == "exact" and place == "apply":
            return None   # the step was already turned into `refine` by another site
        if place == "typed":
            place = s["places"][0]
        anchor = s["step_end"] if place in ("after", "apply") else s["block_end"]
        if anchor in deleted:
            return None
        inserts.setdefault(anchor, []).append(((s["use"],), _moved_lines(s, tc)))
    for ln in list(inserts) + list(whole_sub) + list(bullet_to):
        if ln in deleted:
            return None
    out: list[str] = []
    for i, ln in enumerate(T.L):
        if i in deleted:
            continue
        if i in whole_sub:
            sub = list(whole_sub[i])
            if i in bullet_to and sub:
                sub[0] = bullet_to[i] + sub[0][len(bullet_to[i]):]
            out.extend(sub)
        else:
            if i in inline:
                eds = sorted(inline[i], reverse=True)
                for (x, y, _t), (x2, y2, _t2) in zip(sorted(inline[i]), sorted(inline[i])[1:]):
                    if y > x2:
                        return None
                for x, y, t in eds:
                    ln = ln[:x] + t + ln[y:]
            if i in bullet_to:
                p = bullet_to[i]
                ln = p + ln[len(p):]
            out.append(ln)
        for _k, lines in sorted(inserts.get(i, []), key=lambda x: x[0]):
            # a trailing blank line of the anchor's block stays after the moved lines
            out.extend(lines)
    return "\n".join(out)


def variants(body: str) -> list[dict]:
    """[{"tag", "body", "note", "save" (static token saving), "sel" (the (site, placement) pairs applied)}]: the joint first (2+
    sites), then the singles (first placement of each site first, the largest saving first, then the other placements)."""
    ss = sites(body)
    if not ss:
        return []
    t0 = count_tokens(body)
    singles, seen = [], {body}
    for rank in range(4):
        for s in ss:
            if rank >= len(s["places"]):
                continue
            pl = s["places"][rank]
            nb = _apply(body, [(s, pl)])
            if nb is None or nb in seen:
                continue
            sv = t0 - count_tokens(nb)
            if sv <= 0:
                continue
            seen.add(nb)
            singles.append((rank, -sv, s["line"], {"tag": f"single:{pl}", "body": nb, "save": sv, "sel": [(s, pl)],
                                                   "note": f"`{s['name']}` (line {s['line'] + 1}) deferred to `?_` in its {s['head']} step "
                                                           f"(line {s['step'] + 1}), block {pl}, -{sv} tokens"}))
    singles.sort(key=lambda x: x[:3])
    out = []
    if len(ss) >= 2:
        sel = []
        for s in sorted(ss, key=lambda s: -s["save"]):
            if _apply(body, sel + [(s, s["places"][0])]) is not None:
                sel.append((s, s["places"][0]))
        if len(sel) >= 2:
            sel.sort(key=lambda x: x[0]["line"])
            nb = _apply(body, sel)
            if nb is not None and nb not in seen and count_tokens(nb) < t0:
                out.append({"tag": "joint", "body": nb, "save": t0 - count_tokens(nb), "sel": sel,
                            "note": f"{len(sel)} haves deferred to `?_` goals, -{t0 - count_tokens(nb)} tokens"})
    return out + [x[3] for x in singles]


def raw_variants(body: str) -> list[tuple[str, str, str, int]]:
    """[(tag, new_body, note, static token saving)] of variants()."""
    return [(v["tag"], v["body"], v["note"], v["save"]) for v in variants(body)]


def rejoint(body: str, passing: list[dict]) -> dict | None:
    """The union of the passing single variants (best predicted first; a site once; a conflicting one left out), when it joins 2+
    sites: {"tag": "rejoint", "body", "note", "save", "sel"}; else None."""
    sel: list = []
    used: set = set()
    for v in passing:
        (site, pl), = v["sel"]
        if id(site) in used:
            continue
        if _apply(body, sel + [(site, pl)]) is not None:
            sel.append((site, pl))
            used.add(id(site))
    if len(sel) < 2:
        return None
    sel.sort(key=lambda x: x[0]["line"])
    nb = _apply(body, sel)
    if nb is None:
        return None
    sv = count_tokens(body) - count_tokens(nb)
    return {"tag": "rejoint", "body": nb, "save": sv, "sel": sel,
            "note": f"{len(sel)} haves that each read clean, deferred together, -{sv} tokens"}


def has_sites(proof: str, statement: str) -> bool:
    try:
        body = split_declaration(proof, statement)
        return bool(body) and bool(raw_variants(body))
    except Exception:  # noqa: BLE001
        return False


# ------------------------------------------------------------------------------------------------------------------------------ context
# Vendored from v4_rescreen (branch open-post-v4-v4rescreen f4018ef5, harness/post/v4_rescreen.py: Ctx, attached_lines, mods_private,
# stmt_private, decl_name, row_ctx, rel_name, renamed_fixed, name_expr, text_fixed, opus_plain_fixed, VARIANT, SENTINEL): the screen
# copy keeps the declaration's namespace prefix, `private` and the file's attached `... in` lines (v4_rescreen's module docstring).
DUMMY = "theorem lraV5DDummy : True := trivial\n"
SENTINEL = '#print "LRAD4M\\t999\\t0\\t0\\tsep"\n'
_IN_LINE = re.compile(r"^[ \t]*(?:set_option|omit|include|unseal|variable|open)\b[^\n]*\bin[ \t]*$")
_OPEN_IN = re.compile(r"open\s+[\w.\s]+?\s+in\b")
_DOC = re.compile(r"/--(?:(?!-/).)*-/", re.S)
_HEAD_MODS = re.compile(r"\A(?:\s+|/--(?:(?!-/).)*-/|@\[[^\]]*\])*((?:(?:private|protected|noncomputable|nonrec)\s+)*)(?:theorem|lemma)\s",
                        re.S)
VARIANT = r'''
set_option Elab.async false in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let s : String := LRAD4MSRC
  let i : Nat := LRAD4MI
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command s with
  | .error _ => Lean.logInfo (Lean.toMessageData s!"LRAD4M\t{i}\t0\t0\tparse")
  | .ok stx =>
    let n1 := (← Lean.getCurrNamespace) ++ LRAD4MNAME
    let (ok, dh) ← Lean.withoutModifyingEnv do
      let t0 ← IO.getNumHeartbeats
      Lean.Elab.Command.elabCommand stx
      let t1 ← IO.getNumHeartbeats
      let env ← Lean.getEnv
      let n2 := Lean.mkPrivateName env n1
      let n := if env.contains n2 then n2 else n1
      let mut ok := false
      if env.contains n then
        ok := !((← Lean.collectAxioms n).contains ``sorryAx)
      pure (ok, t1 - t0)
    Lean.logInfo (Lean.toMessageData s!"LRAD4M\t{i}\t{if ok then 1 else 0}\t{dh / 1000}")
'''


class Ctx:
    def __init__(self, attached: str = "", private: bool = False):
        self.attached, self.private = attached, bool(private)


def attached_lines(core: str, mods: str) -> str:
    tail = []
    for ln in reversed(core.rstrip().split("\n")):
        if _IN_LINE.match(ln):
            tail.append(ln)
            continue
        break
    lines = list(reversed(tail)) + [m.group(0) for m in _OPEN_IN.finditer(_DOC.sub(" ", mods or ""))]
    return "".join(" ".join(x.split()) + "\n" for x in lines)


def mods_private(mods: str) -> bool:
    return bool(re.search(r"(?<![\w.])private\b", _DOC.sub(" ", mods or "")))


def stmt_private(statement: str) -> bool:
    m = _HEAD_MODS.match(statement)
    return bool(m and "private" in m.group(1).split())


def decl_name(statement: str) -> str | None:
    m = MS.DECL_RE.match(statement)
    if not m or ".{" in m.group(0):
        return None
    return re.split(r"\s+", m.group(0).strip())[-1]


def row_ctx(row: dict | None, version: str | None) -> Ctx:
    if not row or row.get("source") == "putnambench" or not row.get("file_path") or not version:
        return Ctx("", stmt_private((row or {}).get("statement") or ""))
    try:
        from scorer import compile as C
        core, mods = C.split_modifiers(C.file_prefix(row, version))
    except Exception:  # noqa: BLE001  (no prefix: the statement's own modifiers only)
        core, mods = "", ""
    return Ctx(attached_lines(core, mods), stmt_private(row.get("statement") or "") or mods_private(mods))


def rel_name(statement: str, i) -> str | None:
    nm = decl_name(statement)
    if nm is None or nm.startswith("_root_"):
        return None
    pre = nm.rsplit(".", 1)[0] + "." if "." in nm else ""
    return f"{pre}lraD4M{i}"


def renamed_fixed(statement: str, i, cx: Ctx) -> str | None:
    m = MS.DECL_RE.match(statement)
    rn = rel_name(statement, i)
    if not m or rn is None:
        return None
    priv = "private " if (cx.private or stmt_private(statement)) else ""
    return cx.attached + f"{priv}theorem {rn}" + statement[m.end():]


def name_expr(rel: str) -> str:
    expr = "Lean.Name.anonymous"
    for p in [p for p in rel.split(".") if p]:
        expr = f"(Lean.Name.str {expr} {K.lean_str(p)})"
    return expr


def text_fixed(statement: str, bodies: list[str], cx: Ctx, idx: list[int] | None = None) -> str | None:
    """The measured file: the copies' `#eval` readings after the dummy theorem and the SENTINEL line (copy k reads as index idx[k])."""
    idx = idx if idx is not None else list(range(len(bodies)))
    srcs = []
    for i, b in zip(idx, bodies):
        r = renamed_fixed(statement, i, cx)
        if r is None:
            return None
        srcs.append((i, r.rstrip() + " :=" + SC.selfref(statement, b, i), rel_name(statement, i)))
    return MS.TEXT + SENTINEL + "".join(VARIANT.replace("LRAD4MSRC", K.lean_str(s)).replace("LRAD4MI", str(i)).replace("LRAD4MNAME", name_expr(rn))
                                        for i, s, rn in srcs)


def plain_fixed(statement: str, bodies: list[str], cx: Ctx) -> str | None:
    """opus_screen.plain_text with the fixed copies, after a dummy theorem (opus_screen.plain_parse reads its markers)."""
    out = []
    for i, b in enumerate(bodies):
        r = renamed_fixed(statement, i, cx)
        if r is None:
            return None
        out.append(f'#check "{SC.MARK}{i}"\n' + r.rstrip() + " :=" + SC.selfref(statement, b, i).rstrip() + "\n")
    out.append(f'#check "{SC.MARK}{len(bodies)}"\n')
    return DUMMY + "\n" + "\n".join(out)


# ------------------------------------------------------------------------------------------------------------------------------ op API
_MEMO: dict = {}
_MLOCK = threading.Lock()


def _is_stop(e: BaseException) -> bool:
    return e.__class__.__name__ == "_Stop"


def screen(statement: str, body0: str, raws: list, run, ctx: dict | None, cx: Ctx, version=None, log=None, extra=None) -> dict | None:
    """{"up": [(tag, body, note, predicted)], "mode", "files", "read"} (module docstring, "screen"), or None (no copy can be built).
    extra(up) -> (tag, body, note) | None: one more variant built from the passing ones, read in the second file when the first
    measured file read everything (the rejoint)."""
    if rel_name(statement, 0) is None or MS.DECL_RE.match(statement) is None:
        return None
    exch = (ctx or {}).get("exchange")
    per = MS.budget(ctx or {}) - 1
    up, files, read, mode = [], 0, 0, None
    seen: list = []   # the readings, for the log: (tag, ok, heartbeats / 1000 or None, predicted or None)
    while files < 2 and read < len(raws):
        chunk = raws[read:read + per]
        if mode in (None, "measured"):
            text = text_fixed(statement, [body0] + [r[1] for r in chunk], cx)
            if text is None:
                return None
            files += 1
            rd = SC.measured_parse(getattr(run(text, version), "messages", None), len(chunk) + 1)
            ctl = rd.get(0) or {"ok": False}
            if ctl.get("ok"):
                mode = "measured"
                seen.append(("control", True, ctl.get("hb"), None))
                for k, r in enumerate(chunk, 1):
                    rk = rd.get(k) or {"ok": False}
                    pr = MS.predicted(ctl, body0, r[1], rk, exch)
                    seen.append((r[0], bool(rk.get("ok")), rk.get("hb"), pr))
                    if pr is not None and pr > 0:
                        up.append((r[0], r[1], r[2], pr))
                read += len(chunk)
                continue
            if mode == "measured" or files >= 2:
                break
            mode = "plain"
            if log:
                log(f"{FAMILY}: measured control did not read; plain screen")
        text = plain_fixed(statement, [body0] + [r[1] for r in chunk], cx)
        if text is None:
            return None
        files += 1
        ok = SC.plain_parse(getattr(run(text, version), "messages", None), len(chunk) + 1)
        if ok is None or not ok.get(0):
            break
        t0 = count_tokens(body0)
        for k, r in enumerate(chunk, 1):
            seen.append((r[0], bool(ok.get(k)), None, None))
            if ok.get(k):
                up.append((r[0], r[1], r[2], float(t0 - count_tokens(r[1])) * float(exch or 1.0)))
        read += len(chunk)
    if extra is not None and mode == "measured" and files < 2 and read >= len(raws):
        x = extra(list(up))
        if x is not None:
            text = text_fixed(statement, [body0, x[1]], cx)
            if text is not None:
                files += 1
                rd = SC.measured_parse(getattr(run(text, version), "messages", None), 2)
                ctl, rk = rd.get(0) or {"ok": False}, rd.get(1) or {"ok": False}
                pr = MS.predicted(ctl, body0, x[1], rk, exch)
                seen.append((x[0], bool(rk.get("ok")), rk.get("hb"), pr))
                if pr is not None and pr > 0:
                    up.append((x[0], x[1], x[2], pr))
    if log and seen:
        log(f"{FAMILY}: readings " + "; ".join(f"{t} {'ok' if o else 'FAIL'}" + (f" {h}k" if h is not None else "")
                                                + (f" pred {p:+.0f}" if p is not None else "") for t, o, h, p in seen))
    return {"up": up, "mode": mode or "none", "files": files, "read": read}


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    """The one-file screen of the variants (module docstring); {"dh_key", "dh_up": [(tag, body, note, predicted)], "dh_screened"}."""
    try:
        body0 = split_declaration(proof, statement)
        if body0 is None:
            return {}
        vs_all = variants(body0)
        if not vs_all:
            return {}
        by_body = {v["body"]: v for v in vs_all}
        raws = [(v["tag"], v["body"], v["note"], v["save"]) for v in vs_all]
        joint = [r for r in raws if r[0] == "joint"]
        singles = [r for r in raws if r[0] != "joint"][:MAX_SINGLES]
        raws = joint + singles

        def extra(up):
            passing = [by_body[b] for t, b, _n, _p in sorted(up, key=lambda x: -x[3]) if t.startswith("single") and b in by_body]
            if len(passing) < 2 or any(t == "joint" for t, *_ in up):
                return None
            rj = rejoint(body0, passing)
            if rj is None or rj["body"] in by_body:
                return None
            return rj["tag"], rj["body"], rj["note"]
        key = (K.proof_key(proof), statement)
        with _MLOCK:
            if key in _MEMO:
                return _MEMO[key]
        meter = getattr(run, "meter", None)
        vs = list(versions or getattr(meter, "versions", None) or [None])
        cx = row_ctx(getattr(meter, "row", None), vs[0])
        got = screen(statement, body0, raws, run, ctx, cx, version=None, log=log, extra=extra)
        if got is None:
            out = {"dh_key": K.proof_key(proof), "dh_up": [(r[0], r[1], r[2], None) for r in raws[:UNSCREENED]], "dh_screened": False}
        else:
            up = sorted(got["up"], key=lambda x: (x[0] not in ("joint", "rejoint"), -x[3]))
            out = {"dh_key": K.proof_key(proof), "dh_up": up, "dh_screened": True, "dh_mode": got["mode"]}
            if log:
                log(f"{FAMILY}: {got['mode']} screen, {got['files']} file(s), read {got['read']} of {len(raws)}; predicted up {len(up)}")
        if stats is not None:
            stats[FAMILY] = {"variants": len(raws), "up": len(out["dh_up"]), "screened": out["dh_screened"]}
        with _MLOCK:
            _MEMO[key] = out
        return out
    except Exception as e:  # noqa: BLE001  (a fault: no candidates; a budget stop propagates)
        if _is_stop(e):
            raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:200]}")
        return {}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    """The query's kept variants for the proof it read (joint first, then by predicted gain), MAX_CANDS at most; [] without one."""
    try:
        c = ctx or {}
        if c.get("dh_key") != K.proof_key(proof):
            return []
        hb = K.head_body(proof, statement)
        if hb is None:
            return []
        head, body = hb
        em = K.Emitter(proof, statement, head, body, int(max_per_op or MAX_CANDS))
        cap = int(max_per_op or MAX_CANDS)
        for tag, nb, note, pr in c.get("dh_up") or []:
            if len(em.out) >= cap:
                break
            em.add(f"{FAMILY}:{tag}", nb, note + ("" if pr is None else f"; predicted +{pr:.0f}"))
        return em.out
    except Exception:  # noqa: BLE001
        return []
