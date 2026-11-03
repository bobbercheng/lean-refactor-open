#!/usr/bin/env python3
"""Op "ctorsearch" of the open post-step (harness/open_post.py; lentools plan 2026-11-03, closers lens P3): fixed cheap constructor /
assumption closers in place of explicitly built constructor terms. Pure text plus one measured screen file per call; no table, no row
name, no proof text from anywhere but the proof being edited.

  sites     (masked comments and strings; the `:=` line is never a site)
    step    a step `exact T` / `exacts [T, ..]` / `use T, ..` / `exists T, ..` / `refine T` at tactic position (line start, after a
            bullet, `=>`, `<;>`, `;` or `by`) whose term T is built only from anonymous constructors, constructor applications
            (dot `.c ..` or qualified `C.c ..` heads), locals and their projections (`h.1`, `ih.2.1`), `_`, `..`, `rfl` (`$` / `<|`
            application allowed); never `?_` (it leaves goals) for a single step
    arm     the body of a `case .. =>` / `next .. =>` / `| .. =>` alternative or a `·` bullet made only of ARM steps: such steps (`?_`
            allowed), `left`, `right`, `constructor`, `apply C`, `exact h`, `assumption`, `rfl`, `trivial`, `rename_i ..`
    region  a split step (induction / cases / rcases / obtain / by_cases / split / fun_induction / fun_cases / constructor / refine /
            apply / split_ands) plus the rest of its block, everything after it ARM steps or arms whose bodies are; HEAD = the split
            step (a trailing ` with` before `|` arms dropped)
    tail    the last k >= 2 ARM steps of a block (no split head), as one span
    hole    (v2) a `refine ⟨c1, .., ck, ?_⟩` step -> `exists c1, .., ck` (core `exists` IS `refine ⟨c1, .., ck, ?_⟩; try trivial`),
            `refine ⟨?_, ?_⟩` -> `constructor`, and at a line start (after bullets) `refine ⟨c.., ?_, ?_⟩` -> `exists c..` + newline +
            `constructor`, `exact|refine ⟨c.., by T⟩` (T on one line) -> `exists c..` + newline + `T` (hole_sites); c1..ck any terms
            without `?_` / `..`, the span free of comments and strings, no multi-line `by` block inside
    wide    (OFF: WIDE_SLOTS = 0; MEASURED 0 of 304 read on the 60 final rows) any arm / bullet body, and any split step plus the rest
            of its block ("wregion", `HEAD <;> M` only), whatever they hold: one closer from menu items 2, 3, 5, 6, 7
  menu      (in this order; kept only when it saves >= 1 token at the site: scorer.tokenize.count_tokens)
            1 assumption  2 constructor <;> assumption  3 solve_by_elim  4 constructor <;> constructor <;> assumption
            5 repeat' constructor <;> assumption  6 apply_rules [C1, ..] (Ci = the qualified constructor / lemma heads written in the
            span)  7 constructor <;> solve_by_elim; v2 (2026-11-03 21:00, fixed core syntax): 8 trivial (only where it can rebuild
            the term: And / True / rfl trees of plain locals; never at a witness, a projection, a field application or an `apply L`)
            9 constructor (a term that is one constructor head applied to nothing but `_`)  10 the witness prefix at a step: `exists
            c1, .., cj` (`use c1, .., cj` at a `use` step) for j < the component count, the dropped components left to the closer's
            own discharger (core `exists` = refine + `try trivial`)  11 rfl (a lone `rfl` / `.refl`-like term); a region is
            `HEAD <;> M` or HEAD + newline + `all_goals M` (M from 1-9, 11); a tail also `all_goals M` (a flat proof's tail can span
            several goals)
  query     one screen file per call (the incumbent first as the control; at most d4_measure.budget(ctx) variants, MAX_VARIANTS
            at most; a SECOND file with the next variants only when the first proposes nothing and the incumbent compiles in at most
            SECOND_FILE_S: a pass that adopts nothing ends the row, so this is the only way past the first file's variants): the space ranked by tokens saved times a fixed menu prior, round robin over sites so every site gets its best
            variant first; variants whose (body prefix through the site, replacement) failed before on this statement are not read
            again (a process-wide cache: the goal at a site depends only on the text before it). Runaway `repeat'` / `solve_by_elim`
            stop inside their own `#eval` at the row's heartbeat limit. A recursive proof's references to its own name are renamed to the
            copy's name. A row whose imports have no Lean.Elab (the `#eval` cannot elaborate) falls back, from then on, to a PLAIN file:
            every variant as a renamed theorem plus `#print axioms` (ok = no sorryAx; no heartbeat reading: the prediction is tokens).
  generate  the measured variants predicted to read higher than the control (d4_measure.predicted), best first, at most PROPOSE; when
            two or more predicted-up variants touch disjoint spans, their union first ("ctorsearch:joint", its own reading decides).
The caller measures every proposal (primary reading, all pins, paired re-reading, audit): the screen only chooses what is proposed.
Generic by construction: the menu is fixed Lean syntax; every name in a candidate is written in the proof being edited.
    python3 harness/post/ctorsearch.py --file proof.lean --statement-file stmt.txt      sites and the space as JSON lines (no compile)"""
from __future__ import annotations

import argparse, hashlib, json, os, re, sys, threading, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "ctorsearch"
OPS = ("ctorsearch:step", "ctorsearch:arm", "ctorsearch:region", "ctorsearch:tail", "ctorsearch:wide", "ctorsearch:wregion",
       "ctorsearch:hole", "ctorsearch:anygoals", "ctorsearch:joint")
MENU = ("assumption", "constructor <;> assumption", "solve_by_elim", "constructor <;> constructor <;> assumption",
        "repeat' constructor <;> assumption", "apply_rules [{heads}]", "constructor <;> solve_by_elim",
        "trivial", "constructor", "{kw} {prefix}", "rfl", "constructor <;> rfl", "any_goals {M}")
PRIOR = (0.40, 0.10, 0.45, 0.15, 0.05, 0.25, 0.20, 0.15, 0.50, 0.50, 0.80, 0.70, 0.40)   # fixed menu priors (ranking only; the screen decides)
# v2 priors (2026-11-03 21:15) from the pooled screen readings of runs 3-9 (60 final rows twice: sub29 and open run 3's agent-best
# snapshot; MEASURED read rate / read at most 50 hb over the control): assumption 13%/13%, constructor <;> assumption 2%/2%,
# solve_by_elim 34%/11%, constructor <;> constructor <;> assumption 6%/6%, repeat' 1%/1%, apply_rules 42%/5%, constructor <;>
# solve_by_elim 13%/5%, trivial 88%/0%, constructor 49%/49%, prefix / hole spellings 68%/12%, rfl 4 of 4, constructor <;> rfl 3 of 3
TRIVIAL, CTOR, PREFIX, RFL, CTORRFL, ANYG = 7, 8, 9, 10, 11, 12   # v2 items (2026-11-03): core `trivial` (its `decide` alternative makes it
# costly: MEASURED +3300 hb at one ⟨rfl, rfl⟩ site), bare `constructor`, the witness prefix, `rfl`, `constructor <;> rfl`
FORM_PRIOR = {"plain": 1.0, "seq": 1.0, "allgoals": 0.8}
MAX_VARIANTS = 16          # the screen file (control included)
PROPOSE = 4                # proposals per call (= the driver's READS)
MAX_SITES = 40
MAX_WIDE_SITES = 24
WIDE_PRIOR = 0.04          # wide spans: a whole case rebuilt by one closer (rarely works; large when it does)
WIDE_MENU = (1, 2, 4, 5, 6)
WIDE_SLOTS = 0             # wide variants per screen file at most: OFF (MEASURED 2026-11-03 on the 60 final rows: 0 of 304 read)
WIDE_CAP_TOK = 30          # a wide span ranks as if it saved at most this many tokens (larger spans rarely close by search)
MAX_TAIL = 8
MAX_HEADS = 6
QUERY_TIMEOUT = 300
MAX_FILES = 2              # screen files per call: the second only when the first proposes nothing and the row compiles fast
SECOND_FILE_S = 30.0       # the incumbent's primary compile seconds up to which a second file is read

STEP_RE = re.compile(r"(exacts|exact|use|exists|refine)(?![\w'!?])")
SPLIT_RE = re.compile(r"(induction|cases|rcases|obtain|by_cases|split|fun_induction|fun_cases|constructor|refine|apply|split_ands)"
                      r"(?![\w'!?])")
ARMHDR_RE = re.compile(r"^(?:case'?|next)\b[^\n]*=>|^\|[^\n]*=>")
BULLET_RE = re.compile(r"^[·.][ \t]+")
SIMPLE_STEP_RE = re.compile(r"^(?:left|right|constructor|assumption|rfl|trivial)$")
NOOP_RE = re.compile(r"^(?:rename_i\b.*|rotate_left\b.*|rotate_right\b.*)$")
IDENT = r"[^\W\d][\w'!?₀-₉]*(?:\.(?:\d+|[^\W\d][\w'!?₀-₉]*))*"
ATOM_RE = re.compile(r"\.\.|\?_|_(?![\w'])|\." + IDENT + r"|" + IDENT + r"|\d+")
LEAF_WORDS = frozenset({"rfl", "trivial", "id"})
STOP_WORDS = frozenset({"fun", "λ", "by", "do", "if", "then", "else", "match", "let", "have", "show", "from", "with", "at", "using",
                        "in", "calc", "Type", "Sort", "Prop"})
OPEN_B, CLOSE_B = "([{⟨⦃‹", ")]}⟩⦄›"

_FAILED: dict = {}         # (statement sha, site prefix sha, replacement) -> True; the module docstring's process-wide cache
_MODE: dict = {}           # statement sha -> "plain" once the measuring file's `#eval` cannot elaborate (the row imports no Lean.Elab)
_USE: dict = {}            # statement sha -> whether Mathlib's `use` parses in the row's environment (learnt from the screen's parses)
_LOCK = threading.Lock()
PLAIN_HDR = "theorem lraD4MDummy : True := trivial\n"
AXIOMS_RE = re.compile(r"'(?:[^'\s]*\.)?lraD4M(\d+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)")
NO_ELAB_RE = re.compile(r"Unknown (?:identifier|constant|namespace)[^`]*`Lean\.(?:Elab|Parser|withoutModifyingEnv|getEnv)")


# ------------------------------------------------------------------------------------------------------------------------------ text
def _clean(body: str) -> str:
    """The body with comment / string characters blanked (newlines kept), so offsets are the body's."""
    mask = _mask(body)
    return "".join(" " if mask[i] and body[i] != "\n" else body[i] for i in range(len(body)))


def _lines(clean: str) -> list[tuple[int, str, int]]:
    """[(start offset, code text, indent)] of the lines."""
    out, pos = [], 0
    for ln in clean.split("\n"):
        out.append((pos, ln, len(ln) - len(ln.lstrip(" \t"))))
        pos += len(ln) + 1
    return out


def _block_end(ls, i: int, ind: int) -> int:
    """The index after the last line of the block that line i opens at indentation `ind`: following lines more indented (or blank)."""
    j = i + 1
    last = i
    while j < len(ls):
        s, code, d = ls[j]
        if code.strip():
            if d <= ind:
                break
            last = j
        j += 1
    return last + 1


def _rstrip_at(clean: str, hi: int) -> int:
    while hi > 0 and clean[hi - 1] in " \t\n":
        hi -= 1
    return hi


# ------------------------------------------------------------------------------------------------------------------------------ terms
def _split_top(s: str, sep: str = ",") -> list[str] | None:
    out, d, cur = [], 0, []
    for ch in s:
        if ch in OPEN_B:
            d += 1
        elif ch in CLOSE_B:
            d -= 1
            if d < 0:
                return None
        if ch == sep and d == 0:
            out.append("".join(cur)); cur = []
        else:
            cur.append(ch)
    if d != 0:
        return None
    out.append("".join(cur))
    return [x.strip() for x in out]


def _atoms(s: str) -> list[str] | None:
    """Whitespace-separated application atoms of `s` (bracket groups kept whole), or None on anything else."""
    out, i, n = [], 0, len(s)
    while i < n:
        ch = s[i]
        if ch in " \t\n":
            i += 1; continue
        if ch in "(⟨":
            close = ")" if ch == "(" else "⟩"
            d, j = 0, i
            while j < n:
                if s[j] in OPEN_B:
                    d += 1
                elif s[j] in CLOSE_B:
                    d -= 1
                    if d == 0:
                        break
                j += 1
            if j >= n or s[j] != close:
                return None
            nxt = s[j + 1:j + 2]
            if nxt and nxt not in " \t\n":   # `(f x).symm`: a projection of a compound term is not a piece
                return None
            out.append(s[i:j + 1]); i = j + 1; continue
        m = ATOM_RE.match(s, i)
        if not m or m.end() == i:
            return None
        nxt = s[m.end():m.end() + 1]
        if nxt and nxt not in " \t\n":
            return None
        out.append(m.group(0)); i = m.end()
    return out


def _is_global_head(a: str) -> bool:
    """A constructor / lemma head written qualified (`C.c`, first component capitalised) or with a leading dot."""
    return a.startswith(".") and len(a) > 1 or ("." in a and a[:1].isupper())


def ctor_term(t: str, info: dict | None = None, depth: int = 0, allow_hole: bool = False) -> bool:
    """True when `t` is built only from the module docstring's pieces; `info` collects "heads" (qualified heads), "dots", "leaves",
    "holes", "depth"."""
    info = info if info is not None else {}
    info.setdefault("heads", []); info.setdefault("dots", []); info.setdefault("leaves", []); info.setdefault("holes", 0)
    info["depth"] = max(info.get("depth", 0), depth)
    t = t.strip()
    if not t or depth > 8:
        return False
    for sep in ("$", "<|"):   # right-associative application: `f a $ g b` = `f a (g b)`
        parts = _split_dollar(t, sep)
        if parts is not None and len(parts) > 1:
            return all(ctor_term(p, info, depth, allow_hole) for p in parts) and _is_app(parts[0])
    at = _atoms(t)
    if not at:
        return False
    if len(at) == 1:
        a = at[0]
        if a.startswith("⟨"):
            inner = a[1:-1].strip()
            if not inner:
                return True
            parts = _split_top(inner)
            return parts is not None and all(p and ctor_term(p, info, depth + 1, allow_hole) for p in parts)
        if a.startswith("("):
            return ctor_term(a[1:-1], info, depth + 1, allow_hole)
        if a == "?_":
            info["holes"] += 1
            return allow_hole
        if a in STOP_WORDS:
            return False
        if a.startswith(".") and a != "..":
            info["dots"].append(a)
        elif _is_global_head(a):
            info["heads"].append(a)
        else:
            info["leaves"].append(a)
        return True
    head, args = at[0], at[1:]
    if head in STOP_WORDS or len(args) > 8 or head.startswith(("(", "⟨")):
        return False
    if head.startswith("."):
        info["dots"].append(head)
    elif _is_global_head(head):
        info["heads"].append(head)
    elif "." in head:   # `h.1.c x`: field notation on a local (a constructor or a lemma; the screen tells)
        info["fieldapps"] = info.get("fieldapps", 0) + 1
    else:
        return False
    return all(ctor_term(a, info, depth + 1, allow_hole) for a in args)


def _is_app(s: str) -> bool:
    at = _atoms(s.strip())
    return bool(at) and (len(at) > 1 or at[0].startswith(".") or _is_global_head(at[0]) or "." in at[0])


def _split_dollar(t: str, sep: str) -> list[str] | None:
    out, d, cur, i = [], 0, [], 0
    while i < len(t):
        ch = t[i]
        if ch in OPEN_B:
            d += 1
        elif ch in CLOSE_B:
            d -= 1
        if d == 0 and t.startswith(sep, i) and (sep != "$" or True):
            out.append("".join(cur)); cur = []; i += len(sep); continue
        cur.append(ch); i += 1
    out.append("".join(cur))
    return [x for x in (y.strip() for y in out)] if len(out) > 1 and all(x.strip() for x in out) else None


def step_term(kw: str, rest: str, info: dict, allow_hole: bool) -> bool:
    """The step `kw rest` is a constructor step (module docstring)."""
    rest = rest.strip()
    if not rest:
        return False
    if kw in ("use", "exists"):
        info["witness"] = True
        parts = _split_top(rest)
        return parts is not None and all(p and ctor_term(p, info, 1, allow_hole) for p in parts)
    if kw == "exacts":
        if not (rest.startswith("[") and rest.endswith("]")):
            return False
        parts = _split_top(rest[1:-1])
        return parts is not None and all(p and ctor_term(p, info, 0, allow_hole) for p in parts)
    if kw == "refine" and not allow_hole and "?_" in rest:
        return False
    return ctor_term(rest, info, 0, allow_hole)


# ------------------------------------------------------------------------------------------------------------------------------ steps
TACPOS_RE = re.compile(r"(?:^[ \t]*(?:[·.][ \t]+)*|(?:=>|<;>|;|(?<![\w.'])by)[ \t]*)$")


def _term_end(clean: str, ls, li: int, start: int) -> int:
    """End offset of a step's term starting at `start` on line li: the rest of the logical line (more indented lines continue it),
    cut at a top-level `<;>` / `;` / `|`, or at the bracket that closes an enclosing group."""
    ind = ls[li][2]
    end_line = _block_end(ls, li, ind)
    stop = ls[end_line - 1][0] + len(ls[end_line - 1][1])
    d, i = 0, start
    while i < stop:
        ch = clean[i]
        if ch in OPEN_B:
            d += 1
        elif ch in CLOSE_B:
            d -= 1
            if d < 0:
                return _rstrip_at(clean, i)
        elif d == 0 and (clean.startswith("<;>", i) or ch == ";" or (ch == "|" and not clean.startswith("||", i))):
            return _rstrip_at(clean, i)
        i += 1
    return _rstrip_at(clean, stop)


def step_sites(body: str, allow_hole: bool = False) -> list[dict]:
    """Constructor steps (module docstring, "step"): [{"kind": "step", "lo", "hi", "kw", "info", "line"}] in body order."""
    clean = _clean(body)
    ls = _lines(clean)
    out = []
    for li, (s, code, ind) in enumerate(ls):
        if li == 0:
            continue
        for m in STEP_RE.finditer(code):
            if not TACPOS_RE.search(code[:m.start()]):
                continue
            lo = s + m.start()
            hi = _term_end(clean, ls, li, s + m.end())
            if hi <= s + m.end():
                continue
            info: dict = {}
            if not step_term(m.group(1), clean[s + m.end():hi], info, allow_hole):
                continue
            out.append({"kind": "step", "lo": lo, "hi": hi, "kw": m.group(1), "info": info, "line": li})
    return out


MATHLIB_TAC_RE = re.compile(r"(?<![\w.'])(?:use|linarith|nlinarith|positivity|norm_num|ring_nf|ring|field_simp|gcongr|push_neg|"
                            r"fun_prop|filter_upwards|interval_cases|polyrith|bound)(?![\w'!?])")


def use_mode(statement: str, body: str) -> str | None:
    """How `use` spellings join the space: "first" (the row's environment has `use`: learnt from an earlier screen, or the proof already
    runs a Mathlib-only tactic; ranked before `exists`), "after" (unknown: screened after `exists`, and the screen's parse of it decides
    for the row), None (a `use` spelling did not parse in this environment)."""
    known = _USE.get(hashlib.sha256(statement.encode()).hexdigest()[:16])
    if known is False:
        return None
    return "first" if known or _mathlib(body) else "after"


def _mathlib(body: str) -> bool:
    """The proof already runs a Mathlib-only tactic (so Mathlib's `use` is in scope): `use` spellings are screened beside `exists`
    (its discharger tries rfl / assumption / And.intro but no `decide` / `contradiction`, unlike core `exists`' `trivial`)."""
    return bool(MATHLIB_TAC_RE.search(_clean(body)))


REFINE_RE = re.compile(r"(?:refine|exact)(?![\w'!?])")
LINE_START_RE = re.compile(r"^[ \t]*(?:[·.][ \t]+)*$")
BYTAC_RE = re.compile(r"^by\s+(\S.*)$")


def hole_sites(body: str, use: str | None | bool = True) -> list[dict]:
    """Steps at tactic position, in a span without comments or strings (a trailing bracket flattened; c1..ck hold no `?_` / `..`):
      `refine ⟨c1, .., ck, ?_⟩` -> `exists c1, .., ck` (core: exactly `refine ⟨c1, .., ck, ?_⟩; try trivial`);
      `refine ⟨?_, ?_⟩` -> `constructor`;
      at a line start (after bullets): `refine ⟨c1, .., ck, ?_, ?_⟩` -> `exists c1, .., ck` + newline + `constructor`, and
      `exact|refine ⟨c1, .., ck, by T⟩` (T on one line) -> `exists c1, .., ck` + newline + `T` (the step's column), and
      `exact|refine ⟨c1, .., ck, p⟩` (one line, p a term) -> `exists c1, .., ck` + newline + `exact p`.
    `use` spellings beside `exists` per `use` (use_mode; True: when the proof runs a Mathlib-only tactic).
    [{"kind": "hole", "lo", "hi", "kw", "info", "line", "reps", "use"}]."""
    clean = _clean(body)
    ls = _lines(clean)
    out = []
    if use is True:
        use = "first" if _mathlib(body) else None
    ml = bool(use)
    for li, (s, code, ind) in enumerate(ls):
        if li == 0:
            continue
        for m in REFINE_RE.finditer(code):
            if not TACPOS_RE.search(code[:m.start()]):
                continue
            lo, t0 = s + m.start(), s + m.end()
            hi = _term_end(clean, ls, li, t0)
            if hi <= t0 or body[lo:hi] != clean[lo:hi] or "\t" in code[:m.start()]:
                continue
            at = _atoms(clean[t0:hi])
            if not at or len(at) != 1 or not at[0].startswith("⟨"):
                continue
            if "\n" in at[0] and re.search(r"(?<![\w.'])by(?![\w'!?])", at[0]):
                continue   # a tactic block over several lines: one-line spelling would change it
            cs = _flat_components(at[0])
            if not cs or len(cs) < 2:
                continue
            line_end = clean.find("\n", hi)
            alone = not clean[hi:line_end if line_end >= 0 else len(clean)].strip()   # nothing after the step on its last line
            col = " " * m.start() if LINE_START_RE.match(code[:m.start()]) and alone else None   # the step's column, a line to itself
            bt = BYTAC_RE.match(cs[-1])
            if cs[-1] == "?_" and m.group(0) == "refine":
                two = len(cs) >= 3 and cs[-2] == "?_"   # `refine ⟨c.., ?_, ?_⟩`: `exists c..` then `constructor` (the same goals)
                kept, tail = (cs[:-2], "constructor") if two else (cs[:-1], None)
            elif bt and "\n" not in clean[t0:hi] and not re.search(r"\?_", clean[t0:hi]):
                kept, tail = cs[:-1], bt.group(1)
            elif ("\n" not in clean[t0:hi] and not re.search(r"\?_", clean[t0:hi]) and not HOLE_RE.fullmatch(cs[-1])
                  and not HOLE_RE.fullmatch(cs[-2])):   # a hole witness right before p: nothing would pin it any more
                kept, tail = cs[:-1], "exact " + cs[-1]   # `exact ⟨w.., p⟩` -> `use|exists w..` + newline + `exact p`
            else:
                continue
            if all(c == "?_" for c in cs):
                reps = ["constructor"] if len(cs) == 2 else []
            elif not kept or any(re.search(r"\?_|(?<![\w'.])\.\.(?![\w'])", c) for c in kept) or (tail and col is None):
                reps = []
            else:
                reps = [kw + " " + ", ".join(kept) + ("\n" + col + tail if tail else "")
                        for kw in (("exists", "use") if ml else ("exists",))]
            if reps:
                out.append({"kind": "hole", "lo": lo, "hi": hi, "kw": m.group(0), "info": {}, "line": li, "reps": reps, "use": use})
    return out


def _flat_components(bracket: str) -> list[str] | None:
    """`⟨a, b, ⟨c, d⟩⟩` -> [a, b, c, d] (only a trailing bracket flattened), whitespace runs as one blank; None when unbalanced."""
    cs = _split_top(bracket[1:-1])
    if not cs or any(not c for c in cs):
        return None
    while True:
        at = _atoms(cs[-1])
        if not (at and len(at) == 1 and at[0].startswith("⟨")):
            break
        inner = _split_top(at[0][1:-1])
        if not inner or any(not c for c in inner):
            break
        cs = cs[:-1] + inner
    return [" ".join(c.split()) for c in cs]


CLOSER_LINE_RE = re.compile(r"^(?:assumption|solve_by_elim|trivial|rfl|decide|omega|grind|tauto|linarith|nlinarith|positivity|simp_all|"
                            r"aesop|constructor <;> (?:assumption|solve_by_elim|rfl)|exact [^\s;<>|]+)$")
NEUTRAL_RE = re.compile(r"^(?:exact|exacts|choose|have|obtain|intro|intros|rintro|rename_i|subst|subst_vars|specialize|simp|simp_all|"
                        r"dsimp|rw|rwa|unfold|norm_num|omega|linarith|nlinarith|positivity|grind|aesop|tauto|decide|rfl|assumption|"
                        r"solve_by_elim|trivial|contradiction|exfalso|show|change|replace|let|clear|revert|generalize|field_simp|ring|"
                        r"ring_nf|calc|injection|apply_assumption|use|exists)(?![\w'!?])")


def _neutral(code: str) -> bool:
    """A step that works on the main goal and adds no goal (so goals after it are the ones before it, minus the main one when it
    closes): no `?_`, no rcases alternative `|`, no `<;>` / `;` sequencing."""
    t = code.strip()
    return bool(NEUTRAL_RE.match(t)) and "?_" not in t and not re.search(r"(?<![|])\|(?![|])", t) and "<;>" not in t and ";" not in t


def anygoals_sites(body: str) -> list[dict]:
    """(v2) A closer written as its own line k >= 2 times in one flat block (`assumption`, `solve_by_elim`, `rfl`, `omega`, `grind`,
    `constructor <;> ..`, `exact h`, ..), the copies separated only by goal-neutral steps at the block's indentation (_neutral: they
    work on the main goal and add none; deeper lines belong to them): the first copy -> `any_goals M`, the later copies deleted (every
    goal a later copy closed exists already at the first and M closes it there; the other goals stay in order). One span from the
    first copy to the last: [{"kind": "anygoals", "lo", "hi", "reps", "info", "line"}]."""
    clean = _clean(body)
    ls = _lines(clean)
    groups: dict = {}
    for li, (s, code, ind) in enumerate(ls):
        if li == 0 or not code.strip():
            continue
        t = code.strip()
        nxt = next((ls[j] for j in range(li + 1, len(ls)) if ls[j][1].strip()), None)
        if CLOSER_LINE_RE.match(t) and body[s:s + len(code)] == code and not (nxt and nxt[2] > ind):   # a whole step (no continuation)
            groups.setdefault((ind, t), []).append(li)
    out = []
    for (ind, t), idx_all in groups.items():
        runs, cur = [], [idx_all[0]]
        for a, b in zip(idx_all, idx_all[1:]):   # copies separated only by goal-neutral steps at the block's indentation
            mid = [ls[j] for j in range(a + 1, b) if ls[j][1].strip()]
            if all(d > ind or (d == ind and _neutral(c)) for (_, c, d) in mid):
                cur.append(b)
            else:
                runs.append(cur); cur = [b]
        runs.append(cur)
        for idx in runs:
            if len(idx) >= 2:
                out.append(_anyg_site(body, ls, ind, t, idx))
    return out


def _anyg_site(body: str, ls, ind: int, t: str, idx: list[int]) -> dict:
    """The span from the first copy (line idx[0]) to the last: the first as `any_goals t`, the other copies' lines dropped."""
    i0, i1 = idx[0], idx[-1]
    keep = [" " * ind + "any_goals " + t] + [body[ls[j][0]:ls[j][0] + len(ls[j][1])] for j in range(i0 + 1, i1 + 1) if j not in idx]
    return {"kind": "anygoals", "lo": ls[i0][0] + ind, "hi": ls[i1][0] + len(ls[i1][1]), "reps": ["\n".join(keep)[ind:]], "info": {},
            "line": i0}


def _arm_step_ok(text: str) -> bool:
    """One ARM step (module docstring, "arm")."""
    t = " ".join(text.split())
    if not t:
        return True
    if SIMPLE_STEP_RE.match(t) or NOOP_RE.match(t):
        return True
    m = re.match(r"^apply\s+(.*)$", t)
    if m:
        return ctor_term(m.group(1), {}, 0, True) or bool(re.fullmatch(IDENT, m.group(1)))
    m = STEP_RE.match(t)
    if m and m.start() == 0:
        return step_term(m.group(1), t[m.end():], {}, True)
    return False


def _first_ok(lines: list[str]) -> bool:
    """A bullet's first line is an ARM step on its own, or it starts a step whose term continues on the next lines (the joined text is
    then one ARM step). The joined text is never matched against the one-line no-op forms (`rename_i ..` would swallow the rest)."""
    if _arm_step_ok(lines[0]):
        return True
    m = STEP_RE.match(lines[0].strip())
    return bool(m and m.start() == 0) and _arm_step_ok(" ".join(x.strip() for x in lines))


def _joined_step(lines: list[str]) -> bool:
    """The lines are ONE multi-line constructor step (module docstring, "step")."""
    m = STEP_RE.match(lines[0].strip())
    return len(lines) > 1 and bool(m and m.start() == 0) and _arm_step_ok(" ".join(x.strip() for x in lines))


def _block_steps(clean: str, ls, i0: int, i1: int):
    """[(first line, end line (exclusive), indent, text)] of the steps at the block's base indentation in lines [i0, i1)."""
    steps, i = [], i0
    base = None
    while i < i1:
        s, code, d = ls[i]
        if not code.strip():
            i += 1; continue
        if base is None:
            base = d
        if d < base:
            return None
        e = _block_end(ls, i, d)
        e = min(e, i1)
        txt = clean[s:ls[e - 1][0] + len(ls[e - 1][1])]
        steps.append((i, e, d, txt))
        i = e
    return steps


def _arm_body_ok(clean: str, ls, steps) -> bool:
    """Every step of `steps` is an ARM step, or an arm header / bullet whose body is all ARM steps."""
    for (i, e, d, txt) in steps:
        first = ls[i][1].strip()
        if ARMHDR_RE.match(first):
            hdr_end = first.index("=>") + 2
            inline = first[hdr_end:].strip()
            sub = _block_steps(clean, ls, i + 1, e)
            if sub is None:
                return False
            if inline and not _arm_step_ok(inline):
                return False
            if not _arm_body_ok(clean, ls, sub):
                return False
            continue
        b = BULLET_RE.match(first)
        if b:
            inner = txt.strip()[b.end():]
            parts = [p for p in re.split(r"\n", inner)]
            if not _first_ok(parts):
                return False
            sub = _block_steps(clean, ls, i + 1, e)
            if sub and not _joined_step(parts) and not _arm_body_ok(clean, ls, sub):
                return False
            continue
        if not _arm_step_ok(txt):
            return False
    return True


TAC_WORDS = frozenset({"exact", "exacts", "use", "exists", "refine", "apply", "left", "right", "constructor", "assumption", "trivial",
                       "rename_i", "rotate_left", "rotate_right", "cases", "induction", "rcases", "obtain", "by_cases", "split",
                       "fun_induction", "fun_cases", "split_ands", "with", "generalizing", "at", "using", "case", "next", "all_goals",
                       "any_goals", "fun", "by"})


def _span_info(text: str) -> dict:
    """heads / dots of a span's text, plus "fieldapps" (dotted names of locals: `h.1`, `hr.app`) and "leaves" (`_` witness holes and
    every plain name that is no tactic word: a local, `rfl`, an unqualified lemma)."""
    info: dict = {"heads": [], "dots": [], "leaves": [], "fieldapps": 0}
    for m in ATOM_RE.finditer(text):
        a = m.group(0)
        if a.startswith(".") and a != ".." and len(a) > 1:
            info["dots"].append(a)
        elif _is_global_head(a):
            info["heads"].append(a)
        elif "." in a and a != "..":
            info["fieldapps"] += 1
        elif a == "_" or (a not in TAC_WORDS and a != ".." and not a.isdigit()):
            info["leaves"].append(a)
    info["witness"] = bool(re.search(r"(?<![\w.'])(?:use|exists)(?![\w'!?])", text))
    info["applies"] = bool(re.search(r"(?<![\w.'])apply(?![\w'!?])", text))   # `apply L`: a lemma `trivial` cannot supply
    return info


def arm_sites(body: str) -> list[dict]:
    """Arm / bullet bodies (module docstring, "arm"): [{"kind": "arm", "lo", "hi", "indent", "info", "line"}]."""
    clean = _clean(body)
    ls = _lines(clean)
    out = []
    for li, (s, code, ind) in enumerate(ls):
        if li == 0 or not code.strip():
            continue
        c = code.strip()
        e = _block_end(ls, li, ind)
        if ARMHDR_RE.match(c):
            after = c[c.index("=>") + 2:]
            if after.strip():   # inline body: `| tag => tac` (plus continuation lines)
                lo = s + ind + c.index("=>") + 2
                lo += len(clean[lo:]) - len(clean[lo:].lstrip(" \t"))
                hi = _rstrip_at(clean, ls[e - 1][0] + len(ls[e - 1][1]))
                txt = clean[lo:hi]
                if _arm_step_ok(txt) and not _single_step(txt):
                    out.append({"kind": "arm", "lo": lo, "hi": hi, "indent": None, "info": _span_info(txt), "line": li})
                continue
            if e <= li + 1:
                continue
            steps = _block_steps(clean, ls, li + 1, e)
            if not steps or len(steps) < 2 or not _arm_body_ok(clean, ls, steps):
                continue
            lo = ls[steps[0][0]][0] + steps[0][2]
            hi = _rstrip_at(clean, ls[e - 1][0] + len(ls[e - 1][1]))
            out.append({"kind": "arm", "lo": lo, "hi": hi, "indent": " " * steps[0][2], "info": _span_info(clean[lo:hi]), "line": li})
        else:
            b = BULLET_RE.match(c)
            if not b:
                continue
            lo = s + ind + b.end()
            hi = _rstrip_at(clean, ls[e - 1][0] + len(ls[e - 1][1]))
            # the bullet's steps: the first on the bullet line, the rest more indented at the first step's column
            col = ind + b.end()
            lines_txt = [clean[lo:s + len(code)]] + [ls[k][1] for k in range(li + 1, e)]
            sub = _block_steps(clean, ls, li + 1, e)
            if not _first_ok(lines_txt):
                continue
            if sub and not _joined_step(lines_txt):
                if not all(d == col for (_, _, d, _) in sub) or not _arm_body_ok(clean, ls, sub):
                    continue
            txt = clean[lo:hi]
            if _single_step(txt):
                continue
            out.append({"kind": "arm", "lo": lo, "hi": hi, "indent": " " * col, "info": _span_info(txt), "line": li})
    return out


def _single_step(txt: str) -> bool:
    """One constructor step on its own (the step rule covers it)."""
    t = " ".join(txt.split())
    m = STEP_RE.match(t)
    return bool(m and m.start() == 0 and "\n" not in txt.strip())


def region_sites(body: str) -> list[dict]:
    """Split step + rest of its block, all ARM afterwards (module docstring, "region"), and tails of k >= 2 ARM steps."""
    clean = _clean(body)
    ls = _lines(clean)
    out = []
    n = len(ls)
    # blocks: for every line, the steps that follow it at its indentation until a less indented line
    seen_tail = set()
    for li, (s, code, ind) in enumerate(ls):
        if li == 0 or not code.strip():
            continue
        # the rest of the block from line li at indentation ind
        j = li
        while j < n and (not ls[j][1].strip() or ls[j][2] >= ind):
            j += 1
        rest = _block_steps(clean, ls, li, j)
        if not rest or rest[0][2] != ind or any(d != ind for (_, _, d, _) in rest):
            continue
        c = code.strip()
        bm = BULLET_RE.match(c)
        if bm:
            continue
        m = SPLIT_RE.match(c)
        if m and len(rest) >= 2 and rest[0][1] == li + 1 and _head_ok(c):
            head = re.sub(r"\s+with\s*$", "", c) if (rest[1][3].strip().startswith("|") and c.rstrip().endswith("with")) else c
            if "<;>" not in head and not head.rstrip().endswith("with") and _arm_body_ok(clean, ls, rest[1:]):
                hi = _rstrip_at(clean, ls[j - 1][0] + len(ls[j - 1][1]))
                lo = s + ind
                out.append({"kind": "region", "lo": lo, "hi": hi, "head": head, "indent": " " * ind,
                            "info": _span_info(clean[ls[li + 1][0]:hi]), "line": li})
        # tails: the last k ARM steps of this block (only from its first step, once per block end)
        if (j, ind) in seen_tail:
            continue
        seen_tail.add((j, ind))
        k_ok = 0
        for (i0, e0, d0, txt) in reversed(rest):
            if ARMHDR_RE.match(ls[i0][1].strip()) or BULLET_RE.match(ls[i0][1].strip()) or not _arm_step_ok(txt):
                break
            k_ok += 1
        for k in range(2, min(k_ok, MAX_TAIL) + 1):
            i0 = rest[-k][0]
            lo = ls[i0][0] + ind
            hi = _rstrip_at(clean, ls[j - 1][0] + len(ls[j - 1][1]))
            if any(o["lo"] == lo and o["hi"] == hi for o in out):
                continue
            out.append({"kind": "tail", "lo": lo, "hi": hi, "indent": " " * ind, "info": _span_info(clean[lo:hi]), "line": i0})
    return out


def wide_sites(body: str) -> list[dict]:
    """WIDE spans (module docstring, "wide"): every arm / bullet body and every split step plus the rest of its block, whatever they
    hold, as one span for a single closer (low prior: these rebuild a whole case by search)."""
    clean = _clean(body)
    ls = _lines(clean)
    out, n = [], len(ls)
    for li, (s, code, ind) in enumerate(ls):
        if li == 0 or not code.strip():
            continue
        c = code.strip()
        e = _block_end(ls, li, ind)
        if ARMHDR_RE.match(c):
            k = c.index("=>") + 2
            if c[k:].strip():
                lo = s + ind + k
                lo += len(clean[lo:]) - len(clean[lo:].lstrip(" \t"))
            elif e > li + 1:
                st = next((x for x in range(li + 1, e) if ls[x][1].strip()), None)
                if st is None:
                    continue
                lo = ls[st][0] + ls[st][2]
            else:
                continue
            hi = _rstrip_at(clean, ls[e - 1][0] + len(ls[e - 1][1]))
            if hi > lo:
                out.append({"kind": "wide", "lo": lo, "hi": hi, "indent": None, "info": _span_info(clean[lo:hi]), "line": li})
            continue
        b = BULLET_RE.match(c)
        if b:
            lo = s + ind + b.end()
            hi = _rstrip_at(clean, ls[e - 1][0] + len(ls[e - 1][1]))
            if hi > lo:
                out.append({"kind": "wide", "lo": lo, "hi": hi, "indent": None, "info": _span_info(clean[lo:hi]), "line": li})
            continue
        m = SPLIT_RE.match(c)
        if not (m and _head_ok(c)) or "<;>" in c or c.rstrip().endswith(("with", "=>", "by")):
            continue
        j = li + 1
        while j < n and (not ls[j][1].strip() or ls[j][2] >= ind):
            j += 1
        if not any(ls[x][1].strip() for x in range(li + 1, j)):
            continue
        hi = _rstrip_at(clean, ls[j - 1][0] + len(ls[j - 1][1]))
        lo = s + ind
        out.append({"kind": "wregion", "lo": lo, "hi": hi, "head": c, "indent": " " * ind,
                    "info": _span_info(clean[ls[li + 1][0]:hi]), "line": li})
    return out


def _head_ok(c: str) -> bool:
    """A split head on one line with balanced brackets, not itself a whole closing step."""
    if _split_top(c) is None:
        return False
    if re.match(r"^(?:exact|exacts)\b", c):
        return False
    if c.startswith("refine") and "?_" not in c:
        return False
    if c.startswith("obtain") and ":=" not in c:
        return False
    return True


# ------------------------------------------------------------------------------------------------------------------------------ space
def _heads(info: dict) -> list[str]:
    hs = []
    for h in info.get("heads") or []:
        if h not in hs:
            hs.append(h)
    return hs[:MAX_HEADS]


def menu(info: dict) -> list[tuple[int, str]]:
    """[(menu index, closer text)] for a span's info (item 6 only with qualified heads)."""
    out = []
    for k, m in enumerate(MENU):
        if (k in (PREFIX, ANYG) or (k == CTOR and not _bare_ctor(info)) or (k == TRIVIAL and not _trivial_ok(info))
                or (k == RFL and not _rfl_term(info)) or (k == 0 and _rfl_term(info)) or (k == CTORRFL and not _rfl_pair(info))):
            continue
        if "{heads}" in m:
            hs = _heads(info)
            if not hs:
                continue
            m = m.replace("{heads}", ", ".join(hs))
        out.append((k, m))
    return out


def _bare_ctor(info: dict) -> bool:
    """The term is one constructor head applied to nothing but `_` (`.refl`, `.nil _`, `Foo.mk`): bare `constructor` may rebuild it."""
    return (len(info.get("dots") or []) + len(info.get("heads") or []) == 1 and not info.get("fieldapps")
            and all(x == "_" for x in info.get("leaves") or []))


def _rfl_like(x: str) -> bool:
    return x.rsplit(".", 1)[-1] in ("refl", "rfl")


def _rfl_term(info: dict) -> bool:
    """The term is `rfl` alone, or one `.refl`-like constructor applied to nothing but `_` (core `rfl` tries @[refl] lemmas)."""
    hd = (info.get("heads") or []) + (info.get("dots") or [])
    lv = [x for x in info.get("leaves") or [] if x != "_"]
    return (not info.get("fieldapps") and not info.get("witness") and all(_rfl_like(x) for x in hd)
            and len(hd) + len(lv) == 1 and all(x == "rfl" for x in lv))


def _rfl_pair(info: dict) -> bool:
    """An anonymous constructor (depth 1) of `rfl`s only: `constructor <;> rfl` rebuilds it."""
    lv = info.get("leaves") or []
    return (len(lv) >= 2 and all(x == "rfl" for x in lv) and not info.get("heads") and not info.get("dots")
            and not info.get("fieldapps") and info.get("depth", 0) == 1 and not info.get("witness"))


def _trivial_ok(info: dict) -> bool:
    """Core `trivial` (assumption, rfl, True.intro, decide, And.intro recursively) may rebuild the term: no constructor head but
    `.refl`-like ones, no field application / projection of a local, no witness hole, and not one plain local (`assumption` is as
    short and cheaper)."""
    leaves = info.get("leaves") or []
    if any(not _rfl_like(x) for x in (info.get("heads") or []) + (info.get("dots") or [])) or info.get("fieldapps"):
        return False
    if info.get("witness") or info.get("applies") or _rfl_term(info) or any(x == "_" or "." in x or x[:1].isdigit() for x in leaves):
        return False   # a `use` / `exists` step builds a witness; a lone rfl has the shorter `rfl`
    return not (len(leaves) == 1 and leaves[0] not in LEAF_WORDS and not info.get("dots") and not info.get("heads"))


def components(kw: str, term: str) -> list[str] | None:
    """The components of a step's term as `exists` / `use` would take them: `use a, b` / `exists a, b` -> [a, b]; `exact ⟨a, b, c⟩` /
    `refine ⟨a, b, c⟩` -> [a, b, c] (a trailing anonymous constructor flattened: `⟨a, ⟨b, c⟩⟩` is `⟨a, b, c⟩`); else None."""
    t = term.strip()
    if kw in ("use", "exists"):
        cs = _split_top(t)
        if not cs or any(not c for c in cs):
            return None
        return [" ".join(c.split()) for c in cs]
    if kw in ("exact", "refine"):
        at = _atoms(t)
        if not at or len(at) != 1 or not at[0].startswith("⟨"):
            return None
        return _flat_components(at[0])
    return None


HOLE_RE = re.compile(r"(?<![\w'.])(?:\?_|_|\.\.)(?![\w'])")


def prefixes(site: dict, body: str, use: str | None | bool = True) -> list[tuple[str, dict]]:
    """Menu item PREFIX at a step site: `exists c1, .., cj` (`use c1, .., cj` at a `use` step: Mathlib's discharger) for every j <
    the component count, the dropped components left to the closer's own discharger (core `exists` = `refine ⟨c1, .., cj, ?_⟩; try
    trivial`: assumption, rfl, And.intro recursively). Kept components hold no `_` / `?_` / `..` (refine cannot synthesise them).
    [(replacement, info of the dropped components)]."""
    if site.get("kind") != "step":
        return []
    kw = site.get("kw")
    if _clean(body[site["lo"]:site["hi"]]) != body[site["lo"]:site["hi"]]:
        return []   # a comment or string inside: the one-line spelling could swallow code
    cs = components(kw, body[site["lo"] + len(kw):site["hi"]])
    if not cs or len(cs) < 2:
        return []
    out = []
    if use is True:
        use = "first" if _mathlib(body) else None
    for j in range(1, len(cs)):
        if any(HOLE_RE.search(c) for c in cs[:j]):
            break
        info: dict = {}
        if not all(ctor_term(c, info, 1) for c in cs[j:]):
            continue
        for kw2 in (("use",) if kw == "use" else ("exists", "use") if use else ("exists",)):
            out.append((f"{kw2} {', '.join(cs[:j])}", dict(info, use=kw2 == "use" and kw != "use", use_after=use == "after",
                                                             exists_ml=kw2 == "exists" and use == "first")))
    return out


def all_sites(body: str, wide: bool | None = None, use: str | None | bool = True) -> list[dict]:
    ss = step_sites(body) + arm_sites(body) + region_sites(body) + hole_sites(body, use) + anygoals_sites(body)
    seen, out = set(), []
    for s in ss:
        key = (s["lo"], s["hi"], s.get("head"), s["kind"] in ("hole", "anygoals"))
        if key in seen or s["hi"] <= s["lo"]:
            continue
        seen.add(key); out.append(s)
    out = out[:MAX_SITES]
    if wide if wide is not None else WIDE_SLOTS > 0:
        narrow = {(s["lo"], s["hi"]) for s in out}
        for s in wide_sites(body):
            if (s["lo"], s["hi"]) not in narrow and len(out) < MAX_SITES + MAX_WIDE_SITES:
                narrow.add((s["lo"], s["hi"])); out.append(s)
    return out


def _forms(site: dict, body: str) -> list[tuple[str, str, float]]:
    """[(form tag, replacement text, form prior)] for one menu closer M is filled in later."""
    if site["kind"] == "region":
        return [("seq", site["head"] + " <;> {M}", FORM_PRIOR["seq"]),
                ("allgoals", site["head"] + "\n" + site["indent"] + "all_goals {M}", FORM_PRIOR["allgoals"])]
    if site["kind"] == "tail":
        return [("plain", "{M}", FORM_PRIOR["plain"]), ("allgoals", "all_goals {M}", FORM_PRIOR["allgoals"])]
    if site["kind"] == "wregion":
        return [("seq", site["head"] + " <;> {M}", WIDE_PRIOR)]
    if site["kind"] == "wide":
        return [("plain", "{M}", WIDE_PRIOR)]
    return [("plain", "{M}", FORM_PRIOR["plain"])]


def space(proof: str, statement: str) -> list[dict]:
    """Every (site, form, menu item) variant that saves >= 1 token: [{"op", "body", "note", "lo", "hi", "rep", "dtok", "prio",
    "site"}], grouped per site in menu order."""
    body = split_declaration(proof, statement)
    if body is None:
        return []
    t0 = count_tokens(body)
    out = []
    um = use_mode(statement, body)
    for si, s in enumerate(all_sites(body, use=um)):
        old = body[s["lo"]:s["hi"]]
        told = count_tokens(old)
        for form, tmpl, fp in _forms(s, body):
            items = [] if s["kind"] in ("hole", "anygoals") else [(k, M, s["info"]) for k, M in menu(s["info"])]
            if s["kind"] == "anygoals":
                items = [(ANYG, M, {}) for M in s["reps"]]
            if s["kind"] == "hole":
                items = [(CTOR if M == "constructor" else PREFIX, M, {"use": M.startswith("use "), "use_after": um == "after",
                                                                       "exists_ml": um == "first" and M.startswith("exists ")})
                         for M in s["reps"]]
            elif form == "plain":
                items += [(PREFIX, M, inf) for M, inf in prefixes(s, body, um)]
            for k, M, finfo in items:
                if s["kind"] in ("wide", "wregion") and k not in WIDE_MENU:
                    continue
                rep = tmpl.replace("{M}", M)
                dtok = told - count_tokens(rep)
                if dtok < 1:
                    continue
                nb = body[:s["lo"]] + rep + body[s["hi"]:]
                if count_tokens(nb) >= t0:
                    continue
                note = f"{s['kind']} @L{K.line_of(body, s['lo'])} `{_short(old)}` -> `{_short(rep)}`"
                wide = s["kind"] in ("wide", "wregion")
                prio = (min(dtok, WIDE_CAP_TOK) if wide else dtok) * PRIOR[k] * fp * _feasible(finfo, k)
                out.append({"op": f"{FAMILY}:{s['kind']}", "body": nb, "note": note, "lo": s["lo"], "hi": s["hi"], "rep": rep,
                            "dtok": dtok, "prio": prio, "site": si, "menu": k, "form": form})
    return out


def _feasible(info: dict, k: int) -> float:
    """A fixed ranking factor: assumption-family closers rebuild plain locals, not projections, field-notation applications or
    numerals (the screen decides; this only orders the slots)."""
    leaves = info.get("leaves") or []
    f = 1.0
    if any("." in x for x in leaves) or info.get("fieldapps"):
        f *= 0.3
    if any(x[:1].isdigit() for x in leaves):
        f *= 0.3
    if k == 0 and (info.get("heads") or info.get("dots") or len(leaves) != 1):
        f *= 0.2   # `assumption` alone closes a goal that one hypothesis already is
    if k == PREFIX and info.get("use"):
        f *= 0.9 if info.get("use_after") else 1.2   # `use` beside `exists`: first where the environment has it (MEASURED 2026-11-03 run10, 13 paired sites: use -28..+48 hb over the control,
    if k == PREFIX and info.get("exists_ml"):   # exists +1..+1194; the failing `try trivial` tries decide)
        f *= 0.6
    if k in (TRIVIAL, PREFIX) and any(not _rfl_like(x) for x in (info.get("heads") or []) + (info.get("dots") or [])):
        f *= 0.2   # `trivial` (and the prefix's discharger) builds And / True / rfl, no other constructor
    return f


def _short(s: str, n: int = 60) -> str:
    s = " ".join(s.split())
    return s if len(s) <= n else s[:n - 3] + "..."


def _fail_key(statement: str, body: str, v: dict) -> tuple:
    return (hashlib.sha256(statement.encode()).hexdigest()[:16], hashlib.sha256(body[:v["hi"]].encode()).hexdigest()[:16],
            len(body[:v["lo"]]), v["rep"])


def _body_key(statement: str, body: str) -> tuple:
    return (hashlib.sha256(statement.encode()).hexdigest()[:16], hashlib.sha256(body.encode()).hexdigest()[:16])


def ranked(proof: str, statement: str, n: int, exclude: set | None = None) -> list[dict]:
    """At most n variants of the space (module docstring, "query"): round robin over the sites (best site first), each site's variants
    by priority; cached failures left out."""
    body = split_declaration(proof, statement) or ""
    sp = space(proof, statement)
    with _LOCK:
        sp = [v for v in sp if _fail_key(statement, body, v) not in _FAILED and _body_key(statement, v["body"]) not in _FAILED
              and v["body"] not in (exclude or ())]
    per: dict = {}
    for v in sp:
        per.setdefault(v["site"], []).append(v)
    for vs in per.values():
        vs.sort(key=lambda v: (-v["prio"], v["menu"]))
    order = sorted(per, key=lambda si: -per[si][0]["prio"])
    out, seen, r, nwide = [], set(), 0, 0
    while len(out) < n and any(r < len(per[si]) for si in order):
        for si in order:
            if r < len(per[si]) and len(out) < n:
                v = per[si][r]
                wide = v["op"] in ("ctorsearch:wide", "ctorsearch:wregion")
                if v["body"] not in seen and not (wide and nwide >= WIDE_SLOTS):
                    seen.add(v["body"]); out.append(v); nwide += wide
        r += 1
    return out


def has_sites(proof: str, statement: str) -> bool:
    return bool(space(proof, statement)) and MS.renamed(statement, 0) is not None


# ------------------------------------------------------------------------------------------------------------------------------ query
SCREEN = r'''theorem lraD4MDummy : True := trivial

set_option Elab.async false in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let lraNerr : Lean.MessageLog → Nat := fun lraL =>
    (lraL.toList.filter (fun lraMsg => match lraMsg.severity with | .error => true | _ => false)).length
  let lraSrcs : Array String := #[LRAD4MSRCS]
  let lraNames : Array String := #[LRAD4MNAMES]
  let mut lraI := 0
  for lraSrc in lraSrcs do
    let lraNm := lraNames.getD lraI ""
    match Lean.Parser.runParserCategory (← Lean.getEnv) `command lraSrc with
    | .error _ => Lean.logInfo (Lean.toMessageData s!"LRAD4M\t{lraI}\t0\t0\tparse")
    | .ok lraStx =>
      let lraN0 := (← Lean.getCurrNamespace) ++ String.toName lraNm
      let lraEnv0 ← Lean.getEnv
      let lraN := if LRAD4MPRIV then Lean.mkPrivateName lraEnv0 lraN0 else lraN0
      let (lraOk, lraDh) ← Lean.withoutModifyingEnv do
        let lraE0 := lraNerr (← get).messages
        let lraT0 ← IO.getNumHeartbeats
        Lean.Elab.Command.elabCommand lraStx
        let lraT1 ← IO.getNumHeartbeats
        let mut lraOk := lraNerr (← get).messages == lraE0
        match (← Lean.getEnv).find? lraN with
        | some (.thmInfo _) => lraOk := lraOk && !((← Lean.collectAxioms lraN).contains ``sorryAx)
        | _ => lraOk := false
        pure (lraOk, lraT1 - lraT0)
      Lean.logInfo (Lean.toMessageData s!"LRAD4M\t{lraI}\t{if lraOk then 1 else 0}\t{lraDh / 1000}")
    lraI := lraI + 1
'''


def _decl_name(statement: str) -> str | None:
    m = MS.DECL_RE.match(statement)
    if not m:
        return None
    nm = re.split(r"\s+", m.group(0).strip())[-1]
    return nm.split("{")[0] or None


def copy_name(statement: str, i: int) -> str:
    """The screen copy's name: the declaration's own namespace prefix (`Foo.bar` -> `Foo.lraD4M<i>`, so the names the proof resolves
    through the declaration's namespace still resolve) and `lraD4M<i>`."""
    nm = _decl_name(statement) or ""
    pre = nm.rsplit(".", 1)[0] + "." if "." in nm else ""
    return f"{pre}lraD4M{i}"


def renamed(statement: str, i: int) -> str | None:
    """The statement as `[private] theorem <copy_name> ...` (docstrings and attributes dropped; `private` kept: a private declaration may
    use the module's private names), else None (not a theorem / lemma; universe parameters in the name)."""
    m = MS.DECL_RE.match(statement)
    if not m or ".{" in m.group(0):
        return None
    vis = "private " if re.search(r"(?<![\w.])private\b", statement[:m.end()].split("theorem")[0].split("lemma")[0]) else ""
    return f"{vis}theorem {copy_name(statement, i)}" + statement[m.end():]


def is_private(statement: str) -> bool:
    r = renamed(statement, 0)
    return bool(r and r.startswith("private "))


def self_renamed(statement: str, body: str, i: int) -> str:
    """The body with references to the theorem's own name (a recursive proof) renamed to the screen copy's name."""
    nm = _decl_name(statement)
    if not nm:
        return body
    short = nm.split(".")[-1]
    new = copy_name(statement, i)
    out = re.sub(r"(?<![\w.'])" + re.escape(nm) + r"(?![\w'])", new, body)
    return re.sub(r"(?<![\w.'])" + re.escape(short) + r"(?![\w'])", new.split(".")[-1], out)


def measure_text(statement: str, bodies: list[str], attached: str = "") -> str | None:
    """d4_measure's measurement (each variant elaborated between two heartbeat readings, under Lean.withoutModifyingEnv, the incumbent
    first) as ONE `#eval` command, so the `open .. in` / `set_option .. in` modifiers the compile attaches before the declaration apply
    to every copy (d4_measure's one-command-per-variant file gives them to its first command only: measured 2026-11-03), and: the
    copy keeps the declaration's namespace prefix (copy_name), a recursive proof's self-references are renamed (self_renamed), every
    binder of the screen is `lra`-prefixed (a row's local notation can make a short name such as `s` a token: measured 2026-11-03), and
    ok needs the copy to be a THEOREM in the environment without sorryAx AND no new error message while it elaborated (a declaration the
    kernel rejected, e.g. "declaration has metavariables", is in the environment otherwise: measured 2026-11-03). `attached`: the
    `open .. in` / `set_option .. in` combinators the row's compile attaches to the declaration (open_post passes them; the docstrings
    and attributes it attaches land on the dummy theorem first), written before every copy."""
    items = []
    for i, b in enumerate(bodies):
        r = renamed(statement, i)
        if r is None:
            return None
        src = attached + r.rstrip() + " :=" + self_renamed(statement, b, i)
        items.append((K.lean_str(src), K.lean_str(copy_name(statement, i))))
    return (SCREEN.replace("LRAD4MSRCS", ",\n    ".join(a for a, _ in items)).replace("LRAD4MNAMES", ", ".join(b for _, b in items))
            .replace("LRAD4MPRIV", "true" if is_private(statement) else "false"))


def plain_text(statement: str, bodies: list[str], attached: str = "") -> str | None:
    """The fallback screen for a row whose imports have no Lean.Elab (the measuring `#eval` cannot elaborate): every variant as a plain
    renamed theorem followed by `#print axioms` (ok = it depends on no sorryAx and is no axiom itself; no heartbeat reading)."""
    out = [PLAIN_HDR]
    for i, b in enumerate(bodies):
        r = renamed(statement, i)
        if r is None:
            return None
        out.append(attached + r.rstrip() + " :=" + self_renamed(statement, b, i).rstrip()
                   + f"\n\n#print axioms {copy_name(statement, i)}\n\n")
    return "".join(out)


def plain_parse(messages, n: int) -> dict:
    """{i: {"ok", "hb": 0}} from the `#print axioms` lines of plain_text (no line: not ok)."""
    out = {}
    for m in messages or []:
        for mm in AXIOMS_RE.finditer(K.msg_text(m)):
            i = int(mm.group(1))
            if i < n:
                ax = mm.group(2) or ""
                out[i] = {"ok": "sorryAx" not in ax and not re.search(r"(?:^|[\s,.])lraD4M%d(?:$|[\s,])" % i, ax), "hb": 0}
    return out


PARSE_RE = re.compile(r"LRAD4M\t(\d+)\t0\t0\tparse")


def _learn_use(skey: str, mode: str, vs: list[dict], parse_fails: set) -> None:
    """A `use` spelling screened in a measuring file tells whether the row's environment has Mathlib's `use`: it parsed (True) or every
    one failed to parse (False). Per statement, process-wide (use_mode reads it)."""
    if mode != "measure":
        return
    idx = [i for i, v in enumerate(vs, 1) if v.get("menu") == PREFIX and v["rep"].startswith("use ")]
    if not idx:
        return
    with _LOCK:
        if any(i not in parse_fails for i in idx):
            _USE[skey] = True
        elif skey not in _USE:
            _USE[skey] = False


def _screen(statement: str, bodies: list[str], run, versions, attached: str, skey: str) -> tuple[str, dict, str | None, set]:
    """One screening compile of `bodies` (the incumbent first): (mode, {i: reading}, skip reason or None, {i: did not parse})."""
    with _LOCK:
        mode = _MODE.get(skey, "measure")
    rd: dict = {}
    pf: set = set()
    if mode == "measure":
        mt = measure_text(statement, bodies, attached)
        if mt is None:
            return mode, {}, "no measuring text", pf
        r = run(mt, (list(versions or [None]))[0])
        msgs = getattr(r, "messages", None)
        rd = MS.parse(msgs, len(bodies))
        pf = {int(x) for m in msgs or [] for x in PARSE_RE.findall(K.msg_text(m))}
        if not (rd.get(0) or {}).get("ok") and any(NO_ELAB_RE.search(K.msg_text(m)) for m in msgs or []):
            mode = "plain"
            with _LOCK:
                _MODE[skey] = "plain"
    if mode == "plain":
        pt = plain_text(statement, bodies, attached)
        if pt is None:
            return mode, {}, "no screening text", pf
        r = run(pt, (list(versions or [None]))[0])
        rd = plain_parse(getattr(r, "messages", None), len(bodies))
    return mode, rd, None, pf


def query(proof: str, statement: str, run, *, versions=None, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict:
    """The screen (module docstring, "query"). Returns {"ctorsearch_query": {...}, "ctorsearch_query_for": key}; no site: no compile.
    "variants": [{..space fields.., "ok", "hb", "ctl": its file's control reading}], "control": the first file's control reading."""
    st = stats if stats is not None else {}
    log = log or (lambda *a: None)
    ctx = ctx or {}
    t0 = time.time()
    key = K.proof_key(proof)
    body = split_declaration(proof, statement)
    q = {"answered": False, "variants": [], "control": None, "files": 0}
    if body is None or renamed(statement, 0) is None:
        q["skip"] = "not a theorem / lemma statement"
        return {"ctorsearch_query": q, "ctorsearch_query_for": key}
    n = min(MAX_VARIANTS, MS.budget(ctx))
    skey = hashlib.sha256(statement.encode()).hexdigest()[:16]
    cs = ctx.get("compile_s")
    files = MAX_FILES if (isinstance(cs, (int, float)) and 0 < cs <= SECOND_FILE_S) else 1
    seen: set = set()
    mode = "measure"
    for f in range(files):
        vs = ranked(proof, statement, n - 1, exclude=seen)
        if not vs:
            if f == 0:
                q["skip"] = "no site (or every variant failed before)"
            break
        seen.update(v["body"] for v in vs)
        mode, rd, why, parse_fails = _screen(statement, [body] + [v["body"] for v in vs], run, versions, ctx.get("attached") or "", skey)
        if why:
            q["skip"] = why
            break
        q["files"] += 1
        ctl = rd.get(0) or {"ok": False}
        if f == 0:
            q["control"] = ctl
        if not ctl.get("ok"):
            q["skip"] = "the control did not read in the measuring file"
            break
        q["answered"] = True
        _learn_use(skey, mode, vs, parse_fails)
        new = []
        for i, v in enumerate(vs, 1):
            new.append({**{x: v[x] for x in ("op", "body", "note", "lo", "hi", "rep", "dtok", "site", "menu", "form")},
                        **(rd.get(i) or {"ok": False, "hb": None}), "ctl": ctl})
        q["variants"] += new
        with _LOCK:   # only a file whose control read can say a variant failed
            for v in new:
                if not v.get("ok"):
                    _FAILED[_fail_key(statement, body, v)] = True
                    _FAILED[_body_key(statement, v["body"])] = True
        if proposals({"variants": new, "control": ctl}, body, ctx.get("exchange")):
            break   # a later file only when this one proposes nothing
    q["mode"] = mode
    if q["control"] is None:
        q["control"] = {"ok": False}
    if q.get("skip") and not q["answered"]:
        pass
    elif q["answered"]:
        q.pop("skip", None)
    q["seconds"] = round(time.time() - t0, 2)
    nread = sum(1 for v in q["variants"] if v.get("ok"))
    _stats_out(statement, q)
    st["query"] = {"vars": len(q["variants"]), "read": nread, "files": q["files"], "seconds": q["seconds"],
                   **({"skip": q["skip"]} if q.get("skip") else {})}
    if q["files"] or q.get("skip") != "no site (or every variant failed before)":
        log(f"ctorsearch: {len(q['variants'])} variant(s) over {len({v['site'] for v in q['variants']})} site(s) in {q['files']} "
            f"{mode} file(s), {nread} read; control {q['control'].get('hb')} in {q['seconds']} s"
            + (f" ({q['skip']})" if q.get("skip") else ""))
    return {"ctorsearch_query": q, "ctorsearch_query_for": key}


def _stats_out(statement: str, q: dict) -> None:
    """Dev measurement only: with $LRA_CTORSEARCH_STATS set, one JSON line per screened variant (kind, menu item, form, tokens saved,
    read, heartbeats against the control) appended to that file. Never read back by the op."""
    path = os.environ.get("LRA_CTORSEARCH_STATS")
    if not path:
        return
    try:
        sk = hashlib.sha256(statement.encode()).hexdigest()[:12]
        ctl = (q.get("control") or {}).get("hb")
        with _LOCK, open(path, "a") as fh:
            for v in q.get("variants") or []:
                fh.write(json.dumps({"stmt": sk, "mode": q.get("mode"), "op": v["op"], "menu": v["menu"], "form": v["form"],
                                     "dtok": v["dtok"], "ok": bool(v.get("ok")), "hb": v.get("hb"), "ctl_hb": ctl,
                                     "answered": q.get("answered"), "rep": v["rep"][:80]}) + "\n")
    except Exception:  # noqa: BLE001  (stats are best effort)
        pass


def proposals(q: dict, body: str, exchange: float | None) -> list[tuple[float, dict]]:
    out = []
    for v in q.get("variants") or []:
        pr = MS.predicted(v.get("ctl") or q.get("control") or {}, body, v.get("body") or "", v, exchange)
        if pr is not None and pr > 0:
            out.append((pr, v))
    out.sort(key=lambda x: (-x[0], -x[1]["dtok"]))
    return out


def joint_body(body: str, vs: list[dict]) -> tuple[str, list[dict]]:
    """The body with every variant's replacement applied, overlapping spans skipped (earlier = better kept), right to left."""
    keep: list[dict] = []
    for v in vs:
        if all(v["hi"] <= o["lo"] or v["lo"] >= o["hi"] for o in keep):
            keep.append(v)
    nb = body
    for v in sorted(keep, key=lambda v: -v["lo"]):
        nb = nb[:v["lo"]] + v["rep"] + nb[v["hi"]:]
    return nb, keep


def compiled_spans(ctx: dict) -> list[dict]:
    """[{"lo", "hi", "tokens"}] of the spans where this call's screen read a shorter variant (for an op that skips them)."""
    q = (ctx or {}).get("ctorsearch_query") or {}
    return [{"lo": v["lo"], "hi": v["hi"], "tokens": count_tokens(v["rep"])} for v in q.get("variants") or [] if v.get("ok")]


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int | None = None,
               ctx: dict | None = None) -> list[dict]:
    ctx = ctx or {}
    hb = K.head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    q = ctx.get("ctorsearch_query")
    if not (q and ctx.get("ctorsearch_query_for") == K.proof_key(proof) and q.get("answered")):
        return []
    em = K.Emitter(proof, statement, head, body, int(max_per_op) if max_per_op else PROPOSE)
    props = proposals(q, body, exchange if exchange is not None else ctx.get("exchange"))
    if len(props) >= 2:
        nb, keep = joint_body(body, [v for _, v in props])
        if len(keep) >= 2:
            em.add("ctorsearch:joint", nb, f"union of {len(keep)} sites: " + "; ".join(v["note"][:60] for v in keep)[:150])
    for pr, v in props:
        if len(em.out) >= PROPOSE:
            break
        em.add(v["op"], v["body"], f"{v['note']} (screen: {v['hb']} hb vs control {q['control'].get('hb')}, predicted +{pr:.0f})")
    return em.out[:PROPOSE]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="ctorsearch sites and space of one declaration (no compile)")
    ap.add_argument("--file", required=True); ap.add_argument("--statement-file", required=True)
    a = ap.parse_args(argv)
    proof = Path(a.file).read_text(); stmt = Path(a.statement_file).read_text().rstrip("\n")
    body = split_declaration(proof, stmt) or ""
    for s in all_sites(body):
        print(json.dumps({"kind": s["kind"], "line": K.line_of(body, s["lo"]), "text": _short(body[s["lo"]:s["hi"]], 120)},
                         ensure_ascii=False))
    for v in ranked(proof, stmt, MAX_VARIANTS - 1):
        print(json.dumps({"op": v["op"], "dtok": v["dtok"], "note": v["note"]}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
