#!/usr/bin/env python3
"""Op `sonnet_argdrop` (gap lane sonnet, surface / lexer, extension beyond v3): Lean-verified drops of ARGUMENT-level syntax.

sonnet_listdrop deletes list items / lines / parens; this op deletes or shortens what sits inside an application, units found from the
proof text alone (comments and strings masked), each priced exactly with scorer/tokenize.count_tokens and screened by Lean:
  named  `(x := e)` named argument of an application -> deleted (the argument is then inferred by unification)        -(2+tok(e))
  hole   a parenthesised compound argument `f a (g b)` -> `f a _`  (data arguments fixed by the other arguments / the goal)   -(tok-1)
  asc    a type ascription `(e : T)` -> `e` / `(e)`  (Lean's expected type already fixes it)                               -(1+tok(T))
  mcast  `by exact_mod_cast e` in a term position -> `mod_cast e` (-1);  `by exact e` in a term position -> `e` (-2)
  lam    `fun x =>` -> `λx =>` (the lexer reads `λx` as one token; Lean reads it as `λ x`)                                 -1
  use    `refine ⟨a, b, ?_⟩` -> `use a, b`;  `refine ⟨?_, ?_⟩` -> `constructor`
  at     `@f _ _ x` -> `f x` (the leading holes and the `@`)
  join   two consecutive `intro` / `rw [..]` / `simp only [..]` lines (same indentation, same suffix) -> one line
Nothing here is trusted: query() compiles the proof's own variants in one-file measured batches (harness/post/d4_measure.py), keeps the units
whose copy compiles with no error and no sorry and whose predicted score rises, then tries the cumulative union; the caller's gate
(harness/open_post.py) still reads every candidate on every pin. No table, no row name, no proof text."""

# provenance: research lane gaplane-sonnet (worktree lra-gl-sonnet), commit e0308bc, ported into open-post-v5-lanes (2026-11-04) unchanged
from __future__ import annotations

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from harness.post import sonnet_listdrop as LD  # noqa: E402
from scorer.tokenize import count_tokens  # noqa: E402

FAMILY = "sonnet_argdrop"
Unit = LD.Unit


class Unit2(Unit):
    """A unit made of several edits [(start, end, text)] (a have-inline: the `have` statement goes, its use is replaced); start / end span them."""
    __slots__ = ("edits",)

    def __init__(self, edits, kind, note):
        super().__init__(min(e[0] for e in edits), max(e[1] for e in edits), "", kind, note)
        self.edits = edits


def _apply(body: str, us):
    us = sorted(us, key=lambda u: u.start)
    for x, y in zip(us, us[1:]):
        if y.start < x.end:
            return None
    edits = []
    for u in us:
        edits.extend(getattr(u, "edits", None) or [(u.start, u.end, u.text)])
    edits.sort()
    out, last = [], 0
    for a, b, t in edits:
        if a < last:
            return None
        out.append(body[last:a]); out.append(t); last = b
    out.append(body[last:])
    return "".join(out)
MAX_UNITS = 45
CONFIG_NAMES = frozenset({"config", "disch", "discharger", "occs", "maxDischargeDepth", "zeta", "beta", "eta", "iota", "proj", "decide",
                          "arith", "autoUnfold", "dsimp", "failIfUnchanged", "ground", "unfoldPartialApp", "zetaDelta", "singlePass",
                          "contextual", "memoize", "maxSteps", "maxDischargeDepth", "transparency", "offsetCnstrs", "useCongrLemmas"})
BINDER_KW = ("fun", "λ", "∀", "∃", "∃!", "∑", "∏", "intro", "intros", "rintro", "obtain", "rcases", "have", "let", "set", "show", "from",
             "with", "at", "using", "then", "else", "case", "next", "theorem", "lemma", "match", "generalizing", "in", "to", "by_cases", "calc")
_NAMED = re.compile(r"\s*([^\W\d][\w'.₀-₉]*)\s*:=\s*\S")
_LASTWORD = re.compile(r"([^\s()\[\]{}⟨⟩,:;]+)\s*$")
_ATOM = re.compile(r"[^\W\d][\w'.]*|\d+(?:\.\d+)?|↑[^\W\d][\w'.]*|_")
_IDLIST = re.compile(r"[^\W\d][\w']*(?:\s+[^\W\d][\w']*)*")
_FUN = re.compile(r"(?<![\w.'])fun([ \t]+)(?=[^\W]|_)")
_MCAST = re.compile(r"(?<![\w.'])by exact_mod_cast(?=\s)")
_BYEXACT = re.compile(r"(?<![\w.'])by exact(?=\s)")
_AT = re.compile(r"(?<![\w.'@])@([^\W\d][\w'.]*)((?:[ \t]+_)+)(?![\w'.])")
_USE = re.compile(r"(?m)^([ \t]*(?:·[ \t]*)?)refine ⟨(.+)⟩[ \t]*$")
_JOIN_HEADS = ("intro", "intros", "rintro", "rw", "rewrite", "simp only", "simp_rw", "rwa", "unfold", "norm_num [", "field_simp [")


def _before_ok(before: str) -> bool:
    """The text before an argument group (from the line start): the group follows a term (identifier, closing bracket, `?`) after a blank."""
    return bool(before) and before[-1] in " \t" and bool(re.search(r"[\w'.)\]⟩?]\s+$", before))


def _binder_ctx(before: str) -> bool:
    """Is the group a binder (`fun (x : T) =>`, `∀ (x y : T)`, `intro (x : T)`, `have (h : P) :`): the last word before it is a binder keyword
    or the line so far is only binders after one."""
    s = before.rstrip()
    m = _LASTWORD.search(s)
    if m and m.group(1) in BINDER_KW:
        return True
    # `fun (a : A) (b : B)`: previous binder groups
    j = len(s)
    while j > 0 and s[j - 1] == ")":
        d = 0
        k = j - 1
        while k >= 0:
            if s[k] == ")":
                d += 1
            elif s[k] == "(":
                d -= 1
                if d == 0:
                    break
            k -= 1
        if k < 0:
            break
        s = s[:k].rstrip()
        j = len(s)
        m = _LASTWORD.search(s)
        if m and m.group(1) in BINDER_KW:
            return True
    return False


def kinds_key(u):
    return (u.kind, tuple(getattr(u, "edits", None) or ()))


HAVE_RE = re.compile(r"^([ \t]*)have[ \t]+(?:([^\W\d][\w']*)[ \t]*)?(?::[ \t]*(\S.*?)[ \t]*)?:=[ \t]*(.*)$")
IMPLICIT_USERS = re.compile(r"(?<![\w.'])(omega|linarith|nlinarith|simp_all|assumption|aesop|grind|tauto|positivity|decide|norm_num|simp|cc|polyrith|bound|exact_mod_cast)(?![\w'])")
ATOM_RE = re.compile(r"[^\W\d][\w'.]*")


def _hinl_units(body: str, mask, pairs, lines, offs):
    out = []
    n = len(body)
    for i, ln in enumerate(lines):
        m = HAVE_RE.match(ln)
        if not m or any(mask[offs[i]:offs[i] + len(ln)]):
            continue
        ind = len(m.group(1))
        name = m.group(2) or "this"
        if m.group(2) is None and not ln.lstrip().startswith("have :") and not ln.lstrip().startswith("have :="):
            pass
        ty, rest = m.group(3), m.group(4).rstrip()
        j = i + 1
        while j < len(lines) and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip()) > ind):
            j += 1
        # scope: the lines after the statement while indent >= ind (blank lines inside)
        k = j
        while k < len(lines) and (not lines[k].strip() or len(lines[k]) - len(lines[k].lstrip()) >= ind):
            k += 1
        if k == j:
            continue
        a0, a1 = offs[j], (offs[k] if k < len(lines) else n)
        scope = body[a0:a1]
        uses = [u for u in re.finditer(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'])", scope) if not any(mask[a0 + u.start():a0 + u.end()])]
        if len(uses) != 1:
            continue
        u = uses[0]
        us, ue = a0 + u.start(), a0 + u.end()
        pre = body[max(0, us - 40):us]
        if re.search(r"(\bat|\bwith|\bintro|\bintros|\brintro|\bgeneralizing|\bclear|\bobtain\s+\S+\s*:)\s+(?:[^\n]*\s)?$", body[body.rfind("\n", 0, us) + 1:us]) or re.search(r"(\bfun|λ|∀|∃)[^=\n]*$", body[body.rfind("\n", 0, us) + 1:us]):
            continue
        if re.match(r"\s*(\.|:)", body[ue:ue + 3]) and False:
            continue
        if name == "this" and re.search(r"\b(have|obtain|rcases|cases|by_cases|set|let|show)\b[^\n]*\bthis\b", scope):
            pass
        # the proof text of the have
        first = rest
        block = [lines[x] for x in range(i + 1, j)]
        while block and not block[-1].strip():
            block.pop()
        uls = body.rfind("\n", 0, us) + 1
        uind = len(body[uls:]) - len(body[uls:].lstrip())
        prefix_text = body[uls:us]
        bare_ok = bool(re.search(r"(?:^|\s)(exact|apply|refine|simpa[^\n]*using|using|rcases|obtain\b[^\n]*:=|:=|\$|<\||from|exact\?|calc)\s+$", prefix_text)) and body[ue:ue + 1] in ("", "\n", " ", ")", "]", ",", "⟩")\
            and not re.match(r"[ \t]*[.\[]", body[ue:ue + 2])
        list_ok = bool(re.search(r"(?:\[|,\s|←\s|↓\s)$", prefix_text)) and body[ue:ue + 1] in ("]", ",")
        # build P
        if first.startswith("by") and re.match(r"by(?![\w'])", first):
            kind = "by"
            tac = first[2:].strip()
            if not block:
                if not tac:
                    continue
                core = "by " + tac
                multi = False
            else:
                tl = []
                base = min((len(b) - len(b.lstrip()) for b in block if b.strip()), default=ind + 2)
                for b in block:
                    tl.append(" " * (uind + 2) + b[base:] if b.strip() else "")
                core = ("by " + tac + "\n" if tac else "by\n") + "\n".join(tl)
                multi = True
            variants = [("(" + core + ")", "")]
            if ty:
                variants.append(("(show " + ty + " " + core + ")", "T"))
            if bare_ok or list_ok:   # no parentheses needed: `rw [← show T by tac]`, `exact show T by tac`
                variants = ([("show " + ty + " " + core, "T")] if ty else []) + variants
        else:
            kind = "term"
            if not first and not block:
                continue
            parts = [first] if first else []
            if block:
                base = min((len(b) - len(b.lstrip()) for b in block if b.strip()), default=0)
                if len(block) == 1 and not first:
                    parts = [block[0].strip()]
                else:
                    for b in block:
                        parts.append(" " * (uind + 2) + b[base:] if b.strip() else "")
            core = "\n".join(parts) if len(parts) > 1 or block else parts[0]
            if "\n" in core and not first:
                pass
            plain = core if (bare_ok and ATOM_RE.fullmatch(core) or bare_ok and "\n" not in core and not re.match(r"(fun|λ|show|by)\b", core)) else "(" + core + ")"
            if ATOM_RE.fullmatch(core):
                plain = core
            variants = [(plain, "")]
            if ty:
                variants.append(("(" + core + " : " + ty + ")", "T"))
        hs, he = offs[i], (offs[j] if j < len(lines) else n)
        if ty and kind == "by" and False:
            pass
        for repl, tag in variants:
            out.append(Unit2([(hs, he, ""), (us, ue, repl)], "hinl", f"inline single-use have {name}{' (typed)' if tag else ''}"))
    return out


def _units(body: str, statement: str = "") -> list[Unit]:
    mask = _mask(body)
    pairs = _pairs(body, mask)
    units: list[Unit] = []
    n = len(body)

    def depth0_colon(o, c):
        for i in range(o + 1, c):
            if mask[i] or body[i] != ":" or body.startswith(":=", i):
                continue
            if body[i - 1:i + 1] == "::" or body[i:i + 2] == "::":
                continue
            if all(not (o2 < i < c2) for o2, c2 in pairs.items() if o < o2 and c2 < c):
                return i
        return -1

    for o, c in sorted(pairs.items()):
        if body[o] != "(" or mask[o] or mask[c]:
            continue
        inner = body[o + 1:c]
        ls = body.rfind("\n", 0, o) + 1
        le = body.find("\n", c)
        le = n if le < 0 else le
        before, after = body[ls:o], body[c + 1:le]
        m = _NAMED.match(inner)
        if m and m.group(1) not in CONFIG_NAMES:
            if re.search(r"[\w'.)\]⟩?]\s*$", before) or not before.strip():
                s = o
                if before.strip():
                    while s > ls and body[s - 1] in " \t":
                        s -= 1
                units.append(Unit(s, c + 1, "", "named", f"named arg ({inner[:30]!r})"))
            continue
        stripped = inner.strip()
        if stripped and not stripped.startswith(("by ", "by\n", "show ", "fun ", "λ", "·")) and not after.startswith(("."," ."))\
                and _before_ok(before) and not _binder_ctx(before) and depth0_colon(o, c) < 0 and count_tokens(inner) >= 2:
            units.append(Unit(o, c + 1, "_", "hole", f"hole for ({stripped[:30]!r})"))
        i = depth0_colon(o, c)
        if i > 0 and not _binder_ctx(before) and not after.startswith("."):
            e = body[o + 1:i].strip()
            if e and not (_IDLIST.fullmatch(e) and " " in e):
                if _ATOM.fullmatch(e) and not re.match(r"[\w'.]", after[:1]) and not before.endswith(("↑", "(", "⟨")):
                    units.append(Unit(o, c + 1, e, "asc", f"ascription drop ({stripped[:30]!r})"))
                else:
                    s0 = i
                    while s0 > o + 1 and body[s0 - 1] in " \t":
                        s0 -= 1
                    units.append(Unit(s0, c, "", "asc", f"ascription drop ({stripped[:30]!r})"))
    # -- by exact_mod_cast / by exact in term positions
    for rx, txt, kind in ((_MCAST, "mod_cast", "mcast"), (_BYEXACT, "", "bexact")):
        for m in rx.finditer(body):
            if mask[m.start()]:
                continue
            pre = body[:m.start()].rstrip()
            if not (pre.endswith(("(", "$", "<|", ",", "⟨", ":=", "=>")) and not pre.endswith("by")):
                continue
            end = m.end()
            while end < n and body[end] in " \t" and txt == "":
                end += 1
            units.append(Unit(m.start(), end, txt, kind, f"{m.group(0)} in a term"))
    # -- fun x => -> λx =>
    for m in _FUN.finditer(body):
        if mask[m.start()]:
            continue
        units.append(Unit(m.start(), m.end(), "λ", "lam", "fun x -> λx"))
    # -- @f _ _ x -> f x
    for m in _AT.finditer(body):
        if mask[m.start()]:
            continue
        units.append(Unit(m.start(), m.end(), m.group(1), "at", f"@{m.group(1)} holes"))
    # -- refine ⟨a, b, ?_⟩ -> use a, b ; refine ⟨?_, ?_⟩ -> constructor
    for m in _USE.finditer(body):
        if mask[m.start(2)]:
            continue
        inner = m.group(2)
        items = LD._split_items(body, mask, m.start(2), m.end(2))
        if len(items) >= 2 and body[items[-1][0]:items[-1][1]] == "?_" and "?_" not in body[m.start(2):items[-1][0]]:
            units.append(Unit(m.end(1), m.end(), "use " + ", ".join(body[a:b] for a, b in items[:-1]), "use", "refine ⟨.., ?_⟩ -> use"))
        elif len(items) == 2 and all(body[a:b] == "?_" for a, b in items):
            units.append(Unit(m.end(1), m.end(), "constructor", "use", "refine ⟨?_, ?_⟩ -> constructor"))
    # -- (atom) -> atom ; show T from by tac -> show T by tac ; fun x => F x -> F ; f a $ tail -> f a _ ; (g b) , -> $
    for o, c in sorted(pairs.items()):
        if body[o] != "(" or mask[o] or mask[c]:
            continue
        inner = body[o + 1:c]
        if re.fullmatch(r"[^\W\d][\w'.]*", inner) and body[max(0, o - 1):o] not in ("@", "↑") and not re.match(r"[\w'.]", body[c + 1:c + 2]):
            units.append(Unit(o, c + 1, inner, "patom", f"redundant parens around {inner}"))
        mf = re.fullmatch(r"(?:fun|λ)[ \t]*([^\W\d][\w']*)[ \t]*(?:=>|↦)[ \t]*([^\W\d][\w'.]*)[ \t]+([^\W\d][\w']*)", inner)
        if mf and mf.group(1) == mf.group(3) and mf.group(1) not in mf.group(2).split("."):
            units.append(Unit(o, c + 1, mf.group(2), "eta", f"eta ({inner[:30]})"))
    # -- a trailing `(fun ..)` / `(by ..)` argument: the parens go (-2); a trailing `(f x)` before `,` / `⟩` / `}` -> `$ f x` (-1)
    for o, c in sorted(pairs.items()):
        if body[o] != "(" or mask[o] or mask[c]:
            continue
        inner = body[o + 1:c]
        ls = body.rfind("\n", 0, o) + 1
        le = body.find("\n", c)
        le = n if le < 0 else le
        before, after = body[ls:o], body[c + 1:le]
        if not (before.endswith(" ") and re.search(r"[\w'.)\]⟩?]\s+$", before)) or _binder_ctx(before):
            continue
        if not (not after.strip() or re.match(r"\s*(?:[)\]⟩},]|<;>|;)", after)):
            continue
        hd = re.match(r"(fun|λ|by)(?![\w'])", inner.lstrip())
        if hd and not inner.lstrip().startswith("fun ·"):
            units.append(Unit(o, c + 1, inner.strip(), "ptail", f"drop parens of trailing ({hd.group(1)} ..)"))
        elif not hd and " " in inner.strip() and re.match(r"\s*[,⟩}]", after) and depth0_colon(o, c) < 0 \
                and not re.search(r"[,|]", re.sub(r"\([^()]*\)|\[[^\[\]]*\]|⟨[^⟨⟩]*⟩", "", inner)) \
                and not inner.lstrip().startswith(("·", "show", "have", "calc")):
            units.append(Unit(o, c + 1, "$ " + inner.strip(), "dollar2", "trailing parens before , -> $"))
    for m in re.finditer(r"(?<![\w.'])from by(?![\w'])", body):
        if not mask[m.start()]:
            units.append(Unit(m.start(), m.end(), "by", "showfrom", "from by -> by"))
    for m in re.finditer(r"[ \t]*\$[ \t]+", body):
        a = m.end()
        if mask[m.start()] or re.match(r"(by|fun|λ|show|·)(?![\w'])", body[a:a + 5]):
            continue
        ls = body.rfind("\n", 0, m.start()) + 1
        ind0 = len(body[ls:]) - len(body[ls:].lstrip())
        i = a
        while i < n:
            ch = body[i]
            if mask[i]:
                i += 1; continue
            if ch in "([{⟨" and i in pairs:
                i = pairs[i] + 1; continue
            if ch in ")]}⟩,;" or body.startswith("<;>", i) or body.startswith("$", i) and False:
                break
            if ch == "\n":
                j = i + 1
                while j < n and body[j] in " \t":
                    j += 1
                if j >= n or body[j] == "\n" or j - (i + 1) <= ind0:
                    break
            i += 1
        tail = body[a:i].rstrip()
        if tail and "$" not in tail and count_tokens(tail) >= 2:
            units.append(Unit(m.start(), a + len(tail), " _", "dtail", f"$-tail hole ({tail[:30]!r})"))
    # -- join consecutive lines
    lines = body.split("\n")
    offs, p = [], 0
    for ln in lines:
        offs.append(p); p += len(ln) + 1
    units.extend(_hinl_units(body, mask, pairs, lines, offs))
    for i in range(len(lines) - 1):
        a, b = lines[i], lines[i + 1]
        if not a.strip() or not b.strip() or any(mask[offs[i]:offs[i] + len(a)]) or any(mask[offs[i + 1]:offs[i + 1] + len(b)]):
            continue
        ia, ib = len(a) - len(a.lstrip()), len(b) - len(b.lstrip())
        if ia != ib:
            continue
        ta, tb = a.strip(), b.strip()
        mi = re.fullmatch(r"(intro|intros)((?:\s+[^\W\d][\w']*|\s+_)+)", ta)
        mj = re.fullmatch(r"(intro|intros)((?:\s+[^\W\d][\w']*|\s+_)+)", tb)
        if mi and mj and mi.group(1) == mj.group(1) == "intro":
            units.append(Unit(offs[i] + len(a), offs[i + 1] + ib + len("intro"), "", "join", "intro lines"))
            continue
        mw = re.fullmatch(r"(rw|rewrite)(\s*\[[^\[\]]*\])\s+at\s+([^\W\d][\w']*)", ta)
        if mw and re.fullmatch(r"exact\s+" + re.escape(mw.group(3)) + r"|assumption", tb):
            units.append(Unit(offs[i] + ia, offs[i + 1] + len(b), "rwa" + mw.group(2) + " at " + mw.group(3), "rwa", "rw .. at h; exact h -> rwa"))
            continue
        ms = re.fullmatch(r"(simp(?: only)?|norm_num|simp_all)((?:\s*\[[^\[\]]*\])?)\s+at\s+([^\W\d][\w']*)", ta)
        if ms and ms.group(1) != "simp_all" and re.fullmatch(r"exact\s+" + re.escape(ms.group(3)), tb):
            head = {"simp": "simpa", "simp only": "simpa only", "norm_num": "simpa"}[ms.group(1)]
            units.append(Unit(offs[i] + ia, offs[i + 1] + len(b), head + ms.group(2) + " using " + ms.group(3), "rwa", "simp .. at h; exact h -> simpa using h"))
            continue
        mi = re.fullmatch(r"(rw|rewrite|simp only|simp_rw|rwa|unfold)\s*\[([^\[\]]*)\]((?:\s+at\s+\S+(?:\s+\S+)*)?)", ta)
        mj = re.fullmatch(r"(rw|rewrite|simp only|simp_rw|rwa|unfold)\s*\[([^\[\]]*)\]((?:\s+at\s+\S+(?:\s+\S+)*)?)", tb)
        if mi and mj and mi.group(1) == mj.group(1) and mi.group(3) == mj.group(3):
            # a[..] at x \n a[..] at x  ->  a[.., ..] at x : drop `]` + (` at x`) + newline + head + ` [` ... replace by `,`
            k1 = offs[i] + ia + mi.group(0).index("[") + 0
            tail_start = offs[i] + ia + len(ta) - len(mi.group(3)) - 1  # position of the `]` of the first line
            j2 = offs[i + 1] + ib + tb.index("[") + 1
            units.append(Unit(tail_start, j2, ", ", "join", f"{mi.group(1)} lines"))
    # tokens saved (exact, in context)
    t0 = count_tokens(body)
    seen, out = set(), []
    for u in units:
        nb = _apply(body, [u])
        u.dtok = t0 - count_tokens(nb) if nb is not None else 0
        key = (u.start, u.end, u.text, kinds_key(u))
        if u.dtok <= 0 or key in seen:
            continue
        seen.add(key); out.append(u)
    return out


SURE = ("lam", "rwa", "mcast", "bexact", "patom", "showfrom", "join", "eta", "use", "at")   # high-probability kinds first: they must not be crowded out by long shots


def _ranked(units):
    return sorted(units, key=lambda u: (0 if u.kind in SURE else 1, -u.dtok, u.start))


_FAILED: set = set()
_LAST: dict = {}


def _sync_cache(statement: str, body: str) -> None:
    k = statement.strip()
    prev = _LAST.get(k)
    if prev is None or body not in prev:
        for f in [f for f in _FAILED if f[0] == k]:
            _FAILED.discard(f)


def has_sites(proof: str, statement: str) -> bool:
    hb = K.head_body(proof, statement)
    if hb is None or MS.renamed(statement, 0) is None:
        return False
    try:
        return bool(_units(hb[1], statement))
    except Exception:  # noqa: BLE001
        return False


def query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None, units_fn=None, family=None, max_units=None):
    """Screen the units, then their cumulative union (module docstring). Returns {"variants": [{"body", "pred", "note"}]} or None."""
    try:
        hb = K.head_body(proof, statement)
        if hb is None or MS.renamed(statement, 0) is None:
            return None
        head, body = hb
        exchange = (ctx or {}).get("exchange")
        n = MS.budget(ctx)
        if n < 3:
            return None
        _sync_cache(statement, body)
        _LAST[statement.strip()] = []
        units = [u for u in _ranked((units_fn or _units)(body, statement)) if LD._ukey(statement, body, u) not in _FAILED]
        if not units:
            return {"variants": []}
        units = units[:max(1, min(max_units or MAX_UNITS, (n - 1) * 3))]
        good = []
        mode = "eval"
        for i in range(0, len(units), n - 1):
            chunk = units[i:i + n - 1]
            bodies = [_apply(body, [u]) for u in chunk]
            rd, mode = LD._read(statement, [body] + bodies, run, mode)
            ctl = rd.get(0) or {"ok": False}
            if not ctl.get("ok"):
                if log:
                    log(f"{FAMILY}: control did not read ({mode})")
                return {"variants": []}
            for k, (u, b) in enumerate(zip(chunk, bodies), 1):
                if not (rd.get(k) or {}).get("ok") and k in rd:
                    _FAILED.add(LD._ukey(statement, body, u))
                pr = LD._pred(ctl, body, b, rd.get(k) or {"ok": False}, exchange)
                if pr is not None and pr > 0:
                    good.append((pr, u))
        if stats is not None:
            stats[family or FAMILY] = {"units": len(units), "ok": len(good)}
        if not good:
            return {"variants": []}
        good.sort(key=lambda x: (-x[0], x[1].start))
        variants = [{"body": _apply(body, [u]), "pred": pr, "note": f"single {u.kind}: {u.note}"} for pr, u in good[:3]]
        if len(good) >= 2:
            chosen, bodies, notes = [], [], []
            for pr, u in good:
                if _apply(body, chosen + [u]) is None:
                    continue
                chosen = chosen + [u]
                if len(chosen) >= 2:
                    bodies.append(_apply(body, chosen)); notes.append(f"union of {len(chosen)} ({LD._fmt(chosen)})")
            if len(bodies) > n - 1:
                keep = sorted(set(list(range(len(bodies)))[-(n - 1) // 2:] + list(range(0, len(bodies), max(1, len(bodies) // ((n - 1) // 2 or 1))))))
                keep = keep[:n - 1]
                bodies = [bodies[j] for j in keep]; notes = [notes[j] for j in keep]
            if bodies:
                rd, mode = LD._read(statement, [body] + bodies, run, mode)
                ctl = rd.get(0) or {"ok": False}
                if ctl.get("ok"):
                    for k, (b, nt) in enumerate(zip(bodies, notes), 1):
                        pr = LD._pred(ctl, body, b, rd.get(k) or {"ok": False}, exchange)
                        if pr is not None and pr > 0:
                            variants.append({"body": b, "pred": pr, "note": nt})
        variants.sort(key=lambda v: -v["pred"])
        _LAST[statement.strip()] = [v["body"] for v in variants]
        return {"variants": variants}
    except Exception as e:  # noqa: BLE001
        if e.__class__.__name__ == "_Stop":
            raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:160]}")
        return None


def candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None, units_fn=None, family=None):
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return []
        head, body = hb
        em = K.Emitter(proof, statement, head, body, int(max_per_op or 8))
        var = (ctx or {}).get("variants")
        if var is not None:
            for v in var:
                em.add(f"{family or FAMILY}:verified", v["body"], v["note"], extra={"pred": v["pred"]})
            return em.out
        for u in _ranked((units_fn or _units)(body, statement))[:em.cap]:
            b = _apply(body, [u])
            if b is not None:
                em.add(f"{family or FAMILY}:raw", b, u.note)
        return em.out
    except Exception:  # noqa: BLE001
        return []
