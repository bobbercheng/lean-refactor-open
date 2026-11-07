#!/usr/bin/env python3
"""Op "v4_patelide" of the open post-step (post-step v4, 2026-11-04): a flat destructuring pattern elided, the names taken from Lean.

Mechanism: under `unhygienic`, `rcases e` with no pattern destructures `e` exactly one level and names the parts itself, with the
binder names of the constructor (an `∃` gives `w` / `h`, a conjunction `left` / `right`, a structure its field names), suffixed `_1`,
`_2`, .. when the name is taken (Lean's LocalContext.getUnusedName). So a step that only spells those names,

  site      `obtain ⟨n1, .., nk⟩ := e` | `have ⟨n1, .., nk⟩ := e` | `rcases e with ⟨n1, .., nk⟩` (k >= 2) | `cases' e with n1 .. nk`
            on a line of its own (optionally after a `·` bullet), each n a name, `_` or `-` (no `rfl`, `|`, `@`, nesting or type
            ascription); e on the same line (bracket-balanced, no `;`, `<;>`, `by`, `with` or top-level comma), or, after a bare
            `:=`, on the following deeper lines; the next line starts a new tactic,

becomes `rcases e` (`unhygienic rcases e` when the proof has no top `unhygienic`; a multi-line source as `rcases (first line ...)`)
and every later use of n_i in the site's block becomes Lean's name for that part. A `have` whose source is a bare name used later keeps
it: rcases clears a local it destructures (`have` does not), so that source is written `id s`. A pattern with more names than the first
level has parts is nested (anonymous-constructor patterns nest to the right): its last part is destructured again, `rcases e; rcases t`
(chain, up to MAX_CHAIN levels), or, when that part is a conjunction whose parts are used as terms only, read as projections `t.1`,
`t.2.1`, .. (no further level). A part Lean names with a keyword token (`left`, `right`, `trans`, ..) is written `«left»` after `at`.

The names are never guessed (probe): one compile file holds the proof with a `trace_state` after every site (the names given) and, per
site, the proof with that site rewritten and a `trace_state` after it (Lean's names; t4ind's quiet() stops the rest of that block, whose
later uses still carry the old names); deeper levels take one more file per level (CHAIN_ROUNDS). The two contexts are aligned position
by position: the same goal count; in the main goal the same hypotheses except the parts at the end (a `have` site's cleared source and a
pattern-shadowed `n✝` aside), the given names (`✝` for `_`) at those positions and plain identifiers on Lean's side; the same mapping for
every run of a site that runs several times. Pure checks on the rewrite: Lean's name spelled in the block before the last use of the
given name is a later binder and goes to a fresh name first (alpha; dropped when it is also a named argument, or a keyword spelled
outside a tactic position); a given name used as a named argument or field (`(n := ..)`) drops the site; inside an enclosing
`unhygienic` block no base of a new name may be spelled at all (the block's later tactics name hypotheses with getUnusedName, so a new
name would shift theirs: MEASURED).

Candidates (screened by harness/post/opus_screen.py's one-file screen when there are two or more, then the post-step's gate):
  joint / jointnp   every site with an alignment, in line order, with (joint) or without (jointnp) the projection forms; a later
             site's names predicted from the earlier ones (getUnusedName's rule on the probed context; a chain or projection site whose
             names could collide is left out)
  ..top      (no top `unhygienic`, no `rename_i` / named `case` / `next` anywhere, no `✝` hypothesis that could collide) the joint form
             with one top `unhygienic` instead of one per line
  single / proj   each site alone (each alignment), most tokens saved first
  When no joint form passes the screen but two or more singles do, the joint of exactly those (one more screen file) comes first.
Writes Lean core syntax only (`unhygienic`, `rcases`, `id`, `trace_state`, `«»`, `.1` / `.2`); no table, no row name, no lemma: every
other token of a candidate is the proof's own or a name Lean printed for that proof."""
from __future__ import annotations

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "v4_patelide"
MAX_SITES = 12          # sites probed per proof (line order)
PROBE_FILES = 4         # probe files per query (t4ind.make_compile_batch's file budget, shared by the rounds)
CHAIN_ROUNDS = 3        # extra probe rounds for nested patterns (one more level per round)
MAX_CHAIN = 3           # deeper levels per site at most
MAX_PER_OP = 10
TRACE = "trace_state"
NAME = r"[^\W\d][\w'!?₀-₉ᵢ-ᵪ]*"
NAME_RE = re.compile(NAME)
PNAME_RE = re.compile(rf"(?:{NAME}|_|-)")
LEAD = r"(?P<lead>[ \t]*(?:[·.][ \t]+)?)"
FLAT = r"[^⟨⟩()\[\]{}|:=@]*"
SITE_RES = (
    ("obtain", re.compile(rf"^{LEAD}(?P<kw>obtain|have)[ \t]+⟨(?P<pat>{FLAT})⟩[ \t]*:=[ \t]*(?P<src>\S.*?)[ \t]*$")),
    ("obtainml", re.compile(rf"^{LEAD}(?P<kw>obtain|have)[ \t]+⟨(?P<pat>{FLAT})⟩[ \t]*:=(?P<src>)[ \t]*$")),
    ("rcases", re.compile(rf"^{LEAD}(?P<kw>rcases)[ \t]+(?P<src>\S.*?)[ \t]+with[ \t]+⟨(?P<pat>{FLAT})⟩[ \t]*$")),
    ("casesp", re.compile(rf"^{LEAD}(?P<kw>cases')[ \t]+(?P<src>\S.*?)[ \t]+with(?P<pat>(?:[ \t]+(?:{NAME}|_))+)[ \t]*$")),
)
CONT_START = ("<;>", "|", ")", "]", "}", "⟩", ",", ":=", "=>", "..")
BAL_O, BAL_C = "([{⟨⦃", ")]}⟩⦄"
RENAME_WORDS = re.compile(r"(?m)^\s*(rename_i\b|next\s+[^=\s][^=]*=>|case\s+\S+\s+[^=|]+=>)|<;>\s*rename_i\b")
# Lean / Mathlib keyword tokens that a constructor may still use as a field name (And: left / right; Equivalence: refl / symm / trans):
# a hypothesis so named is referred to as `«name»`: in a location always (MEASURED on a library row: `at left` -> "unexpected token
# 'left'"), and wherever it stands bare in a second variant (MEASURED in a Mathlib row: "unexpected token 'left'; expected term"; a
# core-only row took the bare name in terms, so both variants go to the screen)
KEYWORDS = frozenset((
    "left right at from fun have show by then else do in with only using generalizing if let match calc where end open "
    "exists intro intros constructor exact apply refine rfl simp omega decide trivial exfalso contradiction assumption sorry admit "
    "ring linarith norm_num positivity aesop tauto use obtain rcases rintro cases induction next case first try repeat iterate skip "
    "done stop unhygienic rw rewrite symm trans refl congr ext funext subst clear revert specialize suffices change unfold split "
    "by_cases by_contra push_neg field_simp nlinarith gcongr bound grind set generalize exists_prop infer_instance").split())
CORE_NAMES = frozenset("w h left right fst snd val property mp mpr".split())   # Lean core's ∃ / ∧ / × / Subtype / ↔ binder names
TACTIC_POS = re.compile(r"(^|\n)[ \t]*(?:[·.][ \t]+)?$|(;|<;>|=>|\bthen|\belse|\btry|\ball_goals|\bany_goals|\(|\{)[ \t]*$")
AT_RE = re.compile(r"(?<![\w'.])at(?![\w'!?])")
WORD = r"(?<![\w'!?₀-₉.])"
WEND = r"(?![\w'!?₀-₉])"


def _ident_char(ch: str) -> bool:
    """A character that continues an identifier (Lean: letters except λ / Π / Σ, digits, subscripts, `_ ' ! ?`): `λh` binds h."""
    return (ch.isalnum() or ch in "_'!?") and ch not in "λΠΣ"


def occurrences(name: str, text: str) -> list[int]:
    """Offsets where `name` occurs in `text` as an identifier (a whole word, also as the head of `name.field`), not as `x.name`."""
    out: list[int] = []
    if not name or name == "_":
        return out
    i = 0
    while True:
        j = text.find(name, i)
        if j < 0:
            return out
        before = text[j - 1] if j > 0 else " "
        after = text[j + len(name)] if j + len(name) < len(text) else " "
        if not _ident_char(before) and before != "." and not _ident_char(after):
            out.append(j)
        i = j + 1


def uses(name: str, text: str) -> bool:
    return bool(occurrences(name, text))


def rename_words(lines: list[str], mp: dict, quote=frozenset(), quote_all: bool = False) -> list[str]:
    """Whole-identifier renames (never after `.` or inside a longer identifier; `n.1` -> `w.1`). A new name in `quote` (a keyword
    token) is written `«name»` in a location (after `at` on its line), everywhere it stands bare with quote_all (a dotted `name.f`
    lexes as one identifier and stays plain)."""
    mp = {k: v for k, v in mp.items() if k != v}
    if not mp:
        return list(lines)
    pat = re.compile("|".join(re.escape(k) for k in sorted(mp, key=len, reverse=True)))
    out = []
    for ln in lines:
        res, i = [], 0
        for m in pat.finditer(ln):
            a, b = m.start(), m.end()
            before = ln[a - 1] if a > 0 else " "
            after = ln[b] if b < len(ln) else " "
            if _ident_char(before) or before == "." or _ident_char(after):
                continue
            v = mp[m.group(0)]
            if v in quote and after != "." and (quote_all or AT_RE.search(ln[:a])):
                v = f"«{v}»"
            res.append(ln[i:a]); res.append(v); i = b
        res.append(ln[i:])
        out.append("".join(res))
    return out


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def _blank(line: str) -> bool:
    return not line.strip()


def _balanced(s: str) -> bool:
    d = 0
    for ch in s:
        if ch in BAL_O:
            d += 1
        elif ch in BAL_C:
            d -= 1
            if d < 0:
                return False
    return d == 0


def _top_comma(s: str) -> bool:
    d = 0
    for ch in s:
        if ch in BAL_O:
            d += 1
        elif ch in BAL_C:
            d -= 1
        elif ch == "," and d == 0:
            return True
    return False


def _src_ok(src: str) -> bool:
    if not src or not _balanced(src) or _top_comma(src):
        return False
    if any(x in src for x in (";", "<;>", "--", "/-", "\"")):
        return False
    if re.search(WORD + r"(by|with|fun|λ|match|do|at|using)" + WEND, src):
        return False
    return True


def has_top(lines: list[str]) -> bool:
    """The proof's tactic block starts with `unhygienic` (`by unhygienic` or a first line `unhygienic`)."""
    if not lines:
        return False
    if re.match(r"\s*by\s+unhygienic\s*$", lines[0]):
        return True
    if lines[0].strip() != "by":
        return False
    first = next((ln for ln in lines[1:] if not _blank(ln)), "")
    return first.strip() == "unhygienic"


def scope_end(lines: list[str], i: int, col: int) -> int:
    """End (exclusive) of the block after line i: the following lines indented at `col` or deeper (blank lines inside kept)."""
    j, last = i + 1, i + 1
    while j < len(lines):
        if _blank(lines[j]):
            j += 1
            continue
        if _indent(lines[j]) >= col:
            j += 1
            last = j
        else:
            break
    return last


def sites(body: str | None) -> list[dict]:
    """Every site of the body (module docstring; pure), in line order, at most MAX_SITES."""
    if body is None or "\t" in body:
        return []
    L = body.split("\n")
    if not L or not re.match(r"\s*by\b", L[0]):
        return []
    out = []
    for i, ln in enumerate(L):
        if i == 0 or "--" in ln:
            continue
        for kind, rx in SITE_RES:
            m = rx.match(ln)
            if not m:
                continue
            raw = m.group("pat")
            names = [x.strip() for x in (raw.split() if kind == "casesp" else raw.split(","))]
            if not names or not all(PNAME_RE.fullmatch(x) for x in names) or all(x in ("_", "-") for x in names):
                break
            if kind == "casesp" and "-" in names or kind != "casesp" and len(names) < 2:
                break
            real = [x for x in names if x not in ("_", "-")]
            if len(set(real)) != len(real) or any(x in ("this", "rfl") for x in real):
                break
            lead = m.group("lead")
            col = len(lead)
            last = i
            if kind == "obtainml":           # the source on the following, deeper lines
                j = i + 1
                while j < len(L) and (_blank(L[j]) or _indent(L[j]) > col):
                    if not _blank(L[j]):
                        last = j
                    j += 1
                src = "\n".join(L[i + 1:last + 1])
                if last == i or not _balanced(src) or any(x in src for x in (";", "<;>", "--", "/-", "\"")) \
                        or src.lstrip().startswith(("by", "·", ".", "fun", "λ", "match")):
                    break
            else:
                src = m.group("src").strip()
                if not _src_ok(src):
                    break
            nxt = next((j for j in range(last + 1, len(L)) if not _blank(L[j])), None)
            if nxt is not None and (_indent(L[nxt]) > col or L[nxt].lstrip().startswith(CONT_START)
                                    or not _tactic_start(L[nxt].lstrip())):
                break                         # the source may go on (a deeper line, or an operator / `$ by` line)
            se = scope_end(L, last, col)
            out.append({"line": i, "last": last, "kind": kind, "kw": m.group("kw"), "lead": lead, "col": col, "names": names,
                        "src": src, "end": se})
            break
        if len(out) >= MAX_SITES:
            break
    return out


def _tactic_start(t: str) -> bool:
    """`t` (a stripped line) may start a tactic: a letter (not λ) or `·` / `.` / `(` / `{` / `«` / `_` / `#`."""
    c = t[:1]
    return bool(c) and ((c.isalpha() and c not in "λΠΣ") or c in "·._«({#")


def reread(lines: list[str], s: dict) -> dict | None:
    """Site `s` as it reads now on its line (an earlier site's renames may have changed its source), or None when the line no longer
    is that site."""
    i = s["line"]
    if i >= len(lines):
        return None
    rx = dict(SITE_RES)[s["kind"]]
    m = rx.match(lines[i])
    if not m or m.group("lead") != s["lead"]:
        return None
    raw = m.group("pat")
    names = [x.strip() for x in (raw.split() if s["kind"] == "casesp" else raw.split(","))]
    if len(names) != len(s["names"]):
        return None
    if s["kind"] == "obtainml":
        return dict(s, src="\n".join(lines[i + 1:s["last"] + 1]), names=names)
    if not _src_ok(m.group("src").strip()):
        return None
    return dict(s, src=m.group("src").strip(), names=names)


def site_src(lines: list[str], s: dict) -> str:
    """The rcases target: `id s` for a `have` of a bare name that is used again in the block (rcases would clear that local)."""
    src = s["src"]
    if s["kw"] == "have" and NAME_RE.fullmatch(src) and uses(src, "\n".join(lines[s.get("last", s["line"]) + 1:s["end"]])):
        return "id " + src
    return src


def site_line(lines: list[str], s: dict, top: bool) -> str:
    """The site's new line: `rcases e` (after `unhygienic` without a top one), then `; rcases t` for every deeper level (chain)."""
    return "\n".join(site_lines(lines, s, top))


def site_lines(lines: list[str], s: dict, top: bool) -> list[str]:
    """The site's new lines (in place of lines s["line"] .. s["last"]): a one-line site gives one line; a multi-line one gives its
    source lines, the first one after `rcases` (one line fewer), and the chain follows the last of them."""
    chain = "".join("; rcases " + t for t in s.get("chain") or [])
    first = s["lead"] + ("" if top else "unhygienic ") + "rcases "
    if s["kind"] == "obtainml":
        # the source's first line joins `rcases` (MEASURED: `rcases` alone on its line takes no target and the next line fails),
        # in parentheses: a continuation line left of the moved first line otherwise ends the term (MEASURED: "unexpected token 'λ'")
        src = lines[s["line"] + 1:s.get("last", s["line"]) + 1]
        out = [first + "(" + src[0].strip()] + src[1:]
        return out[:-1] + [out[-1].rstrip() + ")" + chain]
    return [first + site_src(lines, s) + chain]


# ------------------------------------------------------------------------------------------------------------------------------ probe
def given_text(head: str, body: str, ss: list[dict]) -> tuple[str, list[int]]:
    """(the proof with a `trace_state` after every site, the decl line of each of those traces)."""
    L = body.split("\n")
    base = head.count("\n") + 1          # decl line of body line 0
    o_lines, O, add = [], [], 0
    at = {s.get("last", s["line"]): s for s in ss}
    o_lines = [0] * len(ss)
    for i, ln in enumerate(L):
        O.append(ln)
        if i in at:
            O.append(" " * at[i]["col"] + TRACE)
            o_lines[ss.index(at[i])] = base + i + add + 1
            add += 1
    return head + "\n".join(O), o_lines


def lean_text(head: str, body: str, s: dict) -> tuple[str, int]:
    """(the proof with site `s` rewritten (probe form, its chain included) and a `trace_state` after it, that trace's decl line)."""
    L = body.split("\n")
    i, last = s["line"], s.get("last", s["line"])
    new = site_lines(L, s, has_top(L))
    V = L[:i] + new + [" " * s["col"] + TRACE] + L[last + 1:]
    return head + "\n".join(V), head.count("\n") + 1 + i + len(new)


def probe_texts(head: str, body: str, ss: list[dict]) -> tuple[list[str], list[int], list[int]]:
    """(texts, the decl line of every site's trace in text 0 (the given names), per site the decl line of its trace in its own text).
    Text 0 = the proof with a trace after every site; text j+1 = site j rewritten (probe form) with a trace after it."""
    t0, o_lines = given_text(head, body, ss)
    texts, v_lines = [t0], []
    for s in ss:
        t, ln = lean_text(head, body, s)
        texts.append(t)
        v_lines.append(ln)
    return texts, o_lines, v_lines


def _plain(n: str) -> bool:
    return "✝" not in n and bool(NAME_RE.fullmatch(n))


def _same(a: list, b: list, shadowed: tuple = ()) -> bool:
    """Two hypothesis-name lists agree: equal names, inaccessible on both sides, or a given-side `n✝` against a Lean-side `n` for a
    pattern name n (the pattern shadowed an earlier `n`; with Lean's names nothing shadows it)."""
    return len(a) == len(b) and all(x == y or ("✝" in x and "✝" in y) or ("✝" in x and x.split("✝")[0] == y and y in shadowed)
                                    for x, y in zip(a, b))


def conjuncts(ty: str) -> list[str]:
    """The top-level conjuncts of a printed proposition (`A ∧ B ∧ C` -> [A, B, C], right-nested), [ty] when it is not a conjunction
    at the top (a binder, `→`, `↔`, `∨`, `if` .. at depth 0, or no `∧`)."""
    t = " ".join(str(ty).split())
    if not t or re.match(r"^(∀|∃|∃!|fun|λ|let|if|match|Σ|∑|∏|⨆|⨅|⋃|⋂)\b", t) or t[:1] in "∀∃λΣ∑∏":
        return [t]
    parts, d, cur, i = [], 0, "", 0
    while i < len(t):
        ch = t[i]
        if ch in BAL_O:
            d += 1
        elif ch in BAL_C:
            d -= 1
        if d == 0:
            for bad in (" → ", " ↔ ", " ∨ ", ", ", " => ", " := "):
                if t.startswith(bad, i):
                    return [t]
            if t.startswith(" ∧ ", i):
                parts.append(cur.strip()); cur = ""; i += 3
                continue
        cur += ch
        i += 1
    parts.append(cur.strip())
    return parts if len(parts) >= 2 and all(parts) else [t]


def proj_paths(t: str, r: int) -> list[str]:
    """Projection paths of r right-nested parts of a conjunction named t: t.1, t.2.1, .., t.2...2."""
    return [t + ".2" * j + ".1" for j in range(r - 1)] + [t + ".2" * (r - 1)]


def _split(on: list, vn: list, kept: list) -> tuple[int, int] | None:
    """(n, m): the given context is n hypotheses, the pattern's parts (kept: `_` any name, else the name itself), m trailing ones;
    Lean's context the same n (inaccessible / shadowed names aside), its parts, the same m. m = 0 first, then up to 3."""
    ko = len(kept)
    for m in range(0, 4):
        n = len(on) - ko - m
        if n < 0 or len(vn) < n + 2 + m:
            return None
        ot = on[n:n + ko]
        if any(p != "_" and o != p for p, o in zip(kept, ot)):
            continue
        if not _same(on[:n], vn[:n], tuple(kept)) or not _same(on[len(on) - m:], vn[len(vn) - m:]):
            continue
        return n, m
    return None


def align(tos: list, tvs: list, s: dict):
    """The given-names traces `tos` and the rewritten traces `tvs` of one site, compared (module docstring, "probe"):
      {"map": {given name: Lean's name}, "extra": [Lean's names at `_` positions], "before": [main-goal names before the parts],
       "new": [Lean's names of the parts], "chain": the site's chain}        the parts align
      ("deeper", t)    the rewritten site destructured fewer parts than the pattern names (a nested pattern): t, Lean's name of the
                       last part, is the next level's target (every run and goal agreeing)
      None             anything else"""
    if not tos or len(tos) != len(tvs):
        return None
    names = s["names"]
    k = len(names)
    kept = [p for p in names if p != "-"]     # a `-` part is cleared on the given side; rcases keeps it (named, never used)
    ko = len(kept)
    res, deeper = None, None
    for to, tv in zip(tos, tvs):
        if not to or not tv or len(to) != len(tv):
            return None
        for gi, (go, gv) in enumerate(zip(to, tv)):
            on = [h[0] for h in go["hyps"]]
            vn = [h[0] for h in gv["hyps"]]
            if gi > 0:
                if not _same(on, vn):
                    return None
                continue
            src = s["src"]
            if s["kw"] == "have" and NAME_RE.fullmatch(src) and src in on[:len(on) - ko] and src not in vn:
                j = on.index(src)
                on = on[:j] + on[j + 1:]     # rcases cleared the local a `have` keeps
            sp = _split(on, vn, kept)
            if sp is None:
                return None                  # the given side's hypotheses do not show the pattern's (at the end, or before a few
            n, m = sp                        # hypotheses that depend on the destructured term and come back after the parts)
            vt = vn[n:len(vn) - m]
            if not all(_plain(v) for v in vt) or len(set(vt)) != len(vt):
                return None
            if len(vt) < k:
                if res is not None or (deeper is not None and deeper[0] != vt[-1]):
                    return None
                r = k - len(vt) + 1
                cj = conjuncts(dict((h[0], h[1]) for h in gv["hyps"]).get(vt[-1], ""))
                proj = None
                if 2 <= r <= len(cj):
                    pv = list(vt[:-1]) + proj_paths(vt[-1], r)
                    mp = {p: v for p, v in zip(names, pv) if p not in ("_", "-")}
                    proj = {"map": mp, "extra": [v for p, v in zip(names, pv) if p in ("_", "-")], "before": vn[:n], "new": pv,
                            "chain": list(s.get("chain") or []), "proj": vt[-1]}
                if deeper is not None and (deeper[1] is None) != (proj is None):
                    proj = None
                deeper = (vt[-1], proj)
                continue
            if len(vt) != k or deeper is not None:
                return None
            mp, extra = {}, []
            for p, v in zip(names, vt):
                if p in ("_", "-"):
                    extra.append(v)
                else:
                    mp[p] = v
            got = {"map": mp, "extra": extra, "before": vn[:n], "new": vt, "chain": list(s.get("chain") or [])}
            if res is None:
                res = got
            elif res["map"] != got["map"] or res["extra"] != got["extra"]:
                return None
    if deeper is not None:
        return ("deeper", deeper[0], deeper[1])
    return res


def probe(proof: str, statement: str, compile_batch, *, stats: dict | None = None, log=None) -> dict:
    """{site line: alignment} for the proof's sites: one compile_batch call with text 0 and one text per site, then up to CHAIN_ROUNDS
    calls with the deeper sites' chains extended by one level each (only those sites' texts)."""
    st = stats if stats is not None else {}
    from harness import dialect_unhyg as U
    body = split_declaration(proof, statement)
    ss = sites(body)
    if not ss:
        return {}
    head = proof[:len(proof) - len(body)]
    texts, o_lines, v_lines = probe_texts(head, body, ss)
    st["sites"] = st.get("sites", 0) + len(ss)
    got = list(compile_batch(texts) or []) + [None] * (len(texts) + 1)
    out = {}
    say = log or (lambda m: None)
    if got[0] is None:
        say(f"{FAMILY}: the given-names probe copy did not read")
        return {}
    tos_of = {j: U.traces_at(got[0], o_lines[j]) for j in range(len(ss))}
    projs: dict = {}
    cur = {j: (dict(ss[j], chain=[]), got[j + 1], v_lines[j]) for j in range(len(ss))}
    for rnd in range(CHAIN_ROUNDS + 1):
        pend = {}
        for j, (s, msgs, vl) in cur.items():
            tos = tos_of[j]
            tvs = U.traces_at(msgs, vl) if msgs is not None else []
            a = align(tos, tvs, s)
            if isinstance(a, dict):
                out[s["line"]] = a
                st["aligned"] = st.get("aligned", 0) + 1
                continue
            if isinstance(a, tuple) and a[2] is not None:
                projs.setdefault(s["line"], a[2])   # the conjunction's parts as projections of it (the shallowest such level)
            if isinstance(a, tuple) and len(s["chain"]) < MAX_CHAIN:
                pend[j] = dict(s, chain=s["chain"] + [a[1]])
                continue
            if s["line"] in projs:
                continue
            def tail(tr):
                try:
                    return [len(tr[0])] + [h[0] for h in tr[0][0]["hyps"]][-(len(s["names"]) + 3):]
                except Exception:  # noqa: BLE001
                    return None
            say(f"{FAMILY}: site line {s['line']} not aligned (traces {len(tos)} / {len(tvs)}; given {tail(tos)} Lean {tail(tvs)}; "
                f"pattern {s['names']}; chain {s['chain']})")
        if not pend:
            break
        if rnd == CHAIN_ROUNDS:
            say(f"{FAMILY}: site line(s) {sorted(pend[j]['line'] for j in pend)} need more than {CHAIN_ROUNDS} deeper level(s)")
            break
        order = sorted(pend)
        tl = [lean_text(head, body, pend[j]) for j in order]
        got2 = list(compile_batch([t for t, _ in tl]) or []) + [None] * (len(tl) + 1)
        st["chain_round"] = st.get("chain_round", 0) + 1
        cur = {j: (pend[j], got2[x], tl[x][1]) for x, j in enumerate(order)}
    for ln, a in projs.items():
        out.setdefault(-1 - ln, a)               # key -1 - line: the projection variant of the site at `line`
    return out


# ------------------------------------------------------------------------------------------------------------------------------ rewrite
def unused(ctx: set, base: str) -> str:
    """Lean's LocalContext.getUnusedName: `base` when free, else the first free `base_<i>`, i >= 1."""
    if base not in ctx:
        return base
    i = 1
    while f"{base}_{i}" in ctx:
        i += 1
    return f"{base}_{i}"


def predict(a: dict, acc: dict) -> list[str] | None:
    """Lean's names of a site's parts when earlier sites' parts were renamed by `acc` (given name -> Lean's name), or None when the
    probed names cannot be traced back to a suggestion (or, for a chain, when a renamed earlier part could collide with any of its
    names: the chain's targets are Lean's names too)."""
    before = [n for n in a["before"] if "✝" not in n]
    ctx1 = set(before)
    ctx2 = {acc.get(n, n) for n in before}
    if a.get("chain") or a.get("proj"):
        mine = set(a.get("chain") or []) | {n.split(".")[0] for n in a["new"]}
        mine |= {re.sub(r"_\d+$", "", n) for n in mine}
        mine |= {n + "_1" for n in set(mine)}
        return list(a["new"]) if not ((ctx2 - ctx1) & mine) else None   # a chain / projection site keeps its probed names or is left out
    out = []
    for i, v in enumerate(a["new"]):
        base = v
        m = re.fullmatch(r"(.+)_(\d+)", v)
        if m and (m.group(1) in ctx1 or m.group(1) in a["new"][:i]):
            base = m.group(1)
            if unused(ctx1 | set(a["new"][:i]), base) != v:
                return None
        out.append(unused(ctx2 | set(out), base))
    return out


def rewrite(lines: list[str], s: dict, a: dict, new: list[str] | None, top: bool, why: list | None = None,
            quote_all: bool = False) -> tuple[list[str], dict] | None:
    """The lines with site `s` rewritten and its block renamed (new = Lean's names of the parts, default the probed ones), and the
    rename map; None when a pure check fails (module docstring)."""
    i, e, last = s["line"], s["end"], s.get("last", s["line"])
    s = reread(lines, s)
    if s is None:
        _why(why, "site line changed")
        return None
    new = list(new or a["new"])
    mp, extra = {}, []
    for p, v in zip(s["names"], new):
        if p in ("_", "-"):
            extra.append(v)
        else:
            mp[p] = v
    scope = lines[last + 1:e]
    text = "\n".join(scope)
    if top or enclosing_unhyg(lines, i):
        # the site sits in an unhygienic block: the block's later tactics name hypotheses with getUnusedName, so a new name taking a
        # base they use shifts their names (MEASURED: a later `rcases h` then took another hypothesis). Strict: no base of a new name
        # may be spelled in the block, apart from the given names' own uses. (A later one-line `unhygienic tac` is left to the screen.)
        masked = rename_words(scope, {p: "\u2063" for p in mp})
        mtext = "\n".join(masked)
        for v in list(mp.values()) + extra:
            b = re.sub(r"_\d+$", "", v.split(".")[0])
            if re.search(WORD + re.escape(b) + r"(_\d+)?" + WEND, mtext):
                _why(why, f"unhygienic block spells {b}")
                return None
    alpha = {}
    for p, v in mp.items():
        if re.search(r"[({,]\s*" + re.escape(p) + r"\s*:=", text):
            _why(why, f"named arg {p}")
            return None                     # a named argument / structure field spelled like the given name
        if "." in v and any(_not_term(ln, o) for ln in scope for o in occurrences(p, ln)):
            _why(why, f"projection {p}->{v} at a location")
            return None                     # a projection is a term: `at h.1`, `subst h.2`, .. do not take one
        v = v.split(".")[0]
        ov, op_ = occurrences(v, text), occurrences(p, text)
        if v in KEYWORDS:
            # a keyword's spellings: tactic words (harmless) or binders (a capture that alpha cannot fix: the tactic keeps the word)
            if any(o < max(op_ or [-1]) and not TACTIC_POS.search(text[:o]) for o in ov):
                _why(why, f"capture {p}->{v} (keyword)")
                return None
            continue
        if v != p and ov and op_ and min(ov) < max(op_):
            # Lean's name is spelled in the block before the last use of the given name: a later binder of it (Lean chose it, so it
            # names nothing in scope at the site). Every spelling of it in the block is renamed to a fresh name first (alpha), unless
            # it is also a named argument there, or no fresh name is left.
            fresh = _fresh(v, "\n".join(lines), set(a["before"]) | {x.split(".")[0] for x in new} | set(alpha.values()))
            named = re.search(r"[({,]\s*" + re.escape(v) + r"\s*:=", text)
            uh = re.search(WORD + "unhygienic" + WEND, text)
            # a spelling after an unhygienic tactic may be a name that tactic gave (no binder spelled): alpha only when the block's
            # first spelling of Lean's name is a binder
            unhyg = uh is not None and max(ov) > uh.start() and not _binder_like(text, min(ov), v)
            if fresh is None or named or unhyg:
                # an unhygienic tactic in the block may name that hypothesis itself (no spelled binder: MEASURED "Unknown
                # identifier `h'`" after an alpha rename)
                _why(why, f"capture {p}->{v} ({'no fresh name' if fresh is None else 'named argument' if named else 'unhygienic block'})")
                return None
            alpha[v] = fresh
    if len(set(mp.values()) | set(extra)) != len(mp) + len(extra):
        _why(why, "names not distinct")
        return None
    body = rename_words(scope, alpha) if alpha else scope
    out = lines[:i] + site_lines(lines, s, top) + rename_words(body, mp, quote=KEYWORDS, quote_all=quote_all) + lines[e:]
    return out, mp


NOT_TERM_BEFORE = re.compile(r"(?<![\w'.])(subst|clear|revert|specialize|induction|induction'|cases'|rename_i|generalizing|clear_value|"
                             r"intro|intros|rintro|set|by_cases|by_contra|change|with)\s+(?:[^\s:=]+\s+)*$")
PATTERN_HEAD = re.compile(r"(?<![\w'.])(obtain|rintro|intro|fun|λ|with|match|have|let)(?![\w'!?])[^:=]*[⟨,|(]\s*(?:[^\s,⟩:=]+\s*,\s*)*$|^\s*\|")


def _not_term(line: str, o: int) -> bool:
    """The spelling at offset o of `line` is not a term: in an `at ..` location list, the argument of a tactic that takes a local
    (`subst`, `clear`, `induction`, ..), or a binder (`intro x`, a pattern component of `obtain` / `rintro` / `fun` / `with`)."""
    before = line[:o]
    return bool(AT_RE.search(before)) or bool(NOT_TERM_BEFORE.search(before)) or bool(PATTERN_HEAD.search(before))


def enclosing_unhyg(lines: list[str], i: int) -> bool:
    """Line i lies in the block of an earlier `unhygienic` that stands alone on its line (`unhygienic`, `· unhygienic`, `by unhygienic`)."""
    d = _indent(lines[i]) if i < len(lines) else 0   # the least indentation from line i back to j (the block line i is in)
    for j in range(i - 1, -1, -1):
        ln = lines[j]
        if _blank(ln):
            continue
        m = re.search(r"^(\s*)(?:([·.])\s+)?unhygienic\s*$|\bby\s+unhygienic\s*$", ln)
        if m:
            col = (len(m.group(1)) + (2 if m.group(2) else 0)) if m.group(1) is not None else _indent(ln) + 1
            if d >= col:
                return True
        d = min(d, _indent(ln))
    return False


BINDER_BEFORE = re.compile(r"(?<![\w'.])(intro|intros|rintro|fun|next|case|rename_i|obtain|rcases|cases'|induction'|with|have|let|set|"
                           r"by_cases|by_contra|generalize|choose)(?![\w'!?])|[∀∃λ]|[⟨(|,]\s*$")


def _binder_like(text: str, o: int, v: str) -> bool:
    """The spelling of v at offset o looks like a binder: a binding word earlier on its line (`intro`, `fun`, `obtain ⟨..`, `have`,
    `with`, ..), `λ` / `∀` / `∃` before it, or `v :` / `v :=` after it."""
    line_start = text.rfind("\n", 0, o) + 1
    before, after = text[line_start:o], text[o + len(v):]
    return bool(BINDER_BEFORE.search(before)) or bool(re.match(r"\s*:(?!=)|\s*:=", after))


def _fresh(v: str, text: str, taken: set) -> str | None:
    """`v'`, `v''`, .. : the first that the whole proof never spells and no hypothesis carries."""
    for k in range(1, 4):
        c = v + "'" * k
        if c not in taken and not uses(c, text):
            return c
    return None


def _why(why, msg: str) -> None:
    if why is not None:
        why.append(msg)


def build(body: str, ss: list[dict], al: dict, why: list | None = None, *, index: dict | None = None,
          only: dict | None = None) -> list[tuple[str, str, str]]:
    """[(variant, new body, note)]: jointtop, joint, then the singles (most tokens saved first); only bodies with fewer tokens. A site
    may have two alignments: al[line] (flat, or an rcases chain) and al[-1 - line] (the last level's conjunction as projections); the
    joint form takes the first of (projections, chain) whose pure checks pass. index (out): single body -> (site line, al key);
    only: {site line: al key}: the joint forms of exactly those sites and alignments (no singles)."""
    L = body.split("\n")
    top = has_top(L)
    t0 = count_tokens(body)
    vars_of = []
    for s in ss:
        keys = [k for k in (-1 - s["line"], s["line"]) if k in al]
        if only is not None:
            keys = [k for k in keys if only.get(s["line"]) == k]
        if keys:
            vars_of.append((s, [al[k] for k in keys], keys))
    singles = []
    for s, vs, keys in vars_of:
        for a, key in zip(vs, keys):
            if only is not None:
                break
            for q in (False, True):     # keyword names quoted in locations only / wherever bare (a Mathlib env tokenizes `left`)
                r = rewrite(L, dict(s, chain=list(a.get("chain") or [])), a, None, top, None if q else why, quote_all=q)
                if r is None:
                    break
                nb = "\n".join(r[0])
                t = count_tokens(nb)
                if t < t0 and not any(nb == x[2] for x in singles):
                    singles.append((t, s, nb, a))
                    if index is not None:
                        index[nb] = (s["line"], key)
    singles.sort(key=lambda x: (x[0], x[1]["line"]))
    vars_of = [(s, vs) for s, vs, _ in vars_of]
    out = []
    if len({x[1]["line"] for x in singles}) >= 2 or only is not None and len(vars_of) >= 2:
        top_ok = not top and _top_ok(L, [s for s, _ in vars_of], {s["line"]: vs[-1] for s, vs in vars_of})
        # two joint forms: projections first where a site has them, then without projections (a projection that compiles alone
        # can still fail jointly through an automation step that wanted the parts as hypotheses)
        # jointcore: only the sites whose parts take core names (∃ / ∧ / × / subtype / ↔ binders): a library structure's field names
        # may differ on another pin of the row (MEASURED: a joint failed one pin through a field-named site, its other sites passed)
        for tag, use_proj, core, q in [(t, u, c, q) for q in (False, True)
                                       for t, u, c in (("joint", True, False), ("jointnp", False, False), ("jointcore", True, True))]:
            tag = tag + ("q" if q else "")
            n_j, cur, acc, off = 0, list(L), {}, 0
            for s, vs in vars_of:
                s2 = dict(s, line=s["line"] + off, last=s.get("last", s["line"]) + off, end=s["end"] + off)
                for a in vs:
                    if a.get("proj") and not use_proj:
                        continue
                    if core and not all(re.sub(r"_\d+$", "", n.split(".")[0]) in CORE_NAMES
                                        for n in list(a["new"]) + list(a.get("chain") or [])):
                        continue
                    new = predict(a, acc)
                    if new is None:
                        continue
                    r = rewrite(cur, dict(s2, chain=list(a.get("chain") or [])), a, new, top, quote_all=q)
                    if r is None:
                        continue
                    off += len(r[0]) - len(cur)   # a multi-line site gives one line fewer: later sites move up
                    cur, mp = r
                    acc.update({k: v.split(".")[0] for k, v in mp.items()})
                    n_j += 1
                    break
            if n_j < 2:
                continue
            joint = "\n".join(cur)
            if top_ok:
                tl = joint.split("\n")
                tl = [x.replace("unhygienic rcases", "rcases", 1) if re.match(r"^\s*(?:[·.]\s+)?unhygienic rcases\b", x) else x
                      for x in tl]
                tl[0] = tl[0].rstrip() + " unhygienic"
                jt = "\n".join(tl)
                if count_tokens(jt) < t0:
                    out.append((tag + "top", jt, f"{n_j} sites, one top unhygienic"))
            if count_tokens(joint) < t0:
                out.append((tag, joint, f"{n_j} sites"))
    seen, uniq = set(), []
    for x in out:
        if x[1] not in seen:
            seen.add(x[1]); uniq.append(x)
    out = uniq
    for t, s, nb, a in singles:
        if nb not in seen:
            seen.add(nb)
            kind = "proj" if a.get("proj") else "single"
            out.append((kind, nb, f"line {s['line']} {s['kw']} -> rcases" + (f" + {len(a['chain'])} level(s)" if a.get("chain") else "")
                        + (f", parts of {a['proj']} as projections" if a.get("proj") else "") + f" ({t0 - t} tokens)"))
    return out


def _top_ok(L: list[str], good: list[dict], al: dict) -> bool:
    """A top `unhygienic` may replace the per-line ones: the body's first line is a bare `by`, no `rename_i` / named `case` / `next`
    anywhere (formerly inaccessible hypotheses become accessible), and no `✝` hypothesis before a site shares a base with its names."""
    if L[0].strip() != "by" or RENAME_WORDS.search("\n".join(L)):
        return False
    for s in good:
        a = al[s["line"]]
        bases = {re.sub(r"_\d+$", "", v.split(".")[0]) for v in list(a["new"]) + list(a.get("chain") or [])}
        for n in a["before"]:
            if "✝" in n and n.split("✝")[0] in bases:
                return False
    return True


# ------------------------------------------------------------------------------------------------------------------------------ compile
def renamed(statement: str, i: int) -> str | None:
    """The statement as `theorem <namespace>.lraPE<i> ...`: d4_measure.renamed with the declaration's namespace prefix and `private`
    kept (MEASURED for a dotted name: the bare renamed copy loses the namespace, `Unknown identifier`; a private one cannot see the
    file's private constants), else None."""
    from harness.post import d4_measure as MS
    m = MS.DECL_RE.match(statement)
    if not m or ".{" in m.group(0):
        return None
    name = re.split(r"\s+", m.group(0).strip())[-1]
    pre = name.rsplit(".", 1)[0] + "." if "." in name and not name.startswith("_root_.") else ""
    priv = "private " if re.search(r"(?<![\w'.])private(?![\w'])", statement[:m.end() - len(name)]) else ""
    return f"{priv}theorem {pre}lraPE{i}" + statement[m.end():]


def build_file(statement: str, texts: list[str], attached: str = "") -> tuple[str, list]:
    """t4ind.build_file with renamed() above, and the row's attached `.. in` combinators (`open .. in`, `set_option .. in`) before
    every copy (the file prefix's own attach to the anchor, the file's first declaration). Spans as t4ind.build_file's."""
    from harness.post import t4ind as T4I
    out, spans = [T4I.ANCHOR_TEXT, "\n"], []
    line = T4I.ANCHOR_TEXT.count("\n") + 1
    for i, t in enumerate(texts):
        r = renamed(statement, i)
        if r is None or not t.startswith(statement):
            spans.append(None)
            continue
        copy = (r + t[len(statement):]).rstrip() + "\n\n"
        n = copy.count("\n")
        a = attached.count("\n")
        spans.append((line + a, line + a + n, statement.count("\n") - r.count("\n")))
        out.append(attached + copy)
        line += a + n
    return "".join(out), spans


def make_compile_batch(statement: str, run, *, compile_s=None, files: int = PROBE_FILES, stats: dict | None = None, log=None,
                       attached: str = ""):
    """t4ind.make_compile_batch on build_file() above: compile_batch(texts) -> [None | messages with "decl_line"]; one charged
    run(text, None) per file of at most t4ind.per_file(compile_s) copies; the file budget is shared by every call."""
    from harness.post import t4ind as T4I
    st = stats if stats is not None else {}
    for c in ("files", "copies", "copies_skipped", "no_anchor", "timeouts"):
        st.setdefault(c, 0)
    left = [int(files)]
    k = T4I.per_file(compile_s)
    say = log or (lambda m: None)

    def compile_batch(texts: list[str]) -> list:
        out: list = [None] * len(texts)
        for a in range(0, len(texts), k):
            chunk = list(range(a, min(len(texts), a + k)))
            text, spans = build_file(statement, [T4I.quiet(texts[i]) for i in chunk], attached)
            if all(sp is None for sp in spans):
                continue
            if left[0] <= 0:
                st["copies_skipped"] += sum(sp is not None for sp in spans)
                continue
            left[0] -= 1
            r = run(text, None)
            st["files"] += 1
            st["copies"] += sum(sp is not None for sp in spans)
            if getattr(r, "timed_out", False):
                st["timeouts"] += 1
                say(f"{FAMILY}: a probe file of {len(chunk)} cop(ies) timed out")
                continue
            got = T4I.split_messages(getattr(r, "messages", None), spans)
            if got is None:
                st["no_anchor"] += 1
                say(f"{FAMILY}: a probe file printed no anchor: {str((getattr(r, 'errors', None) or ['?'])[0])[:160]}")
                continue
            for i, g in zip(chunk, got):
                out[i] = g
        return out
    return compile_batch


def attached_in(meter) -> str:
    """The `.. in` combinators the row's file prefix attaches to the declaration (open_post.attached_in's rule, computed here): the
    trailing `set_option / omit / include / unseal / variable .. in` line and every `open .. in` among the trailing modifiers, one
    per line; "" without a meter or a file prefix (a header row)."""
    if meter is None:
        return ""
    row = getattr(meter, "row", None) or {}
    try:
        from scorer import compile as SC
        if not row.get("file_path") or row.get("source") == "putnambench":
            return ""
        core, mods = SC.split_modifiers(SC.file_prefix(row, (getattr(meter, "versions", None) or [None])[0]))
        m = SC._ATTACHED_IN.search(core)
        lines = [m.group(0).strip()] if m else []
        lines += [x.group(0).strip() for x in re.finditer(r"open\s+[\w.\s]+?\s+in\b", mods)]
        return "".join(" ".join(x.split()) + "\n" for x in lines)
    except Exception:  # noqa: BLE001  (no prefix: the copies go without; their own compile then tells)
        return ""


# ------------------------------------------------------------------------------------------------------------------------------ op API
def _key(proof: str) -> str:
    import hashlib
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def has_sites(proof: str, statement: str) -> bool:
    try:
        return bool(sites(split_declaration(proof, statement)))
    except Exception:  # noqa: BLE001
        return False


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    """The probe (make_compile_batch above on the post-step's charged `run`: one file, plus one per deeper level), the candidates, and
    their one-file screen (opus_screen) when there are two or more (plus one file for the joint of the passing singles); {} when
    nothing aligned. A budget stop propagates."""
    ctx = ctx or {}
    st = stats if stats is not None else {}
    say = log or (lambda m: None)
    try:
        body = split_declaration(proof, statement)
        ss = sites(body)
        if not ss:
            return {}
        cb = make_compile_batch(statement, run, compile_s=ctx.get("compile_s"), files=PROBE_FILES, stats=st.setdefault("batch", {}),
                                log=say, attached=attached_in(getattr(run, "meter", None)))
        al = probe(proof, statement, cb, stats=st, log=say)
        why: list = []
        index: dict = {}
        raws = build(body, ss, al, why, index=index) if al else []
        say(f"{FAMILY}: {len(ss)} site(s), {len(al)} aligned, {len(raws)} candidate(s)" + (f"; dropped: {why[:6]}" if why else ""))
        if not raws:
            return {}
        got = {"pe_key": _key(proof), "pe_raws": raws}
        if len(raws) >= 2:
            from harness.post import opus_screen as SC
            scr = SC.screen(statement, body, [r[1] for r in raws], run, ctx, log=say, tag=FAMILY, max_files=1)
            if scr is not None:
                got["pe_screen"] = scr
                # the joint forms did not pass but two or more singles did: the joint of exactly those (one more screen file)
                up = {b for b, _ in scr.get("up", [])}
                joints = {b for v, b, _ in raws if v.startswith("joint")}
                ok = {}
                for b, _ in scr.get("up", []):          # best predicted first (a list: the order is deterministic)
                    if b in index and index[b][0] not in ok:
                        ok[index[b][0]] = index[b][1]
                if len(ok) >= 2 and not (joints & up) and not scr.get("unscreened"):
                    more = [r for r in build(body, ss, al, only=ok) if r[1] not in {x[1] for x in raws}]
                    if more:
                        scr2 = SC.screen(statement, body, [r[1] for r in more], run, ctx, log=say, tag=FAMILY + "/joint", max_files=1)
                        st["rejoint"] = st.get("rejoint", 0) + 1
                        raws = more + raws
                        got["pe_raws"] = raws
                        if scr2 is not None:
                            scr["up"] = list(scr2.get("up", [])) + list(scr["up"])
                            scr["unscreened"] = list(scr2.get("unscreened", [])) + list(scr.get("unscreened", []))
                        else:
                            scr["unscreened"] = [r[1] for r in more] + list(scr.get("unscreened", []))
        return got
    except Exception as e:  # noqa: BLE001  (this op's fault proposes nothing; a budget stop propagates)
        if e.__class__.__name__ == "_Stop":
            raise
        say(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:200]}")
        return {}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    """The query's candidates for exactly this proof: the screen's predicted-up ones (best first) and the unscreened ones, or all of
    them in build order when there was no screen."""
    try:
        c = ctx or {}
        if c.get("pe_key") != _key(proof):
            return []
        head_len = len(proof) - len(split_declaration(proof, statement))
        head = proof[:head_len]
        raws = list(c.get("pe_raws") or [])
        scr = c.get("pe_screen")
        if scr is not None:
            up = dict(scr.get("up", []))
            uns = set(scr.get("unscreened", []))
            raws = sorted([r for r in raws if r[1] in up], key=lambda r: -up[r[1]]) + [r for r in raws if r[1] in uns]
        out, seen = [], {proof.rstrip()}
        for var, nb, note in raws:
            decl = head + nb
            if decl.rstrip() in seen or split_declaration(decl, statement) != nb:
                continue
            seen.add(decl.rstrip())
            out.append({"op": f"{FAMILY}:{var}", "decl": decl, "note": note})
        return out[: int(max_per_op or MAX_PER_OP)]
    except Exception:  # noqa: BLE001
        return []
