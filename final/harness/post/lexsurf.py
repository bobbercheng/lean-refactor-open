#!/usr/bin/env python3
"""Lexer-cheap surface rules "lexsurf" of the open post-step (harness/open_post.py; length tools v2, 2026-11-03): pure, deterministic,
model-free rewrites of a proof's surface that the Arena lexer (scorer/tokenize.py) counts as fewer tokens while Lean elaborates the
same proof, verified JOINTLY: every site of every rule is applied at once and compiled in one plain compile on the primary pin, the
compile's own error positions drop the sites that broke it (or move them to their next spelling), at most ROUNDS rounds plus BISECT
half compiles; only what compiled is proposed. Every rule reads only the proof being edited and its statement (no row name, no table,
no proof text, no lemma list); every token a candidate writes is the proof's own or Lean syntax.

  rules (rule tag: site -> spellings, in the order tried)
    anonctor  an anonymous constructor `⟨p1, .., pn⟩`, n >= 2, in a TERM position (never in a binder or pattern position: fun / λ
              binders, obtain / have / let / set before `:=`, rintro / intro, `rcases .. with`, `| .. =>` arms, match patterns, a bracket
              nested in a pattern) -> Lean's leading-dot constructor, one lexer token: n = 2 `.intro A B`, `.mk A B`; n >= 3 `.mk A B C`,
              `.intro A $ .intro B C` (only where the bracket ends its term). An atomic component stays bare, a bracketed one keeps its
              brackets, a compound non-final one gets parentheses, a compound final one `$` (a `fun` none) where the bracket ends its
              term. As an application's last argument (the application's head and arguments plain, the bracket ending its term) the
              same spellings after `$`. Skipped: all components `?_`, a cdot or a binder symbol inside, a multi-line non-final component,
              a projection right after the bracket.
    emcases   a `by_cases h : P` tactic (P may continue on deeper lines) -> `rcases Classical.em _ with h | h` (the proposition is left
              to unification; saves |P| - 4 tokens); under a covering `by unhygienic` also `cases Classical.em _` (both goals name the
              hypothesis `h`, the constructor's field), with h's uses in the rest of the block renamed to `h` when `h` is nowhere in the
              statement or the proof and h is not bound again there. The goal order is by_cases' own (positive first). Skipped when
              the block names the goals `pos` / `neg`.
    ascml     a `have h : T := e` that the end pipe's one-line ascription rule does not see (the term on the lines after `:=`, T over
              several lines, a `with_reducible` or bullet prefix): `: T` dropped, then T as `_ R _` (R its one top-level relation);
              `have h : T := by exact e` and `:= by` + one `exact e` line: `e` in place of the block, with `: T` dropped, then kept.
    bindhave  `have h : ∀ x y, P := fun x y => e` (or `:= by` + a first line `intro x y`) -> `have h x y : P := e` (`:= by` + the
              rest); typed binders keep `(x : T)`; whole binder groups only; binder predicates and implicit binders are skipped.
    typedrop  a type ascription Lean can infer from the expected type: `(x y : T)` -> `x y` in a binder list (fun / λ / ∀ / ∃ / a
              have's or let's binders / intro), `(x : T)` -> `x` as a term (an identifier, not before a projection), `λx : T =>` ->
              `λx =>`; `∀ x : T,` / `∃ x : T,` -> `∀ x,` / `∃ x,`; a numeral's ascription `(2 : T)` -> `2` (term position).
    bundle    `fun x => F (G x)` / `F $ G x` -> `F ∘ G`; `fun x => x` -> `id`; a parenthesised `(fun x y => e)` whose binders occur
              once each, in order, outside any bracket of e -> `(e[·/x, ·/y])`; `f $ a` (a one token, the bracket-free application
              ending its term) -> `f a`; `False.elim (e)` / `False.elim $ e` / `(e).elim` ending a term -> `nomatch e`; `le_refl a` ->
              `le_rfl`, `Eq.refl a` -> `rfl`, `Iff.refl a` -> `Iff.rfl`, `HEq.refl a` -> `HEq.rfl` (a one token); a body
              `:=` + line break + `by` -> `:= by` (no token on this lexer; the official worker counts that line break as one).
  edits     Edit(start, end, text, rule, dtok, ...): body offsets, the replacement, the rule tag and the exact token saving in context
            (count_tokens(body) - count_tokens(body with this edit)); a site's spellings are its alternatives. Overlapping edits
            conflict (the larger saving is kept); two `h`-binding emcases edits with overlapping blocks conflict.
  query     (the post-step's env-query compile, run(text, None) on the primary pin, charged to the row's budget) the joint engine:
            screen  (more than SCREEN_SITES live sites on a row compiling within SCREEN_MAX_S) at most SCREEN_FILES files of renamed
                    copies, the incumbent first (the control), then one copy per site with its current spelling, each followed by a
                    marker: a copy with an error inside its lines fails that spelling; a failed control or a missing marker decides
                    nothing.
            rounds  round k (ROUNDS, up to MAX_ROUNDS on a fast row: ROUND_S / its compile seconds) compiles the declaration with
                    the chosen spelling of every live site (the cheapest non-conflicting set) followed by a `#print` marker that
                    locates the declaration's lines. Blame, per error: a name an edit can break (a have's, a by_cases hypothesis, a
                    dropped binder type's) named in the message outside its goal display, inside that edit's scope -> that edit;
                    else an error on an edit's lines -> that edit; else an `unsolved goals` range holding edits -> its emcases edit
                    for an `inl` / `inr` goal, or its only edit; else the nearest scoped edit (emcases / ascml / bindhave / typedrop)
                    before it. A blamed spelling is dropped (the site moves to its next one); a round that blames nothing, or the
                    last round, is followed by at most BISECT compiles (the remaining set, its first half / the two halves).
            A spelling that failed on a row is not tried again on that row (module cache by statement, its lines and its
            replacement). $LRA_LEXSURF_DUMP (tests only) appends each round's edits and errors as JSON lines.
  candidates  the verified set jointly, then per rule, then its two halves, then its singles by saving (only token savers; the body
            never moves to the line after `:=`). Without a conclusive query the same order over the cheapest non-conflicting set.
Nothing here decides anything: the caller (harness/open_post.py) reads every candidate on the primary pin and keeps one only when it
compiles on every pin and scores higher (the accept gate)."""
from __future__ import annotations

import bisect as _bisect, hashlib, json, os, re, sys, threading
from pathlib import Path
from typing import NamedTuple

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from scorer.tokenize import count_tokens  # noqa: E402

FAMILY = "lexsurf"
RULES = ("anonctor", "emcases", "ascml", "bindhave", "bundle", "typedrop", "dotcall", "hyplist")
ROUNDS = 3             # joint compile rounds per query (up to MAX_ROUNDS on a row whose compile is fast: ROUND_S / compile seconds)
MAX_ROUNDS = 6
ROUND_S = 240.0
SCREEN_SITES = 8       # more live sites than this on a row compiling within SCREEN_MAX_S: one-copy-per-site screen files first
SCREEN_MAX_S = 60.0
SCREEN_FILES = 3
DOTCALL = True         # rules dotcall and hyplist (one probe compile per query for the locals' type heads)
ALIASES = True         # dotcall's alias spellings (`c x` -> `x.f` for `H.f` with c's statement; one env query per query)
ALIAS_MAX = 40         # (type head, root constant) pairs per alias query at most
MSCREEN = True         # measured screen (d4_measure single-site heartbeat readings) on a row with MSCREEN_SITES+ live sites
MSCREEN_SITES = 2
MSCREEN_FILES = 3
HB_TOL_ABS = 1.0       # a spelling is heartbeat-costly when its heartbeats added minus its tokens saved x exchange exceed
HB_TOL_REL = 0.002     #   max(HB_TOL_ABS, HB_TOL_REL x the control's reading)
BISECT = 2             # half compiles after the rounds (first half, then second)
MAX_SITES = 64         # live sites per round at most (largest saving first)
MAX_CANDS = 12         # candidates per call at most
MARK = "LRALEXSURF"
OPEN, CLOSE = "([{⟨", ")]}⟩"
IDC = r"[^\W\d][\w'!?₀-₉]*"
NAME_RE = re.compile(r"[^\W\d][\w'!?₀-₉]*(?:\.[^\W\d][\w'!?₀-₉]*)*")
BINDER_SYMS = "∀∃∑∏⋃⋂ΣΠ∫⨆⨅∮"
TERM_KW = {"exact", "exacts", "refine", "refine'", "apply", "use", "exists", "show", "from", "then", "else", "return", "calc",
           "existsi", "constructor", "at", "in", "do", "by", "suffices", "with"}
PAT_HEAD = re.compile(r"^\s*(obtain|rintro|intro|intros|rcases|cases'|choose|let|have|haveI|letI|set|match|induction'|replace|"
                      r"generalize|lift|ext|funext|filter_upwards|peel|fun_cases|fun_induction)\b")
DELIMS = {"", "(", "[", "{", "⟨", ",", ":=", "$", "<|", "=>", "↦", "←", "|", "·", ";", "<;>"}
REL_OPS = ("≠", "≤", "≥", "↔", "∣", "∈", "∉", "⊆", "⊂", "≡", "=", "<", ">")

_CACHE_LOCK = threading.Lock()
_FAILED: set = set()   # (statement sha, rule, context lines, replacement) of spellings that did not compile on that row


class Edit(NamedTuple):
    start: int          # body offset of the primary hunk
    end: int
    text: str           # its replacement
    rule: str           # rule tag (RULES)
    dtok: int           # exact token saving in context
    site: int = -1      # the site this spelling belongs to
    alt: int = 0        # its index among the site's spellings
    scope: int = 0      # body offset where the region whose errors are blamed on this edit ends (>= end)
    hunks: tuple = ()   # further (start, end, text) hunks (emcases' renames), disjoint from the primary one
    cap: tuple = ()     # (lo, hi): a region where this edit binds `h` (two such edits whose regions meet conflict)
    note: str = ""
    names: tuple = ()   # the names whose later uses this edit can break (a have's name, a by_cases hypothesis, binder names)

    def all_hunks(self):
        return ((self.start, self.end, self.text),) + tuple(self.hunks)


# ------------------------------------------------------------------------------------------------------------------------- text helpers
class _B:
    """A body with its comment / string mask, bracket pairs and line table."""

    def __init__(self, body: str):
        self.s = body
        self.mask = _mask(body)
        self.pairs = _pairs(body, self.mask)
        self.closer = {j: i for i, j in self.pairs.items()}
        self.ls = [0] + [i + 1 for i, ch in enumerate(body) if ch == "\n"]

    def line(self, i: int) -> int:
        return _bisect.bisect_right(self.ls, i) - 1

    def lstart(self, k: int) -> int:
        return self.ls[k]

    def lend(self, k: int) -> int:
        return self.ls[k + 1] - 1 if k + 1 < len(self.ls) else len(self.s)

    def text_line(self, k: int) -> str:
        return self.s[self.lstart(k):self.lend(k)]

    def blank(self, k: int) -> bool:
        a, b = self.lstart(k), self.lend(k)
        return all(self.s[x].isspace() or self.mask[x] for x in range(a, b))

    def indent(self, k: int) -> int:
        t = self.text_line(k)
        return len(t) - len(t.lstrip(" "))

    def content_col(self, k: int) -> int:
        """The column of the line's first token after a leading `·` bullet."""
        t = self.text_line(k)
        m = re.match(r"^(\s*)(?:[·.][ \t]+)?", t)
        if m and m.group(0).strip() in ("·", ".") and len(t) > m.end():
            return m.end()
        return len(t) - len(t.lstrip(" "))

    def next_nonblank(self, k: int):
        for j in range(k + 1, len(self.ls)):
            if not self.blank(j):
                return j
        return None

    def block_end(self, k: int, col: int) -> int:
        """Body offset where the block of line k ends: the end of the last following line indented at `col` or deeper."""
        last = self.lend(k)
        j = k + 1
        while j < len(self.ls):
            if self.blank(j):
                j += 1; continue
            if self.indent(j) >= col:
                last = self.lend(j); j += 1
            else:
                break
        return last

    def extent_end(self, k: int, col: int) -> int:
        """Body offset where the statement of line k ends: its following lines indented deeper than `col`."""
        last = self.lend(k)
        j = k + 1
        while j < len(self.ls):
            if self.blank(j):
                j += 1; continue
            if self.indent(j) > col:
                last = self.lend(j); j += 1
            else:
                break
        return last


def _ident_char(ch: str) -> bool:
    return bool(ch) and (ch.isalnum() or ch in "_'!?₀₁₂₃₄₅₆₇₈₉")


def _word_at(s: str, i: int, w: str) -> bool:
    """`w` occurs at i as a whole identifier (not after `.`, not followed by an identifier character)."""
    if not s.startswith(w, i):
        return False
    b = s[i - 1] if i > 0 else " "
    a = s[i + len(w)] if i + len(w) < len(s) else " "
    return not _ident_char(b) and b != "." and not _ident_char(a)


def _occurrences(s: str, w: str, lo: int = 0, hi: int | None = None, mask=None) -> list[int]:
    hi = len(s) if hi is None else hi
    out, i = [], lo
    while True:
        j = s.find(w, i, hi)
        if j < 0:
            return out
        if _word_at(s, j, w) and not (mask and mask[j]):
            out.append(j)
        i = j + 1


def _split_top(s: str, sep: str = ",") -> list[str]:
    parts, d, cur = [], 0, ""
    for ch in s:
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
        if ch == sep and d == 0:
            parts.append(cur); cur = ""
        else:
            cur += ch
    return parts + [cur]


def _wrapped(p: str) -> bool:
    """p is one bracket group `( .. )`, `⟨ .. ⟩`, `[ .. ]` or `{ .. }`."""
    p = p.strip()
    if len(p) < 2 or p[0] not in OPEN or p[-1] != CLOSE[OPEN.index(p[0])]:
        return False
    d = 0
    for k, ch in enumerate(p):
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
        if d == 0 and k < len(p) - 1:
            return False
    return True


def _atomic(p: str) -> bool:
    p = p.strip()
    return bool(p) and "\n" not in p and (count_tokens(p) == 1 or _wrapped(p)) and not p.startswith(("-", "¬", "↑", "!", "@", "←"))


def _has_top(s: str, chars: str) -> bool:
    d = 0
    for ch in s:
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
        elif d == 0 and ch in chars:
            return True
    return False


def _prev_tok(B: _B, i: int) -> str:
    """The significant token before offset i (comments skipped): an identifier, a two-character operator or one character."""
    s = B.s
    j = i - 1
    while j >= 0 and (s[j].isspace() or B.mask[j]):
        j -= 1
    if j < 0:
        return ""
    if _ident_char(s[j]) or s[j] == ".":
        k = j
        while k >= 0 and (_ident_char(s[k]) or s[k] == "."):
            k -= 1
        return s[k + 1:j + 1]
    if s[max(0, j - 2):j + 1] == "<;>":
        return "<;>"
    two = s[max(0, j - 1):j + 1]
    if two in (":=", "=>", "<|"):
        return two
    return s[j]


def _term_start(B: _B, i: int) -> bool:
    """A term starting at i is not an application argument (it follows a keyword, an opening bracket, a separator or an operator)."""
    t = _prev_tok(B, i)
    if not t:
        return True
    if t in TERM_KW:
        return True
    if _ident_char(t[0]) or t[0] == "." or t in (")", "]", "}", "⟩", "?_", "_"):
        return False
    return True


def _dollar_ok(B: _B, i: int) -> bool:
    """A term starting at i may take a trailing `$` / `fun` argument: it follows a keyword or a delimiter (never an operator)."""
    t = _prev_tok(B, i)
    return t in TERM_KW or t in DELIMS


def _terminal(B: _B, j: int, start_line: int) -> bool:
    """The term ending at offset j (exclusive) ends there: a closing bracket or a comma follows, or the line ends and the next line
    is not a continuation of the statement (deeper than the content column of the line where the term starts)."""
    s = B.s
    k = j
    while k < len(s) and s[k] in " \t":
        k += 1
    if k < len(s) and B.mask[k] and s.startswith("--", k):
        k = B.lend(B.line(k))
    if k >= len(s) or s[k] == "\n":
        nl = B.next_nonblank(B.line(j - 1 if j > 0 else 0))
        return nl is None or B.indent(nl) <= B.content_col(start_line)
    return s[k] in ")]}⟩,"


def _app_left(B: _B, i: int) -> bool:
    """The text from the start of the term that ends at offset i back to its term start is an application: identifiers, numbers and
    bracket groups only (segments after a `$` / `<|` count separately), at least one identifier."""
    s = B.s
    j = i
    parts = 0
    while True:
        k = j - 1
        while k >= 0 and s[k] in " \t":
            k -= 1
        if k < 0:
            break
        if s[k] in CLOSE and k in B.closer:
            j = B.closer[k]; parts += 1; continue
        if _ident_char(s[k]) or s[k] == ".":
            a = k
            while a >= 0 and (_ident_char(s[a]) or s[a] in ".@"):
                a -= 1
            w = s[a + 1:k + 1]
            if w in TERM_KW:
                break
            j = a + 1; parts += 1; continue
        break
    if parts < 1:
        return False
    head = s[j:i].strip()
    m = re.match(r"@?" + IDC, head)
    if not m:
        return False
    # the token before the application must be a keyword or a delimiter (an operator would bind the `$` differently)
    return _dollar_ok(B, j)


def _stmt_prefix(B: _B, i: int) -> str:
    """The text of the statement before offset i: the current line before i, joined after the previous lines it continues."""
    k = B.line(i)
    pre = B.s[B.lstart(k):i]
    j = k
    while True:
        p = None
        for q in range(j - 1, -1, -1):
            if not B.blank(q):
                p = q; break
        if p is None or B.indent(j) <= B.content_col(p):
            break
        pre = B.text_line(p) + " " + pre.lstrip()
        j = p
    return pre


def _line_seg(pre: str) -> str:
    """The part of a statement prefix after its last `;`, `<;>`, `=>`, `↦` or bullet."""
    cut = 0
    for m in re.finditer(r"<;>|;|=>|↦|·|(?<![\w'.])by(?![\w'!?])", pre):
        cut = m.end()
    return pre[cut:]


# ------------------------------------------------------------------------------------------------------------------------- the rules
def _pattern_pos(B: _B, i: int) -> bool:
    """Is the bracket at offset i in a binder / pattern position?"""
    pre = _stmt_prefix(B, i)
    seg = _line_seg(pre)
    for m in re.finditer(r"(?<![\w'])(?:fun(?![\w'])|λ)", seg):
        rest = seg[m.end():]
        if "=>" not in rest and "↦" not in rest:
            return True
    if re.match(r"^\s*\|", pre) and "=>" not in pre:
        return True
    m = PAT_HEAD.match(seg)
    if m:
        h = m.group(1)
        if h in ("rintro", "intro", "intros", "choose", "induction'", "ext", "funext", "filter_upwards", "peel", "lift", "generalize"):
            return True
        if h in ("rcases", "cases'", "fun_cases", "fun_induction"):
            return bool(re.search(r"\bwith\b", seg))
        if h == "match":
            return "=>" not in seg
        return ":=" not in seg
    if re.search(r"\bwith\b[^:=]*$", seg) and re.search(r"\b(rcases|obtain|cases'?|match)\b", pre):
        return True
    return False


def _anonctor(B: _B) -> list[list[tuple]]:
    """Sites [(start, end, [(text, note)])] of rule anonctor (module docstring)."""
    s = B.s
    out, pat_spans = [], []
    for i in sorted(B.pairs):
        j = B.pairs[i]
        if s[i] != "⟨" or B.mask[i]:
            continue
        if any(a < i < b for a, b in pat_spans) or _pattern_pos(B, i):
            pat_spans.append((i, j)); continue
        inner = s[i + 1:j]
        parts = [p.strip() for p in _split_top(inner)]
        if len(parts) < 2 or any(not p for p in parts) or all(p == "?_" for p in parts):
            continue
        if any(re.search(r"(?<![\w.'])·(?![\w.'])", p) for p in parts) or _has_top(inner, BINDER_SYMS):
            continue
        if any("\n" in p for p in parts[:-1]) or any(re.match(r"(?:match|if|let|have|show|calc)\b", p) for p in parts):
            continue
        after = s[j + 1] if j + 1 < len(s) else " "
        if _ident_char(after) or after in ".⁻":
            continue
        k0 = B.line(i)
        term = _terminal(B, j + 1, k0)
        start_ok = _term_start(B, i)
        tail_ok = term and _dollar_ok(B, i)

        def arg(p, last):
            if _atomic(p):
                return p
            if last and tail_ok:
                return p if re.match(r"(?:fun(?![\w'])|λ)", p) else "$ " + p
            return "(" + p + ")"
        forms = []
        if len(parts) == 2:
            for head in (".intro", ".mk"):
                forms.append(f"{head} {arg(parts[0], False)} {arg(parts[1], True)}")
        else:
            forms.append(".mk " + " ".join(arg(p, k == len(parts) - 1) for k, p in enumerate(parts)))
            if tail_ok:
                nest = f".intro {arg(parts[-2], False)} {arg(parts[-1], True)}"
                for p in reversed(parts[:-2]):
                    nest = f".intro {arg(p, False)} $ {nest}"
                forms.append(nest)
        alts = []
        if start_ok:
            alts = [(f, "") for f in forms]
        elif term and _app_left(B, i):
            tail_ok = True
            forms = []
            if len(parts) == 2:
                for head in (".intro", ".mk"):
                    forms.append(f"{head} {arg(parts[0], False)} {arg(parts[1], True)}")
            else:
                forms.append(".mk " + " ".join(arg(p, k == len(parts) - 1) for k, p in enumerate(parts)))
            alts = [("$ " + f, "arg") for f in forms]
        if alts:
            out.append((i, j + 1, alts))
    return out


BYC_RE = re.compile(r"(?<![\w.'])by_cases(?![\w'!?])")
BIND_HEAD = re.compile(r"(?:^|[\s(;⟨,|])(?:intro|intros|rintro|obtain|rcases|cases|induction|have|haveI|let|set|fun|λ|generalize|choose|"
                       r"by_cases|next|case|with|replace|specialize)\b")


def _unhygienic_cover(body: str) -> bool:
    return bool(re.match(r"\s*by\s+(?:classical\s+)?unhygienic\b", body))


def _nested_in_by(B: _B, k: int) -> bool:
    """Line k lies inside a nested `by` block (an ancestor line after the first one holds `by`): the top-level `unhygienic` does not
    reach the names a tactic there introduces."""
    cur = B.indent(k)
    for j in range(k - 1, 0, -1):
        if B.blank(j) or B.indent(j) >= cur:
            continue
        t = "".join(" " if B.mask[B.lstart(j) + q] else ch for q, ch in enumerate(B.text_line(j)))
        if re.search(r"(?<![\w'.])by(?![\w'!?])", t):
            return True
        cur = B.indent(j)
    return False


def _emcases(B: _B, statement: str) -> list[tuple]:
    """Sites [(start, end, scope_end, [(text, note, renames, cap)])] of rule emcases."""
    s = B.s
    out = []
    unh = _unhygienic_cover(s)
    h_free = not _occurrences(statement, "h") and not _occurrences(s, "h", mask=B.mask)
    for m in BYC_RE.finditer(s):
        a = m.start()
        if B.mask[a]:
            continue
        k = B.line(a)
        before = s[B.lstart(k):a]
        if before.strip() not in ("", "·", "."):
            continue
        rest_m = re.match(r"[ \t]+(?:(" + IDC + r")[ \t]*:(?!=)[ \t]*)?", s[m.end():])
        if not rest_m:
            continue
        name = rest_m.group(1)
        p0 = m.end() + rest_m.end()
        col = B.content_col(k)
        # P: to the line's end (a depth-0 `<;>` / `;` / comment ends it), continued on deeper lines
        e = B.extent_end(k, col)
        d, q = 0, p0
        stop = e
        while q < e:
            ch = s[q]
            if B.mask[q] and s.startswith("--", q):
                nl = s.find("\n", q)
                q = e if nl < 0 or nl >= e else nl
                continue
            if ch in OPEN:
                d += 1
            elif ch in CLOSE:
                d -= 1
            elif d == 0 and (s.startswith("<;>", q) or ch == ";"):
                stop = q; break
            q += 1
        P = s[p0:stop].rstrip()
        if not P.strip() or count_tokens(P) < 1:
            continue
        pend = p0 + len(P)
        scope_end = B.block_end(k, col)
        scope = s[pend:scope_end]
        if re.search(r"\bcase\s+(?:pos|neg)\b|\bpos\b\s*=>|\bneg\b\s*=>", scope):
            continue
        nm = name or "h"
        alts = []
        if unh and (nm == "h" or h_free) and not _nested_in_by(B, k):
            renames, ok = [], True
            if nm != "h":
                occ = _occurrences(s, nm, pend, scope_end, B.mask)
                for o in occ:
                    ln = B.text_line(B.line(o))
                    if BIND_HEAD.search(ln[: o - B.lstart(B.line(o))]):
                        ok = False; break
                renames = [(o, o + len(nm), "h") for o in occ]
            if ok:
                alts.append(("cases Classical.em _", "cases", tuple(renames), (a, scope_end) if renames else ()))
        alts.append((f"rcases Classical.em _ with {nm} | {nm}", "rcases", (), ()))
        out.append((a, pend, scope_end, alts))
    return out


HAVE_RE = re.compile(r"^([ \t]*)((?:[·.][ \t]+)?)((?:with_reducible[ \t]+)?)(have|haveI)[ \t]+(" + IDC + r")[ \t]*:(?!=)")


def _top_assign(s: str, a: int, b: int, mask) -> int:
    d = 0
    for q in range(a, b):
        if mask[q]:
            continue
        ch = s[q]
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
        elif d == 0 and s.startswith(":=", q):
            return q
    return -1


def _rel_sides(T: str):
    """(lhs, op, rhs) of T's one top-level relation, else None."""
    d, hits = 0, []
    q = 0
    while q < len(T):
        ch = T[q]
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
        elif d == 0:
            for op in REL_OPS:
                if T.startswith(op, q):
                    nxt = T[q + len(op):q + len(op) + 1]
                    prv = T[q - 1:q] if q else ""
                    if op in ("=", "<", ">") and (nxt in "=>|" or prv in "<>:=!≤≥"):
                        break
                    hits.append((q, op)); q += len(op) - 1
                    break
        q += 1
    if len(hits) != 1:
        return None
    q, op = hits[0]
    return T[:q], op, T[q + len(op):]


def _ascml(B: _B) -> list[tuple]:
    """Sites [(start, end, scope_end, [(text, note)])] of rule ascml."""
    s = B.s
    out = []
    for k in range(len(B.ls)):
        line = B.text_line(k)
        m = HAVE_RE.match(line)
        if not m or B.mask[B.lstart(k) + m.start(4)]:
            continue
        col = len(m.group(1)) + len(m.group(2))
        ext = B.extent_end(k, col)
        t0 = B.lstart(k) + m.end()          # after the `:`
        asg = _top_assign(s, t0, ext, B.mask)
        if asg < 0:
            continue
        T = s[t0:asg]
        rhs_a = asg + 2
        rhs = s[rhs_a:ext]
        multi_T = "\n" in T.strip()
        rhs_next = rhs.strip() != "" and s[rhs_a:].lstrip(" \t").startswith("\n")
        prefixed = bool(m.group(2) or m.group(3))
        scope_end = B.block_end(k, col)
        head_a = B.lstart(k) + m.start(5) + len(m.group(5))   # after the name
        alts = []
        r = rhs.strip()
        mb = re.match(r"by[ \t]+exact[ \t]+", rhs.lstrip(" \t"))
        if mb and not _has_top(rhs, ";") and "<;>" not in rhs:
            e_a = rhs_a + (len(rhs) - len(rhs.lstrip(" \t"))) + mb.end()
            if ext <= B.lend(k):
                e = s[e_a:ext]
                alts.append((head_a, asg, " ", "drop-by-type", ((rhs_a, e_a, " "),), (asg, ext)))
                alts.append((rhs_a, e_a, " ", "drop-by", (), ()))
        elif re.match(r"by[ \t]*(?:--[^\n]*)?\n", rhs.lstrip(" \t")):
            # `:= by` + a block of one `exact e` line (e may continue deeper)
            k1 = B.next_nonblank(B.line(rhs_a))
            if k1 is not None and B.lstart(k1) < ext:
                bcol = B.indent(k1)
                sib = [j for j in range(k1 + 1, B.line(max(ext - 1, 0)) + 1) if not B.blank(j) and B.indent(j) <= bcol]
                tl = B.text_line(k1)
                me = re.match(r"^[ \t]*exact[ \t]+", tl)
                if me and not sib and ";" not in tl and bcol > col:
                    e_a = B.lstart(k1) + me.end()
                    e = s[e_a:ext]
                    alts.append((head_a, asg, " ", "drop-block-type", ((rhs_a, e_a, " "),), (asg, ext)))
                    alts.append((rhs_a, e_a, " ", "drop-block", (), ()))
        elif r and (multi_T or rhs_next or prefixed) and not re.match(r"(?:by|fun|λ|⟨|\.|show|\?|_\b|←|calc)", r):
            alts.append((head_a, asg, " ", "drop-type", (), (asg, ext)))
            rs = _rel_sides(T)
            if rs and not re.match(r"\s*[¬" + BINDER_SYMS + "]", T):
                lhs, op, rhs_t = (re.sub(r"\s+", " ", x).strip() for x in rs)
                n_t = count_tokens(T.replace("\n", " "))
                # `_ R _`, then one side kept (the other side's unification may need it): only spellings that save tokens
                seen_h = set()
                for hole, note in ((f" _ {op} _ ", "typehole"), (f" {lhs} {op} _ ", "typehole-l"), (f" _ {op} {rhs_t} ", "typehole-r")):
                    if lhs and rhs_t and count_tokens(hole) < n_t and hole not in seen_h:
                        seen_h.add(hole)
                        alts.append((t0, asg, hole, note, (), (asg, ext)))
        if alts:
            out.append((B.lstart(k), ext, scope_end, alts))
    return out


def _parse_binders(bs: str):
    """[(names, type or None)] of a ∀ binder list (the text between `∀` and its comma), else None (implicit / instance / predicate
    binders, patterns)."""
    groups = []
    q, n = 0, len(bs)
    while q < n:
        while q < n and bs[q].isspace():
            q += 1
        if q >= n:
            break
        if bs[q] == "(":
            d, r = 0, q
            while r < n:
                if bs[r] in OPEN:
                    d += 1
                elif bs[r] in CLOSE:
                    d -= 1
                    if d == 0:
                        break
                r += 1
            if r >= n:
                return None
            inner = bs[q + 1:r]
            c = _top_colon(inner)
            if c < 0:
                return None
            names = inner[:c].split()
            if not names or not all(re.fullmatch(IDC, x) for x in names):
                return None
            groups.append((names, inner[c + 1:].strip()))
            q = r + 1
            continue
        if bs[q] in "{[⦃⟨":
            return None
        mm = re.match(IDC, bs[q:])
        if not mm:
            return None
        rest = bs[q + mm.end():].lstrip()
        if rest.startswith(":") and not rest.startswith(":="):
            # trailing `x y : T` group: the untyped names just before belong to it
            names = [mm.group(0)]
            ty = rest[1:].strip()
            while groups and groups[-1][1] is None and len(groups[-1][0]) == 1:
                names.insert(0, groups.pop()[0][0])
            groups.append((names, ty))
            return groups
        if rest and not re.match(r"[^\W\d]|\(|_", rest):
            return None   # a binder predicate (`x ∈ s`, `x > 0`, ...)
        groups.append(([mm.group(0)], None))
        q = q + mm.end()
    return groups or None


def _top_colon(s: str) -> int:
    d = 0
    for q, ch in enumerate(s):
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
        elif d == 0 and ch == ":" and s[q + 1:q + 2] != "=":
            return q
    return -1


def _forall_split(T: str):
    """(binder text, body P) of a type `∀ binders, P`, else None."""
    t = T.strip()
    if not t.startswith("∀"):
        return None
    d = 0
    for q in range(1, len(t)):
        ch = t[q]
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
        elif d == 0 and ch == ",":
            return t[1:q], t[q + 1:]
    return None


def _peel(groups, names):
    """(peeled groups with the given names, leftover names) peeling whole groups in order; None when nothing peels."""
    peeled, i = [], 0
    for g in groups:
        k = len(g[0])
        if i + k > len(names):
            break
        new = names[i:i + k]
        if any(x == "_" for x in new):
            break
        peeled.append((g, new))
        i += k
    if not peeled:
        return None
    return peeled, names[i:]


def _render_binders(peeled):
    """(binder text, renaming) of the peeled groups with their new names; None on a capture (a new name already in a later type)."""
    parts, ren = [], {}
    for (old, ty), new in peeled:
        if ty is not None and ren:
            ty = _rename_words(ty, ren)
            if ty is None:
                return None
        for o, n in zip(old, new):
            if o != n:
                ren[o] = n
        parts.append(" ".join(new) if ty is None else f"({' '.join(new)} : {ty})")
    return " ".join(parts), ren


def _rename_words(t: str, ren: dict) -> str | None:
    for o, n in ren.items():
        if _occurrences(t, n):
            return None
    out = t
    for o, n in ren.items():
        occ = _occurrences(out, o)
        for p in reversed(occ):
            out = out[:p] + n + out[p + len(o):]
    return out


def _bind_type(groups, peeled, rest_T: str, ren: dict) -> str | None:
    remaining = groups[len(peeled):]
    newT = rest_T if not remaining else ("∀ " + " ".join(" ".join(n) if t is None else f"({' '.join(n)} : {t})" for n, t in remaining)
                                         + ", " + rest_T)
    return _rename_words(newT, ren) if ren else newT


def _bindhave(B: _B) -> list[tuple]:
    """Sites [(start, end, scope_end, [(text, note)])] of rule bindhave."""
    s = B.s
    out = []
    for k in range(len(B.ls)):
        line = B.text_line(k)
        m = HAVE_RE.match(line)
        if not m or B.mask[B.lstart(k) + m.start(4)]:
            continue
        col = len(m.group(1)) + len(m.group(2))
        ext = B.extent_end(k, col)
        t0 = B.lstart(k) + m.end()
        asg = _top_assign(s, t0, ext, B.mask)
        if asg < 0:
            continue
        fs = _forall_split(s[t0:asg])
        if not fs:
            continue
        groups = _parse_binders(fs[0])
        if not groups:
            continue
        rest_T = fs[1].strip()
        rhs_a = asg + 2
        rhs = s[rhs_a:ext]
        name_end = B.lstart(k) + m.start(5) + len(m.group(5))
        mf = re.match(r"[ \t]*(?:fun[ \t]+|λ[ \t]*)((?:" + IDC + r"[ \t]+)*" + IDC + r")[ \t]*(?:=>|↦)[ \t]*", rhs)
        mb = re.match(r"[ \t]*by[ \t]*\n", rhs)
        if mf:
            pr = _peel(groups, mf.group(1).split())
            if not pr:
                continue
            peeled, left = pr
            rb = _render_binders(peeled)
            if rb is None:
                continue
            bt, ren = rb
            newT = _bind_type(groups, peeled, rest_T, ren)
            if newT is None:
                continue
            lam = ("fun " + " ".join(left) + " => ") if left else ""
            e = rhs[mf.end():]
            sep = "" if re.match(r"[ \t]*\n", e) and not lam else " "
            out.append((B.block_end(k, col), [(name_end, rhs_a + mf.end(), f" {bt} : {newT} :={sep}{lam}", "fun", ())]))
        elif mb:
            k1 = B.next_nonblank(B.line(rhs_a))
            if k1 is None or B.lstart(k1) >= ext or B.lend(k1) >= ext:
                continue
            mi = re.match(r"^([ \t]*)intro[ \t]+((?:" + IDC + r"[ \t]*)+)$", B.text_line(k1))
            if not mi:
                continue
            pr = _peel(groups, mi.group(2).split())
            if not pr:
                continue
            peeled, left = pr
            rb = _render_binders(peeled)
            if rb is None:
                continue
            bt, ren = rb
            newT = _bind_type(groups, peeled, rest_T, ren)
            if newT is None:
                continue
            intro_line = (mi.group(1) + "intro " + " ".join(left) + "\n") if left else ""
            out.append((B.block_end(k, col), [(name_end, asg + 2, f" {bt} : {newT} :=", "intro",
                                               ((B.lstart(k1), B.lend(k1) + 1, intro_line),))]))
    return out


LAM_RE = re.compile(r"(?<![\w'.])(?:fun[ \t]+|λ[ \t]*)(" + IDC + r"(?:[ \t]+" + IDC + r")*)[ \t]*(?:=>|↦)[ \t]*")
REFL = (("le_refl", "le_rfl"), ("Eq.refl", "rfl"), ("Iff.refl", "Iff.rfl"), ("HEq.refl", "HEq.rfl"))


def _lam_end(B: _B, a: int) -> int:
    """End (exclusive) of a lambda body starting at a: the first depth-0 closing bracket or comma, or the end of the statement."""
    s = B.s
    k0 = B.line(a)
    end_stmt = B.extent_end(k0, B.content_col(k0))
    d, q = 0, a
    while q < end_stmt:
        if B.mask[q]:
            q += 1; continue
        ch = s[q]
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            if d == 0:
                return q
            d -= 1
        elif d == 0 and (ch == "," or s.startswith("<;>", q) or ch == ";"):
            return q
        q += 1
    return end_stmt


def _app_chain(t: str) -> bool:
    """t is an application of plain arguments: identifiers / numbers / bracket groups, no operator."""
    t = t.strip()
    if not t or "\n" in t:
        return False
    q, n, d = 0, len(t), 0
    toks = []
    cur = ""
    for ch in t:
        if ch in OPEN:
            if d == 0 and cur.strip():
                toks.append(cur.strip()); cur = ""
            d += 1; cur += ch
        elif ch in CLOSE:
            d -= 1; cur += ch
            if d == 0:
                toks.append(cur.strip()); cur = ""
        elif ch == " " and d == 0:
            if cur.strip():
                toks.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        toks.append(cur.strip())
    if d != 0 or not toks:
        return False
    for x in toks:
        if _wrapped(x):
            continue
        if not re.fullmatch(r"@?[\w'.!?₀-₉]+", x) or x in TERM_KW or x in ("fun", "λ"):
            return False
    return bool(re.match(r"@?" + IDC, toks[0]))


def _compose(body: str, x: str):
    """`F (G x)` / `F $ G x` (nested) -> [F, G, ...] for `F ∘ G ∘ ..`, else None."""
    chain = []
    cur = body.strip()
    while True:
        m = re.fullmatch(r"(.*?)[ \t]*\$[ \t]*(.*)", cur, re.S)
        if m and _app_chain(m.group(1)) and not _occurrences(m.group(1), x):
            chain.append(m.group(1).strip()); cur = m.group(2).strip(); continue
        if cur.endswith(")"):
            d = 0
            for q in range(len(cur) - 1, -1, -1):
                if cur[q] in CLOSE:
                    d += 1
                elif cur[q] in OPEN:
                    d -= 1
                    if d == 0:
                        break
            F = cur[:q].strip()
            if F and q > 0 and cur[q] == "(" and _app_chain(F) and not _occurrences(F, x):
                chain.append(F); cur = cur[q + 1:-1].strip(); continue
        break
    m = re.fullmatch(r"(.*\S)[ \t]+" + re.escape(x), cur)
    if not m or not chain or not _app_chain(m.group(1)) or _occurrences(m.group(1), x):
        return None
    chain.append(m.group(1).strip())
    return chain


def _bundle(B: _B, body_start_newline: bool) -> list[tuple]:
    """Sites [(start, end, [(text, note)])] of rule bundle."""
    s = B.s
    out = []
    for m in LAM_RE.finditer(s):
        a = m.start()
        if B.mask[a]:
            continue
        names = m.group(1).split()
        e_a = m.end()
        e_b = _lam_end(B, e_a)
        e = s[e_a:e_b].rstrip()
        e_b = e_a + len(e)
        if not e or "\n" in e:
            continue
        wrapped = a > 0 and s[a - 1] == "(" and B.pairs.get(a - 1) == e_b + (len(s[e_b:]) - len(s[e_b:].lstrip(" \t")))
        k0 = B.line(a)
        if len(names) == 1:
            x = names[0]
            if e.strip() == x:
                if wrapped:
                    out.append((a - 1, B.pairs[a - 1] + 1, [("id", "id")]))
                elif _terminal(B, e_b, k0):
                    out.append((a, e_b, [("id", "id")]))
                continue
            ch = _compose(e, x)
            if ch:
                comp = " ∘ ".join(ch)
                if wrapped:
                    out.append((a - 1, B.pairs[a - 1] + 1, [(f"({comp})", "comp")]))
                elif _terminal(B, e_b, k0):
                    if _term_start(B, a):
                        out.append((a, e_b, [(comp, "comp")]))
                    else:
                        out.append((a, e_b, [(f"({comp})", "comp")]))
                continue
        if wrapped and all(re.fullmatch(IDC, x) for x in names) and len(set(names)) == len(names):
            # (fun x y => e) -> (e[·/x, ·/y]): each binder once, in order, at e's bracket depth 0, no nested binder / cdot
            if re.search(r"(?<![\w'])(?:fun|by|match|let|have|if)(?![\w'])|[λ·$" + BINDER_SYMS + "]", e):
                continue
            pos, ok = [], True
            for x in names:
                occ = _occurrences(e, x)
                if len(occ) != 1:
                    ok = False; break
                p = occ[0]
                d = 0
                for ch in e[:p]:
                    if ch in OPEN:
                        d += 1
                    elif ch in CLOSE:
                        d -= 1
                if d != 0 or e[p + len(x):p + len(x) + 1] == ".":
                    ok = False; break
                pos.append(p)
            if not ok or pos != sorted(pos):
                continue
            ne = e
            for x, p in sorted(zip(names, pos), key=lambda t: -t[1]):
                ne = ne[:p] + "·" + ne[p + len(x):]
            out.append((a - 1, B.pairs[a - 1] + 1, [(f"({ne})", "cdot")]))
    # `f $ a` ending a term -> `f a`
    for m in re.finditer(r"[ \t]\$[ \t]+([\w'.!?₀-₉]+)", s):
        a = m.start()
        if B.mask[a + 1]:
            continue
        atom = m.group(1)
        if count_tokens(atom) != 1 or atom in TERM_KW or atom in ("fun", "λ", "by"):
            continue
        b = m.end()
        if b < len(s) and (_ident_char(s[b]) or s[b] in ".("):
            continue
        k0 = B.line(a)
        if not _terminal(B, b, k0) or not _app_left(B, a):
            continue
        out.append((a, b, [(" " + atom, "dollar-atom")]))
    # nomatch
    for m in re.finditer(r"(?<![\w'.])False\.elim(?![\w'.])", s):
        a = m.start()
        if B.mask[a] or not _term_start(B, a):
            continue
        q = m.end()
        while q < len(s) and s[q] in " \t":
            q += 1
        if q < len(s) and s[q] == "(" and q in B.pairs:
            inner = s[q + 1:B.pairs[q]]; b = B.pairs[q] + 1
        elif s.startswith("$", q):
            b = _lam_end(B, q + 1); inner = s[q + 1:b].strip(); b = q + 1 + len(s[q + 1:b].rstrip())
        else:
            continue
        if not inner.strip() or "\n" in inner or not _terminal(B, b, B.line(a)):
            continue
        out.append((a, b, [(f"nomatch {inner.strip()}", "nomatch")]))
    for m in re.finditer(r"\)\.elim(?![\w'.])", s):
        c = m.start()
        if B.mask[c] or c not in B.closer:
            continue
        a = B.closer[c]
        inner = s[a + 1:c]
        b = m.end()
        if not inner.strip() or "\n" in inner or not _term_start(B, a) or not _terminal(B, b, B.line(a)):
            continue
        out.append((a, b, [(f"nomatch {inner.strip()}", "nomatch")]))
    # refl spellings
    for old, new in REFL:
        for m in re.finditer(r"(?<![\w'.])" + re.escape(old) + r"[ \t]+([\w'.!?₀-₉]+)(?![\w'.(])", s):
            a = m.start()
            if B.mask[a] or count_tokens(m.group(1)) != 1 or m.group(1) in TERM_KW:
                continue
            b = m.end()
            if a > 0 and s[a - 1] == "(" and B.pairs.get(a - 1) == b:
                out.append((a - 1, b + 1, [(new, "refl")]))
            elif _term_start(B, a) and (_terminal(B, b, B.line(a)) or s[b:b + 1] in " \t"):
                out.append((a, b, [(new, "refl")]))
    # a body `:=` + line break + `by` -> `:= by`
    if body_start_newline:
        mm = re.match(r"[ \t]*\n\s*by(?![\w'])", s)
        if mm:
            out.append((0, mm.end(), [(" by", "newline-by")]))
    return out


_IDA = r"(?>[^\W\d][\w'!?₀-₉]*)"
BINDER_CTX = re.compile(r"(?:(?<![\w'])fun|λ|∀|∃!?|Σ|Π|(?<![\w'])(?:have|haveI|let|intro|rintro)[ \t]+(?!\()" + _IDA + r")[ \t]*"
                        r"(?>(?:" + _IDA + r"|\([^()]*\)|\{[^{}]*\}|\[[^\[\]]*\]|⦃[^⦃⦄]*⦄)[ \t]*)*$")
INTRO_CTX = re.compile(r"(?<![\w'])(?:intro|rintro)[ \t]+(?>(?:" + _IDA + r"|\([^()]*\))[ \t]*)*$")


def _typedrop(B: _B) -> list[tuple]:
    """Sites [(start, end, scope_end, [(text, note)])] of rule typedrop: a binder's or a term's type ascription dropped, Lean infers it
    from the expected type: `(x y : T)` -> `x y` in a binder list (fun / λ / ∀ / ∃ / a have's or let's binders / intro), `(x : T)` -> `x`
    as a term (not before a projection), `λx : T =>` -> `λx =>`."""
    s = B.s
    out = []
    for i in sorted(B.pairs):
        j = B.pairs[i]
        if s[i] != "(" or B.mask[i] or "\n" in s[i:j]:
            continue
        inner = s[i + 1:j]
        c = _top_colon(inner)
        if c < 0:
            continue
        names = inner[:c].split()
        if (len(names) == 1 and re.fullmatch(r"\d+(?:\.\d+)?", names[0]) and inner[c + 1:].strip()
                and not (_ident_char(s[j + 1:j + 2]) or (s[j + 1:j + 2] and s[j + 1:j + 2] in ".⁻")) and not _pattern_pos(B, i)):
            k = B.line(i)
            out.append((i, j + 1, B.extent_end(k, B.content_col(k)), [(names[0], "num")]))
            continue
        if (not names or not all(re.fullmatch(IDC, x) and not x.startswith("λ") and x not in TERM_KW and x not in ("fun", "this")
                                  for x in names) or "_" in names or not inner[c + 1:].strip()):
            continue
        k = B.line(i)
        pre = _line_seg(_stmt_prefix(B, i))[-240:]
        after = s[j + 1:j + 2]
        sc = B.extent_end(k, B.content_col(k))
        if BINDER_CTX.search(pre) or INTRO_CTX.search(pre):
            out.append((i, j + 1, sc, [(" ".join(names), "binder")]))
            # the binder list's only group: `∀ (x y : T),` -> `∀ x y : T,`, `fun (x : T) =>` -> `λx : T =>` (a separate site: the
            # engine takes the type drop when it holds, else this one)
            q = i - 1
            while q >= 0 and s[q] in " \t":
                q -= 1
            kw = None
            if q >= 0 and s[q] in "∀∃" and not B.mask[q]:
                kw = (q, s[q])
            elif q >= 2 and s[q - 2:q + 1] == "fun" and not B.mask[q] and (q < 3 or not _ident_char(s[q - 3])):
                kw = (q - 2, "λ")
            elif q >= 0 and s[q] == "λ" and not B.mask[q]:
                kw = (q, "λ")
            if kw is not None:
                r = j + 1
                while r < len(s) and s[r] in " \t":
                    r += 1
                closer = s.startswith(",", r) if kw[1] in "∀∃" else (s.startswith("=>", r) or s.startswith("↦", r))
                ty = inner[c + 1:].strip()
                if closer and ty and "\n" not in ty:
                    if kw[1] == "λ":
                        out.append((kw[0], j + 1, sc, [("λ" + " ".join(names) + " : " + ty, "unparen")]))
                    else:
                        out.append((i, j + 1, sc, [(" ".join(names) + " : " + ty, "unparen")]))
        elif len(names) == 1 and not (_ident_char(after) or (after and after in ".⁻")) and not re.search(r"(?:obtain|rcases|cases'|match)\b[^:=]*$", pre):
            if _pattern_pos(B, i):
                continue
            out.append((i, j + 1, sc, [(names[0], "term"), ("↑" + names[0], "cast")]))
    for m in re.finditer(r"(?<![\w'])(?:∀|∃!?)[ \t]*((?:" + IDC + r"[ \t]+)*" + IDC + r")[ \t]*:(?!=)", s):
        a = m.start()
        if B.mask[a]:
            continue
        q, d, end = m.end(), 0, -1
        lim = B.lend(B.line(a))
        while q < lim:
            ch = s[q]
            if ch in OPEN:
                d += 1
            elif ch in CLOSE:
                if d == 0:
                    break
                d -= 1
            elif d == 0 and ch == ",":
                end = q; break
            q += 1
        if end < 0 or not s[m.end():end].strip():
            continue
        k = B.line(a)
        out.append((m.start(1) + len(m.group(1)), end, B.extent_end(k, B.content_col(k)), [("", "qtype")]))
    for m in re.finditer(r"(?<![\w'])(?:fun[ \t]+|λ[ \t]*)((?:" + IDC + r"[ \t]+)*" + IDC + r")[ \t]*:(?!=)", s):
        a = m.start()
        if B.mask[a]:
            continue
        q = m.end()
        d, end = 0, -1
        lim = B.lend(B.line(a))
        while q < lim:
            ch = s[q]
            if ch in OPEN:
                d += 1
            elif ch in CLOSE:
                if d == 0:
                    break
                d -= 1
            elif d == 0 and (s.startswith("=>", q) or ch == "↦"):
                end = q; break
            q += 1
        if end < 0:
            continue
        k = B.line(a)
        out.append((a + len(m.group(0)) - len(m.group(0).lstrip()) if False else m.start(1) + len(m.group(1)), end, B.extent_end(k, B.content_col(k)),
                    [(" ", "lamtype")]))
    return out


# dotcall: generalized field notation from the locals' type heads (a probe compile's trace_state contexts, the statement's binders and
# the proof's `have` types). Notation and relation heads map to the constants Lean's field notation resolves.
DOT_RE = re.compile(r"(?<![\w.'@₀-₉!?])((?:[^\W\d][\w'₀-₉!?]*\.)+)([^\W\d][\w'₀-₉!?]*)[ \t]+([^\W\d][\w'₀-₉!?]*)(?![\w.'₀-₉!?])")
REL_HEAD = (("↔", "Iff"), ("∨", "Or"), ("∧", "And"), ("≠", "Ne"), ("≤", "LE.le"), ("≥", "GE.ge"), ("∉", "Not"), ("∈", "Membership.mem"),
            ("⊆", "HasSubset.Subset"), ("⊂", "HasSSubset.SSubset"), ("∣", "Dvd.dvd"), ("=", "Eq"), ("<", "LT.lt"), (">", "GT.gt"))   # leak-ok: Lean core relation heads (notation -> constant), no row's lemma
TYPE_ALIAS = {"ℕ": "Nat", "ℤ": "Int", "ℚ": "Rat", "ℝ": "Real", "ℂ": "Complex", "Prop": None, "Type": None, "Sort": None}
HYP_RE = re.compile(r"^([^\s:⊢][^:⊢]*?) : (.*)$")


def _top_ops(T: str):
    """[(offset, op)] of the relation / connective symbols at bracket depth 0 of T (binder bodies included: callers cut them)."""
    d, out, q = 0, [], 0
    while q < len(T):
        ch = T[q]
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
        elif d == 0:
            for op, _h in REL_HEAD:
                if T.startswith(op, q):
                    nxt = T[q + 1:q + 2]
                    prv = T[q - 1:q] if q else ""
                    if op in ("=", "<", ">") and (nxt in "=>ᶠ[" and nxt or prv in "<>:=!≤≥-|"):
                        break
                    out.append((q, op))
                    break
            if T.startswith("→", q):
                out.append((q, "→"))
        q += 1
    return out


def type_head(T: str):
    """The constant Lean's field notation would look under for a local of type T (pretty-printed), else None."""
    T = re.sub(r"\s+", " ", T).strip()
    if not T or T.startswith(("∀", "fun", "λ", "Π", "(", "{", "[", "⦃", "↑", "Type", "Sort")):
        return None
    if T.startswith("∃"):
        return "Exists" if not T.startswith("∃!") else None
    ops = _top_ops(T)
    if any(o == "→" for _, o in ops):
        return None
    neg = T.startswith("¬")
    for op, h in REL_HEAD:            # the loosest connective first (REL_HEAD's order); `¬` binds looser than a relation
        if any(o == op for _, o in ops):
            if neg and op not in ("↔", "∨", "∧"):
                return "Not"
            return h
    if neg:
        return "Not"
    d = 0
    for ch in T:                      # an application only: any other operator at depth 0 is notation we do not map
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d -= 1
        elif d == 0 and not (ch.isalnum() or ch in " _.'!?@·" or "₀" <= ch <= "₉"):
            return None
    m = re.match(r"@?([^\W\d][\w'₀-₉!?]*(?:\.[^\W\d][\w'₀-₉!?]*)*)", T)
    if not m:
        return None
    w = m.group(1)
    if T[m.end():m.end() + 1] == "[":
        return None
    if "." in w and w[0].islower():   # field-notation display `s.Nonempty` of `Ns.Nonempty s`: only the last component is known
        return "?." + w.rsplit(".", 1)[1]
    return TYPE_ALIAS.get(w, w) if w in TYPE_ALIAS else w


def parse_contexts(texts) -> dict:
    """{local name: {type heads}} from trace_state goal displays (hypothesis lines `x y : T`, T continued on deeper lines)."""
    out: dict = {}
    for t in texts:
        lines = str(t).split("\n")
        k = 0
        while k < len(lines):
            ln = lines[k]
            m = HYP_RE.match(ln)
            if not m or ln.startswith((" ", "case ")):
                k += 1; continue
            names = m.group(1).split()
            T = m.group(2)
            k += 1
            while k < len(lines) and lines[k].startswith(" ") and not lines[k].lstrip().startswith("⊢"):
                T += " " + lines[k].strip(); k += 1
            T = re.split(r" := ", T, maxsplit=1)[0]
            if not all(re.fullmatch(IDC, x) for x in names):
                continue
            h = type_head(T)
            for x in names:
                out.setdefault(x, set()).add(h)
    return out


def _decl_binder_types(statement: str, body: str) -> dict:
    """{name: {type heads}} of the statement's explicit / implicit binders `(x y : T)` and the proof's `have x : T` lines."""
    out: dict = {}
    for m in re.finditer(r"[({⦃]\s*((?:" + IDC + r"\s+)*" + IDC + r")\s*:(?!=)", statement):
        a = m.end()
        d, q = 0, a
        while q < len(statement):
            ch = statement[q]
            if ch in OPEN:
                d += 1
            elif ch in CLOSE:
                if d == 0:
                    break
                d -= 1
            q += 1
        h = type_head(statement[a:q])
        for x in m.group(1).split():
            out.setdefault(x, set()).add(h)
    for ln in body.split("\n"):
        m = HAVE_RE.match(ln)
        if m:
            t = ln[m.end():]
            c = _top_assign(t, 0, len(t), [False] * len(t))
            out.setdefault(m.group(5), set()).add(type_head(t[:c] if c >= 0 else t))
    return out


def _ns_match(ns: str, head: str | None) -> bool:
    if not head:
        return False
    if head.startswith("?."):
        return ns.rsplit(".", 1)[-1] == head[2:]
    return ns == head or ns.endswith("." + head) or head.endswith("." + ns)


def _dotcall_raw(B: _B) -> list:
    """[(match)] of `Ns.f x` candidates (x a plain identifier, not a projection), before any type knowledge."""
    out = []
    for m in DOT_RE.finditer(B.s):
        if B.mask[m.start()]:
            continue
        x = m.group(3)
        if x in TERM_KW or x in ("fun", "λ", "by", "at", "with", "then", "else", "using", "from"):
            continue
        out.append(m)
    return out


ALIAS_RE = re.compile(r"(?<![\w.'@₀-₉!?])([a-z][\w'₀-₉!?]*_[\w'₀-₉!?]*)[ \t]+([^\W\d][\w'₀-₉!?]*)(?![\w.'₀-₉!?])")
ALIAS_MARK = "LRALEXALIAS"
ALIAS_UNFOLD = {"GT.gt": "LT.lt", "GE.ge": "LE.le"}   # reducible heads field notation sees through


def _alias_raw(B: _B, types: dict | None) -> list:
    """[(match, head)] of `c x ..`: c a root name (lower case, with `_`), x a local whose one known type head is a constant."""
    if not types:
        return []
    out = []
    for m in ALIAS_RE.finditer(B.s):
        if B.mask[m.start()]:
            continue
        c, x = m.group(1), m.group(2)
        if c in TERM_KW or x in TERM_KW or c in ("by_cases", "by_contra", "fun_cases", "fun_induction", "simp_all", "norm_num",
                                                   "field_simp", "simp_rw", "nth_rw", "nth_rewrite", "split_ifs", "push_cast"):
            continue
        if c in types:          # a local applied to x, not a library constant
            continue
        ls = B.s[B.lstart(B.line(m.start())):m.start()]
        if re.fullmatch(r"\s*(?:[·.]\s+)?", ls) or re.search(r"(?:<;>|;)\s*$", ls):
            continue                # a tactic at the start of its line (`linear_combination h`), not an application
        hs = types.get(x)
        if not hs or len(hs) != 1:
            continue
        h = next(iter(hs))
        if not h or h.startswith("?."):
            continue
        out.append((m, h))
    return out


def alias_text(pairs) -> str:
    """The env query listing, for each (type head H, root constant c), the constants `H.f` whose type is c's type (Mathlib's
    `alias H.f := c` and any same-statement lemma in H's namespace): `LRALEXALIAS <H> <c> <H.f>` lines."""
    lst = ", ".join(f"({K.lean_str(h)}, {K.lean_str(c)})" for h, c in sorted(pairs))
    return ("theorem lraLexAliasDummy : True := trivial\n"   # takes a doc comment / attribute the row's file prefix may end with
            "set_option maxHeartbeats 0 in\n"
            "#eval show Lean.CoreM Unit from do\n"
            "  let env ← Lean.getEnv\n"
            f"  let raw : List (String × String) := [{lst}]\n"
            "  let tg : Array (Lean.Name × Lean.Name × Lean.Expr) := raw.foldl (fun t (h, c) =>\n"
            "    match env.find? c.toName with\n"
            "    | some ci => t.push (h.toName, c.toName, ci.type)\n"
            "    | none => t) #[]\n"
            "  let out := env.constants.fold (init := (#[] : Array String)) fun acc n ci =>\n"
            "    tg.foldl (fun a (h, c, ty) => if n.getPrefix == h && n != c && ci.type == ty then\n"
            f"      a.push s!\"{ALIAS_MARK}\\t{{h}}\\t{{c}}\\t{{n}}\" else a) acc\n"
            "  Lean.logInfo (Lean.toMessageData (String.intercalate \"\\n\" out.toList))\n")


def parse_aliases(messages) -> dict:
    """{(H, c): [field names f]} from the alias query's messages (one-component fields only)."""
    out: dict = {}
    for m in messages or []:
        for ln in K.msg_text(m).split("\n"):
            p = ln.strip().split("\t")
            if len(p) == 4 and p[0] == ALIAS_MARK and p[3].startswith(p[1] + "."):
                f = p[3][len(p[1]) + 1:]
                if f and "." not in f and re.fullmatch(IDC, f):
                    out.setdefault((p[1], p[2]), [])
                    if f not in out[(p[1], p[2])]:
                        out[(p[1], p[2])].append(f)
    for k in out:
        out[k].sort(key=lambda f: (len(f), f))
    return out


def _dotcall(B: _B, types: dict | None, aliases: dict | None = None) -> list[tuple]:
    """Sites [(start, end, [(text, note)])] of rule dotcall: `Ns.f x ..` -> `x.f ..` where x is a local whose every known type head
    is Ns (Lean's generalized field notation passes x as the first explicit argument of that type: only the first argument is moved);
    `(Ns.f x)` -> `x.f` (one lexer token: the parentheses go, also before a projection `.g`)."""
    if not types:
        return []
    s = B.s
    out = []
    for m in _dotcall_raw(B):
        ns, f, x = m.group(1)[:-1], m.group(2), m.group(3)
        hs = types.get(x)
        if not hs or len(hs) != 1:
            continue
        h = next(iter(hs))
        if not _ns_match(ns, h):
            continue
        a, b = m.start(), m.end()
        new = f"{x}.{f}"
        if a > 0 and s[a - 1] == "(" and B.pairs.get(a - 1) is not None:
            c = B.pairs[a - 1]
            if s[b:c].strip() == "":
                pre = s[a - 2] if a >= 2 else " "
                post = s[c + 1] if c + 1 < len(s) else " "
                lead = " " if (_ident_char(pre) or pre in ")]}⟩") else ""
                trail = " " if (_ident_char(post) or post in "([{⟨") else ""
                out.append((a - 1, c + 1, [(lead + new + trail, "paren"), (f"({new})", "dot")]))
                continue
        out.append((a, b, [(new, "dot")]))
    seen = {(a, b) for a, b, _ in out}
    for m, h in (_alias_raw(B, types) if aliases else []):
        fs = aliases.get((h, m.group(1))) or aliases.get((ALIAS_UNFOLD.get(h, h), m.group(1)))
        if not fs:
            continue
        x = m.group(2)
        a, b = m.start(), m.end()
        if (a, b) in seen:
            continue
        alts = [(f"{x}.{f}", "alias") for f in fs[:2]]
        if a > 0 and s[a - 1] == "(" and B.pairs.get(a - 1) is not None and s[b:B.pairs[a - 1]].strip() == "":
            c = B.pairs[a - 1]
            pre = s[a - 2] if a >= 2 else " "
            post = s[c + 1] if c + 1 < len(s) else " "
            lead = " " if (_ident_char(pre) or pre in ")]}⟩") else ""
            trail = " " if (_ident_char(post) or post in "([{⟨") else ""
            out.append((a - 1, c + 1, [(lead + t + trail, "alias-paren") for t, _n in alts] + [(f"({t})", n) for t, n in alts]))
        else:
            out.append((a, b, alts))
    return out


PROBE_NO_BEFORE = re.compile(r"^\s*(?:\||<;>|[)\]}⟩,]|then\b|else\b|with\b|at\b|using\b|from\b|fun\b|λ|_\s|calc\b|[-+*/=<>≤≥≠∧∨→↔∘$])")
PROBE_OPEN_ARROW = re.compile(r"^\s*(?:case\b|next\b|\|)")
PROBE_INTRO = re.compile(r"(?<![\w'.])(?:intro|intros|rintro|obtain|rcases|cases|cases'|induction|induction'|have|haveI|let|set|by_cases|"
                         r"by_contra!?|choose|generalize|ext|funext|use|next|case|specialize|replace|subst|match|fun_induction|"
                         r"fun_cases|lift|peel|filter_upwards|constructor|refine|exists|unhygienic|split_ifs|split)(?![\w'!?])|=>")
PROBE_MAX = 80                # trace_state insertions per probe at most


def _probe_body(body: str) -> str | None:
    """The body with `trace_state` before every tactic that starts a line at its tactic block's column (Lean's tactic blocks are
    column-sensitive: such a line is a new tactic unless the previous line is unfinished), never before the first tactic of a block,
    an alternative `|`, a combinator or a continuation. A block opens after a line ending in `by`, after a `case` / `next` / `|` line
    ending in `=>`, and at a bullet's content column. None when the body is not a tactic block."""
    B = _B(body)
    s = body
    if not re.match(r"\s*by\b", s):
        return None
    lines = s.split("\n")
    out, stack = [], []
    pending, prev = True, None   # the body's own `by` opens the outermost block
    since, n_tr = "", 0          # text since the last trace (a trace only after a line that may bind names), traces so far
    for k, ln in enumerate(lines):
        if B.blank(k):
            out.append(ln); continue
        a = B.lstart(k)
        t = "".join(" " if B.mask[a + q] else ch for q, ch in enumerate(ln)).rstrip()
        ind = len(t) - len(t.lstrip(" "))
        while stack and stack[-1] > ind:
            stack.pop()
        if pending and k > 0 and (not stack or ind > stack[-1]):
            stack.append(ind)
            pending = False
            fresh = True
        else:
            fresh = False
        if k > 0 and not fresh and stack and ind == stack[-1] and prev is not None and not PROBE_NO_BEFORE.match(t) \
                and (_ident_char(prev[-1:]) or prev[-1:] in ")]}⟩_") and not re.search(r"(?<![\w'.])(?:by|with|at|using|from|then|else|do|fun|λ)$", prev) \
                and PROBE_INTRO.search(since) and n_tr < PROBE_MAX:
            out.append(" " * ind + "trace_state")
            n_tr += 1
            since = ""
        out.append(ln)
        since += " " + t
        if k > 0 or t.strip() != "by":
            if re.search(r"(?<![\w'.])by$", t) or (t.endswith("=>") and PROBE_OPEN_ARROW.match(t)):
                pending = True
            mb = re.match(r"^(\s*)[·.][ \t]+(?=\S)", t)
            if mb and stack and ind == stack[-1]:
                stack.append(len(mb.group(0)))
        if k == 0 and t.strip() != "by":
            pending = True   # `by tac` on the `:=` line: the block goes on at the next line's column
        prev = t.strip()
    return "\n".join(out)


# hyplist: local hypotheses in a tactic's lemma list. simp-family lists with two or more local hypotheses -> `*` (all hypotheses);
# linarith / nlinarith / simp_all / grind already use every local hypothesis -> the local names are dropped (an emptied list goes).
HYPLIST_RE = re.compile(r"(?<![\w'.])(simp_all|simp_arith|simpa|simp|dsimp|norm_num|field_simp|linarith|nlinarith|grind)!?"
                        r"((?:[ \t]+only)?)[ \t]*(\[)")
PROP_HEADS = {None, "Eq", "Ne", "LE.le", "LT.lt", "GE.ge", "GT.gt", "Not", "And", "Or", "Iff", "Membership.mem", "HasSubset.Subset",
              "HasSSubset.SSubset", "Dvd.dvd", "Exists"}   # leak-ok: Lean core relation heads (notation -> constant), no row's lemma
USES_ALL = ("linarith", "nlinarith", "simp_all", "grind")


def _hyplist_raw(B: _B) -> list:
    """[(tactic, `[` offset, `]` offset, items)] of lemma lists with an identifier item."""
    out = []
    for m in HYPLIST_RE.finditer(B.s):
        a = m.start(3)
        if B.mask[m.start()] or a not in B.pairs:
            continue
        b = B.pairs[a]
        inner = B.s[a + 1:b]
        if "\n" in inner:
            continue
        items = [x.strip() for x in _split_top(inner)]
        if any(re.fullmatch(IDC, x) for x in items):
            out.append((m.group(1), a, b, items))
    return out


def _hyplist(B: _B, types: dict | None) -> list[tuple]:
    """Sites [(start, end, [(text, note)])] of rule hyplist (a list's local hypotheses: the names the probe saw in a goal display or the
    declaration binds, every known type head a proposition's or unknown)."""
    if not types:
        return []
    s = B.s
    out = []
    for tac, a, b, items in _hyplist_raw(B):
        loc = [x for x in items if re.fullmatch(IDC, x) and types.get(x) and types[x] <= PROP_HEADS]
        rest = [x for x in items if x not in loc]
        if not loc or any(x.startswith(("-", "←", "<-")) for x in loc):
            continue
        if tac in USES_ALL:
            if rest:
                out.append((a, b + 1, [("[" + ", ".join(rest) + "]", "drop")]))
            else:
                q = a
                while q > 0 and s[q - 1] in " \t":
                    q -= 1
                out.append((q, b + 1, [("", "drop")]))
            continue
        if "*" in rest:
            out.append((a, b + 1, [("[" + ", ".join(rest) + "]", "star-dup")]))
        elif len(loc) >= 2:
            out.append((a, b + 1, [("[" + ", ".join(["*"] + rest) + "]", "star")]))
    return out


def probe_types(proof: str, statement: str, run) -> dict | None:
    """One probe compile (the env query): the proof with `trace_state` before its tactic steps (_probe_body); the goal displays of its
    messages (traces and error goals alike) give each local's type head, merged with the statement's and the proof's declared types.
    None when the proof does not start with the statement."""
    hb = K.head_body(proof, statement)
    if hb is None:
        return None
    head, body = hb
    out = _decl_binder_types(statement, body)
    nb = _probe_body(body)
    if nb is None:
        return out
    r = run((head + nb).rstrip() + "\n", None)
    texts = [str(m.get("data", "")) for m in (getattr(r, "messages", None) or [])
             if isinstance(m, dict) and "⊢" in str(m.get("data", ""))]
    for k, v in parse_contexts(texts).items():
        out.setdefault(k, set()).update(v)
    return out


# ------------------------------------------------------------------------------------------------------------------------- edits
def _apply(body: str, edits) -> tuple[str, list]:
    """(new body, [(edit, new start, new end) per hunk]); the edits' hunks must not overlap."""
    hs = sorted(((a, b, t, e) for e in edits for (a, b, t) in e.all_hunks()), key=lambda x: x[0])
    out, pos, spans, delta = [], 0, [], 0
    for a, b, t, e in hs:
        out.append(body[pos:a])
        ns = a + delta
        out.append(t)
        spans.append((e, ns, ns + len(t)))
        delta += len(t) - (b - a)
        pos = b
    out.append(body[pos:])
    return "".join(out), spans


def _newpos(edits, p: int) -> int:
    """Offset p of the old body in the new body (a p inside a hunk maps to that hunk's new start)."""
    d = 0
    for a, b, t in sorted((h for e in edits for h in e.all_hunks()), key=lambda h: h[0]):
        if b <= p:
            d += len(t) - (b - a)
        elif a < p:
            return a + d
        else:
            break
    return p + d


def _overlap(x: Edit, y: Edit) -> bool:
    for a, b, _ in x.all_hunks():
        for c, d, _ in y.all_hunks():
            if a < d and c < b:
                return True
            if a == b == c == d:
                return True
    if x.rule == y.rule == "emcases" and x.cap and y.cap and x.cap[0] < y.cap[1] and y.cap[0] < x.cap[1]:
        return True
    for u, v in ((x, y), (y, x)):   # a have whose type is dropped gives no expected type to a leading-dot constructor in its term
        if u.rule == "ascml" and u.cap and v.rule in ("anonctor", "bundle") and u.cap[0] <= v.start < u.cap[1]:
            return True
    return False


def sites(proof: str, statement: str, types: dict | None = None, aliases: dict | None = None) -> list[list[Edit]]:
    """Every site's spellings as Edits (body offsets), in body order; only token savers (the newline-by spelling saves on the official
    count only and rides with the others). `types` ({local: {type heads}}, probe_types) enables rule dotcall."""
    hb = K.head_body(proof, statement)
    if hb is None:
        return []
    _head, body = hb
    B = _B(body)
    t0 = count_tokens(body)
    raw = []   # (rule, scope, [(start, end, text, note, hunks, cap)])
    for a, b, alts in _anonctor(B):
        raw.append(("anonctor", b, [(a, b, t, n or "", (), ()) for t, n in alts]))
    for a, b, sc, alts in _emcases(B, statement):
        raw.append(("emcases", sc, [(a, b, t, n, h, c) for t, n, h, c in alts]))
    for a, b, sc, alts in _ascml(B):
        raw.append(("ascml", sc, [(x, y, t, n, h, c) for x, y, t, n, h, c in alts]))
    for sc, alts in _bindhave(B):
        raw.append(("bindhave", sc, [(a, b, t, n, h, ()) for a, b, t, n, h in alts]))
    for a, b, sc, alts in _typedrop(B):
        raw.append(("typedrop", sc, [(a, b, t, n, (), ()) for t, n in alts]))
    for a, b, alts in _bundle(B, not K.term_line_ok(body)):
        raw.append(("bundle", b, [(a, b, t, n, (), ()) for t, n in alts]))
    for a, b, alts in _dotcall(B, types, aliases):
        raw.append(("dotcall", b, [(a, b, t, n, (), ()) for t, n in alts]))
    for a, b, alts in _hyplist(B, types):
        raw.append(("hyplist", b, [(a, b, t, n, (), ()) for t, n in alts]))
    out = []
    for rule, sc, alts in raw:
        site = []
        for a, b, t, n, hunks, cap in alts:
            e = Edit(a, b, t, rule, 0, len(out), len(site), max(sc, b), tuple(hunks), tuple(cap), n, _bound_names(rule, B, a, b, t, n))
            if body[a:b] == t and not hunks:
                continue
            d = _local_dtok(body, e)
            if d <= 0 and n != "newline-by":
                continue
            site.append(e._replace(dtok=d, alt=len(site)))
        if site:
            out.append(site)
    out.sort(key=lambda st: (st[0].start, st[0].end))
    return [[e._replace(site=i) for e in st] for i, st in enumerate(out)]


def _bound_names(rule: str, B: _B, a: int, b: int, t: str, note: str) -> tuple:
    """The names whose later uses an edit can break (module docstring, "query": an error naming one is blamed on the edit)."""
    if rule in ("ascml", "bindhave"):
        m = HAVE_RE.match(B.text_line(B.line(a)))
        return (m.group(5),) if m else ()
    if rule == "emcases":
        m = re.match(r"by_cases[ \t]+(" + IDC + r")[ \t]*:", B.s[a:b])
        return ((m.group(1) if m else "h"), "h") if note == "cases" else ((m.group(1),) if m else ("h",))
    if rule == "typedrop":
        if note == "unparen":
            return tuple(t.split(" : ", 1)[0].lstrip("λ").split())
        if note in ("lamtype", "qtype"):
            m = re.search(r"((?:" + IDC + r"[ \t]+)*" + IDC + r")[ \t]*$", B.s[max(0, a - 120):a])
            return tuple(m.group(1).split()) if m else ()
        return tuple(t.split())
    return ()


def _local_dtok(body: str, e: Edit) -> int:
    """count_tokens saving of one edit, counted on the lines it touches (the lexer is line-local)."""
    hs = sorted(e.all_hunks(), key=lambda h: h[0])
    lo = body.rfind("\n", 0, hs[0][0]) + 1
    hi = body.find("\n", max(b for _, b, _ in hs))
    hi = len(body) if hi < 0 else hi
    seg = body[lo:hi]
    new, pos = [], lo
    for a, b, t in hs:
        new.append(body[pos:a]); new.append(t); pos = b
    new.append(body[pos:hi])
    return count_tokens(seg) - count_tokens("".join(new))


def _ctx_key(statement: str, body: str, e: Edit) -> tuple:
    B = (body.rfind("\n", 0, e.start) + 1, body.find("\n", e.end))
    lo, hi = B[0], (len(body) if B[1] < 0 else B[1])
    return (hashlib.sha256(statement.encode()).hexdigest()[:16], e.rule, body[lo:hi], e.text, tuple(e.hunks))


def _is_failed(statement, body, e) -> bool:
    with _CACHE_LOCK:
        return _ctx_key(statement, body, e) in _FAILED


def _mark_failed(statement, body, e) -> None:
    with _CACHE_LOCK:
        _FAILED.add(_ctx_key(statement, body, e))


def select(site_list: list[list[Edit]], alt_of: dict) -> list[Edit]:
    """The cheapest non-conflicting set: each live site's current spelling, largest saving first (ties: body order)."""
    cand = []
    for st in site_list:
        k = alt_of.get(st[0].site, 0)
        if k is None or k >= len(st):
            continue
        cand.append(st[k])
    cand.sort(key=lambda e: (-e.dtok, e.start))
    chosen = []
    for e in cand:
        if len(chosen) >= MAX_SITES:
            break
        if any(_overlap(e, c) for c in chosen):
            continue
        chosen.append(e)
    chosen.sort(key=lambda e: e.start)
    return chosen


# ------------------------------------------------------------------------------------------------------------------------- the query
def _decl_lines(messages, decl: str):
    """The file line of the declaration's first line, from the marker's position; None when the marker did not print."""
    n = decl.count("\n")
    for m in messages or []:
        if not isinstance(m, dict):
            continue
        if m.get("severity") == "information" and str(m.get("data", "")).strip().strip('"') == MARK:
            ln = (m.get("pos") or {}).get("line")
            if isinstance(ln, int):
                return ln - n - 1
    return None


DOT_FAIL = re.compile(r"Unknown constant|dotted identifier|Inferred this name|[Ii]nvalid constructor|type mismatch|"
                      r"[Ii]nvalid field|does not contain|expected type|[Aa]nonymous constructor")
RISKY = ("emcases", "ascml", "bindhave", "typedrop")
HYP_LINE = re.compile(r"^\s*(?:case\b.*|[^\s:][^:]*\s:\s.*|⊢.*)$")


def _msg_names(data: str) -> str:
    """An error message without its goal display (case tags, hypothesis lines `x y : T`, `⊢` lines)."""
    return "\n".join(ln for ln in data.split("\n") if not HYP_LINE.match(ln))


def localize(messages, decl: str, head_len: int, new_body: str, spans, chosen) -> tuple[set, int]:
    """({site of a blamed edit}, unexplained error count) for the errors of a joint compile (module docstring, "query").
    Three tiers; a round blames only from the first tier that blames anything (a later error is often a consequence of an earlier
    one, and the next round re-reads it). Tier 1, per error: a name an edit can break, named in the message outside its goal display,
    inside that edit's scope -> that edit; else an error on an edit's lines -> that edit (for an anonctor edit only a constructor-
    failure message); else an `unsolved goals` range holding edits -> its emcases edit for an `inl` / `inr` goal, or its only edit.
    Tier 2: the nearest scoped edit (emcases / ascml / bindhave / typedrop) before the error whose scope holds it. Tier 3: a weak
    anonctor line hit goes to the nearest scoped edit before it (else to the anonctor), an error past every scope to the nearest
    scoped edit before it, and a lone edit takes the blame."""
    first = _decl_lines(messages, decl)
    if first is None:
        return set(), -1
    starts = [0] + [i + 1 for i, ch in enumerate(decl) if ch == "\n"]
    nlines = len(starts)
    first_new = {}
    for (e, ns, ne) in spans:
        first_new.setdefault(id(e), ns)
    scopes = [(e, first_new[id(e)], _newpos(chosen, e.scope)) for e in chosen]

    def offset(pos):
        if not isinstance(pos, dict):
            return None
        ln, cl = pos.get("line"), pos.get("column")
        if not isinstance(ln, int) or not isinstance(cl, int):
            return None
        k = ln - first
        if k < 0 or k >= nlines:
            return None
        off = starts[k] + cl - head_len
        return off if off >= 0 else None

    def risky_before(off):
        prev = [(e, a) for (e, a, sc) in scopes if e.rule in RISKY and a < off]
        return max(prev, key=lambda x: x[1])[0] if prev else None

    strong, scoped, weak, unexpl = set(), set(), [], 0
    for m in messages or []:
        if not isinstance(m, dict) or m.get("severity") != "error":
            continue
        off = offset(m.get("pos"))
        if off is None:
            unexpl += 1; continue
        data = str(m.get("data", ""))
        hit = None
        if data.startswith("unsolved goals"):
            # reported at the enclosing `by` / bullet: the weakest evidence (only its range, else tier 3)
            end = offset(m.get("endPos"))
            if end is not None:
                inr = [e for (e, a, sc) in scopes if off <= a <= end]
                em = [e for e in inr if e.rule == "emcases"]
                if em and re.search(r"\bcase\s+in[lr]\b", data):
                    hit = max(em, key=lambda e: e.start)
                elif len(inr) == 1:
                    hit = inr[0]
            if hit is None:
                weak.append(("goals", off, None)); continue
            strong.add(hit.site); continue
        if True:
            txt = _msg_names(data)
            best = None
            for (e, a, sc) in scopes:
                if e.names and a <= off < max(sc, a + 1) and any(_occurrences(txt, x) for x in e.names):
                    if best is None or a > best[1]:
                        best = (e, a)
            hit = best[0] if best else None
        if hit is None:
            on_line = []
            for (e, ns, ne) in spans:
                lo = new_body.rfind("\n", 0, ns) + 1
                hi = new_body.find("\n", ne)
                hi = len(new_body) if hi < 0 else hi
                if lo <= off <= hi:
                    on_line.append((e, ns, ne))
            inside = [x for x in on_line if x[1] <= off <= x[2]]
            before = [x for x in on_line if x[1] <= off]
            if inside:
                hit = max(inside, key=lambda x: x[1])[0]
            elif before:
                hit = max(before, key=lambda x: x[1])[0]
            elif on_line:
                hit = min(on_line, key=lambda x: x[1])[0]
            if hit is not None and hit.rule == "anonctor" and not DOT_FAIL.search(data):
                weak.append(("line", off, hit)); continue
        if hit is None:
            best = None
            for (e, a, sc) in scopes:
                if a <= off < max(sc, a + 1) and e.rule not in ("anonctor", "bundle"):
                    if best is None or a > best[1]:
                        best = (e, a)
            if best:
                scoped.add(best[0].site); continue
        if hit is None:
            weak.append(("none", off, None)); continue
        strong.add(hit.site)
    if strong:   # a later error is often a consequence of an earlier one: the next round re-reads it
        return strong, unexpl + len(weak) + len(scoped)
    if scoped:
        return scoped, unexpl + len(weak)
    blamed = set()
    for kind, off, e in weak:
        h = risky_before(off) or e
        if h is None and len(chosen) == 1:
            h = chosen[0]
        if h is None:
            unexpl += 1
        else:
            blamed.add(h.site)
    return blamed, unexpl


def _dump(rec: dict) -> None:
    """Test aid: one JSON line per engine round to $LRA_LEXSURF_DUMP when set (never in a package run)."""
    path = os.environ.get("LRA_LEXSURF_DUMP")
    if not path:
        return
    try:
        with _CACHE_LOCK, open(path, "a") as fh:
            fh.write(json.dumps(rec, ensure_ascii=False) + "\n")
    except OSError:
        pass


SCREEN_DUMMY = "theorem lraLexDummy : True := trivial\n"


def _screen(statement: str, body: str, S, alt_of: dict, run, compile_s: float, fail, info: dict, say) -> None:
    """One-copy-per-site screen (module docstring, "query"): a file of renamed copies of the declaration, copy 0 the incumbent (the
    control), copy i with one site's current spelling, each followed by a marker; a copy with an error inside its lines fails that
    spelling (the site moves to its next one). A file whose control fails, or whose markers do not all print, decides nothing."""
    from harness.post import d4_measure as MS
    if MS.renamed(statement, 0) is None:
        return
    per = MS.budget({"compile_s": compile_s})
    for _f in range(SCREEN_FILES):
        live = [st[alt_of[st[0].site]] for st in S if alt_of.get(st[0].site) is not None and alt_of[st[0].site] < len(st)]
        live = [e for e in live if not e.note == "newline-by"]
        live.sort(key=lambda e: (-e.dtok, e.start))
        live = [e for e in live if e.site not in info.setdefault("screened", set())][:max(1, per - 1)]
        if not live:
            return
        parts, n_lines = [SCREEN_DUMMY], [SCREEN_DUMMY.count("\n")]
        for i, e in enumerate([None] + live):
            nb = body if e is None else _apply(body, [e])[0]
            cp = MS.renamed(statement, i).rstrip() + " :=" + nb.rstrip() + f'\n#print "{MARK}_C{i}"\n'
            parts.append(cp)
        r = run("".join(parts), None)
        info["compiles"] += 1
        info["screens"] = info.get("screens", 0) + 1
        msgs = getattr(r, "messages", None) or []
        marks = {}
        for m in msgs:
            d = str(m.get("data", "")).strip().strip('"') if isinstance(m, dict) else ""
            if d.startswith(MARK + "_C") and d[len(MARK) + 2:].isdigit():
                ln = (m.get("pos") or {}).get("line")
                if isinstance(ln, int):
                    marks[int(d[len(MARK) + 2:])] = ln
        if len(marks) != len(live) + 1:
            say(f"lexsurf screen: {len(marks)} of {len(live) + 1} markers printed; no verdicts")
            return
        bad = set()
        for m in msgs:
            if not isinstance(m, dict) or m.get("severity") != "error":
                continue
            ln = (m.get("pos") or {}).get("line")
            if not isinstance(ln, int):
                continue
            for i in range(len(live) + 1):
                lo = marks[i - 1] + 1 if i else 0
                if lo <= ln < marks[i]:
                    bad.add(i); break
        if 0 in bad:
            say("lexsurf screen: the control copy fails; no verdicts")
            return
        for i, e in enumerate(live, 1):
            info["screened"].add(e.site)
            if i in bad:
                fail(e)
        say(f"lexsurf screen {_f + 1}: {len(live)} spelling(s), {len(bad)} failed")


def _mscreen(statement: str, body: str, S, alt_of: dict, run, compile_s: float, exchange, fail, info: dict, say) -> bool:
    """Measured screen (module docstring, "query"): d4_measure's one-file heartbeat readings of single-site variants, the incumbent
    first (the control). A variant that reads not ok fails its spelling; one that reads ok but whose heartbeats added outweigh its
    tokens saved at the row's exchange rate (by more than HB_TOL) is dropped the same way (the site moves to its next spelling, which a
    later file reads). A file whose control does not read decides nothing (False: the plain screen may run instead)."""
    from harness.post import d4_measure as MS
    if MS.renamed(statement, 0) is None:
        return False
    per = MS.budget({"compile_s": compile_s})
    done = info.setdefault("mscreened", set())
    preds = info.setdefault("pred", {})
    decided = False
    for _f in range(MSCREEN_FILES):
        live = [st[alt_of[st[0].site]] for st in S if alt_of.get(st[0].site) is not None and alt_of[st[0].site] < len(st)]
        live = [e for e in live if e.note != "newline-by" and (e.site, e.alt) not in done]
        live.sort(key=lambda e: (-e.dtok, e.start))
        live = live[:max(1, per - 1)]
        if not live:
            break
        bodies = [body] + [_apply(body, [e])[0] for e in live]
        text = MS.text(statement, bodies)
        if text is None:
            return decided
        r = run(text, None)
        info["compiles"] += 1
        info["mscreens"] = info.get("mscreens", 0) + 1
        rd = MS.parse(getattr(r, "messages", None), len(bodies))
        ctl = rd.get(0) or {"ok": False}
        if not ctl.get("ok"):
            say("lexsurf mscreen: the control does not read; no verdicts")
            return decided
        decided = True
        nbad = nh = 0
        tol = max(HB_TOL_ABS, HB_TOL_REL * float(ctl["hb"]))
        for k, e in enumerate(live, 1):
            v = rd.get(k)
            if v is None:
                if getattr(r, "timed_out", False):
                    continue    # not read: undecided, the rounds decide it
                v = {"ok": False}
            done.add((e.site, e.alt))
            if not v.get("ok"):
                fail(e); nbad += 1; continue
            cost = float(v["hb"] - ctl["hb"]) - (float(e.dtok) * float(exchange) if exchange else 0.0)
            preds[(e.site, e.alt)] = -cost
            if exchange and cost > tol:
                fail(e); nh += 1
        _dump({"key": info.get("key"), "st": hashlib.sha256(statement.encode()).hexdigest()[:12], "mscreen": _f + 1,
               "ctl": ctl.get("hb"), "edits": [[e.rule, e.note, e.dtok, body[e.start:e.end][:160], e.text[:160],
                                                (rd.get(k) or {}).get("ok"), (rd.get(k) or {}).get("hb")] for k, e in enumerate(live, 1)]})
        say(f"lexsurf mscreen {_f + 1}: {len(live)} spelling(s), {nbad} failed, {nh} heartbeat-costly")
    return decided


def query(proof: str, statement: str, run, *, versions=None, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict:
    """The joint engine (module docstring, "query"): {"lexsurf": {"key", "verified": [Edit], "status", "rounds", ...}}."""
    say = log or (lambda *a: None)
    hb = K.head_body(proof, statement)
    if hb is None:
        return {}
    head, body = hb
    info = {"key": K.proof_key(proof), "sites": 0, "verified": [], "status": "no_site", "rounds": 0, "compiles": 0, "dropped": 0}
    types = None
    if DOTCALL and (ctx or {}).get("dotcall", True) and (_dotcall_raw(_B(body)) or _hyplist_raw(_B(body))):
        try:
            types = probe_types(proof, statement, run)
        except Exception as ex:  # noqa: BLE001  (a failed probe only means no dotcall sites)
            say(f"lexsurf probe: {type(ex).__name__}: {str(ex)[:120]}")
            types = None
        info["compiles"] += 1
        info["typed"] = len(types or {})
    aliases = None
    if types and ALIASES:
        pairs = {(hh, m.group(1)) for m, h in _alias_raw(_B(body), types) for hh in {h, ALIAS_UNFOLD.get(h, h)}}
        if pairs:
            try:
                ra = run(alias_text(sorted(pairs)[:ALIAS_MAX]), None)
                aliases = parse_aliases(getattr(ra, "messages", None))
            except Exception as ex:  # noqa: BLE001  (a failed alias query only means no alias sites)
                say(f"lexsurf alias query: {type(ex).__name__}: {str(ex)[:120]}")
            info["compiles"] += 1
            info["aliases"] = sum(len(v) for v in (aliases or {}).values())
    S = [[e for e in st if not _is_failed(statement, body, e)] for st in sites(proof, statement, types, aliases)]
    S = [st for st in S if st]
    S = [[e._replace(site=i, alt=k) for k, e in enumerate(st)] for i, st in enumerate(S)]
    info["sites"] = len(S)
    if not S:
        return {"lexsurf": info}
    alt_of = {st[0].site: 0 for st in S}

    def compile_set(chosen):
        nb, spans = _apply(body, chosen)
        decl = (head + nb).rstrip()
        r = run(decl + f'\n#print "{MARK}"\n', None)
        info["compiles"] += 1
        return r, nb, spans, decl

    def fail(e, cache=True):
        if cache:
            _mark_failed(statement, body, e)
        info["dropped"] += 1
        alt_of[e.site] = e.alt + 1

    cs = (ctx or {}).get("compile_s")
    fast = isinstance(cs, (int, float)) and 0 < cs <= SCREEN_MAX_S
    measured = False
    if fast and MSCREEN and (ctx or {}).get("mscreen", True) and len(S) >= MSCREEN_SITES:
        measured = _mscreen(statement, body, S, alt_of, run, cs, (ctx or {}).get("exchange"), fail, info, say)
    if not measured and len(S) > SCREEN_SITES and fast:
        _screen(statement, body, S, alt_of, run, cs, fail, info, say)
    rounds = ROUNDS
    if isinstance(cs, (int, float)) and cs > 0:
        rounds = max(ROUNDS, min(MAX_ROUNDS, int(ROUND_S / float(cs))))
    status = "exhausted"
    chosen = []
    for rnd in range(rounds):
        chosen = select(S, alt_of)
        if not chosen:
            status = "all_failed"; break
        info["rounds"] = rnd + 1
        r, nb, spans, decl = compile_set(chosen)
        msgs = getattr(r, "messages", None) or []
        if getattr(r, "timed_out", False):
            status = "timeout"; chosen = []; break
        errs = [m for m in msgs if isinstance(m, dict) and m.get("severity") == "error"]
        if getattr(r, "ok", False) and not errs:
            info["verified"] = chosen; status = "verified"
            _dump({"key": info["key"], "st": hashlib.sha256(statement.encode()).hexdigest()[:12], "round": rnd + 1, "verified": True,
                   "edits": [[e.rule, e.note, e.dtok, body[e.start:e.end][:160], e.text[:160], False] for e in chosen]})
            break
        blamed, unexplained = localize(msgs, decl, len(head), nb, spans, chosen)
        _dump({"key": info["key"], "st": hashlib.sha256(statement.encode()).hexdigest()[:12], "round": rnd + 1,
               "edits": [[e.rule, e.note, e.dtok, body[e.start:e.end][:160], e.text[:160], e.site in blamed] for e in chosen],
               "errors": [str(m.get("data", ""))[:300] for m in errs[:6]], "unexplained": unexplained})
        if unexplained < 0:
            status = "no_marker"; chosen = []; break
        say(f"lexsurf round {rnd + 1}: {len(chosen)} edit(s), {len(errs)} error(s), {len(blamed)} blamed, {unexplained} unexplained")
        if not blamed:
            status = "unexplained"; break
        passed = info.get("pred") or {}
        for e in chosen:
            if e.site in blamed:
                # a spelling that elaborated alone in the measured screen and broke only jointly is dropped for this query but not
                # cached: the next pass retries it on the new incumbent
                fail(e, cache=(e.site, e.alt) not in passed)
    else:
        chosen = select(S, alt_of)
        status = "exhausted" if chosen else "all_failed"
    if status in ("unexplained", "exhausted") and chosen:
        half = len(chosen) // 2
        parts = [chosen, chosen[:half]] if status == "exhausted" else [chosen[:half], chosen[half:]]
        for part in parts[:BISECT]:
            if not part:
                continue
            r, nb, spans, decl = compile_set(part)
            if getattr(r, "ok", False) and not getattr(r, "timed_out", False):
                info["verified"] = part; status = "verified_half"; break
    info["status"] = status
    info["remaining"] = select(S, alt_of) if status in ("timeout", "no_marker") else []
    if stats is not None:
        stats.update({k: v for k, v in info.items() if k not in ("verified", "remaining", "screened", "mscreened", "pred")})
    say(f"lexsurf query: {len(S)} site(s), {info['rounds']} round(s), {info['compiles']} compile(s), {status}, "
        f"{len(info['verified'])} verified edit(s) saving {sum(e.dtok for e in info['verified'])} token(s)")
    return {"lexsurf": info}


# ------------------------------------------------------------------------------------------------------------------------- candidates
def _groups(chosen: list[Edit], singles: bool = True) -> list[tuple[str, list[Edit]]]:
    """The candidate edit sets in the engine's order: joint, per rule, halves, singles (by saving; only for an unverified set)."""
    out = [("joint", chosen)]
    if len({e.rule for e in chosen}) > 1:
        for rule in RULES:
            sub = [e for e in chosen if e.rule == rule]
            if sub:
                out.append((f"rule:{rule}", sub))
    if len(chosen) >= 4:
        h = len(chosen) // 2
        out += [("half:1", chosen[:h]), ("half:2", chosen[h:])]
    if singles:
        for e in sorted(chosen, key=lambda e: (-e.dtok, e.start)):
            out.append((f"single:{e.rule}", [e]))
    return out


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int | None = None,
               ctx: dict | None = None) -> list[dict]:
    """[{"op": "lexsurf:<kind>", "decl", "note", "dtok"}]: the verified set's groups when the query answered for this exact proof,
    nothing when it answered that every site failed, else the groups of the cheapest non-conflicting set (unverified)."""
    hb = K.head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    q = (ctx or {}).get("lexsurf")
    verified = False
    if q and q.get("key") == K.proof_key(proof):
        verified = bool(q.get("verified"))
        chosen = list(q.get("verified") or []) or list(q.get("remaining") or [])
        if not chosen:
            return []
    else:
        S = [[e for e in st if not _is_failed(statement, body, e)] for st in sites(proof, statement)]
        S = [[e._replace(site=i, alt=k) for k, e in enumerate(st)] for i, st in enumerate([x for x in S if x])]
        chosen = select(S, {st[0].site: 0 for st in S})
    em = K.Emitter(proof, statement, head, body, int(max_per_op) if max_per_op else MAX_CANDS)
    t0 = count_tokens(body)
    out = []
    for kind, es in _groups(chosen, singles=not verified):
        if len(em.out) >= (int(max_per_op) if max_per_op else MAX_CANDS):
            break
        nb, _ = _apply(body, es)
        rules = sorted({e.rule for e in es})
        note = f"{kind}: {len(es)} edit(s) [{','.join(rules)}] -{t0 - count_tokens(nb)} tok; " + "; ".join(
            f"{e.rule}/{e.note or 'x'} {body[e.start:e.end][:24]!r}->{e.text[:24]!r}" for e in es[:4])
        if em.add(f"lexsurf:{kind.split(':')[0]}", nb, note[:300], extra={"dtok": t0 - count_tokens(nb), "rules": rules}):
            out.append(em.out[-1])
    return out


def has_site(proof: str, statement: str) -> bool:
    if sites(proof, statement):
        return True
    hb = K.head_body(proof, statement)
    return bool(DOTCALL and hb is not None and (_dotcall_raw(_B(hb[1])) or _hyplist_raw(_B(hb[1]))))
