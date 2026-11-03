#!/usr/bin/env python3
"""Projection-path op "projpath" of the open post-step (harness/open_post.py; length tools v2, 2026-11-03): a flat destructuring
pattern `⟨p1, …, pk⟩` becomes ONE name plus projection paths at the uses. The scorer's lexer reads `t.2.1` as one token, so every use
keeps its length while the pattern's brackets, commas and names go away.

  sites     flat anonymous-constructor patterns with k >= 2 components (and the flat patterns nested one level inside them, kind
            "inner": replaced by one name inside the outer pattern) in
              `obtain ⟨..⟩ := e` / `obtain ⟨..⟩ : T := e`, `have ⟨..⟩ := e`, `rcases e with ⟨..⟩`   (tactic position)
              `intro` / `rintro` arguments                                                         (tactic position)
              `fun ⟨..⟩ =>` / `λ⟨..⟩ ↦` binders
            A component is a name, `_` or `-` (anything else, e.g. `rfl`, a nested pattern, a typed pattern or `this`, is "complex").
            Scope: the rest of the enclosing tactic block by indentation (a tactic nested after `by` on the same line: from its own
            column; inside brackets: up to the closing bracket), or the λ body (with a `?_` hole in it: the rest of the tactic block).
            Blocked component: a complex one, or a name that occurs in the scope as anything but a plain reference: bound again (a
            fun / quantifier / pattern / have / intro-family binder, `if h :`, `by_cases h :` ...), the target of `at`, `subst`,
            `clear`, `revert`, `specialize`, `cases`, `rcases`, `induction`, `generalize` ..., `@name`, `?name`. Blocked components and
            everything before them stay named.
  forms     (per site, tested in this order: drop, chain 0, exw, flat, chain 1 .. k-2; t = the last component's name when it is
            one, else a fresh name not in the proof)
              drop     (no component kept; obtain / have / rcases alone on its lines; e one token, e.g. `h` or `h.2`) the line is
                       deleted and the uses become `e.1`, `e.2.1`, ..., `e.2.2`
              chain j  the first j components stay named (j = 0 .. k-2; j >= 1 is what an ∃ witness needs), the rest is bound to t
                       (j = 0: `have t := e` / `intro t` / `fun t =>`; j >= 1: `⟨p1, .., pj, t⟩`) and its uses become the And-chain
                       paths `t.1`, `t.2.1`, ..., `t.2.….2`
              exw      (obtain / have / rcases, an untyped one-line rhs e) `unhygienic rcases e`: an ∃ is split with Lean's own
                       names for `Exists.intro`'s fields, the witness `w` and its proof `h` (`w_1` / `h_1` when the name is taken in
                       the local context: Lean then avoids it; both guesses when unsure); the first component's uses become the witness name, the others
                       the And-chain paths of the proof name (that name alone for k = 2). Only when the scope uses neither name
                       otherwise (no capture). An ∃ witness cannot be projected, so this is the form that saves the brackets of
                       `⟨x, hx, ..⟩` (2k+1 tokens, against 2k-4 for chain 1)
              flat     (k >= 3, j = 0) the k-field structure paths `t.1`, `t.2`, ..., `t.k`
            Renaming is at identifier level (word boundary, not after `.`, never in a binder position; `(x := ..)` named arguments
            and structure fields are left alone).
  query     (the only compiles; primary pin; one plain file per round, at most QUERY_FILES rounds per proof) one renamed copy of the
            declaration per (site, form), each after a `#print "LRAPP i"` marker, plus the incumbent as the control (variant 0, the
            first round only): a copy is OK when no error (and no sorry warning) falls between its marker and the next one. Forms are
            tested best first, breadth first over the sites; a site is settled by its best compiling form. A control that does not
            compile (e.g. a proof that names its own theorem) leaves the query unusable: the pure fallback below is used. Answers are
            cached per (statement, site text, scope text, form) for the process, so a later pass re-tests only what changed.
  generate  projpath:joint  every settled site at its best compiling form at once (applied last site first, each site re-parsed
                            on the text the later ones left), then without each one (leave-one-out, most saving first)
            projpath:site   each settled site alone, most tokens saved first
            Without a usable query: the joint and single candidates of each site's first form (and second form, singles only).
Pure text building and parsing; the query's compiles go through run(text, version) of the caller (charged to the row's budget). Generic
by construction: no row names, theorem names, lemma lists or proof text; names, paths and scopes come from the proof being edited. The
caller measures every candidate and keeps it only when it compiles on every pin and scores higher (harness/open_post.py).
Provenance: the same generic idea as the closed line's `udialect:projtail`, re-implemented here from the v2 ops spec in open code (no
closed code imported); designed by studying typical differences between open and closed proofs on the final rows (Nov 3;
disclosed in the tech report)."""
from __future__ import annotations

import argparse, hashlib, json, re, sys, threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.tools.t1_compress import _binder_regions  # noqa: E402
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402

FAMILY = "projpath"
OPS = ("projpath:joint", "projpath:site")
MAX_PER_OP = 6
QUERY_FILES = 4          # query rounds (files) per proof at most
MEASURE_S = 210.0        # seconds of copies per file (the caller's query timeout is 300 s; imports and the control fit)
MAX_VARIANTS = 16        # copies per file at most (the control included)
DEFAULT_VARIANT_S = 15.0
FRESH = ("h", "t", "p", "q", "w", "u", "v", "x", "y", "z", "hp", "hq", "ht", "hw", "hu", "hv", "hx", "hy", "hh", "tt", "pp", "qq")
MARK = "LRAPP"
UNHYG = "unhygienic"     # core Lean tactic combinator (every pin): the names `cases` makes are accessible
EXW = ("w", "h")         # the field names of `Exists.intro` (core): the witness and its proof after `unhygienic rcases e`
ANL = ("left", "right")  # the field names of `And.intro` (core)
MAX_GUESSES = 3          # name pairs per nameless form and site
COVER_RE = re.compile(r"\s*by\s+unhygienic[ \t]*(?:--[^\n]*)?\n")   # a proof whose whole tactic block is one `unhygienic` block

_IDC = r"\w'!?₀-₉"
_ID_L = r"(?<![" + _IDC + r".])"
_ID_R = r"(?![" + _IDC + r"])"
NAME = r"[^\W\d][" + _IDC + r"]*"
NAME_RE = re.compile(NAME)
TOKEN_RE = re.compile(r"[^\W\d][" + _IDC + r"]*(?:\.(?:\d+|[^\W\d][" + _IDC + r"]*))*")   # one identifier token, dotted paths allowed
WORD_RE = re.compile(r"[^\W\d][" + _IDC + r"]*")
DECL_RE = re.compile(r"\A(?P<pre>(?:\s*(?:open|set_option)\b[^\n]*?\bin\b)*)"
                     r"(?P<mods>(?:\s+|/--(?:(?!-/).)*-/|@\[[^\]]*\]|(?:private|protected|noncomputable|nonrec)\b)*)(?:theorem|lemma)\s+"
                     r"(?P<ns>(?:[^\s(:{\[⦃.]+\.)*)[^\s(:{\[⦃.]+(?P<univ>\.\{[^}]*\})?", re.S)
TAC_HEADS = ("obtain", "have", "rcases", "intro", "rintro")
FUN_HEADS = ("fun", "λ")
TACTIC_PREV = ("·", ";", "<;>", "by", "=>", "then", "else", "do")
# a name right after one of these words is (re)bound there
BINDER_PREV = frozenset({"if", "by_cases", "by_contra", "by_contra!", "replace", "set", "generalize", "rename'", "intro", "intros",
                         "rintro", "obtain", "have", "let", "haveI", "letI", "suffices", "fun", "λ", "choose", "using_hyp"})
# a name anywhere in a tactic headed by one of these words is its target (changed, cleared or split) or one of its new names
# a bare name (not followed by `.` / `[`) in a tactic headed by one of these words is its target (changed or cleared) or a new name;
# `cases` / `rcases` / `obtain` accept a projection as their target (`cases t.1`), so they are not here
TARGET_HEADS = frozenset({"subst", "clear", "revert", "specialize", "induction", "induction'", "generalize", "interval_cases",
                          "fin_cases", "clear_value", "choose", "contrapose", "contrapose!", "rename_i", "rename'", "subst_vars",
                          "exists_intro", "unfold_let", "set"})
SORRY_RE = re.compile(r"\bdeclaration uses\b.*\bsorry", re.S)

_LOCK = threading.Lock()
_CACHE: dict = {}        # signature -> True / False (a (site, form) single-copy compile on the primary pin)


def sha(*parts: str) -> str:
    h = hashlib.sha256()
    for p in parts:
        h.update(p.encode()); h.update(b"\x00")
    return h.hexdigest()[:20]


# ------------------------------------------------------------------------------------------------------------------------------ parse
class Comp:
    __slots__ = ("text", "s", "e", "kind")

    def __init__(self, text: str, s: int, e: int):
        self.text, self.s, self.e = text, s, e
        t = text.strip()
        if t in ("_", "-"):
            self.kind = t
        elif NAME_RE.fullmatch(t) and t not in ("this", "rfl", "fun", "λ"):
            self.kind = "name"
        else:
            self.kind = "complex"

    @property
    def name(self) -> str | None:
        return self.text.strip() if self.kind == "name" else None


class Site:
    """One flat pattern: kind (obtain / have / rcases / intro / rintro / fun), the head keyword start kw, the pattern [ps, pe), its
    components, the rhs e [es, ee) (obtain / have / rcases), the scope [ss, se), whole (alone on its lines: [ls, le) incl. its
    newline), the uses {name: [offsets]}, the blocked component indices, the tail name t and the forms."""

    def __init__(self, kind: str, kw: int, ps: int, pe: int, comps: list):
        self.kind, self.kw, self.ps, self.pe, self.comps = kind, kw, ps, pe, comps
        self.es = self.ee = None
        self.ts = self.te = None   # the type of a typed obtain / have (`obtain ⟨..⟩ : T := e`)
        self.typed = False
        self.ss = self.se = pe
        self.whole = None
        self.uses: dict = {}
        self.blocked: set = set()
        self.targets: dict = {}    # name -> offsets where it is the target of a tactic (`at h`, `subst h`, `specialize h ..`)
        self.rebound: set = set()  # component indices that are re-bound / named holes in the scope (or complex)
        self.plain_ok = False      # blocked only as targets, and every blocked component maps to a plain name in a nameless form
        self.deep_ok = False       # blocked only as targets, later components among them: plain names need more `rcases` levels
        self.t: str | None = None
        self.forms: list = []
        self.droppable = False

    @property
    def k(self) -> int:
        return len(self.comps)

    @property
    def sid(self) -> int:
        return self.ps


class Prep:
    """A proof prepared for projpath: head, body, mask, pairs, binder regions and the sites (with scopes, uses, blocked components,
    tail names and forms)."""

    def __init__(self, proof: str, statement: str):
        self.ok = False
        self.sites: list[Site] = []
        body = split_declaration(proof, statement)
        if body is None:
            return
        self.proof, self.statement, self.body = proof, statement, body
        self.head = proof[:len(proof) - len(body)]
        self.mask = _mask(body)
        self.pairs = _pairs(body, self.mask)
        self.closers = {j: i for i, j in self.pairs.items()}
        self.regions = [(a, b) for a, b in _binder_regions(body, self.mask, self.pairs)
                        if not (body[:a].endswith("suffices") and not (body.startswith(":", b) and not body.startswith(":=", b)))]
        # (an anonymous `suffices T by` / `from`: t1_compress counts T as a binder region; only `suffices h : T` binds a name)
        self.lines = body.split("\n")
        self.starts, p = [], 0
        for ln in self.lines:
            self.starts.append(p); p += len(ln) + 1
        self.words = set(WORD_RE.findall(body)) | set(WORD_RE.findall(statement))
        self.ok = True
        self.cover = bool(COVER_RE.match(body))   # every tactic is already unhygienic: the nameless form needs no prefix
        fresh = [f for f in FRESH if f not in self.words]
        for outer in self._find():
            if not self._scope(outer):
                continue
            for st in [outer] + self._inner(outer):
                if not self._analyse(st):
                    continue
                if st.t is None:
                    if not fresh:
                        continue
                    st.t = fresh.pop(0)
                st.forms = self._forms(st)
                if st.forms or ((st.plain_ok or st.deep_ok) and self.nameless_ok(st)):
                    self.sites.append(st)
        self.sites.sort(key=lambda s: s.ps)

    def _inner(self, outer: Site) -> list[Site]:
        """The flat patterns nested one level in a site's pattern (`⟨a, ⟨b, c⟩, d⟩`): sites of kind "inner" with the outer site's
        scope; the nested pattern is replaced by one name (the outer pattern keeps its shape)."""
        out = []
        for c in outer.comps:
            if c.kind != "complex" or not c.text.startswith("⟨") or self.pairs.get(c.s) != c.e - 1:
                continue
            st = self._mk("inner", outer.kw, c.s)
            if st is None or any(x.kind == "complex" for x in st.comps):
                continue
            st.ss, st.se, st.es, st.ee, st.typed = outer.ss, outer.se, outer.es, outer.ee, True
            out.append(st)
        return out

    # ---- small helpers
    def line_of(self, i: int) -> int:
        lo, hi = 0, len(self.starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.starts[mid] <= i:
                lo = mid
            else:
                hi = mid - 1
        return lo

    def ind(self, li: int) -> int:
        ln = self.lines[li]
        return len(ln) - len(ln.lstrip(" \t"))

    def blank(self, li: int) -> bool:
        s = self.starts[li]
        return all(self.body[p].isspace() or self.mask[p] for p in range(s, s + len(self.lines[li])))

    def code(self, a: int, b: int) -> str:
        return "".join(" " if self.mask[p] else self.body[p] for p in range(a, b))

    def enclosing(self, i: int) -> int | None:
        """The closing index of the innermost bracket pair around i, else None."""
        best = None
        for a, b in self.pairs.items():
            if a < i < b and (best is None or a > best[0]):
                best = (a, b)
        return best[1] if best else None

    def binds(self, i: int) -> bool:
        for a, b in self.regions:
            if a <= i < b and ":" not in self.code(a, i):
                return True
        return False

    def skip_ws(self, i: int, nl: bool = False) -> int:
        while i < len(self.body) and (self.body[i] in " \t" or (nl and self.body[i] == "\n")):
            i += 1
        return i

    def prev_word(self, i: int) -> str:
        j = i - 1
        while j >= 0 and self.body[j] in " \t":
            j -= 1
        k = j
        while k >= 0 and re.match(r"[" + _IDC + r"]", self.body[k]):
            k -= 1
        return self.body[k + 1:j + 1]

    def segment_start(self, i: int) -> int:
        """Start of the tactic segment holding i on its line (after the last `;`, `<;>`, `·`, `=>` or `by` before i)."""
        ls = self.starts[self.line_of(i)]
        c = self.code(ls, i)
        best = 0
        for m in re.finditer(r"<;>|;|·|=>|(?<![\w.'!?])by(?![\w'!?])", c):
            best = m.end()
        return ls + best

    def tactic_pos(self, kw: int) -> bool:
        """Is the keyword at kw the head of a tactic (line start, or after `·`, `;`, `<;>`, `by`, `=>`, then / else / do)?"""
        ls = self.starts[self.line_of(kw)]
        pre = self.code(ls, kw).rstrip()
        if not pre.strip():
            return True
        if pre.endswith("|"):
            return False
        return any(pre.endswith(x) and (not x[0].isalpha() or not re.match(r"[" + _IDC + r".]", pre[-len(x) - 1:-len(x)] or " "))
                   for x in TACTIC_PREV)

    def depth0(self, a: int, b: int, stops: tuple) -> int | None:
        """The first position in [a, b) at bracket depth 0 (relative to a) where one of `stops` starts, else None."""
        i = a
        while i < b:
            if self.mask[i]:
                i += 1
                continue
            if i in self.pairs:
                i = self.pairs[i] + 1
                continue
            if self.body[i] in ")]}⟩":
                return None
            for s in stops:
                if self.body.startswith(s, i):
                    if s[0].isalpha() and (re.match(r"[" + _IDC + r".]", self.body[i - 1:i] or " ") or
                                           re.match(r"[" + _IDC + r"]", self.body[i + len(s):i + len(s) + 1] or " ")):
                        continue
                    return i
            i += 1
        return None

    def pattern(self, ps: int) -> list[Comp] | None:
        """The components of the bracket pattern starting at ps (depth-0 commas), or None (unbalanced, empty)."""
        if ps not in self.pairs or self.body[ps] != "⟨":
            return None
        pe = self.pairs[ps]
        out, a, i = [], ps + 1, ps + 1
        while i < pe:
            if self.mask[i]:
                return None
            if i in self.pairs:
                i = self.pairs[i] + 1
                continue
            if self.body[i] == ",":
                out.append(Comp(self.body[a:i], a, i)); a = i + 1
            i += 1
        out.append(Comp(self.body[a:pe], a, pe))
        if any(not c.text.strip() for c in out):
            return None
        for c in out:   # trim the component spans to their text
            lead = len(c.text) - len(c.text.lstrip())
            c.s += lead
            c.e = c.s + len(c.text.strip())
            c.text = c.text.strip()
            if "|" in c.text and c.kind != "complex":
                c.kind = "complex"
        return out

    # ---- site finding
    def _find(self) -> list[Site]:
        out = []
        B = self.body
        for m in re.finditer(r"(?<![" + _IDC + r".])(obtain|have|rcases|intro|rintro|fun)(?![" + _IDC + r"])|λ", B):
            kw = m.start()
            if self.mask[kw]:
                continue
            head = m.group(1) or "λ"
            if head in TAC_HEADS and not self.tactic_pos(kw):
                continue
            k = self.skip_ws(m.end())
            if head in ("obtain", "have"):
                if k < len(B) and B[k] == "⟨":
                    st = self._mk(head, kw, k)
                    if st is not None:
                        out.append(st)
            elif head == "rcases":
                ext = self._extent_end(self.line_of(kw), kw - self.starts[self.line_of(kw)])
                w = self.depth0(m.end(), ext, ("with",))
                if w is None:
                    continue
                k2 = self.skip_ws(w + 4)
                if k2 < len(B) and B[k2] == "⟨":
                    st = self._mk(head, kw, k2)
                    if st is not None:
                        st.es, st.ee = m.end(), w
                        out.append(st)
            elif head in ("intro", "rintro"):
                end = self.depth0(m.end(), self._line_end(kw), (";", "<;>"))
                end = self._line_end(kw) if end is None else end
                if self.depth0(m.end(), end, ("|",)) is not None:
                    continue
                i = m.end()
                while i < end:
                    if self.mask[i]:
                        i += 1
                        continue
                    if B[i] == "⟨" and i in self.pairs:
                        st = self._mk(head, kw, i)
                        if st is not None:
                            out.append(st)
                        i = self.pairs[i] + 1
                        continue
                    if i in self.pairs:
                        i = self.pairs[i] + 1
                        continue
                    i += 1
            else:   # fun / λ
                lim = self.enclosing(kw)
                lim = len(B) if lim is None else lim
                arrow = self.depth0(m.end(), lim, ("=>", "↦"))
                if arrow is None:
                    continue
                bl = self.code(m.end(), arrow)
                if bl.strip().startswith("|") or "\n" in bl:
                    continue
                i = m.end()
                while i < arrow:
                    if self.mask[i]:
                        i += 1
                        continue
                    if B[i] == "⟨" and i in self.pairs:
                        st = self._mk("fun", kw, i)
                        if st is not None:
                            st.es = arrow   # the arrow (the scope starts after it)
                            out.append(st)
                        i = self.pairs[i] + 1
                        continue
                    if i in self.pairs:
                        i = self.pairs[i] + 1
                        continue
                    i += 1
        return out

    def _mk(self, kind: str, kw: int, ps: int) -> Site | None:
        comps = self.pattern(ps)
        if comps is None or len(comps) < 2:
            return None
        names = [c.name for c in comps if c.name]
        if len(names) != len(set(names)):
            return None
        return Site(kind, kw, ps, self.pairs[ps] + 1, comps)

    def _line_end(self, i: int) -> int:
        li = self.line_of(i)
        return self.starts[li] + len(self.lines[li])

    def _extent_end(self, li: int, col: int) -> int:
        """End offset (the newline position) of line li and its continuation lines (indented deeper than col)."""
        j, last = li + 1, li
        while j < len(self.lines):
            if not self.blank(j):
                if self.ind(j) <= col:
                    break
                last = j
            j += 1
        return self.starts[last] + len(self.lines[last])

    def _block_end(self, li: int, col: int) -> int:
        """Start offset of the first line after li indented less than col (non-blank), else the body's end."""
        j = li + 1
        while j < len(self.lines):
            if not self.blank(j) and self.ind(j) < col:
                return self.starts[j]
            j += 1
        return len(self.body)

    def _tactic_col(self, li: int, kw: int) -> int:
        """The column of the tactic sequence holding the keyword: its own column after a same-line `by` / `=>`, else the line's first
        tactic column (after a leading `·`)."""
        ls = self.starts[li]
        pre = self.code(ls, kw)
        if re.search(r"(?<![\w.'!?])by(?![\w'!?])|=>", pre):
            return kw - ls
        c = self.ind(li)
        if self.body[ls + c:ls + c + 1] == "·":
            return self.skip_ws(ls + c + 1) - ls
        return c

    # ---- scope
    def _scope(self, st: Site) -> bool:
        B = self.body
        li = self.line_of(st.kw)
        ls = self.starts[li]
        encl = self.enclosing(st.kw)
        if st.kind == "fun":
            st.ss = st.es + (2 if B.startswith("=>", st.es) else 1)
            end = encl if encl is not None else self._extent_end(li, self.ind(li))
            if re.search(r"\?(?:_|" + NAME + ")", self.code(st.ss, end)):
                end = self._block_end(li, self._tactic_col(li, st.kw))
            st.se = end
            return st.se > st.ss
        col = self._tactic_col(li, st.kw)
        ext = self._extent_end(li, st.kw - ls)
        if encl is not None:
            ext = min(ext, encl)
        if st.kind in ("obtain", "have"):
            k = self.skip_ws(st.pe, nl=True)
            if B.startswith(":=", k):
                st.es = k + 2
            elif B.startswith(":", k):
                d = self.depth0(k + 1, ext, (":=",))
                if d is None:
                    return False
                st.typed = True
                st.ts, st.te = k + 1, d
                st.es = d + 2
            else:
                return False
            stop = self.depth0(st.es, ext, (";", "<;>", "by", "fun", "λ", "=>"))
            if stop is not None and (B.startswith(";", stop) or B.startswith("<;>", stop)):
                st.ee = stop
            else:
                st.ee = ext
            st.ss = st.ee
        elif st.kind == "rcases":
            if self.depth0(st.es, st.ee, (":",)) is not None:
                st.typed = True   # `rcases h : e with ..`: no `have` form
            st.ss = st.pe
        else:   # intro / rintro
            st.ss = st.pe
        se = self._block_end(li, col)
        if encl is not None:
            se = min(se, encl)
        st.se = se
        # alone on its lines: nothing before the keyword on its line, the tactic ends its last line
        if st.kind in ("obtain", "have", "rcases") and not self.code(ls, st.kw).strip():
            last_end = ext if st.kind != "rcases" else self._line_end(st.pe)
            tail = st.ee if st.kind != "rcases" else st.pe
            if not self.code(tail, last_end).strip() and last_end == self._line_end(last_end):
                st.whole = (ls, min(last_end + 1, len(B)))
        return st.se > st.ss

    # ---- uses and blocking
    def classify(self, name: str, s: int, e: int) -> tuple[list[int], bool]:
        """(plain reference offsets of `name` in [s, e), blocked?)."""
        uses, blocked, _, _ = self.classify2(name, s, e)
        return uses, blocked

    def classify2(self, name: str, s: int, e: int) -> tuple[list[int], bool, bool, list[int]]:
        """(plain reference offsets, blocked?, re-bound (a binder or a named hole)?, target offsets)."""
        rx = re.compile(_ID_L + re.escape(name) + _ID_R)
        uses, blocked, rebound, targets = [], False, False, []
        B = self.body
        for mm in rx.finditer(B, s, e):
            i = mm.start()
            if self.mask[i]:
                continue
            if B[i - 1:i] == "?":
                blocked = rebound = True; continue   # a named hole `?x`
            after = B[mm.end():mm.end() + 4].lstrip(" \t")
            if after.startswith(":=") and not self.binds(i):
                pre = self.code(self.starts[self.line_of(i)], i).rstrip()
                if not pre or pre[-1] in "({,":
                    continue   # a named argument `(x := ..)` or a structure instance field `{ x := .. }`: not this name
                # else the end of a type before `:=` (`have : P x := ..`): a plain reference
            if self.binds(i):
                blocked = rebound = True; continue
            if self.prev_word(i) in BINDER_PREV:
                blocked = rebound = True; continue
            seg = self.segment_start(i)
            segc = self.code(seg, i)
            fw = WORD_RE.match(segc.strip())
            if fw and fw.group(0) in TARGET_HEADS and B[mm.end():mm.end() + 1] not in (".", "["):
                if fw.group(0) in ("rename_i", "rename'", "set", "choose", "generalize", "induction'", "exists_intro"):
                    rebound = True
                blocked = True; targets.append(i); continue
            if re.search(r"(?<![\w.'!?])at(?![\w'!?])", segc):
                blocked = True; targets.append(i); continue
            uses.append(i)
        return uses, blocked, rebound, targets

    def _analyse(self, st: Site) -> bool:
        for idx, c in enumerate(st.comps):
            if c.kind == "complex":
                st.blocked.add(idx)
            elif c.kind == "name":
                u, b, rb, tg = self.classify2(c.name, st.ss, st.se)
                st.uses[c.name] = u
                if b:
                    st.blocked.add(idx)
                    st.targets[c.name] = tg
                if rb:
                    st.rebound.add(idx)
        if st.blocked and not any(st.comps[i].kind == "complex" for i in st.blocked) and not st.rebound:
            st.plain_ok = st.k == 2 or st.blocked <= {0}   # k = 2: both map to plain names; else only the first one does
            st.deep_ok = not st.plain_ok and not any(c.kind == "complex" for c in st.comps)
        last = st.comps[-1]
        if last.kind == "name":
            st.t = last.name
        if st.kind in ("obtain", "have", "rcases") and st.whole and not st.blocked and st.es is not None:
            e = self.body[st.es:st.ee].strip()
            if TOKEN_RE.fullmatch(e) and not self.mask[st.es + self.body[st.es:st.ee].index(e)]:
                root = e.split(".")[0]
                _, b = self.classify(root, st.ss, st.se)
                comp_names = {c.name for c in st.comps if c.name}
                st.droppable = not b or root in comp_names
        return True

    def _forms(self, st: Site) -> list[tuple]:
        """The site's forms, best first: drop, nameless And (`left` / `right`), chain 0, nameless ∃ (`w` / `h`), chain 1 .. k-2,
        flat (structure fields; rare, so last: an ∃ site settles on its chain form before it)."""
        jmin = (max(st.blocked) + 1) if st.blocked else 0
        if st.plain_ok:   # blocked components are targets only: the nameless forms rename them to plain names everywhere
            nl = [("exw", 1, n) for n in self._nameless(st, ANL) + self._nameless(st, EXW)]
            return nl + [("chain", j) for j in range(jmin, st.k - 1)]
        if jmin > st.k - 2:
            return []
        forms = []
        if jmin == 0:
            if st.droppable:
                forms.append(("drop", 0))
            for names in self._nameless(st, ANL):
                forms.append(("exw", 1, names))
            if not (st.kind == "rcases" and st.typed):
                forms.append(("chain", 0))
            for names in self._nameless(st, EXW):
                forms.append(("exw", 1, names))
        for j in range(max(1, jmin), st.k - 1):
            forms.append(("chain", j))
        if jmin == 0 and st.k >= 3 and not (st.kind == "rcases" and st.typed):
            forms.append(("flat", 0))
        return forms

    def _nameless(self, st: Site, fields: tuple) -> list[tuple]:
        """The nameless form's name pairs (first field, second field), at most MAX_GUESSES, best guess first. `rcases e` without a
        pattern splits one level and, behind `unhygienic` (or under a covering one), names the new hypotheses after the
        constructor's fields (`Exists.intro`: w / h; `And.intro`: left / right), each the first of f, f_1, f_2 .. not in the local
        context. It applies to an obtain / have / rcases site whose first component is a name or `_` (a typed obtain / have as
        `show T from e`). The context is not known statically: a name of the statement is taken (D); one written in the proof
        before the site or in the rhs, or referenced in the scope with no visible binder (a name a nameless tactic made), may be
        (M). Guesses: the lowest name not in D and the lowest not in D or M, per field, paired (both low, both high, mixed). A pair
        is kept only when no renamed use would be captured: no use inside the extent of a later binder of the name, and no use
        after a plain reference of it that no visible binder covers."""
        if not self.nameless_ok(st):
            return []
        rhs = self.body[st.es:st.ee].strip() if st.es is not None else ""
        own = {c.name for c in st.comps if c.name}
        uses = sorted(i for c in st.comps if c.name for i in st.uses.get(c.name, []) + st.targets.get(c.name, []))
        D = set(WORD_RE.findall(self.statement))
        M = set(WORD_RE.findall(self.code(0, st.kw))) | set(WORD_RE.findall(rhs))
        guesses = []
        for f in fields:
            seq = [f] + [f"{f}_{i}" for i in range(1, 8)]
            info = {n: self._refs(n, st.ss, st.se) for n in seq}
            M2 = M | {n for n, (_, plain) in info.items() if plain}
            lo = next((n for n in seq if n not in D), None)
            hi = next((n for n in seq if n not in D and n not in M2), None)
            if lo is None or hi is None:
                return []
            guesses.append((lo, hi, info))
        (lo0, hi0, i0), (lo1, hi1, i1) = guesses
        out = []
        for pair in ((lo0, lo1), (hi0, hi1), (lo0, hi1), (hi0, lo1)):
            if pair in out:
                continue
            ok = True
            for n, info in zip(pair, (i0, i1)):
                if n in own:
                    continue
                ext, plain = info[n]
                if any(a <= u < b for u in uses for a, b in ext) or (plain and uses and plain[0] <= uses[-1]):
                    ok = False
            if ok:
                out.append(pair)
        return out[:MAX_GUESSES]

    def nameless_ok(self, st: Site) -> bool:
        """Can the site take a nameless form (`rcases e` / `rintro ⟨⟩` without names)? An obtain / have / rcases site with a rhs, or
        an intro / rintro pattern, with a first component that is a name or `_` (a typed rcases `rcases h : e` is not)."""
        if st.kind in ("intro", "rintro"):
            return st.comps[0].kind in ("name", "_")
        if st.kind not in ("obtain", "have", "rcases") or st.es is None or st.comps[0].kind not in ("name", "_"):
            return False
        if st.typed and (st.kind == "rcases" or st.ts is None or not self.body[st.ts:st.te].strip()):
            return False
        return bool(self.body[st.es:st.ee].strip())

    def capture_ok(self, st: Site, names) -> bool:
        """No renamed use of the site would be captured by one of the new names (the rule of _nameless)."""
        own = {c.name for c in st.comps if c.name}
        uses = sorted(i for c in st.comps if c.name for i in st.uses.get(c.name, []) + st.targets.get(c.name, []))
        for n in set(names) - own:
            if not NAME_RE.fullmatch(n):
                return False
            ext, plain = self._refs(n, st.ss, st.se)
            if any(a <= u < b for u in uses for a, b in ext) or (plain and uses and plain[0] <= uses[-1]):
                return False
        return True

    def _refs(self, name: str, s: int, e: int) -> tuple[list, list]:
        """The occurrences of `name` in [s, e): (binder extents [(a, b)], the plain references no extent covers, in order)."""
        ext, plain = [], []
        for mm in re.compile(_ID_L + re.escape(name) + _ID_R).finditer(self.body, s, e):
            i = mm.start()
            if self.mask[i]:
                continue
            x = self.binder_extent(i)
            if x:
                ext.append(x)
            else:
                plain.append(i)
        return ext, [i for i in plain if not any(a <= i < b for a, b in ext)]

    def binder_extent(self, i: int) -> tuple[int, int] | None:
        """When the name at i is bound there: (i, the end of what the binding covers), else None. A term binder (fun / ∀ / ∃ /
        `(x : T)` / `if h :` / a `fun ⟨..⟩` pattern) covers the rest of its line's extent (inside its bracket); a tactic binder
        (intro family, have / obtain / set / by_contra .., an obtain / rcases / rintro pattern) the rest of its tactic block."""
        li = self.line_of(i)
        reg = next((a for a, b in self.regions if a <= i < b and ":" not in self.code(a, i)), None)
        encl = self.enclosing(reg if reg is not None else i)   # a binder group's own brackets `(h : T)` do not end the binding

        def cap(x):
            return min(x, encl) if encl is not None else x
        pw = self.prev_word(i)
        if reg is not None or pw in ("if", "fun", "λ"):
            return (i, cap(self._extent_end(li, self.ind(li))))
        a, j = None, i
        while (o := self.enclosing(j)) is not None:   # the outermost ⟨..⟩ around i
            op = next((x for x, y in self.pairs.items() if y == o), None)
            if op is None or self.body[op] != "⟨":
                break
            a, j = op, op
        if pw not in BINDER_PREV and a is None:
            return None
        if a is not None and pw not in BINDER_PREV:
            pw = self.prev_word(a)
            if pw in ("fun", "λ"):
                return (i, cap(self._extent_end(li, self.ind(li))))
            if pw not in BINDER_PREV and pw != "with":
                return None
        return (i, cap(self._block_end(li, self.ind(li) + 1)))

    def first_ref(self, name: str, s: int, e: int) -> int | None:
        """The first unmasked identifier occurrence of `name` in [s, e) (word boundary, not after `.`), else None."""
        for mm in re.compile(_ID_L + re.escape(name) + _ID_R).finditer(self.body, s, e):
            if not self.mask[mm.start()]:
                return mm.start()
        return None

    def site_text(self, st: Site) -> str:
        return self.body[st.kw:max(st.pe, st.ee or 0, st.ss)]


def paths(m: int, kind: str) -> list[str]:
    """The projection suffixes of m tail components: And-chain (`.1`, `.2.1`, ..., `.2.….2`) or flat structure (`.1` .. `.m`)."""
    if kind == "flat":
        return [f".{q + 1}" for q in range(m)]
    return [".2" * q + (".1" if q < m - 1 else "") for q in range(m)]


def edit(P: Prep, st: Site, form: tuple) -> str | None:
    """The body with one site rewritten in the given form (module docstring, "forms"), or None."""
    kind = form[0]
    if kind in ("nl", "probe"):
        return _edit_nameless(P, st, form)
    j = form[1]
    B = P.body
    tail = st.comps[j:]
    m = len(tail)
    if m < 2 and kind not in ("drop", "exw"):
        return None
    hunks = []
    if kind == "drop":
        if not st.whole or j != 0:
            return None
        root = B[st.es:st.ee].strip()
        hunks.append((st.whole[0], st.whole[1], ""))
    elif kind == "exw" and st.kind in ("intro", "rintro"):
        # `rintro .. ⟨p1, .., pk⟩ ..` -> `[unhygienic] rintro .. ⟨⟩ ..` (an intro pattern: `rintro`): Lean's names for the fields
        ls = P.starts[P.line_of(st.kw)]
        covered = P.cover or P.code(ls, st.kw).rstrip().endswith(UNHYG)
        head = "rintro" if st.kind == "intro" else None
        hunks.append((st.kw, st.kw, "" if covered else UNHYG + " "))
        if head:
            hunks[-1] = (st.kw, st.kw + len("intro"), ("" if covered else UNHYG + " ") + head)
        hunks.append((st.ps, st.pe, "⟨⟩"))
        wit, root = form[2]
        c0 = st.comps[0]
        if c0.kind == "name":
            for i in st.uses.get(c0.name, []) + st.targets.get(c0.name, []):
                hunks.append((i, i + len(c0.name), wit))
    elif kind == "exw":
        e = B[st.es:st.ee].strip()
        if st.typed:   # `obtain ⟨..⟩ : T := e` -> `unhygienic rcases show T from e` (`show T by ..` for a `by` rhs)
            T = B[st.ts:st.te].strip()
            e = f"show {T} " + (e if re.match(r"by(?![" + _IDC + r"])", e) else "from " + e)
        pre = "" if P.cover else UNHYG + " "
        new = f"{pre}rcases {e}"
        if "\n" in new:   # continuation lines must stay right of `rcases` (the inner tactic block's column); spaces are free
            col = st.kw - P.starts[P.line_of(st.kw)]
            nl = new.split("\n")
            mi = min((len(x) - len(x.lstrip(" ")) for x in nl[1:] if x.strip()), default=None)
            sh = max(0, col + len(pre) + 1 - mi) if mi is not None else 0
            new = "\n".join([nl[0]] + [(" " * sh + x) if x.strip() else x for x in nl[1:]])
        hunks.append((st.kw, st.pe if st.kind == "rcases" else st.ee, new))
        wit, root = form[2]
        c0 = st.comps[0]
        if c0.kind == "name":
            for i in st.uses.get(c0.name, []) + st.targets.get(c0.name, []):
                hunks.append((i, i + len(c0.name), wit))
    else:
        root = st.t
        if j == 0:
            if st.kind in ("obtain", "have"):
                hunks.append((st.kw, st.pe, "have " + st.t))
            elif st.kind == "rcases":
                if st.typed:
                    return None
                hunks.append((st.kw, st.pe, "have " + st.t + " := " + B[st.es:st.ee].strip()))
            else:
                hunks.append((st.ps, st.pe, st.t))
        else:
            hunks.append((tail[0].s, tail[-1].e, st.t))
    for q, (c, suf) in enumerate(zip(tail, paths(m, "flat" if kind == "flat" else "chain"))):
        if c.kind != "name":
            continue
        tg = st.targets.get(c.name, []) if kind == "exw" else []
        if tg and suf:
            return None   # a tactic target cannot be a projection path
        for i in st.uses.get(c.name, []) + tg:
            hunks.append((i, i + len(c.name), root + suf))
    hunks.sort(key=lambda h: h[0])
    for a, b in zip(hunks, hunks[1:]):
        if a[1] > b[0]:
            return None
    out = B
    for s, e, t in reversed(hunks):
        out = out[:s] + t + out[e:]
    return out


def _rhs_term(P: Prep, st: Site) -> str:
    B = P.body
    e = B[st.es:st.ee].strip()
    if st.typed:   # `obtain ⟨..⟩ : T := e` -> `show T from e` (`show T by ..` for a `by` rhs)
        T = B[st.ts:st.te].strip()
        e = f"show {T} " + (e if re.match(r"by(?![" + _IDC + r"])", e) else "from " + e)
    return e


def _shifted(text: str, mincol: int) -> str:
    """text's continuation lines moved right (all by the same amount) so that each starts at column >= mincol; spaces are free."""
    nl = text.split("\n")
    mi = min((len(x) - len(x.lstrip(" ")) for x in nl[1:] if x.strip()), default=None)
    sh = max(0, mincol - mi) if mi is not None else 0
    return "\n".join([nl[0]] + [(" " * sh + x) if x.strip() else x for x in nl[1:]])


def _edit_nameless(P: Prep, st: Site, form: tuple) -> str | None:
    """("nl", targets, mapping): `rcases e` and then `rcases t` per target (Lean's names; one `unhygienic` block, or bare under a
    covering one), each component's uses replaced by its mapping (None: unused); ("probe",): the nameless `rcases e` and a
    `trace_state` line after it, uses unchanged (the screen reads Lean's names from the trace)."""
    if not P.nameless_ok(st):
        return None
    B = P.body
    if form[0] == "probe" and st.kind in ("intro", "rintro"):
        if P.code(st.pe, P._line_end(st.pe)).strip():
            return None   # the pattern is not the line's last argument: the new fields would not be the last hypotheses
        b2 = B[:st.kw] + _rintro_line(P, st) + B[st.pe:]
        le2 = P._line_end(st.pe) + (len(b2) - len(B))
        return b2[:le2] + "\n" + " " * (st.kw - P.starts[P.line_of(st.kw)]) + "trace_state" + b2[le2:]
    if st.kind in ("intro", "rintro"):
        return None
    end = st.pe if st.kind == "rcases" else st.ee
    col = st.kw - P.starts[P.line_of(st.kw)]
    e = _rhs_term(P, st)
    if form[0] == "probe":
        if P.code(end, P._line_end(end)).strip():
            return None   # the site does not end its line: no room for the trace line
        pre = "" if P.cover else UNHYG + " "
        new = _shifted(f"{pre}rcases {e}", col + len(pre) + 1) + "\n" + " " * col + "trace_state"
        return B[:st.kw] + new + B[end:]
    targets, mapping = form[1], form[2]
    if len(mapping) != st.k:
        return None
    if P.cover:
        ind = col
        lines = [_shifted(f"rcases {e}", col + 1)] + [f"rcases {t}" for t in targets]
        new = ("\n" + " " * ind).join(lines)
    else:
        ind = col + 2
        lines = [_shifted(f"rcases {e}", ind + 1)] + [f"rcases {t}" for t in targets]
        new = UNHYG + "\n" + " " * ind + ("\n" + " " * ind).join(lines)
    hunks = [(st.kw, end, new)]
    for c, x in zip(st.comps, mapping):
        if c.kind != "name":
            continue
        tg = st.targets.get(c.name, [])
        if x is None:
            if st.uses.get(c.name) or tg:
                return None
            continue
        if tg and "." in x:
            return None   # a tactic target cannot be a projection path
        for i in st.uses.get(c.name, []) + tg:
            hunks.append((i, i + len(c.name), x))
    hunks.sort(key=lambda h: h[0])
    for a, b in zip(hunks, hunks[1:]):
        if a[1] > b[0]:
            return None
    out = B
    for s0, e0, t in reversed(hunks):
        out = out[:s0] + t + out[e0:]
    return out


def _rintro_line(P: Prep, st: Site) -> str:
    """The text from the head keyword to the pattern's end with the pattern as `⟨⟩` (and `intro` -> `rintro`, the prefix)."""
    B = P.body
    ls = P.starts[P.line_of(st.kw)]
    covered = P.cover or P.code(ls, st.kw).rstrip().endswith(UNHYG)
    mid = B[st.kw:st.ps]
    if st.kind == "intro":
        mid = "rintro" + mid[len("intro"):]
    return ("" if covered else UNHYG + " ") + mid + "⟨⟩"


_BINDER_HEAD = re.compile(r"(?:∃!?|∀|fun\b|λ|Σ'?|∑|∏|⨆|⨅|⋃|⋂)")


def and_parts(t: str) -> list[str]:
    """A pretty-printed type split into its top-level ∧ chain (right-nested: `A ∧ B ∧ ∃ x, C` -> [A, B, ∃ x, C]); a part that starts
    with a binder runs to the end; [t] when a lower-precedence connective (∨ → ↔) sits at the top."""
    t = " ".join(t.split())
    parts, depth, a, i = [], 0, 0, 0
    while i < len(t):
        ch = t[i]
        if depth == 0 and i == a + (len(t[a:]) - len(t[a:].lstrip())) and _BINDER_HEAD.match(t, i):
            parts.append(t[a:].strip())
            return parts
        if ch in "([{⟨⦃":
            depth += 1
        elif ch in ")]}⟩⦄":
            depth -= 1
        elif depth == 0 and ch in "∨→↔":
            return [t.strip()]
        elif depth == 0 and ch == "∧":
            parts.append(t[a:i].strip())
            a = i + 1
        i += 1
    parts.append(t[a:].strip())
    return [x for x in parts if x] or [t.strip()]


def probe_forms(P: Prep, st: Site, names: tuple, types: tuple) -> list[tuple]:
    """The nameless forms Lean's names from the probe allow: one level (`rcases e`, the first component the first field, the rest
    the And-chain paths of the second); and when the second field's type is an ∧ chain ending in an ∃ that more components need
    (a second witness: `∃ x y, ..`, `∃ x ∈ s, ∃ y ∈ s, ..`), two levels (`rcases e` + `rcases h.2..`), the second level's names
    guessed (the next witness name; the proof name reused when the first proof is consumed, else the next one); the components
    after the second witness taken as an And chain."""
    n1, n2 = names
    out = []
    if P.capture_ok(st, (n1, n2)):
        out.append(("exw", 1, (n1, n2)))
    out += deep_forms(P, st, names, types)
    parts = and_parts(types[1])
    m = len(parts) - 1                     # And parts before the last one
    rest = st.k - 1
    if m + 1 < rest and parts[-1].startswith("∃") and not parts[-1].startswith("∃!"):
        target = n2 + ".2" * m
        rem = st.k - (m + 2)               # components after the second witness
        w2 = _bump(n1, 1)
        for p2 in ([n2, _bump(n2, 1)] if m == 0 else [_bump(n2, 1)]):
            mp = [n1] + [n2 + x for x in paths(m + 1, "chain")[:m]] + [w2] + [p2 + x for x in paths(rem, "chain")]
            if rem >= 1 and P.capture_ok(st, (n1, n2, w2, p2)):
                out.append(("nl", (target,), tuple(mp)))
    return out


def deep_forms(P: Prep, st: Site, names: tuple, types: tuple) -> list[tuple]:
    """For a site whose later components are tactic targets (they need plain names, not projection paths): the second field, an ∧
    chain (its type from the probe), split again with `rcases` until every target component has a plain name: `rcases e` (Lean's
    names n1, n2), `rcases n2` (And's fields left / right), `rcases right` (left_1 and right again: the consumed name is free) ..;
    the components after the last split are the And-chain paths of the last right name. Name guesses: the field names first free
    in the statement, the proof before the site and the level names already taken (and, when a name may be taken, the next one)."""
    tg = {i for i, c in enumerate(st.comps) if c.name and st.targets.get(c.name)}
    if not tg or st.rebound or st.k < 3:
        return []
    parts = and_parts(types[1])
    if len(parts) < st.k - 1 or any(x.startswith(("∃", "Σ")) for x in parts[:st.k - 2]):
        return []   # the components after the first are not a plain ∧ chain of the second field
    n1, n2 = names
    D = set(WORD_RE.findall(P.statement))
    M = set(WORD_RE.findall(P.code(0, st.kw)))
    out = []
    for loose in (False, True):
        taken = D | {n1, n2} | (set() if loose else M)
        seqL = [ANL[0]] + [f"{ANL[0]}_{i}" for i in range(1, 8)]
        seqR = [ANL[1]] + [f"{ANL[1]}_{i}" for i in range(1, 8)]
        R = next((x for x in seqR if x not in taken - {n2}), None)   # the split second field is consumed: its name is free
        if R is None:
            return out
        mapping, lines, cur, i = [n1] + [None] * (st.k - 1), [], n2, 1
        while i < st.k - 1 and any(j >= i for j in tg):   # a target in the tail would be a path: split once more
            L = next((x for x in seqL if x not in taken), None)
            if L is None:
                break
            taken.add(L)
            lines.append(cur)
            mapping[i] = L
            cur, i = R, i + 1
        if not lines:
            continue
        rem = st.k - i
        for q, x in enumerate(paths(rem, "chain")):
            mapping[i + q] = cur + x
        mp = tuple(m if st.comps[j].kind == "name" else None for j, m in enumerate(mapping))
        f = ("nl", tuple(lines), mp)
        if f not in out and all("." not in (mp[j] or "") for j in tg) and P.capture_ok(st, [x for x in mp if x] + [n2]):
            out.append(f)
    return out


def probe_names(messages, a: int, b: int) -> tuple | None:
    """Lean's names and types of the last two hypotheses (the new fields) of the main goal in the `trace_state` display between
    declaration lines a and b, else None."""
    from harness.tools.t4_nameless import parse_goals
    for m in messages or []:
        line = (m.get("pos") or {}).get("line")
        if m.get("severity") != "information" or not isinstance(line, int) or not (a <= line < b):
            continue
        g = parse_goals(m.get("data"))
        if not g:
            continue
        if len(g[0]["hyps"]) < 2:   # the main goal first: the one `rcases` acted on (other goals of the block may follow)
            return None
        (x, tx), (y, ty) = g[0]["hyps"][-2], g[0]["hyps"][-1]
        if "✝" in x + y or not NAME_RE.fullmatch(x) or not NAME_RE.fullmatch(y) or x == y:
            return None
        return (x, y), (tx, ty)
    return None


def marks_of(messages) -> dict:
    out = {}
    for m in messages or []:
        d = str(m.get("data", ""))
        if m.get("severity") == "information" and d.startswith(MARK + " "):
            tag = d[len(MARK) + 1:].strip()
            out["END" if tag == "END" else (int(tag) if tag.isdigit() else None)] = (m.get("pos") or {}).get("line")
    return out


def find_site(P: Prep, sid: int) -> Site | None:
    for s in P.sites:
        if s.sid == sid:
            return s
    return None


def _base(name: str) -> str:
    return re.sub(r"_\d+$", "", name)


def _bump(name: str, n: int) -> str:
    """Lean's name for a hypothesis whose name (and n - 1 of its `_k` forms) is taken: `h` -> `h_n`, `h_1` -> `h_(1+n)`."""
    m = re.fullmatch(r"(.*)_(\d+)", name)
    return f"{m.group(1)}_{int(m.group(2)) + n}" if m else f"{name}_{n}"


def apply_many(proof: str, statement: str, choices: list[tuple[int, tuple]]) -> tuple[str | None, list]:
    """Apply several (site id, form) choices: the last site first, each one found again (same pattern offset) on the text the later
    ones left. An exw site inside the scope of earlier exw sites of the same joint takes Lean's `_k` names (the earlier ones hold
    the plain names there). Returns (the new proof or None when nothing applied, the choices applied)."""
    cur, done = proof, []
    P0 = Prep(proof, statement)
    exws = [(sid, f) for sid, f in choices if f[0] == "exw"]
    adj = {}
    for sid, f in exws:   # a field name of an exw site inside the scope of n earlier exw sites with that field: the n-th `_k` form
        B = find_site(P0, sid) if P0.ok else None
        if B is None:
            continue
        names = list(f[2])
        for q in range(len(names)):
            n = sum(1 for s2, f2 in exws if s2 < sid and _base(f2[2][q]) == _base(names[q])
                    and (A := find_site(P0, s2)) is not None and A.ss <= B.kw < A.se)
            if n:
                names[q] = _bump(names[q], n)
        if tuple(names) != tuple(f[2]):
            adj[sid] = (f[0], f[1], tuple(names))
    for sid, form in sorted(choices, key=lambda x: -x[0]):
        P = Prep(cur, statement)
        if not P.ok:
            break
        st = find_site(P, sid)
        if st is None:
            continue
        if sid in adj and P.nameless_ok(st):
            own = {c.name for c in st.comps if c.name}
            if (set(adj[sid][2]) - own) & set(WORD_RE.findall(P.code(st.ss, st.se))):
                continue
            form = adj[sid]
        elif form not in st.forms and not (form[0] in ("exw", "nl") and P.nameless_ok(st)):
            continue
        b = edit(P, st, form)
        if b is None:
            continue
        cur = P.head + b
        done.append((sid, form))
    return (cur if done else None), done


# ------------------------------------------------------------------------------------------------------------------------------ query
def renamed(statement: str, i) -> str | None:
    m = DECL_RE.match(statement)
    if not m:
        return None
    vis = "".join(w + " " for w in re.findall(r"\b(private|protected|noncomputable|nonrec)\b",
                                              re.sub(r"/--(?:(?!-/).)*-/|@\[[^\]]*\]", " ", m.group("mods"), flags=re.S)))
    # the visibility modifiers and the name's namespace are kept: a private theorem may use private declarations, and Lean resolves
    # the body's names in the theorem's namespace (`theorem A.B.c` sees `A.B.x` as `x`)
    pre = (m.group("pre") or "").strip()
    return (pre + "\n" if pre else "") + f"{vis}theorem {m.group('ns') or ''}lraPP{i}" + (m.group("univ") or "") + statement[m.end():]


def budget(compile_s) -> int:
    per = max(1.0, float(compile_s) / 2.0) if isinstance(compile_s, (int, float)) and compile_s > 0 else DEFAULT_VARIANT_S
    return max(2, min(MAX_VARIANTS, int(MEASURE_S / per)))


def file_text(statement: str, bodies: list[str]) -> str | None:
    parts = ["theorem lraPPDummy : True := trivial\n"]
    for i, b in enumerate(bodies):
        r = renamed(statement, i)
        if r is None:
            return None
        parts.append(f'#print "{MARK} {i}"\n' + r.rstrip() + " :=" + b.rstrip() + "\n")
    parts.append(f'#print "{MARK} END"\n')
    return "".join(parts)


def parse_file(messages, n: int) -> dict:
    """{i: True / False} for the copies whose marker and the next one both printed (False: an error or a sorry warning between)."""
    marks, errs = {}, []
    for m in messages or []:
        if not isinstance(m, dict):
            continue
        line = (m.get("pos") or {}).get("line")
        data = str(m.get("data", ""))
        sev = m.get("severity")
        if sev == "information" and data.startswith(MARK + " "):
            tag = data[len(MARK) + 1:].strip()
            marks["END" if tag == "END" else (int(tag) if tag.isdigit() else None)] = line
        elif isinstance(line, int) and (sev == "error" or SORRY_RE.search(data)):
            errs.append(line)
    out = {}
    for i in range(n):
        a = marks.get(i)
        b = marks.get(i + 1) if i + 1 < n else marks.get("END")
        if not isinstance(a, int) or not isinstance(b, int):
            continue
        out[i] = not any(a <= x < b for x in errs)
    return out


def _sig(P: Prep, st: Site, form: tuple) -> str:
    return sha(P.statement, P.site_text(st), P.body[st.ss:st.se], repr(form), st.t or "")


def saving(P: Prep, st: Site, form: tuple) -> int:
    b = edit(P, st, form)
    return (count_tokens(P.body) - count_tokens(b)) if b is not None else -1


def query(proof: str, statement: str, run, *, versions=None, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict:
    """The single-site compile screen (module docstring, "query"). run(text, version) -> a CompileResult-like with messages, charged
    by the caller. Returns {"projpath_query": {...}, "projpath_query_for": proof key}; q["ok_forms"][sid] lists the forms that
    compiled (static ones and the ones Lean's names from a probe gave)."""
    log = log or (lambda *a: None)
    st_ = stats if stats is not None else {}
    key = K.proof_key(proof)
    q = {"usable": False, "ok": {}, "ok_forms": {}, "tested": {}, "files": 0, "cached": 0, "probes": 0, "probed": 0}
    P = Prep(proof, statement)
    if not P.ok or not P.sites:
        q["skip"] = "no site"
        return {"projpath_query": q, "projpath_query_for": key}
    if renamed(statement, 0) is None:
        q["skip"] = "not a theorem / lemma statement"
        return {"projpath_query": q, "projpath_query_for": key}
    n = budget((ctx or {}).get("compile_s"))
    forms = {s.sid: list(s.forms) for s in P.sites}   # per site; a probe appends the forms Lean's names allow
    res: dict = {}   # (sid, form) -> bool
    sav: dict = {}
    probed: dict = {}   # sid -> ((names), (types)) or None

    def sv(s: Site, f: tuple) -> int:
        k = (s.sid, f)
        if k not in sav:
            sav[k] = saving(P, s, f)
        return sav[k]

    for s in P.sites:
        for f in forms[s.sid]:
            with _LOCK:
                c = _CACHE.get(_sig(P, s, f))
            if c is not None:
                res[(s.sid, f)] = c
                q["cached"] += 1
        with _LOCK:
            pk = _CACHE.get("probe:" + _sig(P, s, ("probe",)))
        if pk is not None:   # a probe answer of an earlier pass: (names, types) or () for "no names"
            probed[s.sid] = pk or None
            for f in (probe_forms(P, s, *pk) if pk else []):
                if f not in forms[s.sid]:
                    forms[s.sid].append(f)
                with _LOCK:
                    c = _CACHE.get(_sig(P, s, f))
                if c is not None:
                    res[(s.sid, f)] = c

    def best_ok(s: Site) -> int:
        return max([sv(s, f) for f in forms[s.sid] if res.get((s.sid, f)) is True], default=0)

    def todo() -> list[tuple[int, tuple]]:
        """The next (site, form) tests: breadth first over the forms' rank, sites by their saving; a form is worth a test while it
        would save more than the site's best compiling form."""
        out = []
        for rank in range(max(len(v) for v in forms.values())):
            lvl = []
            for s in P.sites:
                fs = forms[s.sid]
                if rank >= len(fs):
                    continue
                f = fs[rank]
                if (s.sid, f) in res or sv(s, f) <= best_ok(s):
                    continue
                lvl.append((-sv(s, f), s.sid, rank))
            out += [(sid, forms[sid][r]) for _, sid, r in sorted(lvl)]
        return out

    def probe_due(s: Site) -> bool:
        """A site whose nameless guesses all failed (or that has none) and whose nameless form would beat its best compiling form."""
        if s.sid in probed or not P.nameless_ok(s):
            return False
        nl = [f for f in forms[s.sid] if f[0] in ("exw", "nl")]
        if any(res.get((s.sid, f)) is True for f in nl) or any((s.sid, f) not in res for f in nl):
            return False
        ub = sv(s, ("exw", 1, EXW))
        if ub <= 0 and s.deep_ok:
            ub = 2 * s.k - 3   # the deep form: the pattern goes, one `rcases` line per extra level comes
        return ub > best_ok(s)

    control = True
    while q["files"] < QUERY_FILES:
        tests = todo()
        prb = [s for s in P.sites if probe_due(s)]
        if not tests and not prb:
            break
        room = n - (1 if control else 0)
        tests = tests[:room]
        prb = prb[:max(0, room - len(tests))]
        bodies = ([P.body] if control else [])
        keep_t, keep_p = [], []
        for sid, f in tests:
            b = edit(P, find_site(P, sid), f)
            if b is None:
                res[(sid, f)] = False
                continue
            bodies.append(b); keep_t.append((sid, f))
        for s in prb:
            b = edit(P, s, ("probe",))
            if b is None:
                probed[s.sid] = None
                continue
            bodies.append(b); keep_p.append(s)
        if len(bodies) == (1 if control else 0):
            continue
        text = file_text(statement, bodies)
        if text is None:
            q["skip"] = "the statement cannot be renamed"; break
        r = run(text, None)
        q["files"] += 1
        msgs = getattr(r, "messages", None)
        got = parse_file(msgs, len(bodies))
        off = 1 if control else 0
        if control:
            if got.get(0) is not True:
                q["skip"] = "the control copy did not compile: " + str((getattr(r, "errors", None) or ["?"])[0])[:160]
                log(f"projpath: query unusable ({q['skip'][:120]})")
                break
            control = False
            q["usable"] = True
        for k, (sid, f) in enumerate(keep_t):
            v = got.get(k + off)
            if v is None:
                continue
            res[(sid, f)] = v
            with _LOCK:
                _CACHE[_sig(P, find_site(P, sid), f)] = v
        mk = marks_of(msgs)
        for k, s in enumerate(keep_p):
            i = k + off + len(keep_t)
            lo, hi = mk.get(i), (mk.get(i + 1) if i + 1 < len(bodies) else mk.get("END"))
            got_p = probe_names(msgs, lo, hi) if isinstance(lo, int) and isinstance(hi, int) else None
            probed[s.sid] = got_p
            q["probes"] += 1
            with _LOCK:
                _CACHE["probe:" + _sig(P, s, ("probe",))] = got_p or ()
            if got_p:
                q["probed"] += 1
                for f in probe_forms(P, s, *got_p):
                    if f not in forms[s.sid]:
                        forms[s.sid].append(f)
    if not control:
        q["usable"] = True
    if q["cached"] and not q["files"]:
        q["usable"] = True   # every answer came from this process's cache
    for s in P.sites:
        fs = forms[s.sid]
        oks = [fi for fi, f in enumerate(fs) if res.get((s.sid, f)) is True]
        q["tested"][str(s.sid)] = {str(fi): res.get((s.sid, f)) for fi, f in enumerate(fs) if (s.sid, f) in res}
        if oks:
            q["ok"][str(s.sid)] = oks
            q["ok_forms"][str(s.sid)] = [fs[fi] for fi in oks]
    st_["query"] = {"sites": len(P.sites), "files": q["files"], "cached": q["cached"], "ok_sites": len(q["ok"]),
                    "probes": q["probes"], "probed": q["probed"]}
    abbr = {"drop": "d", "chain": "c", "flat": "f", "exw": "x", "nl": "n"}

    def tag(f):
        if f[0] == "chain":
            return f"c{f[1]}"
        if f[0] == "exw":
            return "x_" + f[2][1]
        if f[0] == "nl":
            return "n" + str(len(f[1]) + 1)
        return abbr[f[0]]
    detail = " ".join(f"L{P.line_of(s.kw) + P.head.count(chr(10)) + 1}:" + ",".join(
        f"{tag(f)}{'+' if res[(s.sid, f)] else '-'}" for f in forms[s.sid] if (s.sid, f) in res)
        + ("" if s.sid not in probed else ",p" + ("+" if probed[s.sid] else "-")) for s in P.sites)
    q["detail"] = detail
    log(f"projpath: {len(P.sites)} site(s), {q['files']} file(s) of {n}, {len(q['ok'])} site(s) with a compiling form"
        + (f", {q['cached']} cached" if q["cached"] else "") + (f", {q['probed']}/{q['probes']} probe(s) read" if q["probes"] else "")
        + f" [{detail}]")
    return {"projpath_query": q, "projpath_query_for": key}


# ------------------------------------------------------------------------------------------------------------------------------ generate
def sites(proof: str, statement: str) -> list[Site]:
    P = Prep(proof, statement)
    return P.sites if P.ok else []


def _note(P: Prep, choices) -> str:
    parts = []
    for sid, form in choices:
        s = find_site(P, sid)
        if s is None:
            continue
        ln = P.line_of(s.kw) + P.head.count("\n") + 1
        extra = form[1] if form[0] == "chain" else ""
        if form[0] == "exw":
            extra = "/" + "/".join(form[2])
        elif form[0] == "nl":
            extra = "/" + "+".join(form[1]) + "/" + "/".join(x or "_" for x in form[2])
        parts.append(f"L{ln} {s.kind} k{s.k} {form[0]}{extra}")
    return "; ".join(parts)


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int | None = None,
               ctx: dict | None = None) -> list[dict]:
    hb = K.head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    P = Prep(proof, statement)
    if not P.ok or not P.sites:
        return []
    ctx = ctx or {}
    q = ctx.get("projpath_query") if ctx.get("projpath_query_for") == K.proof_key(proof) else None
    em = K.Emitter(proof, statement, head, body, int(max_per_op) if max_per_op else MAX_PER_OP)
    usable = bool(q and q.get("usable"))
    best: list = []   # (saving, sid, form)
    if usable:
        for s in P.sites:
            oks = [tuple(f) for f in ((q.get("ok_forms") or {}).get(str(s.sid)) or [])]
            if oks:
                f = max(oks, key=lambda x: (saving(P, s, x), -oks.index(x)))
                best.append((saving(P, s, f), s.sid, f))
    else:
        for s in P.sites:
            best.append((saving(P, s, s.forms[0]), s.sid, s.forms[0]))
    best = [b for b in best if b[0] > 0]
    best.sort(key=lambda x: (-x[0], x[1]))
    if len(best) >= 2:
        ch = [(sid, f) for _, sid, f in best]
        new, done = apply_many(proof, statement, ch)
        if new is not None:
            em.add("projpath:joint", split_declaration(new, statement), "joint: " + _note(P, done))
        if usable and len(best) >= 3:
            for drop in best[:3]:
                ch2 = [(sid, f) for _, sid, f in best if sid != drop[1]]
                new, done = apply_many(proof, statement, ch2)
                if new is not None:
                    em.add("projpath:joint", split_declaration(new, statement), f"joint-1: " + _note(P, done))
    for sv, sid, f in best:
        s = find_site(P, sid)
        b = edit(P, s, f)
        if b is not None:
            em.add("projpath:site", b, f"site: {_note(P, [(sid, f)])} (-{sv})")
    if not usable:
        sec = []
        for s in P.sites:
            if len(s.forms) > 1:
                sv = saving(P, s, s.forms[1])
                if sv > 0:
                    sec.append((sv, s.sid, s.forms[1]))
        for sv, sid, f in sorted(sec, key=lambda x: (-x[0], x[1])):
            s = find_site(P, sid)
            b = edit(P, s, f)
            if b is not None:
                em.add("projpath:site", b, f"site: {_note(P, [(sid, f)])} (-{sv})")
    joint = [c for c in em.out if c["op"] == "projpath:joint"]
    single = [c for c in em.out if c["op"] == "projpath:site"]
    return joint + single


def describe(proof: str, statement: str) -> list[dict]:
    P = Prep(proof, statement)
    out = []
    for s in P.sites:
        out.append({"sid": s.sid, "line": P.line_of(s.kw) + P.head.count("\n") + 1, "kind": s.kind, "k": s.k,
                    "comps": [c.text for c in s.comps], "blocked": sorted(s.blocked), "t": s.t, "droppable": s.droppable,
                    "uses": {k: len(v) for k, v in s.uses.items()},
                    "forms": [(f, saving(P, s, f)) for f in s.forms], "scope_lines": [P.line_of(s.ss), P.line_of(max(s.ss, s.se - 1))]})
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="projpath sites and pure candidates of one proof")
    ap.add_argument("--file", required=True); ap.add_argument("--statement-file", required=True)
    a = ap.parse_args(argv)
    proof, st = Path(a.file).read_text(), Path(a.statement_file).read_text().rstrip("\n")
    for d in describe(proof, st):
        print(json.dumps(d, ensure_ascii=False))
    for c in candidates(proof, st):
        print(json.dumps({"op": c["op"], "note": c["note"]}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
