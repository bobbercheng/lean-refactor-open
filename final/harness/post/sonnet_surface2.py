#!/usr/bin/env python3
"""Op "sonnet_surface2" (lane sonnet surface v15, SURFACE / LEXER rules): token-saving local rewrites, each screened by Lean before it is proposed.

Rules (pure, on the proof body; every site carries its exact token saving under scorer/tokenize.py):
  dot     `Ns.f x` -> `x.f`                    Ns a capitalised namespace, f one lowercase name, x a local-looking identifier (one token
                                               fewer; Lean's field notation finds `Ns.f` when x's type is headed by `Ns`, else the site fails)
  dotp    `(Ns.f x).g` -> `x.f.g`              (four tokens fewer: the parentheses, the name and the argument merge into one dotted token)
  bindty  `λx : T =>` / `λ x y : T ↦` -> `λx =>`; `fun (x : T) =>` -> `fun x =>`; `∑ x : T,` / `∀ x : T,` / `∃ x : T,` -> without `: T`
          (the binder type is inferred from the use; fails when it is not)
  bypar   `f a (by tac)` ending its term -> `f a $ by tac`; `exact (by tac)` / `⟨a, (by tac)⟩` -> `by tac` (the parentheses of a final
          `by` block are redundant)
  ascr    `(e : T)` -> `e`  e an identifier / numeral, not in a binder position  (the type is inferred from the context; fails when not)
  coe     `(x : T)` -> `↑x`                    the same site's second spelling (a coercion; 3 tokens fewer when T is one token)
  ascr2   `(E : T)` -> `(E)`  for a compound E (the expected type is then the context's)
  eta     `(λx => F args x)` -> `(F args)` / `F`   (x only as the last argument; the abstraction is the whole parenthesised term)
Engine (query): the sites alone are measured in one-file batches (harness/post/d4_measure.py: the incumbent as control, each variant its own
`#eval` elaboration with its heartbeat reading); the variants that elaborate and are predicted not to lose are combined, and the combination
is itself checked (halved on failure, <= JOINT_TRIES files).  Candidates: the verified combination, then the best verified singles.  The gate
(open_post.improve_row, unchanged) decides; nothing here is trusted.  No row names, tables or proof text: rules read syntax only."""

# provenance: research lane gaplane2-sonnet (worktree lra-gl2-sonnet), commit c9d1fb4 (code of 81b99b1, surface v15), ported into open-post-v5-lanes (2026-11-04) as sonnet_surface2 (renamed: open-post-v3 already has a module sonnet_surface; only its op/family names changed)
from __future__ import annotations

import re, sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs, KEYWORDS as TACTICS  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "sonnet_surface2"
MAX_SITES = 60
JOINT_TRIES = 3
NS = r"[A-Z][\w']*(?:\.[A-Z][\w']*)*"
LOCAL = r"[a-z_][\w'₀-₉]*(?:\.(?:\d+|[a-z_][\w'₀-₉]*))*"
DOT_RE = re.compile(rf"(?<![\w.'])({NS})\.([a-z_][\w'!?]*)[ ]+({LOCAL})(?![\w.'(⟨\[])")
DOTP_RE = re.compile(rf"\(({NS})\.([a-z_][\w'!?]*)[ ]+({LOCAL})\)(\.[\w'.]+)")
ASCR_RE = re.compile(r"\(([\w'₀-₉]+(?:\.[\w'₀-₉]+)*)[ ]*:(?!=)[ ]*([^()\n:]+?)\)")
BINDER_BEFORE = re.compile(r"(?:λ|\bfun|[∀∃∑∏]|\bintro|\brintro|\bhave [\w'₀-₉]+(?: [\w'₀-₉]+)*|\bobtain|\blet [\w'₀-₉]+|\btheorem [\w.']+|\bset|\bchoose!?|\bcases'?)[ ]*(?:(?:\([^()]*\)|\{[^{}]*\}|⦃[^⦃⦄]*⦄|\[[^\[\]]*\])[ ]*)*$")
ASCR2_RE = re.compile(r"\(([^()\n:]*?[^()\n: ])[ ]*:(?!=)[ ]*([^()\n:]+?)\)")
DOT_STOP = frozenset("fun by at with using from then else do in show have let if match".split())
LAM_RE = re.compile(r"(λ|\bfun\b)[ ]*((?:[a-z_][\w'₀-₉]*[ ]*)+):[ ]*([^=↦,⟨⟩]*?)[ ]*(=>|↦)")
QUANT_RE = re.compile(r"([∑∏∀∃])[ ]*((?:[a-z_][\w'₀-₉]*[ ]+)*[a-z_][\w'₀-₉]*)[ ]*:[ ]*([^,=:]*?)[ ]*,")
PARLAM_RE = re.compile(r"(λ|\bfun\b)[ ]*\(([a-z_][\w'₀-₉]*)[ ]*:[ ]*([^()]*)\)[ ]*(=>|↦)")
ETA_RE = re.compile(r"\((?:λ|fun)[ ]*([a-z_][\w'₀-₉]*)[ ]*(?:=>|↦)[ ]*([\w.'₀-₉]+(?:[ ]+[\w.'₀-₉]+)*)[ ]+\1\)")
KEYWORD_BEFORE = re.compile(r"(?:exact|refine|apply|exacts|use|from|:=|,|\(|\[|⟨|\{|<;>|\||\$|<\|)\s*$")


@dataclass(frozen=True)
class Edit:
    start: int
    end: int
    text: str
    rule: str
    dtok: int

    def overlaps(self, o: "Edit") -> bool:
        return self.start < o.end and o.start < self.end


def _masked(body: str) -> str:
    m = _mask(body)
    return "".join(" " if m[i] and body[i] != "\n" else body[i] for i in range(len(body)))


def sites(body: str) -> list[Edit]:
    """All rule sites of the body, each with its exact local token saving (counted on the edited line pair), best first."""
    clean = _masked(body)
    raw: list[tuple[int, int, str, str]] = []
    for m in DOT_RE.finditer(clean):
        if m.group(3) in DOT_STOP:
            continue
        raw.append((m.start(), m.end(), f"{m.group(3)}.{m.group(2)}", "dot"))
    for m in ASCR_RE.finditer(clean):
        if m.group(1) in ("by", "fun") or m.group(1).startswith("λ") or "=>" in m.group(2) or "↦" in m.group(2) or BINDER_BEFORE.search(clean[max(0, m.start() - 60):m.start()]):
            continue
        raw.append((m.start(), m.end(), m.group(1), "ascr"))
        if not m.group(1)[0].isdigit():
            raw.append((m.start(), m.end(), "↑" + m.group(1), "coe"))   # a cast: the arrow, when the bare name does not elaborate
    for m in ASCR2_RE.finditer(clean):
        e, t = m.group(1), m.group(2)
        if (" " not in e.strip() and "." not in e.strip() and e.strip().replace("'", "").isalnum()) or "=>" in t or "↦" in t or "=>" in e or "↦" in e:
            continue   # a plain identifier: rule ascr; a binder / lambda: not here
        if e.lstrip().startswith(("λ", "fun", "by", "show", "↑")) or BINDER_BEFORE.search(clean[max(0, m.start() - 60):m.start()]):
            continue
        raw.append((m.start(), m.end(), f"({e})", "ascr2"))
    for m in DOTP_RE.finditer(clean):
        if m.group(3) in DOT_STOP:
            continue
        raw.append((m.start(), m.end(), f"{m.group(3)}.{m.group(2)}{m.group(4)}", "dotp"))
    for m in LAM_RE.finditer(clean):
        binders = m.group(2).strip()
        raw.append((m.start(), m.end(), f"{m.group(1)}{binders} {m.group(4)}" if m.group(1) == "λ" else f"fun {binders} {m.group(4)}", "bindty"))
    for m in PARLAM_RE.finditer(clean):
        raw.append((m.start(), m.end(), f"{m.group(1)}{m.group(2)} {m.group(4)}" if m.group(1) == "λ" else f"fun {m.group(2)} {m.group(4)}", "bindty"))
    for m in QUANT_RE.finditer(clean):
        raw.append((m.start(), m.end(), f"{m.group(1)} {m.group(2)},", "bindty"))
    for m in ETA_RE.finditer(clean):
        f = m.group(2).strip()
        raw.append((m.start(), m.end(), f if len(f.split()) == 1 else f"({f})", "eta"))
    raw += _bypar(body, clean)
    raw += _anon(body, clean)
    raw += _havedrop(body, clean)
    raw += _showfrom(body, clean)
    # _casesp disabled: `cases'` passes the primary pin but is an unknown tactic on another pin (gate verdict 'unknown tactic'), poisoning joint candidates
    raw += _smallsyn(body, clean)
    out: list[Edit] = []
    seen = set()
    for a, b, text, rule in raw:
        if body[a:b] == text or (a, b, text) in seen:
            continue
        seen.add((a, b, text))
        d = count_tokens(body[a:b]) - count_tokens(text)
        if rule == "bypar":
            d = _local_dtok(body, a, b, text)
        if d > 0:
            out.append(Edit(a, b, text, rule, d))
    out.sort(key=lambda e: (-e.dtok, e.start))
    return out


ANON_PRE = re.compile(r"(?:\bexact|\brefine'?|\bexacts|:=|\bfrom|\$|<\||=>|↦|·)[ ]*$")
ATOM_RE = re.compile(r"[\w.'₀-₉?!]+$")
OPEN_B, CLOSE_B = "(⟨[{⦃", ")⟩]}⦄"


def _split_top(inner: str) -> list[str] | None:
    parts, depth, cur = [], 0, []
    for ch in inner:
        if ch in OPEN_B:
            depth += 1
        elif ch in CLOSE_B:
            depth -= 1
            if depth < 0:
                return None
        if ch == "," and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    parts.append("".join(cur))
    return parts


def _closes(c: str) -> bool:
    depth = 0
    for i, ch in enumerate(c):
        if ch in OPEN_B:
            depth += 1
        elif ch in CLOSE_B:
            depth -= 1
            if depth == 0 and i < len(c) - 1:
                return False
    return depth == 0


def _grp(c: str, final: bool) -> str | None:
    c = c.strip()
    if not c or "\n" in c or "·" in c:
        return None
    if ATOM_RE.match(c):
        return c
    if c[0] in "(⟨[" and c[-1] in CLOSE_B and _closes(c):
        return c
    if final:
        return "$ " + c
    return "(" + c + ")"


def _nest(gs: list[str]) -> str:
    if len(gs) == 2:
        return f".intro {gs[0]} {gs[1]}"
    return f".intro {gs[0]} $ {_nest(gs[1:])}"


PATTERN_KW = frozenset("rintro intro obtain rcases cases cases' induction match fun λ with rename_i case at using from else then in do have let show by exact refine apply".split())
PATTERN_LINE = re.compile(r"^[ \t]*(?:·[ \t]*)?(?:rintro|intro|obtain|rcases|cases'?|induction'?|match|fun|λ|rename_i|case|\|)\b")


def _lastarg_ok(clean: str, o: int) -> bool:
    """`f x ⟨..⟩` ending its term: the bracket is the last argument of an application (not a pattern)."""
    ls = clean.rfind("\n", 0, o) + 1
    line = clean[ls:o]
    m = re.search(r"([\w'.₀-₉]+|[)\]⟩}])[ ]+$", line)
    if not m or m.group(1) in PATTERN_KW:
        return False
    if PATTERN_LINE.match(line) and ":=" not in line and "=>" not in line:
        return False
    return "=>" not in line[-4:] and not re.search(r"\b(?:rintro|intro|rcases|obtain|cases|fun|λ|with)\b[^:=]*$", line)


def _anon(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    """`⟨a, b⟩` in a term position with a known expected type -> `.intro a b` / `.mk a b` (two to four components)."""
    out = []
    pairs = _pairs(body, _mask(body))
    for o, c in pairs.items():
        if body[o] != "⟨":
            continue
        inner = clean[o + 1:c]
        if "\n" in inner:
            continue
        pre = clean[max(0, o - 12):o]
        j = c + 1
        while j < len(body) and body[j] in " \t":
            j += 1
        nxt = body[j] if j < len(body) else "\n"
        arg = False
        if re.search(r"[,⟨][ ]*$", pre):
            if nxt != "⟩":
                continue
        elif ANON_PRE.search(pre):
            if nxt not in "\n)]}⟩":
                continue
        elif nxt in "\n)]}" and _lastarg_ok(clean, o):
            arg = True
        else:
            continue
        parts = _split_top(inner)
        if not parts or len(parts) < 2 or len(parts) > 4:
            continue
        gs = [_grp(x, k == len(parts) - 1) for k, x in enumerate(parts)]
        if any(g is None for g in gs):
            continue
        a0, pfx = o, ""
        if arg:
            a0, pfx = o, "$ "
            while a0 > 0 and body[a0 - 1] in " \t":
                a0 -= 1
            pfx = " $ "
        if len(parts) == 2:
            for nm in (".intro", ".mk"):
                out.append((a0, c + 1, f"{pfx}{nm} {gs[0]} {gs[1]}", "anon"))
        else:
            out.append((a0, c + 1, pfx + ".mk " + " ".join(gs), "anon"))
            out.append((a0, c + 1, pfx + f".intro {gs[0]} $ {_nest(gs[1:])}".replace("$ $", "$"), "anon"))
    return out


HAVE_RE = re.compile(r"(?m)^[ \t]*(?:·[ \t]*)?(?:have(?:[ \t]+[\w'₀-₉]+)?|(?:let|set)[ \t]+[\w'₀-₉]+)[ \t]*:(?!=)")


def _havedrop(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    """`have h : T := E` (E a term, not a `by` block / lambda) -> `have h := E`: the type is inferred from E."""
    out = []
    for m in HAVE_RE.finditer(clean):
        colon = m.end() - 1
        a = colon
        while a > 0 and clean[a - 1] in " \t":
            a -= 1
        depth, i, n = 0, colon + 1, len(clean)
        end = None
        while i < min(n, colon + 500):
            ch = clean[i]
            if ch in OPEN_B:
                depth += 1
            elif ch in CLOSE_B:
                depth -= 1
                if depth < 0:
                    break
            elif ch == ":" and clean[i + 1:i + 2] == "=" and depth == 0:
                end = i
                break
            elif depth == 0 and clean.startswith(" by", i) and not clean[i + 3:i + 4].isalnum():
                break   # `have h : T by` / a `by` inside the type at depth 0: not this shape
            i += 1
        if end is None:
            continue
        rest = clean[end + 2:end + 60].lstrip()
        if re.match(r"(?:by\b|fun\b|λ|\?_|_\s*$)", rest) or not rest:
            continue
        out.append((a, end, " ", "havedrop"))
    return out


CASES_RE = re.compile(
    r"(?m)^([ \t]*(?:·[ \t]*)?)(?:obtain[ \t]+⟨[ \t]*([\w'₀-₉]+)[ \t]*,[ \t]*([\w'₀-₉]+)[ \t]*⟩[ \t]*:=[ \t]*([^\n]+?)"
    r"|rcases[ \t]+([^\n]+?)[ \t]+with[ \t]+⟨[ \t]*([\w'₀-₉]+)[ \t]*,[ \t]*([\w'₀-₉]+)[ \t]*⟩)[ \t]*$")


def _casesp(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    """`obtain ⟨x, y⟩ := E` / `rcases E with ⟨x, y⟩` (two plain names, one line) -> `cases' E with x y` (3 tokens fewer)."""
    out = []
    for m in CASES_RE.finditer(clean):
        e = m.group(4) or m.group(5)
        x, y = (m.group(2), m.group(3)) if m.group(4) else (m.group(6), m.group(7))
        if re.search(r"\bby\b|<;>|\||:=|\bfun\b|λ|\bwith\b|[;]", e) or e.endswith(","):
            continue
        # a continuation line (more indented than the tactic) belongs to the term: skip
        ind = len(m.group(1).replace("·", " "))
        nxt = re.match(r"[ \t]*\n([ \t]*)\S", clean[m.end():])
        if nxt and len(nxt.group(1)) > ind:
            continue
        out.append((m.start() + len(m.group(1)), m.end(), f"cases' {e} with {x} {y}", "casesp"))
    return out


REFINE2_RE = re.compile(r"(?<![\w'.])refine'?[ \t]*⟨[ \t]*\?_[ \t]*,[ \t]*\?_[ \t]*⟩")


ELLIP_RE = re.compile(r"(?<![\w'.])_(?:[ ]+_)+(?=[ ]*(?:[)\]⟩,]|$))", re.M)
ELLIP_NOT = re.compile(r"^[ ]*(?:rename_i|intro|rintro|next|case|obtain|rcases|cases|induction|generalizing|\|)\b|(?:λ|\bfun\b|\bwith\b|\bat\b)[^\n]*$")
IDENT_END = re.compile(r"[\w.'₀-₉!?]$")
CDOT_HEAD = re.compile(r"\((?:λ|\bfun\b)[ ]*((?:[a-z][\w'₀-₉]*[ ]+)*[a-z][\w'₀-₉]*)[ ]*(?:=>|↦)[ ]*")
CDOT_BAD = re.compile(r"λ|\bfun\b|\bby\b|·|⟨|:=|\bmatch\b|\bif\b|\bshow\b|\bat\b|\bwith\b|\bfrom\b|<;>|\bhave\b|\blet\b|[∀∃∑∏∫]|\|")


def _line_next_indent(clean: str, i: int) -> int | None:
    j = clean.find("\n", i)
    if j < 0:
        return None
    k = j + 1
    while k < len(clean) and clean[k] in " \t":
        k += 1
    if k >= len(clean) or clean[k] == "\n":
        return None
    return k - (j + 1)


def _ellip(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    """`f a _ _ _` -> `f a ..` for a run of >= 2 trailing placeholder arguments that ends its application (the ellipsis fills the remaining
    explicit arguments with `_`, as the run does; a following argument on the next line / after `$` would break it and the screen says so)."""
    out = []
    for m in ELLIP_RE.finditer(clean):
        ls = clean.rfind("\n", 0, m.start()) + 1
        before = clean[ls:m.start()].rstrip()
        if not before or not IDENT_END.search(before) or ELLIP_NOT.search(clean[ls:m.end()]):
            continue
        le = clean.find("\n", m.end())
        rest_same_line = clean[m.end():le if le >= 0 else len(clean)].strip()
        if not rest_same_line:   # the line ends: a deeper-indented next line continues the application
            ni = _line_next_indent(clean, m.end())
            cur = len(clean[ls:]) - len(clean[ls:].lstrip(" \t"))
            if ni is not None and ni > cur:
                continue
        out.append((m.start(), m.end(), "..", "ellip"))
    return out


def _cdot(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    """`(λx => F x 1)` -> `(F · 1)`: every binder used exactly once, at the top level of the parenthesised body, in binder order."""
    out = []
    for m in CDOT_HEAD.finditer(clean):
        binders = m.group(1).split()
        depth, i = 1, m.end()
        while i < len(clean) and depth > 0:
            if clean[i] in OPEN_B:
                depth += 1
            elif clean[i] in CLOSE_B:
                depth -= 1
            i += 1
        if depth != 0:
            continue
        inner = clean[m.end():i - 1]
        if not inner.strip() or CDOT_BAD.search(inner) or "\n" in inner:
            continue
        top, d, order = [], 0, []
        pos = 0
        for mm in re.finditer(r"(?<![\w.'₀-₉])([a-z][\w'₀-₉]*)(?![\w'₀-₉])", inner):
            if mm.group(1) in binders:
                dd = sum(1 for ch in inner[:mm.start()] if ch in OPEN_B) - sum(1 for ch in inner[:mm.start()] if ch in CLOSE_B)
                order.append((mm.group(1), mm.start(), mm.end(), dd))
        if [o[0] for o in order] != binders or any(o[3] != 0 for o in order):
            continue
        if re.search(r",", "".join(ch if sum(1 for c in inner[:k] if c in OPEN_B) - sum(1 for c in inner[:k] if c in CLOSE_B) == 0 else " " for k, ch in enumerate(inner))):
            continue
        new, last = [], 0
        for _, a, b, _ in order:
            new.append(inner[last:a]); new.append("·"); last = b
        new.append(inner[last:])
        out.append((m.start(), i, "(" + "".join(new) + ")", "cdot"))
    return out


RWA_RE = re.compile(r"^([ ]*)(rw|rewrite)([ ]+\[[^\n]*)\n\1(assumption|exact[ ]+[\w'.₀-₉]+|exact[ ]+rfl|rfl)[ ]*$", re.M)


def _rwa(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    """`rw [..] (at h)` + next line `assumption` / `exact h` -> `rwa [..] (at h)`; `rewrite [..]` + `rfl` -> `rw [..]` (rw closes by rfl itself)."""
    out = []
    for m in RWA_RE.finditer(clean):
        rest = m.group(3)
        if ";" in rest or "<;>" in rest or rest.count("[") != rest.count("]") or rest.rstrip().endswith((",", "$", "<|")) or "by " in rest and False:
            continue
        if _split_top("(" + rest + ")") is None:
            continue
        kind = m.group(4)
        if "rfl" in kind:
            if m.group(2) == "rewrite":
                out.append((m.start(2), m.end(), "rw" + rest, "rwrfl"))
        else:
            out.append((m.start(2), m.end(), "rwa" + rest, "rwa"))
    return out


HAVE1_RE = re.compile(r"^([ ]*)have[ ]+([\w'₀-₉]+)[ ]*:=[ ]*([^\n]+)$", re.M)


def _inline1(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    """`have h := E` (one line, E without `by` / `fun`) whose name occurs exactly once later, within the next 8 lines -> the occurrence becomes `(E)` / `E` / `$ E`
    and the `have` line is deleted (a composite edit: the text between the two places is carried along)."""
    out = []
    for m in HAVE1_RE.finditer(clean):
        name, e = m.group(2), m.group(3).strip()
        if re.search(r"\bby\b|\bfun\b|λ|;|<;>|--|:=|\bfrom\b|\bshow\b|\bwith\b|\bat\b|\bhave\b", e) or not e:
            continue
        rest_from = m.end() + 1
        ni = _line_next_indent(clean, m.end())
        if ni is not None and ni > len(m.group(1)):
            continue   # the term continues on the next line
        occ = [x for x in re.finditer(r"(?<![\w.'₀-₉])" + re.escape(name) + r"(?![\w'₀-₉])", clean[rest_from:])]
        if len(occ) != 1:
            continue
        o = occ[0]
        a, b = rest_from + o.start(), rest_from + o.end()
        if clean.count("\n", rest_from, a) > 8:
            continue
        ls = clean.rfind("\n", 0, a) + 1
        if re.match(r"[ ]*(?:intro|rintro|obtain|rcases|cases|fun|λ|have|let|set|rename_i|next|case)\b", clean[ls:a]) and not re.match(r"[ ]*(?:have|let)[^:]*:=", clean[ls:a]):
            continue
        if re.search(r"\bat[ ]+(?:[\w'₀-₉]+[ ]+)*$", clean[ls:a]):
            continue
        # the occurrence must not be a binder: not preceded by `λ`/`fun`/`∀`/`∃` binder lists on its line
        if re.search(r"(?:λ|\bfun\b|[∀∃∑∏]|\bintro|\bwith)[ ]*[^\n=:]*$", clean[ls:a]):
            continue
        atom = re.fullmatch(r"[\w.'₀-₉]+", e) is not None
        dotted = clean[b:b + 1] == "."
        mid = body[rest_from:a]
        tail_ok = re.match(r"[ ]*(?:$|[)\]⟩,])", clean[b:b + 40].split("\n")[0] + "") is not None
        start = m.start()
        variants = []
        if atom:
            variants.append(e)
        elif not dotted:
            variants.append("(" + e + ")")
            if tail_ok and clean[a - 1:a] == " ":
                variants.append("$ " + e)
        else:
            variants.append("(" + e + ")")
        for v in variants:
            out.append((start, b, mid + v, "inline1"))
    return out


def _smallsyn(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    """`refine ⟨?_, ?_⟩` -> `constructor` (five fewer); `f _ _ _` -> `f ..`; `(λx => F x 1)` -> `(F · 1)`."""
    out = []
    for m in REFINE2_RE.finditer(clean):
        out.append((m.start(), m.end(), "constructor", "refine2"))
    out += _ellip(body, clean)
    out += _cdot(body, clean)
    out += _rwa(body, clean)
    out += _inline1(body, clean)
    out += _sonly(body, clean)
    return out


SONLY_RE = re.compile(r"(?<![\w'.])((?:simp|simp_all|simpa|dsimp|norm_num)(?:\?)?) only(?=[ ]*(?:\[|at\b|⊢|\n|$|<;>|;))")


def _sonly(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    """`simp only [..]` -> `simp [..]` (one token fewer; Lean and the heartbeat reading decide: the full simp set may close or cost more)."""
    out = [(m.start(), m.end(), m.group(1), "sonly") for m in SONLY_RE.finditer(clean)]
    for m in re.finditer(r"(?<![\w'.])((?:simp|simp_all|simpa|dsimp|norm_num)) only[ ]*\[", clean):
        depth, i = 1, m.end()
        while i < len(clean) and depth:
            depth += (clean[i] in "([{⟨") - (clean[i] in ")]}⟩")
            i += 1
        if depth == 0 and i - m.start() < 700:
            out.append((m.start(), i, m.group(1), "sbare"))   # the whole `only [..]` list: Lean's default simp set may close the goal alone
    return out


def _showfrom(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    """`show T from E` -> `E` (the expected type of the context replaces the annotation)."""
    out = []
    for m in re.finditer(r"(?<![\w'.])show\b", clean):
        depth, i, n = 0, m.end(), len(clean)
        while i < min(n, m.end() + 600):
            ch = clean[i]
            if ch in OPEN_B:
                depth += 1
            elif ch in CLOSE_B:
                depth -= 1
                if depth < 0:
                    break
            elif depth == 0:
                if re.match(r"from\b", clean[i:i + 5]) and not re.match(r"[\w'.]", clean[i - 1]):
                    out.append((m.start(), i + 4 + (1 if clean[i + 4:i + 5] == " " else 0), "", "showfrom"))
                    break
                if clean.startswith(":=", i) or clean.startswith("=>", i) or re.match(r"by\b", clean[i:i + 3]) and not re.match(r"[\w'.]", clean[i - 1]):
                    break
            i += 1
    return out


def _local_dtok(body: str, a: int, b: int, text: str) -> int:
    la = body.rfind("\n", 0, a) + 1
    lb = body.find("\n", b)
    lb = len(body) if lb < 0 else lb
    before = body[la:lb]
    after = body[la:a] + text + body[b:lb]
    return count_tokens(before) - count_tokens(after)


def _bypar(body: str, clean: str) -> list[tuple[int, int, str, str]]:
    out = []
    mask = _mask(body)
    pairs = _pairs(body, mask)
    for o, c in pairs.items():
        if body[o] != "(" or not re.match(r"\(by\b", clean[o:o + 4]):
            continue
        inner = body[o + 1:c]
        if "\n" in inner and not re.match(r"[ \t]*\n", body[o + 3:o + 3 + 40]) and inner.count("\n") > 8:
            continue
        j = c + 1
        while j < len(body) and body[j] in " \t":
            j += 1
        if j < len(body) and body[j] not in "\n)]}⟩,":
            continue
        if j < len(body) and body[j] == "\n":   # the next code line must start a new tactic: indented less than this `(by`'s line
            ls = body.rfind("\n", 0, o) + 1
            ind = len(body[ls:]) - len(body[ls:].lstrip(" "))
            m2 = re.match(r"(?:[ \t]*\n)*([ ]*)\S", body[j:])
            first = body[ls:].lstrip(" ").split(" ", 1)[0]
            is_tac = first in TACTICS or first.startswith("·")
            if m2 and len(m2.group(1)) >= ind + (1 if is_tac else 0):
                continue
        pre = clean[max(0, o - 40):o]
        if KEYWORD_BEFORE.search(pre):
            out.append((o, c + 1, inner, "bypar"))
        elif re.search(r"[\w'.)\]⟩}_?]\s*$", pre) and "\n" not in pre[-1:]:
            lo = o
            while lo > 0 and body[lo - 1] in " \t":
                lo -= 1
            out.append((lo, c + 1, " $ " + inner, "bypar"))
    return out


def apply(body: str, edits: list[Edit]) -> str:
    for e in sorted(edits, key=lambda x: -x.start):
        body = body[:e.start] + e.text + body[e.end:]
    return body


def combine(edits: list[Edit]) -> list[Edit]:
    """A non-overlapping subset, taking the biggest savings first."""
    chosen: list[Edit] = []
    for e in sorted(edits, key=lambda x: (-x.dtok, x.start)):
        if not any(e.overlaps(c) for c in chosen):
            chosen.append(e)
    return chosen


def has_sites(proof: str, statement: str) -> bool:
    body = split_declaration(proof, statement)
    return body is not None and bool(sites(body))


# ---------------------------------------------------------------------------------------------------------------------- engine
def _screen_plain(statement: str, body0: str, bodies: list[str], run, ver) -> list[dict] | None:
    """The same screen as plain theorem copies in ONE file (rows whose file has no `import Lean`, so d4_measure's `#eval` cannot run):
    copy i = `theorem lraD4M<i> ... := body_i`, each followed by `#check @lraD4M<i>` whose message line delimits the copy; a copy fails
    when an error message falls inside its lines.  No heartbeat reading (hb None)."""
    items = [body0] + list(bodies)
    parts = []
    nm = re.match(r"\s*(?:theorem|lemma)\s+([^\s(:{\[⦃]+)", statement)
    for i, b in enumerate(items):
        r = MS.renamed(statement, i)
        if r is None:
            return None
        if nm:   # a recursive proof calls the declaration by its own name: the copy calls itself
            b = re.sub(r"(?<![\w.'])" + re.escape(nm.group(1).split(".")[-1]) + r"(?![\w'])", f"lraD4M{i}", b)
        parts.append(r.rstrip() + " :=" + b.rstrip() + f"\n#check @lraD4M{i}\n")
    msgs = getattr(run("".join(parts), ver), "messages", None) or []
    lines: dict[int, int] = {}
    for m in msgs:
        mm = re.match(r"@?lraD4M(\d+)\b", str((m or {}).get("data", "")))
        if isinstance(m, dict) and m.get("severity") == "information" and mm and isinstance(m.get("pos"), dict):
            lines.setdefault(int(mm.group(1)), int(m["pos"]["line"]))
    if len(lines) != len(items):
        return None
    errs = [int(m["pos"]["line"]) for m in msgs if isinstance(m, dict) and m.get("severity") == "error" and isinstance(m.get("pos"), dict)]
    res, prev = [], 0
    for i in range(len(items)):
        res.append({"ok": not any(prev < e <= lines[i] for e in errs), "hb": None, "ctl": None, "pred": None})
        prev = lines[i]
    return res if res[0]["ok"] else None


def _screen(statement: str, body0: str, bodies: list[str], run, ver, ctx, exchange) -> list[dict] | None:
    """[{ok, hb, pred}] per body (None when the control did not read).  d4_measure's one-file measured batches; when its `#eval` cannot run
    (no `import Lean`) or its control does not read, the plain-copies screen (no heartbeats)."""
    n = max(2, MS.budget(ctx))
    out: list[dict] = []
    plain = False
    for i in range(0, len(bodies), n - 1):
        chunk = bodies[i:i + n - 1]
        txt = MS.text(statement, [body0] + chunk)
        if txt is None:
            return None
        rd, ctl = {}, None
        if not plain:
            rd = MS.parse(getattr(run(txt, ver), "messages", None), len(chunk) + 1)
            ctl = rd.get(0)
        if plain or not ctl or not ctl.get("ok"):
            plain = True
            pl = _screen_plain(statement, body0, chunk, run, ver)
            if pl is None:
                return None
            out += pl[1:]
            continue
        for k, b in enumerate(chunk, 1):
            v = rd.get(k) or {"ok": False}
            out.append({"ok": bool(v.get("ok")), "hb": v.get("hb"), "ctl": ctl.get("hb"), "pred": MS.predicted(ctl, body0, b, v, exchange)})
    return out


LATE_MIN_TOK = 12
_CALLS: dict[str, int] = {}   # per statement: how many times query() ran (the passes of the row)
_FAILED: dict[str, set] = {}   # per statement: edits (context + replacement) that did not elaborate, so later passes of the row skip them


def _key(body: str, e: Edit) -> str:
    return f"{e.rule}|{body[max(0, e.start - 40):e.start]}|{body[e.start:e.end]}|{e.text}|{body[e.end:e.end + 40]}"


def query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None):
    ver = (versions or [None])[0]
    try:
        body0 = split_declaration(proof, statement)
        if body0 is None or MS.renamed(statement, 0) is None:
            return None
        failed = _FAILED.setdefault(statement, set())
        es = [e for e in sites(body0) if _key(body0, e) not in failed][:MAX_SITES]
        if not es:
            return None
        calls = _CALLS[statement] = _CALLS.get(statement, 0) + 1
        if calls >= 3 or (calls == 2 and sum(e.dtok for e in es) < LATE_MIN_TOK):
            return None   # later passes of a row: the compile / wall budget of the row is worth more than a few more tokens
        exchange = (ctx or {}).get("exchange")
        singles = [apply(body0, [e]) for e in es]
        res = _screen(statement, body0, singles, run, ver, ctx, exchange)
        if res is None:
            return {"verified": None}
        for e, r in zip(es, res):
            if not r["ok"]:
                failed.add(_key(body0, e))
        good = [e for e, r in zip(es, res) if r["ok"] and (r["pred"] is None or r["pred"] > 0)]
        if not good:
            return {"verified": [], "screen": len(es)}
        pick = combine(good)
        tries = 0
        while pick and tries < JOINT_TRIES:
            tries += 1
            if len(pick) == 1:
                break
            r = _screen(statement, body0, [apply(body0, pick)], run, ver, ctx, exchange)
            if r and r[0]["ok"]:
                break
            pick = pick[:len(pick) // 2]
        return {"verified": good, "joint": pick, "screen": len(es)}
    except Exception as e:  # noqa: BLE001
        if log:
            log(f"sonnet_surface2.query error {type(e).__name__}: {str(e)[:160]}")
        return None


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    out: list[dict] = []
    try:
        head_body = K.head_body(proof, statement)
        if head_body is None:
            return []
        head, body0 = head_body
        t0 = count_tokens(body0)
        ctx = ctx or {}
        ver = ctx.get("verified")
        if ver is None:   # no Lean feedback: the biggest non-overlapping set, then the single biggest site
            es = sites(body0)
            sets = [combine(es)] + [[e] for e in es[:4]]
        else:
            sets = ([ctx["joint"]] if ctx.get("joint") else []) + [[e] for e in ver[:2]]
        em = K.Emitter(proof, statement, head, body0, 6)
        for s in sets:
            if not s:
                continue
            tag = "+".join(sorted({e.rule for e in s}))
            em.add(f"{FAMILY}:{tag}", apply(body0, list(s)), f"{len(s)} site(s) {tag}: -{sum(e.dtok for e in s)} tok")
        return em.out
    except Exception:  # noqa: BLE001
        return []
