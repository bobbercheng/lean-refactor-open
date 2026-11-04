#!/usr/bin/env python3
"""Gap-91 token-structural rule families (2026-10-16; probe/gap91/families.md, operator: close the pipeline 90.90 -> union 92.84 gap with




























"""
from __future__ import annotations

import re
import sys
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs, OPEN, CLOSE              
from harness.hb_rewrite import _first_by, _in_conv, _line_end, _ls, _code, _prev_token, TAC_PREV_SYMS, TAC_PREV_WORDS              
from scorer.tokenize import count_tokens              

IDENT_RE = re.compile(r"^[^\W\d][\w'!?]*$")
BLOCK_OPENERS = ("by", "=>", "<;>", "with", "do", ":=", "then", "else", "all_goals", "any_goals", "repeat", "repeat'", "try", "focus",
                 "classical", "unhygienic", "with_reducible", "first", "·")
SINGLE_CLOSERS = ("grind", "simp_all", "aesop", "omega", "simp", "rfl", "trivial", "assumption", "decide", "norm_num", "linarith")
MULTI_CLOSERS = ("all_goals assumption", "repeat' constructor", "all_goals simp_all",                                                       
                 "all_goals grind", "all_goals aesop", "all_goals constructor <;> assumption", "all_goals omega",
                 "all_goals rfl", "all_goals trivial", "all_goals constructor <;> simp_all")
CLOSERS = tuple(c for pair in zip(SINGLE_CLOSERS, MULTI_CLOSERS) for c in pair) + SINGLE_CLOSERS[len(MULTI_CLOSERS):] + MULTI_CLOSERS[len(SINGLE_CLOSERS):]
DEFAULT_CAPS = {"tail-closer": 24, "arg-underscore": 10, "wit-underscore": 8, "show-underscore": 6, "ih-simp": 6, "inline-have": 12,
                "obtain-proj": 8, "bullet-merge": 6, "bullet-hoist": 6, "by-exact": 8, "eta-lam": 8, "eta-intro": 6, "rwa": 8,
                "simpa": 8, "refine-constructor": 4, "constructor-pair": 4, "apply-exact": 8}
KINDS = tuple(DEFAULT_CAPS)


@dataclass(frozen=True)
class Rule:
    """One candidate edit of a body: `edits` = ((pos, delete_len, insert), ...) in body offsets, as harness.normalize.apply takes them."""
    kind: str
    edits: tuple
    note: str
    priority: int = 0


@dataclass
class Line:
    idx: int
    start: int
    end: int                                                  
    indent: int
    code: str                                            
    raw: str                         
    bullet: bool                                              
    tac: int                                                                  


                                                                                                                                       
def _lines(body: str, mask: list) -> list[Line]:
    out, s, i = [], 0, 0
    while s <= len(body):
        e = _line_end(body, s)
        k = s
        while k < e and (body[k] in " \t" or mask[k]):
            k += 1
        bullet = k < e and body[k] == "·"
        t = k + 1 if bullet else k
        while t < e and body[t] in " \t":
            t += 1
        out.append(Line(i, s, e, k - s if k < e else 0, _code(body, mask, s, e).strip(), body[s:e], bullet, t))
        s, i = e + 1, i + 1
        if e >= len(body):
            break
    return out


def _stmts(lines: list[Line], lo: int, hi: int, indent: int) -> list[tuple[int, int]]:
    """Statements (head line index, last line index) at exactly `indent` among lines[lo:hi]; deeper lines belong to the head before them;
"""
    out, i = [], lo
    while i < hi:
        ln = lines[i]
        if not ln.code:
            i += 1
            continue
        if ln.indent < indent:
            break
        if ln.indent > indent:
            i += 1
            continue
        j = i + 1
        while j < hi and (not lines[j].code or lines[j].indent > indent):
            j += 1
        last = j - 1
        while last > i and not lines[last].code:
            last -= 1
        out.append((i, last))
        i = j
    return out


class Body:
    """A proof body with its mask, bracket pairs, lines and the top-level tactic statements."""

    def __init__(self, body: str):
        self.body = body
        self.mask = _mask(body)
        self.pairs = _pairs(body, self.mask)
        self.fb = _first_by(body, self.mask)
        self.lines = _lines(body, self.mask)
        self.first = None                                                
        self.top = None                                                
        if self.fb >= 0:
            by_line = next(ln for ln in self.lines if ln.start <= self.fb <= ln.end)
            self.first = by_line.idx + 1
            cands = [ln.indent for ln in self.lines[self.first:] if ln.code and not _in_conv(body, self.mask, ln.tac)]
            if cands:
                self.top = min(cands)

    def code_lines(self):
        return [ln for ln in self.lines[(self.first or 0):] if ln.code] if self.first is not None else []

    def in_conv(self, ln: Line) -> bool:
        return _in_conv(self.body, self.mask, ln.tac)

    def tactic(self, ln: Line) -> bool:
        """Is the line's first code a tactic (after `by`, at a line start or a bullet, outside conv)?"""
        return self.first is not None and ln.idx >= self.first and bool(ln.code) and not self.in_conv(ln)

    def top_stmts(self) -> list[tuple[int, int]]:
        if self.top is None:
            return []
        return _stmts(self.lines, self.first, len(self.lines), self.top)

    def all_stmts(self) -> list[tuple[int, int, int]]:
        """(head, last, indent) of every statement at every indent after the `by` line (outer before inner)."""
        out = []
        if self.first is None:
            return out
        stack = [(self.first, len(self.lines), self.top)]
        seen = set()
        while stack:
            lo, hi, ind = stack.pop()
            if ind is None:
                continue
            for h, l in _stmts(self.lines, lo, hi, ind):
                if (h, l) in seen:
                    continue
                seen.add((h, l))
                out.append((h, l, ind))
                inner = [ln.indent for ln in self.lines[h + 1:l + 1] if ln.code]
                if inner:
                    stack.append((h + 1, l + 1, min(inner)))
        out.sort()
        return out

    def span_text(self, h: int, l: int) -> str:
        return self.body[self.lines[h].start:self.lines[l].end]

    def uses(self, name: str, start: int) -> list[int]:
        """Offsets of whole-word uses of `name` in the unmasked code from `start`."""
        rx = re.compile(r"(?<![\w'.])" + re.escape(name) + r"(?![\w'])")
        return [m.start() for m in rx.finditer(self.body, start) if not self.mask[m.start()]]


def _split_top(text: str) -> list[tuple[int, int]]:
    """Spans (start, end) of the top-level comma-separated components of `text`."""
    out, depth, a = [], 0, 0
    for i, ch in enumerate(text):
        if ch in OPEN:
            depth += 1
        elif ch in CLOSE:
            depth -= 1
        elif ch == "," and depth == 0:
            out.append((a, i))
            a = i + 1
    out.append((a, len(text)))
    return [(s, e) for s, e in out if text[s:e].strip()]


def _strip_span(text: str, s: int, e: int) -> tuple[int, int]:
    while s < e and text[s] in " \t\n":
        s += 1
    while e > s and text[e - 1] in " \t\n":
        e -= 1
    return s, e


def _atomic(term: str) -> bool:
    t = term.strip()
    return bool(t) and not any(ch in t for ch in " \t\n") and not (t[0] in OPEN and t[-1] in CLOSE and len(t) > 2) and "$" not in t


def _fresh(body: str, stem: str) -> str:
    name = stem
    while re.search(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", body):
        name += "_"
    return name


def _indent_text(text: str, indent: int) -> str:
    """Multi-line closer text with its relative indentation placed at `indent`."""
    return "\n".join((" " * indent + l if i else l) for i, l in enumerate(text.split("\n")))


def _is_tactic_stmt(B: Body, h: int) -> bool:
    ln = B.lines[h]
    return B.tactic(ln) and not ln.bullet


                                                                                                                                        
def _bullets(B: Body):
    out = []
    for h, l, ind in B.all_stmts():
        ln = B.lines[h]
        if ln.bullet or not B.tactic(ln):
            continue
        sibs = _stmts(B.lines, l + 1, len(B.lines), ind)
        group = []
        for bh, bl in sibs:
            if B.lines[bh].bullet:
                group.append((bh, bl))
            else:
                break
        if len(group) < 2:
            continue
        blocks = []
        for bh, bl in group:
            bln = B.lines[bh]
            col = bln.tac - bln.start
            block = [(0, bln.raw[bln.tac - bln.start:].rstrip(), bln.code[1:].strip())]
            ok = True
            for ln2 in B.lines[bh + 1:bl + 1]:
                if not ln2.code:
                    continue
                rel = ln2.indent - col
                if rel < 0:
                    ok = False
                    break
                block.append((rel, ln2.raw.strip(), ln2.code))
            if not ok:
                blocks = None
                break
            blocks.append(block)
        if not blocks:
            continue
        out.append((h, l, ind, group, blocks))
    return out


def bullet_merge(B: Body) -> list[Rule]:
    out = []
    for h, l, ind, group, blocks in _bullets(B):
        codes = [[(r, c) for r, _, c in b] for b in blocks]
        if any(c != codes[0] for c in codes[1:]):
            continue
        head = B.span_text(h, l).rstrip()
        first = blocks[0]
        span = (B.lines[h].start, B.lines[group[-1][1]].end)
        saved = (len(group) - 1) * count_tokens("\n".join(c for _, c in codes[0])) + len(group) - 1
        if saved < 1:
            continue
        if len(first) == 1:
            rep = head + " <;> " + first[0][1]
        else:
            rep = head + " <;> (\n" + "\n".join(" " * (ind + 2 + r) + t for r, t, _ in first) + ")"
        note = f"{B.lines[h].code[:40]} <;> {codes[0][0][1][:40]} ({len(group)} identical bullets)"
        out.append(Rule("bullet-merge", ((span[0], span[1] - span[0], rep),), note, saved))
        rep2 = head + "\n" + " " * ind + "all_goals\n" + "\n".join(" " * (ind + 2 + r) + t for r, t, _ in first)
        out.append(Rule("bullet-merge", ((span[0], span[1] - span[0], rep2),), note + " [all_goals]", saved - 1))
    return out


def bullet_hoist(B: Body) -> list[Rule]:
    out = []
    for h, l, ind, group, blocks in _bullets(B):
        codes = [[(r, c) for r, _, c in b] for b in blocks]
        if all(c == codes[0] for c in codes[1:]):
            continue                        
        first = codes[0][0][1]
        if any(c[0][1] != first for c in codes) or any(len(c) > 1 and c[1][0] != 0 for c in codes):
            continue
        if first.split()[-1] in BLOCK_OPENERS or first.endswith(("with", "=>", "by", "<;>")):
            continue
        head = B.span_text(h, l).rstrip()
        saved = (len(group) - 1) * count_tokens(first) - 1 + sum(1 for b in blocks if len(b) == 1)
        if saved < 1:
            continue
        parts = [head + " <;> " + blocks[0][0][1]]
        for b in blocks:
            rest = b[1:]
            if not rest:
                continue
            lines = []
            for i, (r, t, _) in enumerate(rest):
                lines.append((" " * ind + "· " if i == 0 else " " * (ind + 2 + r)) + t)
            parts.append("\n".join(lines))
        span = (B.lines[h].start, B.lines[group[-1][1]].end)
        out.append(Rule("bullet-hoist", ((span[0], span[1] - span[0], "\n".join(parts)),),
                        f"hoist `{first[:40]}` out of {len(group)} bullets", saved))
    return out


                                                                                                                                       
def tail_closer(B: Body) -> list[Rule]:
    stmts = [s for s in B.top_stmts() if B.tactic(B.lines[s[0]])]
    if not stmts:
        return []
    n = len(stmts)
    spans = [(0, "whole proof")] + [(n - k, "last %d" % k) for k in (1, 2, 3) if k < n]
    per_span = []
    for a, label in spans:
        h, l = stmts[a][0], stmts[-1][1]
        s, e = B.lines[h].start + B.lines[h].indent, B.lines[l].end
        text = B.body[s:e]
        tok = count_tokens(text)
        lst = []
        for c in CLOSERS:
            saved = tok - count_tokens(c)
            if saved < 1:
                continue
            lst.append(Rule("tail-closer", ((s, e - s, _indent_text(c, B.top)),), f"{label} -> `{c.split(chr(10))[0]}`", saved))
        per_span.append(lst)
    out = []                                                                                                          
    for i in range(max((len(l) for l in per_span), default=0)):
        out += [l[i] for l in per_span if i < len(l)]
    return out


                                                                                                                                    
HAVE_RE = re.compile(r"^(have|let)\s+([^\W\d][\w'!?]*)\s*(?::\s*(.+?))?\s*:=\s*(.+)$", re.S)
LIST_OK = re.compile(r"[$λ▸;]|<\||\|>|\bfun\b|←")


def inline_have(B: Body) -> list[Rule]:
    out = []
    for h, l, ind in B.all_stmts():
        if h != l or not _is_tactic_stmt(B, h):
            continue
        ln = B.lines[h]
        m = HAVE_RE.match(ln.code)
        if not m:
            continue
        name, typ, term = m.group(2), m.group(3), m.group(4).strip()
        if term.startswith("by") and not term.startswith("by "):
            continue
        uses = B.uses(name, ln.end)
        if len(uses) != 1:
            continue
        u = uses[0]
        after = B.body[u + len(name):u + len(name) + 1]
        prev = _prev_token(B.body, B.mask, u)
                                                                                                                                        
        in_list = any(o < u < c for o, c in B.pairs.items() if B.body[o] == "[")
        if after == ".":
            rep = f"({term})"
        elif _atomic(term):
            rep = term
        elif in_list and not LIST_OK.search(term) and "\n" not in term:
            rep = term
        elif prev in ("exact", "apply", "using", ":=", "refine", "$", "<|", "from", "⟨", ",") and after in (" ", "\n", "", ")", "⟩", "]", ","):
            rep = term if not LIST_OK.search(term) or prev in ("exact", "apply", "using", ":=", "$", "<|", "from") else f"({term})"
        else:
            rep = f"({term})"
        if term.startswith("by ") and rep == term:
            rep = f"({term})"
        saved = count_tokens(f"have {name} :=" + (f" : {typ}" if typ else "")) + count_tokens(name) - (count_tokens(rep) - count_tokens(term))
        if saved < 1:
            continue
        edits = ((ln.start, min(ln.end + 1, len(B.body)) - ln.start, ""), (u, len(name), rep))
        out.append(Rule("inline-have", tuple(sorted(edits)), f"inline `{name}` := {term[:50]}", saved))
    return out


                                                                                                                                   
BY_EXACT_RE = re.compile(r"(?<![\w.'])by[ \t]+exact[ \t]+")


def by_exact(B: Body) -> list[Rule]:
    out = []
    for m in BY_EXACT_RE.finditer(B.body):
        i = m.start()
        if B.mask[i] or i < B.fb or _in_conv(B.body, B.mask, i):
            continue
        prev = _prev_token(B.body, B.mask, i)
        if prev in TAC_PREV_SYMS or prev in TAC_PREV_WORDS:
            continue
        out.append(Rule("by-exact", ((i, m.end() - i, ""),), f"`by exact` -> term at {B.body[m.end():m.end() + 30]!r}", 2))
    for ln in B.lines:
        if not ln.code or not ln.code.endswith("by") or ln.idx + 1 >= len(B.lines) or B.mask[ln.end - 1]:
            continue
        nxt = next((x for x in B.lines[ln.idx + 1:] if x.code), None)
        if nxt is None or nxt.indent <= ln.indent or not nxt.code.startswith("exact ") or nxt.bullet:
            continue
        sib = _stmts(B.lines, nxt.idx, len(B.lines), nxt.indent)
        if len(sib) != 1 or not B.tactic(nxt):
            continue
        by_pos = ln.end - 2
        while by_pos > ln.start and B.body[by_pos - 1] in " \t":
            by_pos -= 1
        ex = B.body.find("exact ", nxt.tac)
        out.append(Rule("by-exact", ((by_pos, ln.end - by_pos, ""), (ex, len("exact "), "")),
                        f"`by` block with only `exact` at line {nxt.idx + 1} -> term", 2))
    return out


                                                                                                                                  
INTRO_RE = re.compile(r"^intro((?:\s+[^\W\d][\w'!?]*)+)$")
EXACT_RE = re.compile(r"^exact\s+(.+)$", re.S)


def eta_intro(B: Body) -> list[Rule]:
    out = []
    for h, l, ind in B.all_stmts():
        if h != l or not _is_tactic_stmt(B, h):
            continue
        m = INTRO_RE.match(B.lines[h].code)
        if not m:
            continue
        names = m.group(1).split()
        nxt = next(((h2, l2) for h2, l2, i2 in B.all_stmts() if i2 == ind and h2 > l), None)
        if nxt is None or nxt[0] != nxt[1] or B.lines[nxt[0]].bullet:
            continue
        me = EXACT_RE.match(B.lines[nxt[0]].code)
        if not me:
            continue
        term = me.group(1).strip()
        words = term.split()
        j = 0
        while j < len(names) and len(words) > j + 1 and words[-1 - j] == names[-1 - j]:
            j += 1
        if j == 0:
            continue
        prefix = " ".join(words[:len(words) - j])
        if any(re.search(r"(?<![\w'.])" + re.escape(n) + r"(?![\w'])", prefix) for n in names[len(names) - j:]):
            continue
        keep = names[:len(names) - j]
        ln, ln2 = B.lines[h], B.lines[nxt[0]]
        if keep:
            rep = " " * ind + "intro " + " ".join(keep) + "\n" + " " * ind + "exact " + prefix
        else:
            rep = " " * ind + "exact " + prefix
        out.append(Rule("eta-intro", ((ln.start, ln2.end - ln.start, rep),), f"intro {' '.join(names)} + exact .. -> exact {prefix[:40]}",
                        2 + j))
    return out


LAM_RE = re.compile(r"(?<![\w'])(λ|fun(?![\w']))\s*([^\W\d][\w'!?]*(?:\s+[^\W\d][\w'!?]*)*)\s*=>\s*")


def eta_lam(B: Body) -> list[Rule]:
    out = []
    for m in LAM_RE.finditer(B.body):
        i = m.start()
        if B.mask[i] or i < B.fb:
            continue
        names = m.group(2).split()
                                                                                                                       
        k = i - 1
        while k >= 0 and B.body[k] in " \t":
            k -= 1
        enclosing = None
        if k >= 0 and B.body[k] in OPEN and k in B.pairs:
            enclosing = k
        end = _line_end(B.body, m.end())
        depth = 0
        for p in range(m.end(), end):
            ch = B.body[p]
            if ch in OPEN:
                depth += 1
            elif ch in CLOSE:
                if depth == 0:
                    end = p
                    break
                depth -= 1
            elif ch == "," and depth == 0:
                end = p
                break
        term = B.body[m.end():end].rstrip()
        words = term.split()
        if len(words) <= len(names) or words[-len(names):] != names:
            continue
        prefix = " ".join(words[:len(words) - len(names)])
        if any(re.search(r"(?<![\w'.])" + re.escape(n) + r"(?![\w'])", prefix) for n in names):
            continue
        if enclosing is not None and B.pairs[enclosing] == end and _atomic(prefix) and B.body[enclosing] == "(":
            edits = ((enclosing, B.pairs[enclosing] + 1 - enclosing, prefix),)
        else:
            edits = ((i, end - i, prefix),)
        out.append(Rule("eta-lam", edits, f"λ{' '.join(names)} => {term[:40]} -> {prefix[:40]}", 2 * len(names) + 1))
    return out


                                                                                                                                 
RW_RE = re.compile(r"^(rw|rewrite)\s*(\[.*\])(?:\s+at\s+(\S+))?$", re.S)
SIMP_RE = re.compile(r"^simp(?P<rest>(?:\s+only)?(?:\s*\[[^\]]*\])?)(?:\s+at\s+(?P<loc>\S+))?$", re.S)
CLOSE_RE = re.compile(r"^(assumption|exact\s+([^\W\d][\w'!?]*))$")


def _pairs_of_stmts(B: Body):
    """Consecutive single-line tactic statement pairs (first, second) at the same indent."""
    stmts = B.all_stmts()
    for h, l, ind in stmts:
        if h != l or not _is_tactic_stmt(B, h):
            continue
        nxt = next(((h2, l2) for h2, l2, i2 in stmts if i2 == ind and h2 > l), None)
        if nxt is None or nxt[0] != nxt[1] or B.lines[nxt[0]].bullet:
            continue
        if any(ln.code and ln.indent > ind for ln in B.lines[l + 1:nxt[0]]):
            continue
        yield B.lines[h], B.lines[nxt[0]], ind


def rwa(B: Body) -> list[Rule]:
    out = []
    for ln, ln2, ind in _pairs_of_stmts(B):
        m, c = RW_RE.match(ln.code), CLOSE_RE.match(ln2.code)
        if not m or not c:
            continue
        loc, name = m.group(3), c.group(2)
        if name and loc and loc != name:
            continue
        rep = " " * ind + "rwa " + m.group(2) + (f" at {loc}" if loc else "")
        out.append(Rule("rwa", ((ln.start, ln2.end - ln.start, rep),), f"{ln.code[:40]} + {ln2.code} -> rwa", 2))
    return out


def simpa(B: Body) -> list[Rule]:
    out = []
    for ln, ln2, ind in _pairs_of_stmts(B):
        m, c = SIMP_RE.match(ln.code), CLOSE_RE.match(ln2.code)
        if not m or not c:
            continue
        loc, name = m.group("loc"), c.group(2)
        if loc in ("*", "⊢") or (name and loc and loc != name):
            continue
        using = name or loc
        rep = " " * ind + "simpa" + m.group("rest") + (f" using {using}" if using else "")
        out.append(Rule("simpa", ((ln.start, ln2.end - ln.start, rep),), f"{ln.code[:40]} + {ln2.code} -> simpa", 2))
    return out


                                                                                                                                          
NAME_ONLY = {"clear", "subst", "revert", "specialize", "rename_i", "generalize", "at", "clear_value", "replace", "induction", "with"}
OBTAIN_RE = re.compile(r"^obtain\s+⟨([^⟨⟩]*)⟩\s*:=\s*(.+)$", re.S)
RCASES_RE = re.compile(r"^rcases\s+(.+?)\s+with\s+⟨([^⟨⟩]*)⟩$", re.S)


def obtain_proj(B: Body) -> list[Rule]:
    out = []
    for h, l, ind in B.all_stmts():
        if h != l or not _is_tactic_stmt(B, h):
            continue
        ln = B.lines[h]
        m = OBTAIN_RE.match(ln.code)
        if m:
            pat, term = m.group(1), m.group(2).strip()
        else:
            m = RCASES_RE.match(ln.code)
            if not m:
                continue
            term, pat = m.group(1).strip(), m.group(2)
        names = [p.strip() for p in pat.split(",")]
        if len(names) < 2 or any(not IDENT_RE.match(n) or n in ("rfl", "_") for n in names):
            continue
        new = _fresh(B.body, "h")
        k = len(names)

        def projs(exists_first: bool) -> list[str]:
            ps = []
            for i in range(k):
                if exists_first:
                    if i == 0:
                        ps.append(new + ".choose")
                    else:
                        ps.append(new + ".choose_spec" + ".2" * (i - 1) + (".1" if i < k - 1 else ""))
                else:
                    ps.append(new + ".2" * i + (".1" if i < k - 1 else ""))
            return ps
        saved = count_tokens("⟨" + pat + "⟩") - 1
        if saved < 1:
            continue
        all_uses = {n: B.uses(n, ln.end) for n in names}
        if any(_prev_token(B.body, B.mask, u) in NAME_ONLY for us in all_uses.values() for u in us):
            continue                                                                                           
        for exists_first in (False, True):
            edits = [(ln.start, ln.end - ln.start, " " * ind + f"have {new} := {term}")]
            for n, p in zip(names, projs(exists_first)):
                edits += [(u, len(n), p) for u in all_uses[n]]
            out.append(Rule("obtain-proj", tuple(sorted(edits)), f"⟨{pat}⟩ -> {new} projections" + (" (∃ first)" if exists_first else ""),
                            saved - (1 if exists_first else 0)))
    return out


                                                                                                                                    
WIT_RE = re.compile(r"^(use|exists)\s+(.+)$", re.S)
ANON_RE = re.compile(r"^(refine|exact|use)\s+⟨")
SHOW_RE = re.compile(r"(?<![\w'])show\b(.*?)(?<![\w'])from\b")
TERM_RE = re.compile(r"^(exact|apply|refine|refine')\s+(.+)$", re.S)


def _skip_component(t: str) -> bool:
    t = t.strip()
    return (not t or t in ("_", "?_", "rfl") or t.startswith(("by", "?", "λ", "fun ", "(by", "(λ", "(fun ")) or count_tokens(t) < 2)


def wit_underscore(B: Body) -> list[Rule]:
    out = []
    for h, l, ind in B.all_stmts():
        if h != l or not _is_tactic_stmt(B, h):
            continue
        ln = B.lines[h]
        m = WIT_RE.match(ln.code)
        if m:
            kw_end = B.body.find(m.group(1), ln.tac) + len(m.group(1))
            s = kw_end
            while s < ln.end and B.body[s] in " \t":
                s += 1
            e = ln.end
            comps = [(s + a, s + b) for a, b in _split_top(B.body[s:e])]
        elif ANON_RE.match(ln.code):
            o = B.body.find("⟨", ln.tac)
            if o < 0 or o not in B.pairs or B.pairs[o] > ln.end:
                continue
            s, e = o + 1, B.pairs[o]
            comps = [(s + a, s + b) for a, b in _split_top(B.body[s:e])]
        else:
            continue
        for a, b in comps:
            a, b = _strip_span(B.body, a, b)
            t = B.body[a:b]
            if _skip_component(t) or any(B.mask[a:b]):
                continue
            out.append(Rule("wit-underscore", ((a, b - a, "_"),), f"witness `{t[:40]}` -> _", count_tokens(t) - 1))
    return out


def _paren_groups(B: Body, s: int, e: int) -> list[tuple[int, int]]:
    """Top-level parenthesised groups `( .. )` inside body[s:e]."""
    out, p = [], s
    while p < e:
        if B.body[p] == "(" and p in B.pairs and B.pairs[p] < e and not B.mask[p]:
            out.append((p, B.pairs[p] + 1))
            p = B.pairs[p] + 1
        elif B.body[p] in OPEN and p in B.pairs:
            p = B.pairs[p] + 1
        else:
            p += 1
    return out


def show_underscore(B: Body) -> list[Rule]:
    out = []
    for m in SHOW_RE.finditer(B.body):
        if B.mask[m.start()] or m.start() < B.fb or "\n" in m.group(0):
            continue
        groups = [(a, b) for a, b in _paren_groups(B, m.start(1), m.end(1)) if not _skip_component(B.body[a:b])]
        for a, b in groups:
            out.append(Rule("show-underscore", ((a, b - a, "_"),), f"show-argument `{B.body[a:b][:40]}` -> _", count_tokens(B.body[a:b]) - 1))
        if len(groups) > 1:
            out.append(Rule("show-underscore", tuple((a, b - a, "_") for a, b in groups), f"all {len(groups)} show-arguments -> _",
                            sum(count_tokens(B.body[a:b]) - 1 for a, b in groups)))
    return out


def arg_underscore(B: Body) -> list[Rule]:
    out = []
    for h, l, ind in B.all_stmts():
        if h != l or not _is_tactic_stmt(B, h):
            continue
        ln = B.lines[h]
        m = TERM_RE.match(ln.code)
        if not m or ln.code.startswith(("exact ⟨", "refine ⟨")):
            continue
        s = B.body.find(m.group(1), ln.tac) + len(m.group(1))
        for a, b in _paren_groups(B, s, ln.end):
            t = B.body[a:b]
            if _skip_component(t) or re.match(r"\(\s*[A-Za-z_]+\s*:=", t) or "?_" in t:
                continue
            out.append(Rule("arg-underscore", ((a, b - a, "_"),), f"argument `{t[:40]}` -> _", count_tokens(t) - 1))
    return out


                                                                                                                              
def refine_constructor(B: Body) -> list[Rule]:
    out = []
    for h, l, ind in B.all_stmts():
        if h != l or not _is_tactic_stmt(B, h):
            continue
        ln = B.lines[h]
        if re.sub(r"\s+", "", ln.code) == "refine⟨?_,?_⟩":
            out.append(Rule("refine-constructor", ((ln.tac, ln.end - ln.tac, "constructor"),), "refine ⟨?_, ?_⟩ -> constructor", 5))
    return out


def constructor_pair(B: Body) -> list[Rule]:
    out = []
    for h, l, ind in B.all_stmts():
        if h != l or not _is_tactic_stmt(B, h) or B.lines[h].code != "constructor":
            continue
        sibs = [(h2, l2) for h2, l2, i2 in B.all_stmts() if i2 == ind and h2 > l][:2]
        if len(sibs) != 2 or any(h2 != l2 or not B.lines[h2].bullet for h2, l2 in sibs):
            continue
        terms = []
        for h2, _ in sibs:
            me = EXACT_RE.match(B.lines[h2].code[1:].strip())
            if not me:
                break
            terms.append(me.group(1).strip())
        if len(terms) != 2:
            continue
        rep = " " * ind + f"exact ⟨{terms[0]}, {terms[1]}⟩"
        out.append(Rule("constructor-pair", ((B.lines[h].start, B.lines[sibs[1][1]].end - B.lines[h].start, rep),),
                        "constructor + two exact bullets -> exact ⟨_, _⟩", 1))
    return out


APPLY_RE = re.compile(r"^(apply|refine)\s+(.+)$", re.S)


def apply_exact(B: Body) -> list[Rule]:
    out = []
    for ln, ln2, ind in _pairs_of_stmts(B):
        m, me = APPLY_RE.match(ln.code), EXACT_RE.match(ln2.code)
        if not m or not me or not _atomic(me.group(1)):
            continue
        f, g = m.group(2).strip(), me.group(1).strip()
        if m.group(1) == "refine":
            if not f.endswith("?_") or f.count("?_") != 1:
                continue
            f = f[:-2].rstrip()
        rep = " " * ind + f"exact {f} {g}"
        out.append(Rule("apply-exact", ((ln.start, ln2.end - ln.start, rep),), f"{ln.code[:40]} + {ln2.code} -> exact", 1 if m.group(1) == "apply" else 2))
    return out


IH_RE = re.compile(r"(?<![\w'.])((?:[^\W\d][\w'!?]*_)?ih\w*|IH\w*)(?![\w'])")
SIMP_CALL_RE = re.compile(r"(?<![\w.'?!])(simp(?:\s+only)?)\s*(\[)")


def ih_simp(B: Body) -> list[Rule]:
    out = []
    names = []
    for m in IH_RE.finditer(B.body):
        if not B.mask[m.start()] and m.group(1) not in names:
            names.append((m.group(1), m.start()))
    names = [(n, p) for n, p in names if isinstance(n, str)]
    for m in SIMP_CALL_RE.finditer(B.body):
        o = m.end() - 1
        if B.mask[o] or o not in B.pairs or o < B.fb:
            continue
        c = B.pairs[o]
        lst = B.body[o + 1:c]
        for n, p in names:
            if p > o or re.search(r"(?<![\w'.])" + re.escape(n) + r"(?![\w'])", lst):
                continue
            ins = n if not lst.strip() else ", " + n
            out.append(Rule("ih-simp", ((c, 0, ins),), f"`{n}` added to {m.group(1)} [..]", 0))
    return out


FAMILIES = (bullet_merge, bullet_hoist, tail_closer, inline_have, by_exact, eta_intro, eta_lam, rwa, simpa, obtain_proj, wit_underscore,
            show_underscore, arg_underscore, refine_constructor, constructor_pair, apply_exact, ih_simp)


def candidates(body: str, caps: dict | None = None, kinds=None) -> list[Rule]:
    """Every family's candidates on `body`, priority-ordered (ties: family order, then position), per-kind caps applied."""
    B = Body(body)
    if B.fb < 0 or B.first is None:
        return []
    caps = dict(DEFAULT_CAPS, **(caps or {}))
    groups: dict[str, list[Rule]] = {}
    for fam in FAMILIES:
        try:
            rules = fam(B)
        except Exception:                                                                             
            continue
        for r in rules:
            if kinds and r.kind not in kinds:
                continue
            groups.setdefault(r.kind, []).append(r)
    res = []
    for kind in sorted(groups, key=lambda k: (-max(r.priority for r in groups[k]), KINDS.index(k) if k in KINDS else len(KINDS))):
        lst = groups[kind]
        if kind != "tail-closer":                                                                                                 
            lst = sorted(lst, key=lambda r: (-r.priority, r.edits[0][0] if r.edits else 0))
        res += lst[:caps.get(kind, 1 << 30)]
    return res


if __name__ == "__main__":
    import json
    from harness.normalize import apply
    text = Path(sys.argv[1]).read_text()
    i = text.find(":=")
    body = text[i + 2:] if "--body" not in sys.argv else text
    for r in candidates(body):
        print(json.dumps({"kind": r.kind, "priority": r.priority, "note": r.note}, ensure_ascii=False))
        if "--show" in sys.argv:
            print(apply(body, [r]))
