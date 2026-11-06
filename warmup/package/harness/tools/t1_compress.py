#!/usr/bin/env python3
"""T1 elaboration compressor (tools build plan, round R1): candidate generator for the end stage, same contract as harness/sweep.candidates.







































"""
from __future__ import annotations

import argparse, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs, OPEN, CLOSE, KEYWORDS              
from harness.hb_rewrite import _prev_token              
from harness import gap_rules as GR              
from scorer.tokenize import split_declaration, count_tokens              

OPS = ("t1:proj", "t1:projapp", "t1:inline", "t1:hole", "t1:hole2", "t1:field")
HOLE_OPS = ("t1:hole", "t1:hole2")
LAST_OPS = ("t1:field",)                                                                                                        
OPT_IN_OPS = ("t1:field",)                                                                          
DEFAULT_OPS = tuple(o for o in OPS if o not in OPT_IN_OPS)
TABLE_PATH = Path(__file__).resolve().parent / "tables" / "projections.json"
MAX_PER_OP = 40
PER_SITE = 2                                                     
PAIR_TOP = 8                                                          
MAX_USES = 3                                                                                      


def _load_table() -> dict:
    try:
        return json.loads(TABLE_PATH.read_text())
    except (OSError, ValueError):
        return {}


_T = _load_table()
TABLES = ({"projections": {"rule": _T.get("rule"), "query": _T.get("query"), "path": str(TABLE_PATH.relative_to(ROOT)),
                           "generated_at": _T.get("generated_at")}} if _T else {})


def _index_table(t: dict) -> tuple[dict, dict, dict, dict]:
    """From the non-class structures of the table: field name -> {1-based index: #structures}; 1-based index -> {name: [#Prop

"""
    by_name, by_idx, projfn, share = {}, {}, {}, {}
    for s, d in (t.get("structures") or {}).items():
        if d.get("class"):                                                                                                  
            continue
        for i, f in enumerate(d.get("fields") or [], 1):
            by_name.setdefault(f, {}).setdefault(i, 0)
            by_name[f][i] += 1
            if "." not in s:                                                                                                        
                c = by_idx.setdefault(i, {}).setdefault(f, [0, 0])                                                            
                c[0] += bool(d.get("prop"))
                c[1] += 1
            projfn[f"{s}.{f}"] = (i, f)
    for f, c in (t.get("names") or {}).items():
        p, o = int(c.get("proj") or 0), int(c.get("other") or 0)
        share[f] = p / (p + o) if p + o else 0.0
    return by_name, by_idx, projfn, share


BY_NAME, BY_IDX, PROJFN, SHARE = _index_table(_T)

IDENT_CH = "_'!?"
NAME_RE = re.compile(r"(?<![\w.'!?@])([^\W\d][\w'!?]*(?:\.(?:\d+|[^\W\d][\w'!?]*))*)")
AFTER_CLOSE_RE = re.compile(r"(?<=[)⟩])((?:\.(?:\d+|[^\W\d][\w'!?]*))+)(?![\w'!?])")
BINDER_TO_ARROW = ("fun", "λ", "case", "case'", "next")
BINDER_TO_COMMA = ("∀", "∃", "∃!", "Π", "Σ", "∑", "∏", "⋃", "⋂", "⨆", "⨅")
NO_USE_PREV = ("at", "clear", "revert", "subst", "specialize", "rename_i", "generalize", "set", "clear_value")


def _word(c: str) -> bool:
    return c.isalnum() or c in IDENT_CH


def _flat(t: str) -> str:
    return re.sub(r"\s+", " ", t).strip()


                                                                                                                                        
class Src:
    """A body with its mask (comments and strings), bracket pairs, binder / pattern regions and gap_rules' line structure."""

    def __init__(self, body: str, statement: str = ""):
        self.body = body
        self.statement = statement
        self.mask = _mask(body)
        self.pairs = _pairs(body, self.mask)
        self.B = GR.Body(body)
        self.regions = _binder_regions(body, self.mask, self.pairs)

    def in_region(self, i: int) -> bool:
        return any(a <= i < b for a, b in self.regions)

    def binds(self, i: int) -> bool:
        """Is position i a bound name (inside a binder / pattern span and not after a `:` there, i.e. not in a binder's type)?"""
        for a, b in self.regions:
            if a <= i < b and ":" not in "".join(ch for p, ch in enumerate(self.body[a:i], a) if not self.mask[p]):
                return True
        return False

    def line_of(self, i: int) -> int:
        return self.body.count("\n", 0, i)


def _scan_to(body: str, mask: list, pairs: dict, k: int, stops: tuple, line_only: bool = True) -> int:
    """From k, the first position at bracket depth 0 where one of `stops` starts (or a closing bracket of an enclosing group, or the line
"""
    n = len(body)
    while k < n:
        if mask[k]:
            k += 1
            continue
        ch = body[k]
        if ch in OPEN and k in pairs:
            k = pairs[k] + 1
            continue
        if ch in CLOSE or (line_only and ch == "\n"):
            return k
        if any(body.startswith(s, k) for s in stops):
            return k
        k += 1
    return n


def _binder_regions(body: str, mask: list, pairs: dict) -> list[tuple[int, int]]:
    """Spans holding binders or patterns (never rewritten into holes or projections): `fun`/`λ`/`case`/`next` .. `=>`, quantifier binders

"""
    out = []
                                                                                                      
    for m in re.finditer(r"(?<![\w.'!?])(?:(fun|case'?|next|intros?|rintro|rename_i|ext|funext|obtain|with|have|let|suffices|haveI|letI|"
                         r"set)(?![\w'!?])|(λ|∀|∃!?|Π|Σ|∑|∏|⋃|⋂|⨆|⨅))", body):
        k = m.start()
        if mask[k]:
            continue
        kw, e = m.group(1) or m.group(2), m.end()
        if kw in BINDER_TO_ARROW:
            end = _scan_to(body, mask, pairs, e, ("=>", "↦"), line_only=False)
        elif kw in BINDER_TO_COMMA:
            end = _scan_to(body, mask, pairs, e, (",",), line_only=False)
        elif kw in ("have", "let", "suffices", "haveI", "letI", "set", "obtain"):
            end = _scan_to(body, mask, pairs, e, (":=", ":"))
        else:
            end = _scan_to(body, mask, pairs, e, ("<;>", ";"))
        out.append((e, end))
    for m in re.finditer(r"(?m)^[ \t]*(\|)", body):                           
        k = m.start(1)
        if not mask[k]:
            out.append((k + 1, _scan_to(body, mask, pairs, k + 1, ("=>",))))
    for m in re.finditer(r"(?m)^[ \t]*(set_option|open|attribute|@\[)", body):                                              
        if not mask[m.start(1)]:
            e = body.find("\n", m.start(1))
            out.append((m.start(1), len(body) if e < 0 else e))
    return out


def _prev_word(S: Src, i: int) -> tuple[str, int]:
    """The code token before position i, skipping blanks and line breaks (so a continuation line's first argument sees the previous line):
"""
    b, j = S.body, i - 1
    while j >= 0 and (b[j] in " \t\n" or S.mask[j]):
        j -= 1
    if j < 0:
        return "", -1
    if _word(b[j]) or b[j] == ".":
        k = j
        while k >= 0 and (_word(b[k]) or b[k] == "."):
            k -= 1
        return b[k + 1:j + 1], k + 1
    return b[j], j


def _first_on_line(S: Src, k: int) -> bool:
    ls = S.body.rfind("\n", 0, k) + 1
    return not S.body[ls:k].strip(" \t·")


def _not_term(S: Src, w: str, k: int) -> bool:
    """Is the word w (starting at k) no term: a keyword (normalize.KEYWORDS), a numeral, or the first word of a tactic line (a tactic
"""
    return (w in KEYWORDS or w.replace(".", "").isdigit()
            or (_first_on_line(S, k) and S.B.first is not None and S.line_of(k) >= S.B.first))


def _arg_position(S: Src, i: int) -> bool:
    """Is the bracket group / `$` at i an explicit argument of an application (after a function head or a previous argument)?"""
    w, k = _prev_word(S, i)
    if not w:
        return False
    if w in ")⟩":
        return True
    return (_word(w[0]) or w[0] == ".") and not _not_term(S, w, k)


                                                                                                                                        
def _name_sites(S: Src):
    """(start of `.field`, end, head text, field text) for every dotted field access on a term: `h.f`, `lemma.f`, `h.1.f`, `(e).f`. A head
"""
    b = S.body
    for m in NAME_RE.finditer(b):
        if S.mask[m.start()] or S.in_region(m.start()):
            continue
        comps = m.group(1).split(".")
        pos = m.start() + len(comps[0])
        for j in range(1, len(comps)):
            f, last = comps[j], comps[j - 1]
            if not last[:1].isupper():
                yield pos, pos + 1 + len(f), ".".join(comps[:j]), f
            pos += 1 + len(f)
    for m in AFTER_CLOSE_RE.finditer(b):
        if S.mask[m.start()] or S.in_region(m.start()):
            continue
        pos = m.start()
        for f in m.group(1).split(".")[1:]:
            yield pos, pos + 1 + len(f), b[pos - 1], f
            pos += 1 + len(f)


def _proj(S: Src) -> list[tuple]:
    out = []
    for a, e, head, f in _name_sites(S):
        if f.isdigit() or f not in BY_NAME:
            continue
        idx = sorted(BY_NAME[f].items(), key=lambda x: (-x[1], x[0]))[:PER_SITE]
        for i, n in idx:
            out.append(("t1:proj", f"{head}.{f} -> .{i}", ((a, e - a, f".{i}"),), SHARE.get(f, 0.0), a))
    return out


def _field(S: Src) -> list[tuple]:
    out = []
    for a, e, head, f in _name_sites(S):
        if not f.isdigit() or int(f) not in BY_IDX:
            continue
                                                                                                                     
        names = sorted(BY_IDX[int(f)].items(), key=lambda x: (-x[1][0], -SHARE.get(x[0], 0.0), -x[1][1], x[0]))[:PER_SITE]
        for name, n in names:
            out.append(("t1:field", f"{head}.{f} -> .{name}", ((a, e - a, f".{name}"),), SHARE.get(name, 0.0), a))
    return out


def _projapp(S: Src) -> list[tuple]:
    """`S.f a` at an application head -> `a.i` / `a.f` (one token saved for an atomic a)."""
    b, out = S.body, []
    for m in NAME_RE.finditer(b):
        name = m.group(1)
        if name not in PROJFN or S.mask[m.start()] or S.in_region(m.start()):
            continue
        if _arg_position(S, m.start()):
            continue                                                                            
        i, f = PROJFN[name]
        p = m.end()
        while p < len(b) and b[p] in " \t":
            p += 1
        if p == m.end() or p >= len(b) or S.mask[p]:
            continue
        if b[p] == "(" and p in S.pairs:
            arg_end = S.pairs[p] + 1
        else:
            am = NAME_RE.match(b, p)
            if not am or am.start() != p or am.group(1) in KEYWORDS:
                continue
            arg_end = am.end()
        arg = b[p:arg_end]
        if arg in ("_", "?_"):
            continue
        for sp in (f".{i}", f".{f}"):
            out.append(("t1:projapp", f"{name} {arg[:24]} -> {arg[:24]}{sp}", ((m.start(), arg_end - m.start(), arg + sp),),
                        SHARE.get(f, 0.0), m.start()))
    return out


                                                                                                                                       
def _skip_hole(t: str) -> bool:
    t = t.strip()
    return (not t or t in ("_", "?_") or t.startswith(("by ", "by\n", "?", "(by ", "(by\n", "·", "(·")) or t == "by"
            or count_tokens(t) < 2 or bool(re.match(r"\(\s*[^\W\d][\w'.]*\s*:=", t)))


def _dollar_end(S: Src, k: int) -> int:
    """End of a `$` / `<|` argument starting at k: the enclosing group's close, a depth-0 comma / `;` / `<;>` / `at` / `with` / `using`,
"""
    b, n = S.body, len(S.body)
    e = _scan_to(b, S.mask, S.pairs, k, (",", ";", "<;>", " at ", " with ", " using ", " from ", ":="))
    if e < n and b[e] == "\n":
        nxt = b[e + 1:]
        ind = len(nxt) - len(nxt.lstrip(" "))
        ls = b.rfind("\n", 0, k) + 1
        cur = len(b[ls:]) - len(b[ls:].lstrip(" "))
        if nxt.strip() and ind > cur and not nxt.lstrip().startswith(("·", "|", "<;>")):
            return -1
    while e > k and b[e - 1] in " \t":
        e -= 1
    while e > k and S.mask[e - 1]:                       
        e -= 1
        while e > k and b[e - 1] in " \t":
            e -= 1
    return e


def _holes(S: Src) -> list[tuple]:
    b, out = S.body, []
    seen = set()

    def add(a, e, kind):
        t = b[a:e]
        if (a, e) in seen or _skip_hole(t) or any(S.mask[a:e]):
            return
        if e < len(b) and b[e] == ".":
            return
        seen.add((a, e))
        out.append(("t1:hole", f"{kind} `{_flat(t)[:36]}` -> _", ((a, e - a, "_"),), _inferable(S, a, e, t), a))

    for o, c in sorted(S.pairs.items()):
        if S.mask[o] or b[o] not in "(⟨" or S.in_region(o):
            continue
        if _arg_position(S, o):
            add(o, c + 1, "argument")
        if b[o] == "⟨":
            for x, y in GR._split_top(b[o + 1:c]):
                x, y = GR._strip_span(b, o + 1 + x, o + 1 + y)
                add(x, y, "component")
    for m in re.finditer(r"\$|<\|", b):
        k = m.start()
        if S.mask[k] or S.in_region(k) or not _arg_position(S, k):
            continue
        e = _dollar_end(S, m.end())
        if e > m.end():
            t = b[m.end():e].strip()
            if not _skip_hole(t):
                a = k
                while a > 0 and b[a - 1] in " \t":
                    a -= 1
                if (a, e) not in seen:
                    seen.add((a, e))
                    out.append(("t1:hole", f"`{m.group(0)}` argument `{t[:30]}` -> _", ((a, e - a, " _"),),
                                _inferable(S, m.end(), e, t), k))
    for ln in (S.B.lines if S.B.first is not None else []):
        if ln.idx < S.B.first or not ln.code:
            continue
        mm = re.match(r"(use|exists|use!)\s+", ln.code)
        if not mm:
            continue
        s = S.body.find(mm.group(1), ln.tac) + len(mm.group(1))
        for x, y in GR._split_top(b[s:ln.end]):
            x, y = GR._strip_span(b, s + x, s + y)
            add(x, y, "witness")
    return out


def _inferable(S: Src, a: int, e: int, t: str) -> float:
    """1.0 when the hole's term (outer parentheses dropped) also occurs in the statement or elsewhere in the body, so unification with
"""
    t = t.strip()
    if t[:1] == "(" and t[-1:] == ")":
        t = t[1:-1]
    t = _flat(t)
    if len(t) < 3:
        return 0.0
    rest = _flat(S.statement) + " \n " + _flat(S.body[:a]) + " \n " + _flat(S.body[e:])
    return 1.0 if t in rest else 0.0


def _hole_pairs(singles: list[tuple]) -> list[tuple]:
    top = singles[:PAIR_TOP]
    out = []
    for x in range(len(top)):
        for y in range(x + 1, len(top)):
            (a1, l1, _), (a2, l2, _) = top[x][2][0], top[y][2][0]
            if a1 < a2 + l2 and a2 < a1 + l1:                                                                   
                continue
            out.append(("t1:hole2", f"{top[x][1][:30]} + {top[y][1][:30]}", (top[x][2][0], top[y][2][0]),
                        min(top[x][3], top[y][3]), min(a1, a2)))
    return out


                                                                                                                                       
HAVE_HEAD_RE = re.compile(r"(have|let)(?![\w'!?])\s*")


def _stmt_parts(S: Src, h: int, l: int):
    """A `have`/`let` tactic statement on lines h..l: (name, type or None, value start, value end, value is a `by` block) or None.
"""
    B, b = S.B, S.body
    ln = B.lines[h]
    a, z = ln.tac, B.lines[l].end
    m = HAVE_HEAD_RE.match(b, a)
    if not m or any(S.mask[a:z]):
        return None
    k = m.end()
    nm = re.compile(r"[^\W\d][\w'!?]*").match(b, k)
    name = None
    if nm and nm.group(0) not in ("by",):
        name, k = nm.group(0), nm.end()
    while k < z and b[k] in " \t":
        k += 1
    if k >= z or b[k] in "(⟨{[":
        return None
    typ = None
    if b[k] == ":" and not b.startswith(":=", k):
        e = _scan_to(b, S.mask, S.pairs, k + 1, (":=",), line_only=False)
        if e >= z:
            return None
        typ = re.sub(r"\s+", " ", b[k + 1:e]).strip()
        k = e
    if not b.startswith(":=", k):
        return None
    v = k + 2
    while v < z and b[v] in " \t":
        v += 1
    if v >= z:
        return None
    is_by = bool(re.match(r"by(?![\w'!?])", b[v:v + 3]))
    if m.group(1) == "let" and is_by:
        return None
    return (name or "this"), typ, v, z, is_by


def _scope_end(S: Src, l: int, ind: int) -> int:
    """Body offset where the scope of a statement ending on line l at indent `ind` ends (first shallower code line)."""
    for ln in S.B.lines[l + 1:]:
        if ln.code and ln.indent < ind:
            return ln.start
    return len(S.body)


def _uses(S: Src, name: str, a: int, z: int) -> list[int] | None:
    """Whole-word uses of `name` in body[a:z]; the scope is cut at a re-binding (a bound name in a binder / pattern span, or an anonymous
"""
    out = []
    for u in S.B.uses(name, a):
        if u >= z:
            break
        if S.binds(u):
            break
        if re.match(r"[ \t]*:=", S.body[u + len(name):]):                                                        
            continue
        prev = _prev_token(S.body, S.mask, u)
        if prev in NO_USE_PREV or _in_at_list(S, u):
            return None
        out.append(u)
    if name == "this":
        for m in re.finditer(r"(?<![\w'])have\s*:", S.body[a:z]):
            cut = a + m.start()
            out = [u for u in out if u < cut]
            break
    return out


def _in_at_list(S: Src, u: int) -> bool:
    ls = S.body.rfind("\n", 0, u) + 1
    seg = S.body[ls:u]
    m = list(re.finditer(r"(?<![\w'])at(?![\w'])", seg))
    return bool(m) and re.fullmatch(r"[\s\w'.!?⊢]*", seg[m[-1].end():]) is not None


def _use_ctx(S: Src, u: int, name: str) -> tuple[str, str, bool]:
    """(token before the use, character after it, the use ends its term: nothing but blanks, or a closing bracket first, follows it on
"""
    b = S.body
    prev = _prev_token(b, S.mask, u)
    e = u + len(name)
    after = b[e:e + 1]
    rest = b[e:b.find("\n", e) if b.find("\n", e) >= 0 else len(b)]
    code_rest = "".join(ch for p, ch in enumerate(rest, e) if not S.mask[p]).strip()
    return prev, after, code_rest == "" or code_rest[0] in ")⟩]}"


WHOLE_PREV = ("exact", "apply", "refine", "refine'", "using", ":=", "$", "<|", "from", "⟨", ",", "[", "=>")                           
TAIL_PREV = ("exact", "using", ":=", "from", "$", "<|")                                                                          


def _term_rep(S: Src, u: int, name: str, val: str, typ: str | None, ascribe: bool) -> str:
    """The text replacing the use of `name` at u by the term `val` (ascribed with `typ` when `ascribe`)."""
    prev, after, ends = _use_ctx(S, u, name)
    whole = prev in WHOLE_PREV and after in (" ", "\n", "", ")", "⟩", "]", ",")
    if ascribe:
        if ends and prev in TAIL_PREV and "\n" not in val:
            return f"show {typ} from {val}"
        return f"({val} : {typ})"
    if after == ".":
        return f"({val})"
    if GR._atomic(val):
        return val
    if whole and (ends or after in ")⟩],") and (not GR.LIST_OK.search(val) or prev in TAIL_PREV):
        return val
    return f"({val})"


def _reindent(lines: list[str], col: int) -> list[str]:
    ind = min(len(x) - len(x.lstrip(" ")) for x in lines if x.strip())
    return [(" " * col + x[ind:]) if x.strip() else "" for x in lines]


def _inline(S: Src) -> list[tuple]:
    """t1:inline (see the module docstring): every `have`/`let` tactic statement at any depth whose uses in its scope can take a term."""
    B, b, out = S.B, S.body, []
    if B.first is None:
        return out
    for h, l, ind in B.all_stmts():
        if not GR._is_tactic_stmt(B, h) or B.in_conv(B.lines[h]):
            continue
        parts = _stmt_parts(S, h, l)
        if parts is None:
            continue
        name, typ, v, z, is_by = parts
        uses = _uses(S, name, B.lines[l].end, _scope_end(S, l, ind))
        if not uses:
            continue
        at = B.lines[h].start
        del_edit = (at, min(B.lines[l].end + 1, len(b)) - at, "")
        val = b[v:z].rstrip()
        note0 = f"inline `{name}`"
        if not is_by:
            multi = "\n" in val
            if len(uses) > (1 if multi else MAX_USES):
                continue
            if multi:                                                                         
                uind = B.lines[S.line_of(uses[0])].indent
                first, *cont = val.split("\n")
                val = "\n".join([first] + [(" " * max(0, uind - ind) + x) if x.strip() else x for x in cont])
            for asc in ((False, True) if typ and not multi else (False,)):
                edits = (del_edit,) + tuple((u, len(name), _term_rep(S, u, name, val, typ, asc)) for u in uses)
                out.append(("t1:inline", f"{note0} := {_flat(val)[:40]}" + (" (ascribed)" if asc else ""), edits, 0.0, at))
            continue
        if len(uses) != 1:
            continue
        u = uses[0]
        prev, after, ends = _use_ctx(S, u, name)
        tail = ends and prev in TAIL_PREV
        tac = b[v + 2:z]
        uline = B.lines[S.line_of(u)]
        if "\n" not in tac and tac.strip():                          
            t = tac.strip()
            reps = [f"by {t}" if tail else f"(by {t})"]
            if typ:
                reps.append(f"show {typ} by {t}" if tail else f"(by {t} : {typ})")
            for r in reps:
                out.append(("t1:inline", f"{note0} := {r[:44]}", (del_edit, (u, len(name), r)), 0.0, at))
            continue
                                                                               
        first, *rest = tac.split("\n")
        if not any(x.strip() for x in rest):
            continue
        rind = min(len(x) - len(x.lstrip(" ")) for x in rest if x.strip())
        block = ([" " * rind + first.strip()] if first.strip() else []) + rest
        ucol = uline.tac - uline.start
        line_code = b[uline.tac:uline.end].strip()
        if line_code in (f"exact {name}", f"apply {name}", f"refine {name}"):                                          
            nb = _reindent(block, ucol)
            out.append(("t1:inline", f"{note0}: its block replaces `{line_code}`",
                        (del_edit, (uline.tac, uline.end - uline.tac, "\n".join(nb)[ucol:])), 0.0, at))
        nb = "\n".join(_reindent(block, uline.indent + 2))
        if tail:
            out.append(("t1:inline", f"{note0}: `by` block at the use", (del_edit, (u, len(name), "by\n" + nb)), 0.0, at))
            if typ:
                out.append(("t1:inline", f"{note0}: `show T by` block at the use", (del_edit, (u, len(name), f"show {typ} by\n" + nb)),
                            0.0, at))
        elif not any(S.mask[u:uline.end]):
            rest_t = b[u + len(name):uline.end]
            out.append(("t1:inline", f"{note0}: `(by` block `)` at the use",
                        (del_edit, (u, uline.end - u, "(by\n" + nb + ")" + rest_t)), 0.0, at))
    return out


def _gap_inline(S: Src) -> list[tuple]:
    """harness/gap_rules.inline_have's single-line candidates (its bare-term placement), relabelled. Kept only when the deleted statement

"""
    if S.B.fb < 0 or S.B.first is None:
        return []
    try:
        rules = GR.inline_have(S.B)
    except Exception:                
        return []
    out = []
    for r in rules:
        dels = [e for e in r.edits if e[2] == ""]
        if len(dels) != 1:
            continue
        h = S.line_of(dels[0][0])
        parts = _stmt_parts(S, h, h)
        if parts is None:
            continue
        val = S.body[parts[2]:parts[3]].strip()
        if all(val in e[2] for e in r.edits if e[2]):
            out.append(("t1:inline", r.note, r.edits, 0.0, r.edits[0][0]))
    return out


                                                                                                                                       
def _apply(body: str, edits) -> str:
    for pos, dl, ins in sorted(edits, key=lambda e: (-e[0], -e[1])):
        body = body[:pos] + ins + body[pos + dl:]
    return body


def _profile(ctx: dict | None) -> dict:
    p = (ctx or {}).get("profile")
    out = {}
    if isinstance(p, dict):
        for k, v in p.items():
            try:
                out[int(k)] = float(v)
            except (TypeError, ValueError):
                pass
    elif isinstance(p, (list, tuple)):
        for x in p:
            try:
                if isinstance(x, dict):
                    out[int(x["line"])] = float(x.get("heartbeats", x.get("hb", 0)))
                else:
                    out[int(x[0])] = float(x[1])
            except (KeyError, TypeError, ValueError, IndexError):
                pass
    return out


FINDERS = (_proj, _projapp, _gap_inline, _inline, _holes, _field)
FINDER_OPS = {_proj: ("t1:proj",), _projapp: ("t1:projapp",), _gap_inline: ("t1:inline",), _inline: ("t1:inline",), _holes: HOLE_OPS,
              _field: ("t1:field",)}                                                                           


def _op_names(v) -> list[str]:
    """Op names from a list / tuple / set or a comma-separated string, each with the "t1:" prefix."""
    if isinstance(v, str):
        v = v.split(",")
    out = []
    for x in v or ():
        x = str(x).strip()
        if x:
            out.append(x if x.startswith("t1:") else f"t1:{x}")
    return out


def ops_for(ctx: dict | None) -> tuple[str, ...]:
    """The op set of a call, in OPS order (module docstring, "Op selection"): ctx["ops"] when given (an allow-list), else DEFAULT_OPS
"""
    ctx = ctx or {}
    if ctx.get("ops") is not None:
        want = set(_op_names(ctx["ops"]))
        return tuple(o for o in OPS if o in want)
    extra = set(_op_names(ctx.get("opt_in"))) & set(OPT_IN_OPS)
    return tuple(o for o in OPS if o in DEFAULT_OPS or o in extra)


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = MAX_PER_OP,
               ctx: dict | None = None) -> list[dict]:
    """T1 candidates of one declaration: [{"op", "decl", "note"}], round-robin over OPS, each op ordered by estimated value."""
    body = split_declaration(proof, statement)
    if body is None:
        return []
    head = proof[:len(proof) - len(body)]
    ops = ops_for(ctx)
    if not ops:
        return []
    S = Src(body, statement)
    ex = float(exchange) if exchange else 1.0
    prof = _profile(ctx)
    line0 = head.count("\n") + 1                                                     
    newline0 = bool(re.match(r"[ \t]*\n", body))
    t0 = count_tokens(body)
    raw = []
    for find in FINDERS:
        if find in FINDER_OPS and not any(o in ops for o in FINDER_OPS[find]):                                                 
            continue
        try:
            raw += find(S)
        except Exception:                                                                             
            continue
    singles = []
    by_op: dict = {}
    seen = {proof, proof.rstrip()}
    for op, note, edits, prior, pos in raw:
        nb = _apply(body, edits)
        if not newline0 and re.match(r"[ \t]*\n", nb):
            continue
        decl = head + nb
        if decl in seen or decl.rstrip() in seen or split_declaration(decl, statement) != nb:
            continue
        dtok = t0 - count_tokens(nb)
        if op == "t1:inline" and dtok < 1:
            continue
        lhb = prof.get(line0 + S.line_of(pos), 0.0)
        val = dtok * ex + lhb
                                                                                                                    
        item = (-prior, -val, pos, note, decl, edits) if op in HOLE_OPS else (-val, -prior, pos, note, decl, edits)
        by_op.setdefault(op, []).append(item)
        if op == "t1:hole":
            singles.append((op, note, edits, prior, pos, val))
    singles.sort(key=lambda x: (-x[3], -x[5], x[4]))
    for op, note, edits, prior, pos in _hole_pairs([(s[0], s[1], s[2], s[3], s[4]) for s in singles]):
        nb = _apply(body, edits)
        if not newline0 and re.match(r"[ \t]*\n", nb):
            continue
        decl = head + nb
        if decl in seen or split_declaration(decl, statement) != nb:
            continue
        dtok = t0 - count_tokens(nb)
        by_op.setdefault(op, []).append((-prior, -(dtok * ex + prof.get(line0 + S.line_of(pos), 0.0)), pos, note, decl, edits))
    lists, tail = [], []
    for op in OPS:
        if op not in ops:
            continue
        items, kept = sorted(by_op.get(op, ()), key=lambda x: x[:3]), []
        for it in items:
            if len(kept) >= max_per_op:
                break
            decl = it[4]
            if decl in seen or decl.rstrip() in seen:
                continue
            seen.add(decl); seen.add(decl.rstrip())
            pos = it[2]
            kept.append({"op": op, "decl": decl, "note": f"{it[3]} @L{line0 + S.line_of(pos)}"})
        (tail if op in LAST_OPS else lists).append(kept)
    out = []
    for i in range(max((len(x) for x in lists), default=0)):
        out += [x[i] for x in lists if i < len(x)]
    return out + [c for x in tail for c in x]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="T1 elaboration-compressor candidates of one declaration (no compile)")
    ap.add_argument("--file", required=True)
    ap.add_argument("--statement-file", required=True)
    ap.add_argument("--exchange", type=float, default=None)
    ap.add_argument("--max-per-op", type=int, default=MAX_PER_OP)
    ap.add_argument("--show", action="store_true", help="print each candidate's body")
    ap.add_argument("--opt-in", action="append", default=[], metavar="OP",
                    help=f"add an opt-in op to the default set (repeatable or comma-separated; opt-in ops: {', '.join(OPT_IN_OPS)})")
    ap.add_argument("--ops", help="the op set itself, comma-separated (an allow-list; default: DEFAULT_OPS plus --opt-in)")
    a = ap.parse_args(argv)
    proof = Path(a.file).read_text(); stmt = Path(a.statement_file).read_text().rstrip("\n")
    t0 = count_tokens(split_declaration(proof, stmt) or "")
    ctx = {"ops": a.ops} if a.ops is not None else {"opt_in": [o for s in a.opt_in for o in _op_names(s)]} if a.opt_in else None
    for d in candidates(proof, stmt, exchange=a.exchange, max_per_op=a.max_per_op, ctx=ctx):
        body = split_declaration(d["decl"], stmt)
        print(json.dumps({"op": d["op"], "note": d["note"], "dtok": count_tokens(body) - t0}, ensure_ascii=False))
        if a.show:
            print(body)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
