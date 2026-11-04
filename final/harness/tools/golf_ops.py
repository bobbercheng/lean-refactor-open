#!/usr/bin/env python3
"""Golf ops (b65, docs/argon_review_value.md item 3, operator 2026-10-27): the mechanical golf the Argon review keeps finding in Sol's proofs

















"""
from __future__ import annotations

import argparse, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs, OPEN, KEYWORDS              
from harness.lint_delete import _list_items              
from scorer.tokenize import split_declaration, count_tokens              

OPS = ("golf:trailarg", "golf:casewrap", "golf:use", "golf:dot", "golf:havefun")
ALL_OPS = OPS
OPT_IN_OPS = OPS                                                    
DEFAULT_OPS = tuple(o for o in OPS if o not in OPT_IN_OPS)
TABLES: dict = {}
MAX_PER_OP = 40

_W = r"(?<![\w.'?!₀-₉])"
IDENT = r"[^\W\d][\w'!?₀-₉]*(?:\.(?:\d+|[^\W\d][\w'!?₀-₉]*))*"
ATOM_RE = re.compile(r"(?:%s|\d+|\?_|_|\?[^\W\d][\w'₀-₉]*)" % IDENT)
LIST_HEAD_RE = re.compile(r"(?:^|[\s;(])(?:simp_all|simp_arith|simpa|simp|dsimp|field_simp|norm_num|rw|rwa|rewrite|erw|simp_rw|nth_rewrite"
                          r"(?:\s+\d+)+|nth_rw(?:\s+\d+)+|linarith|nlinarith|push_cast)[!?]?(?:\s+only)?\s*$")
HEAD_TACS = ("apply", "exact", "refine", "refine'")
DOT_PREV_WORDS = {"exact", "apply", "refine", "refine'", "use", "exists", "from", "using", "convert", "rcases", "cases", "exact_mod_cast",
                  "then", "else", "calc", "specialize", "obtain"}
DOT_PREV_PUNCT = ("(", "⟨", "[", ",", ":=", "=>", "↦", "←", "$", "<|", "{", ";")
NON_ARGS = KEYWORDS | {"at", "with", "using", "only", "fun", "λ", "by", "from", "in", "then", "else", "do"}


def _op_names(ops) -> list[str]:
    out = []
    for o in (ops.split(",") if isinstance(ops, str) else list(ops or [])):
        o = str(o).strip()
        if o:
            out.append(o if o.startswith("golf:") else "golf:" + o)
    return out


def ops_for(ctx: dict | None) -> tuple[str, ...]:
    """The op set of a call, in OPS order: ctx["ops"] when given (an allow-list), else DEFAULT_OPS plus ctx["opt_in"]."""
    ctx = ctx or {}
    if ctx.get("ops") is not None:
        want = set(_op_names(ctx["ops"]))
        return tuple(o for o in OPS if o in want)
    extra = set(_op_names(ctx.get("opt_in"))) & set(OPT_IN_OPS)
    return tuple(o for o in OPS if o in DEFAULT_OPS or o in extra)


                                                                                                                                     
class _Body:
    def __init__(self, body: str):
        self.s, self.mask = body, _mask(body)
        self.pairs = _pairs(body, self.mask)

    def line(self, i: int) -> tuple[int, int]:
        ls = self.s.rfind("\n", 0, i) + 1
        le = self.s.find("\n", i)
        return ls, (len(self.s) if le < 0 else le)

    def code_end(self, ls: int, le: int) -> int:
        """End of the code on the line [ls, le) before a comment, trailing blanks excluded."""
        p = ls
        while p < le and not (self.mask[p] and self.s.startswith(("--", "/-"), p)):
            p += 1
        while p > ls and self.s[p - 1] in " \t":
            p -= 1
        return p

    def args(self, i: int, end: int) -> list[tuple[int, int]] | None:
        """Spans of the whitespace-separated arguments in [i, end): bracket groups and atoms (names, numerals, holes); None when something
"""
        out, s = [], self.s
        while True:
            while i < end and s[i] in " \t":
                i += 1
            if i >= end:
                return out
            if self.mask[i]:
                return None
            if s[i] in OPEN:
                j = self.pairs.get(i)
                if j is None or j >= end:
                    return None
                out.append((i, j + 1)); i = j + 1
                if i < end and s[i] not in " \t":
                    return None                                          
                continue
            m = ATOM_RE.match(s, i)
            if not m or m.end() > end or (m.end() < end and s[m.end()] not in " \t") or m.group(0) in NON_ARGS:
                return None
            out.append((i, m.end())); i = m.end()


def _continues(s: str, le: int, col: int) -> bool:
    """Does the term go on below line end `le` (the next non-blank line indented deeper than column `col`)?"""
    for t in s[le + 1:].split("\n"):
        if t.strip():
            return len(t) - len(t.lstrip(" ")) > col
    return False


def _hole(t: str) -> bool:
    return t in ("?_", "_")


                                                                                                                                     
def _trailarg(B: _Body) -> list[tuple]:
    s, out = B.s, []
    for k in sorted(B.pairs):                
        if s[k] != "[" or B.mask[k]:
            continue
        ls, _ = B.line(k)
        if not LIST_HEAD_RE.search(s[ls:k]):
            continue
        for a, b in _list_items(s, B.mask, B.pairs, k) or []:
            m = re.match(r"(←\s*|<-\s*)?(%s)" % IDENT, s[a:b])
            if not m or s[a:b].startswith("@"):
                continue
            hs, he = a + m.start(2), a + m.end(2)
            args = B.args(he, b)
            if not args or any(B.mask[p] for p in range(a, b)):
                continue
            out.append(("golf:trailarg", s[a:b][:40], ((args[-2][1] if len(args) > 1 else he, b - (args[-2][1] if len(args) > 1 else he), ""),)))
            if len(args) > 1:
                out.append(("golf:trailarg", s[a:b][:40] + " (all)", ((he, b - he, ""),)))
    for m in re.finditer(_W + r"(apply|exact|refine'|refine)[ \t]+(?=[^\s(⟨])", s):                 
        i = m.start()
        if B.mask[i]:
            continue
        ls, le = B.line(i)
        if s[ls:i].strip() not in ("", "·") and not s[ls:i].rstrip().endswith((";", "=>", "<;>", "by")):
            continue
        tac, h0 = m.group(1), m.end()
        hm = re.compile(IDENT).match(s, h0)
        if not hm or hm.group(0) in NON_ARGS:
            continue
        end = B.code_end(ls, le)
        args = B.args(hm.end(), end)
        if not args or _continues(s, le, i - ls):
            continue
        texts = [s[a:b] for a, b in args]
        nh = len(texts)
        while nh > 0 and _hole(texts[nh - 1]) and (tac != "refine" or texts[nh - 1] == "?_"):
            nh -= 1
        head = s[h0:hm.end()]

        def cand(keep, note, new_tac="apply"):
            rest = "".join(" " + t for t in texts[:keep])
            return ("golf:trailarg", f"{tac} {head} {note}", ((i, end - i, f"{new_tac} {head}{rest}"),))
        if tac == "apply":
            out.append(cand(nh - 1 if nh == len(texts) else nh, "-1"))
            if len(texts) > 1:
                out.append(cand(0, "(all)"))
        elif tac == "exact":
            out.append(cand(nh if nh < len(texts) else nh - 1, "-> apply"))
        elif nh < len(texts):                                         
            out.append(cand(nh, "holes -> apply"))
    return out


def _casewrap(B: _Body) -> list[tuple]:
    s, out = B.s, []
    for m in re.finditer(r"(?m)^([ \t]*)case'[ \t]+[^\n]*?=>[ \t]*", s):
        i = m.start() + len(m.group(1))
        if B.mask[i]:
            continue
        c = len(m.group(1))
        ls, le = B.line(i)
        rest_end = B.code_end(ls, le)
        nl = le + 1
                                                                                                                            
        lines, p = [], nl
        while p < len(s):
            q = s.find("\n", p); q = len(s) if q < 0 else q
            t = s[p:q]
            if t.strip() and len(t) - len(t.lstrip(" ")) <= c:
                break
            lines.append((p, q)); p = q + 1
        while lines and not s[lines[-1][0]:lines[-1][1]].strip():
            lines.pop()
        if m.end() < rest_end:                                                                
            col = m.end() - ls
            new_first = " " * c + s[m.end():le]
        else:
            if not lines:
                continue
            col = min(len(s[a:b]) - len(s[a:b].lstrip(" ")) for a, b in lines if s[a:b].strip())
            new_first = None
        body_new = []
        ok = True
        for a, b in lines:
            t = s[a:b]
            if not t.strip():
                body_new.append(""); continue
            ind = len(t) - len(t.lstrip(" "))
            if ind < col:
                ok = False; break
            body_new.append(" " * (c + ind - col) + t.lstrip(" "))
        if not ok:
            continue
        new = ([new_first] if new_first is not None else []) + body_new
        stop = lines[-1][1] if lines else le
        out.append(("golf:casewrap", s[i:min(le, i + 40)], ((ls, stop - ls, "\n".join(new)),)))
    return out


def _use(B: _Body) -> list[tuple]:
    s, out = B.s, []
    for m in re.finditer(_W + r"(refine'|refine)[ \t]+⟨", s):
        i = m.start()
        lb = m.end() - 1
        if B.mask[i] or lb not in B.pairs:
            continue
        rb = B.pairs[lb]
        ls, le = B.line(i)
        if rb >= le or B.code_end(ls, le) != rb + 1:
            continue
        comps, d, a = [], 0, lb + 1
        for p in range(lb + 1, rb + 1):
            ch = s[p]
            if p < rb and B.mask[p]:
                continue
            if p < rb and ch in "([{⟨":
                d += 1
            elif p < rb and ch in ")]}⟩":
                d -= 1
            elif p == rb or (ch == "," and d == 0):
                comps.append(s[a:p].strip()); a = p + 1
        holes = ("?_",) if m.group(1) == "refine" else ("?_", "_")
        n = len(comps)
        while n > 0 and comps[n - 1] in holes:
            n -= 1
        keep = comps[:n]
        if n == len(comps) or not keep or any(not c or re.search(r"(?<![\w'])\?_", c) for c in keep):
            continue
        out.append(("golf:use", s[i:rb + 1][:40], ((i, rb + 1 - i, "use " + ", ".join(keep)),)))
    return out


def _prev_ok(s: str, mask, i: int) -> bool:
    j = i - 1
    while j >= 0 and s[j] in " \t":
        j -= 1
    if j < 0 or s[j] == "\n":
        return True
    for p in DOT_PREV_PUNCT:
        if s.endswith(p, 0, j + 1):
            return True
    w = re.search(r"[\w'!?]+$", s[:j + 1])
    return bool(w) and w.group(0) in DOT_PREV_WORDS


def _dot(B: _Body) -> list[tuple]:
    s, out = B.s, []
    pat = re.compile(_W + r"(?<!@)((?:[A-Z][\w'₀-₉]*)(?:\.[A-Z][\w'₀-₉]*)*)\.([a-z_][\w'!?₀-₉]*)[ \t]+([^\W\d][\w'₀-₉]*(?:\.\d+)*)(?![\w'.!?₀-₉])")
    for m in pat.finditer(s):
        i = m.start()
        if B.mask[i] or B.mask[m.start(3)] or not m.group(3)[0].islower() or m.group(3) in NON_ARGS:
            continue
        if not _prev_ok(s, B.mask, i):
            continue
        out.append(("golf:dot", m.group(0)[:40], ((i, m.end() - i, f"{m.group(3)}.{m.group(2)}"),)))
    return out


def _havefun(B: _Body) -> list[tuple]:
    s, out = B.s, []
    for m in re.finditer(_W + r"(have|haveI|let)[ \t]+(%s)[ \t]*:=[ \t]*fun[ \t]+" % IDENT, s):
        i = m.start()
        if B.mask[i]:
            continue
        ls, le = B.line(i)
        p, binders = m.end(), []
        while p < le:                                                                                    
            while p < le and s[p] in " \t":
                p += 1
            if s.startswith(("=>", "↦"), p):
                break
            if s[p] in "({⦃[" and p in B.pairs and B.pairs[p] < le:
                q = B.pairs[p] + 1
                inner = s[p + 1:q - 1]
                if ":" not in inner and s[p] == "(":
                    binders = None; break
                binders.append(s[p:q]); p = q; continue
            nm = re.compile(r"[^\W\d][\w'₀-₉]*").match(s, p)
            if s[p] == ":":                                      
                q = s.find("=>", p, le)
                q = q if q >= 0 else s.find("↦", p, le)
                if q < 0 or not binders or any(b.startswith(("(", "{", "⦃", "[")) for b in binders):
                    binders = None; break
                binders = [f"({' '.join(binders)} {s[p:q].strip()})"]; p = q; break
            if not nm or nm.group(0) in NON_ARGS or nm.group(0) == "_":
                binders = None; break
            binders.append(nm.group(0)); p = nm.end()
        if not binders or not s.startswith(("=>", "↦"), p):
            continue
        arrow_end = p + (2 if s.startswith("=>", p) else 1)
        new = f"{m.group(1)} {m.group(2)} {' '.join(binders)} :="
        out.append(("golf:havefun", s[i:arrow_end][:40], ((i, arrow_end - i, new),)))
    return out


FINDERS = {"golf:trailarg": _trailarg, "golf:casewrap": _casewrap, "golf:use": _use, "golf:dot": _dot, "golf:havefun": _havefun}


def _apply(body: str, edits) -> str:
    for pos, dl, ins in sorted(edits, key=lambda e: (-e[0], -e[1])):
        body = body[:pos] + ins + body[pos + dl:]
    return body


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = MAX_PER_OP, ctx: dict | None = None) -> list[dict]:
    """Golf candidates of one declaration: [{"op", "decl", "note"}] for the ops of ops_for(ctx) (none by default), OPS order, then position;
"""
    ops = ops_for(ctx)
    body = split_declaration(proof, statement)
    if body is None or not ops:
        return []
    head = proof[:len(proof) - len(body)]
    B = _Body(body)
    t0 = count_tokens(body)
    newline0 = bool(re.match(r"[ \t]*\n", body))
    out, seen = [], {proof.rstrip()}
    for op in ops:
        n = 0
        try:
            found = FINDERS[op](B)
        except Exception:                                                         
            continue
        for _op, note, edits in sorted(found, key=lambda x: min(e[0] for e in x[2])):
            if n >= max_per_op:
                break
            nb = _apply(body, edits)
            decl = head + nb
            if decl.rstrip() in seen or (not newline0 and re.match(r"[ \t]*\n", nb)) or split_declaration(decl, statement) != nb:
                continue
            if count_tokens(nb) >= t0:
                continue
            seen.add(decl.rstrip()); n += 1
            line = decl.count("\n", 0, len(head) + min(e[0] for e in edits)) + 1
            out.append({"op": op, "decl": decl, "note": f"{note} @L{line}"})
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="golf-op candidates of one declaration (no compile)")
    ap.add_argument("--file", required=True); ap.add_argument("--statement-file", required=True)
    ap.add_argument("--ops", default=",".join(OPS), help="comma-separated op names (default: every op)")
    a = ap.parse_args(argv)
    proof = Path(a.file).read_text(); stmt = Path(a.statement_file).read_text().rstrip("\n")
    t0 = count_tokens(split_declaration(proof, stmt) or "")
    for d in candidates(proof, stmt, ctx={"ops": _op_names(a.ops)}):
        print(json.dumps({"op": d["op"], "note": d["note"], "dtok": count_tokens(split_declaration(d["decl"], stmt)) - t0}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
