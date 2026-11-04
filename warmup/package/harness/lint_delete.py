#!/usr/bin/env python3
"""Lint deletions and a bounded deletion search (2026-10-13): a deterministic, model-free $0 CPU post-pass next to the heartbeat



































"""
from __future__ import annotations

import argparse, json, re, sys, time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs, OPEN, CLOSE              
from harness.hb_polish import prov, _pick              
from harness.hb_rewrite import (_tac_pos, _first_by, _ls, _line_end, _indent_at, _code, _skip_ws, _next_code_line, _is_final,              
                                _block_must_close, valid_run_id, KINDS)
from scorer.tokenize import count_tokens, split_declaration              

OPS = ("lint", "delsearch")              
LINT_OPTS = ("linter.unusedSimpArgs", "linter.unusedTactic")
MAX_COMPILES = 24
MIN_GAIN = 0.05                                                                                               
EPS = 1e-9

UNUSED_ARG_RE = re.compile(r"This simp argument is unused:\s*\n(.*?)(?:\n\s*\n|\Z)", re.S)
UNUSED_TAC_RE = re.compile(r"\A\s*(?:'(?P<a>.*?)' tactic does nothing|Unused tactic linter: `(?P<b>.*?)` does nothing)", re.S)
UNKNOWN_OPT_RE = re.compile(r"[Uu]nknown option [`'\"]?([\w.]+)")
SIMP_HEAD_RE = re.compile(r"(?<![\w.'?!])(simp_all|simpa|simp|dsimp)(?![\w'?!])")
SIMPLE_ARG_RE = re.compile(r"(?:(?:←|<-|↑|↓|-)\s*)?[^\W\d][\w.'!?]*|\*")
WORD_RE = re.compile(r"[^\W\d][\w.'!?]*")
                                                                     
SKIP_WORDS = {"_", "case", "case'", "next", "fun", "λ", "by", "with", "then", "else", "at", "using", "from", "termination_by",
              "decreasing_by", "where", "in", "do", "match", "calc", "if", "let", "open", "set_option"}
CLEANUP_WORDS = {"simp", "simp_all", "simpa", "dsimp", "norm_num", "ring_nf", "push_cast", "norm_cast", "field_simp", "unfold", "delta",
                 "show", "change", "clear", "skip", "simp_rw", "beta_reduce", "subst_vars", "try", "push_neg", "rfl"}
STRUCT_WORDS = {"intro", "intros", "rintro", "induction", "induction'", "cases", "cases'", "rcases", "obtain", "constructor", "refine",
                "refine'", "use", "exists", "exact", "apply", "split", "split_ifs", "by_cases", "by_contra", "ext", "funext", "congr",
                "subst", "specialize", "generalize", "revert", "fun_induction", "exfalso", "left", "right"}
COMBINATOR_WORDS = {"all_goals", "any_goals", "try", "repeat", "repeat'", "iterate", "focus", "classical", "skip"}
OPENER_TAILS = ("by", "=>", "do", "then", "else", "with", "·")
CONT_TAILS = (",", "(", "[", "⟨", "{", ":=", "←", "<;>", "<|>", "<|", "|>", "|", "+", "=", "∧", "∨", "↔", "→", "$", "in", "at",
              "using", "from", ":")                                       


@dataclass(frozen=True)
class Del:
    kind: str                                                                               
    span: tuple                                                                                                               
    lb: int = -1                                     
    note: str = ""
    src: str = ""                             
    key: tuple = ()                                                                                   
    pos: int = -1                                                      
    whole: bool = False                               


                                                                                                                                           
def _list_items(body: str, mask: list, pairs: dict, lb: int):
    """Stripped (start, end) spans of the depth-0 comma-separated items of the list opened at lb; [] for `[]`; None when an item is empty
"""
    if lb not in pairs or body[lb] != "[":
        return None
    rb = pairs[lb]; out = []; s = p = lb + 1; cmt = set()
    while p <= rb:
        if p < rb and mask[p]:
            q = p
            while q < rb and mask[q]:
                q += 1
            if body[p] != '"':                                                                                   
                cmt.update(range(p, q))
            p = q; continue
        if p < rb and body[p] in OPEN and p in pairs:
            p = pairs[p] + 1; continue
        if p == rb or body[p] == ",":
            a, b = s, p
            while a < b and (body[a].isspace() or a in cmt):
                a += 1
            while b > a and (body[b - 1].isspace() or b - 1 in cmt):
                b -= 1
            out.append((a, b)); s = p + 1
        p += 1
    if len(out) == 1 and out[0][0] == out[0][1]:
        return []
    return None if any(a == b for a, b in out) else out


def _line_span(body: str, a: int, b: int) -> tuple:
    """The span deleting the whole lines holding body[a:b] with one of their newlines (the preceding one on the body's last line)."""
    ls, le = _ls(body, a), _line_end(body, max(a, b - 1))
    return (ls, le + 1) if le < len(body) else (max(ls - 1, 0), le)


def render(body: str, dels) -> str:
    """body with the deletions applied together: the items deleted from one list leave its other items with the separator that preceded

"""
    return render_kept(body, dels)[0]


def render_kept(body: str, dels) -> tuple:
    """(render(body, dels), the deletions that rendering actually applied, in their input order, one per span). Review 2026-10-13: an
"""
    mask = _mask(body); pairs = _pairs(body, mask); edits = []; done: set = set()
    for a, b in sorted({d.span for d in dels if d.kind == "tac"}):
        if not any(a < y and x < b for x, y, _ in edits):
            edits.append((a, b, "")); done.add(("tac", (a, b)))
    tac_spans = [(x, y) for x, y, _ in edits]
    by_list: dict = {}
    for d in dels:
        if d.kind == "arg" and not any(x <= d.span[0] < y for x, y in tac_spans):
            by_list.setdefault(d.lb, set()).add(d.span)
    for lb, spans in sorted(by_list.items()):
        items = _list_items(body, mask, pairs, lb)
        if not items:
            continue
        keep = [it for it in items if it not in spans]
        if len(keep) == len(items):
            continue
        rb = pairs[lb]
        if not keep:
            a = lb
            while a > 0 and body[a - 1] in " \t":
                a -= 1
            e = (a, rb + 1, "")
        else:
            out = body[lb + 1:items[0][0]] + body[keep[0][0]:keep[0][1]]
            for it in keep[1:]:
                j = items.index(it)
                out += body[items[j - 1][1]:it[0]] + body[it[0]:it[1]]
            e = (lb + 1, rb, out + body[items[-1][1]:rb])
        if not any(e[0] < y and x < e[1] for x, y, _ in edits):
            edits.append(e); done.update(("arg", s) for s in spans if s in items)
    for a, b, ins in sorted(edits, key=lambda e: -e[0]):
        body = body[:a] + ins + body[b:]
    kept, seen = [], set()
    for d in dels:
        k = (d.kind, d.span)
        if k in done and k not in seen:
            kept.append(d); seen.add(k)
    return body, kept


def _norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def _keyed(body: str, mask: list, dels: list) -> list:
    """The deletions with their keys, intrinsic to the body (lint's and delsearch's keys of one deletion agree):


"""
    pairs = _pairs(body, mask); items_of, seen = {}, {}
    for lb in sorted(k for k in pairs if body[k] == "[" and not mask[k]):
        pre = _norm(_code(body, mask, _ls(body, lb), lb))
        for it in _list_items(body, mask, pairs, lb) or []:
            kk = (pre, _norm(body[it[0]:it[1]])); items_of[it] = kk + (seen.get(kk, 0),); seen[kk] = seen.get(kk, 0) + 1
    line_of, seen, ls = {}, {}, 0                                                   
    while ls <= len(body):
        le = _line_end(body, ls); code = _norm(_code(body, mask, ls, le))
        line_of[ls] = (code, seen.get(code, 0)); seen[code] = seen.get(code, 0) + 1; ls = le + 1
    out = []
    for d in dels:
        if d.kind == "arg":
            key = ("arg",) + items_of.get(d.span, (_norm(body[_ls(body, d.pos):d.lb]), _norm(body[d.span[0]:d.span[1]]), -1))
        else:
            code, occ = line_of[_ls(body, d.pos)]
            key = ("tac", code, "" if d.whole else d.note, occ)
        out.append(Del(d.kind, d.span, d.lb, d.note, d.src, key, d.pos, d.whole))
    return out


                                                                                                                                           
def probe_prefix(opts) -> str:
    return "".join(f"set_option {o} true in\n" for o in opts)


def _offset(text: str, line: int, col: int):
    """Offset of the 1-based line / 0-based codepoint column in text; None when out of range."""
    if line < 1:
        return None
    p = 0
    for _ in range(line - 1):
        p = text.find("\n", p)
        if p < 0:
            return None
        p += 1
    le = text.find("\n", p); le = len(text) if le < 0 else le
    return p + col if col <= le - p else None


def _innermost_list(body: str, mask: list, pairs: dict, off: int):
    best = None
    for k, v in pairs.items():
        if body[k] == "[" and k < off <= v and (best is None or k > best):
            best = k
    return best


def _tail_op(body: str, mask: list, q: int):
    """The start of a `<;>` / `<|>` / `;` ending the code of the line at q (comments and blanks after it skipped), else None."""
    e = _line_end(body, q)
    while e > q and (mask[e - 1] or body[e - 1].isspace()):
        e -= 1
    for op in ("<;>", "<|>", ";"):
        s = e - len(op)
        if s >= q and body.startswith(op, s) and not any(mask[s:e]):
            return s
    return None


def _tac_deletion(body: str, mask: list, a: int, b: int):
    """(span, whole) deleting the tactic body[a:b] cleanly, or None: its whole line(s) when nothing else is on them (whole), but from the



"""
    ls, le = _ls(body, a), _line_end(body, max(a, b - 1))
    pre = _code(body, mask, ls, a).rstrip(); post = _code(body, mask, b, le).strip()
    if not pre.strip() and not post:
        q = _prev_code_line(body, mask, ls)
        k = _tail_op(body, mask, q) if q is not None else None
        if k is None:
            return _line_span(body, a, b), True
        while k > q and body[k - 1] in " \t":
            k -= 1
        return ((k, le), False) if _code(body, mask, q, k).strip() else None
    if pre.strip() in ("<;>", "<|>") and not post and _prev_code_line(body, mask, ls) is not None:
        return _line_span(body, a, b), True
    if pre.endswith("<;>") or (pre.endswith(";") and not post.startswith(";")):
        k = body.rfind("<;>" if pre.endswith("<;>") else ";", ls, a)
        while k > ls and body[k - 1] in " \t":
            k -= 1
        return ((k, b), False) if _code(body, mask, ls, k).strip() else None
    if post.startswith(";") and not post.startswith(";;") and (not pre.strip() or pre.endswith("·")):
        return (a, _skip_ws(body, body.find(";", b) + 1, newlines=False)), False
    return None


def _same_text(src: str, printed: str) -> bool:
    """Is the printed syntax the source text, up to blanks and the ASCII `<-` arrow?"""
    def f(s: str) -> str:
        return re.sub(r"\s+", "", s).replace("<-", "←")
    return bool(src.strip()) and f(src) == f(printed)


def lint_dels(body: str, head_len: int, prefix_len: int, probe: str, messages, head_lines: int, head_col: int = 0):
    """(deletions, counts) from the probe's warnings. probe = <set_option lines> + head + body; Lean's lines are offset by head_lines (the



"""
    mask = _mask(body); pairs = _pairs(body, mask); out = []
    c = {"warnings": 0, "args": 0, "tactics": 0, "unmatched": 0}
    base = prefix_len + head_len

    def at(pos):
        if not isinstance(pos, dict) or pos.get("line") is None:
            return None
        ln, col = int(pos["line"]) - head_lines, int(pos.get("column") or 0)
        col -= head_col if ln == 1 else 0
        o = _offset(probe, ln, col) if col >= 0 else None
        return None if o is None or o < base else o - base
    for m in messages or []:
        if m.get("severity") != "warning":
            continue
        d = str(m.get("data", "")); ma = UNUSED_ARG_RE.search(d); mt = UNUSED_TAC_RE.match(d)
        if not ma and not mt:
            continue
        a = at(m.get("pos"))
        if a is None:
            continue
        c["warnings"] += 1
        if ma:
            lb = _innermost_list(body, mask, pairs, a)
            items = _list_items(body, mask, pairs, lb) if lb is not None else None
            it = next((x for x in items or [] if x[0] <= a < x[1]), None)
            if it is None or not _same_text(body[it[0]:it[1]], ma.group(1)):
                c["unmatched"] += 1; continue
            out.append(Del("arg", it, lb, body[it[0]:it[1]], "lint", pos=it[0]))
        else:
            tac = mt.group("a") if mt.group("a") is not None else mt.group("b")
            b = at(m.get("endPos"))
            if b is None or b <= a:
                b = a + len(tac) if body.startswith(tac, a) else None
            got = _tac_deletion(body, mask, a, b) if b is not None and _same_text(_code(body, mask, a, b), tac) else None
            if got is None:
                c["unmatched"] += 1; continue
            out.append(Del("tac", got[0], -1, re.sub(r"\s+", " ", tac)[:48], "lint", pos=a, whole=got[1]))
    uniq = list({(x.kind, x.span): x for x in out}.values())                                                                     
    c["args"] = sum(x.kind == "arg" for x in uniq); c["tactics"] = sum(x.kind == "tac" for x in uniq)
    return _keyed(body, mask, uniq), c


_UNKNOWN_OPTS: dict = {}                                                                                                                      


def lint_probe(decl: str, compile_fn, opts, budget, unknown_out: set | None = None) -> tuple:
    """(compile result or None, the set_option prefix used): the options probe, retried without an unknown option, then plain (at most

"""
    cur = list(opts)
    while budget():
        pre = probe_prefix(cur)
        r = compile_fn(pre + decl)
        if getattr(r, "ok", False):
            return r, pre
        if not cur or getattr(r, "timed_out", False):
            break
        errs = [str(e) for e in getattr(r, "errors", []) or []] + [str(m.get("data", "")) for m in getattr(r, "messages", []) or []
                                                                   if m.get("severity") == "error"]
        unknown = {u for e in errs for u in UNKNOWN_OPT_RE.findall(e)} & set(cur)
        if unknown_out is not None:
            unknown_out.update(unknown)
        cur = [o for o in cur if o not in unknown] if unknown else []
    return None, ""


                                                                                                                                           
def _list_after_head(body: str, pairs: dict, k: int):
    """The '[' of a simp-family call's list after its head (config / discharger groups, +opt / -opt flags and `only` skipped), or None."""
    n = len(body)
    while True:
        k = _skip_ws(body, k, newlines=False)
        if k >= n:
            return None
        if body[k] == "(" and k in pairs:
            k = pairs[k] + 1; continue
        if body.startswith("only", k) and not (k + 4 < n and (body[k + 4].isalnum() or body[k + 4] in "_'")):
            k += 4; continue
        if body[k] in "+-" and k + 1 < n and body[k + 1].isalpha():
            m = WORD_RE.match(body, k + 1); k = m.end() if m else k + 1; continue
        return k if body[k] == "[" and k in pairs else None


def _arg_dels(body, mask, pairs, fb):
    out = []
    for m in SIMP_HEAD_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        lb = _list_after_head(body, pairs, m.end())
        items = _list_items(body, mask, pairs, lb) if lb is not None else None
        for s, e in items or []:
            if SIMPLE_ARG_RE.fullmatch(body[s:e]):
                out.append(Del("arg", (s, e), lb, body[s:e], "delsearch", pos=s))
    return out


def _prev_code_line(body: str, mask: list, ls: int):
    e = ls - 1
    while e >= 0:
        q = body.rfind("\n", 0, e) + 1
        if _code(body, mask, q, e).strip():
            return q
        e = q - 1
    return None


def _ends_with(code: str, tails) -> bool:
    for t in tails:
        if code.endswith(t) and (not t[-1].isalnum() or len(code) == len(t) or not (code[-len(t) - 1].isalnum() or code[-len(t) - 1] in "_.'")):
            return True
    return False


def _bullet_col(body: str, q: int):
    """The content column of a bullet line (`· tac`), else None."""
    st = q + _indent_at(body, q)
    if st < len(body) and (body[st] == "·" or (body[st] == "." and body[st + 1:st + 2] in (" ", "\t"))):
        return _skip_ws(body, st + 1, newlines=False) - q
    return None


def _sibling_before(body: str, mask: list, ls: int, ind: int) -> bool:
    q = _prev_code_line(body, mask, ls)
    while q is not None:
        qi = _indent_at(body, q)
        if _bullet_col(body, q) == ind:
            return True
        if qi == ind:
            return not body[q + qi:q + qi + 1] == "|"
        if qi < ind:
            return False
        q = _prev_code_line(body, mask, q)
    return False


def _line_dels(body, mask, pairs, fb):
    """Whole-line deletions of standalone single-line tactics, ordered cleanup first, structural last, by position inside a class. Review


"""
    out = []; ls = _line_end(body, fb) + 1 if fb >= 0 else len(body); base_ind = None
    while ls < len(body):
        le = _line_end(body, ls); ind = _indent_at(body, ls); st = ls + ind; nxt_ls = le + 1
        code = _code(body, mask, st, le).strip()
        wm = WORD_RE.match(body, st) if st < le and not mask[st] else None
        if code and base_ind is None:
            base_ind = ind
        if wm and wm.group(0) in ("where", "termination_by", "decreasing_by") and ind <= base_ind:
            break
        if not code or not wm or wm.group(0) in SKIP_WORDS or _ends_with(code, OPENER_TAILS + CONT_TAILS) \
                or code.split()[-1] in COMBINATOR_WORDS - {"skip"} or re.search(r"(?<![\w.'])iterate\s+\d+$", code):
            ls = nxt_ls; continue
        depth, bad = 0, False
        for p in range(st, le):
            if mask[p]:
                continue
            depth += body[p] in OPEN; depth -= body[p] in CLOSE
            bad = bad or depth < 0
        nx = _next_code_line(body, mask, ls)
        if bad or depth or (nx is not None and nx[1] > ind) \
                or (nx is not None and nx[1] == ind and body.startswith(("|", "<;>", "<|>"), nx[0] + nx[1])):
            ls = nxt_ls; continue
        q = _prev_code_line(body, mask, ls)
        if q is None:
            ls = nxt_ls; continue
        qc = _code(body, mask, q, _line_end(body, q)).strip(); qi = _indent_at(body, q)
        if qi < ind and not (_ends_with(qc, OPENER_TAILS) or qc.split()[-1] in COMBINATOR_WORDS or _bullet_col(body, q) == ind):
            ls = nxt_ls; continue                                            
        if _ends_with(qc, CONT_TAILS):
            ls = nxt_ls; continue
        sib_after = nx is not None and nx[1] == ind and body[nx[0] + nx[1]] != "|"
        if not (sib_after or _sibling_before(body, mask, ls, ind)):
            ls = nxt_ls; continue                                 
        w = wm.group(0)
        if _is_final(body, mask, st, le) and _block_must_close(body, mask, st) and w not in COMBINATOR_WORDS:
            ls = nxt_ls; continue                                                                                            
        cls = 0 if w in CLEANUP_WORDS else 2 if w in STRUCT_WORDS else 1
        out.append((cls, Del("tac", _line_span(body, st, le), -1, re.sub(r"\s+", " ", code)[:48], "delsearch", pos=st, whole=True)))
        ls = nxt_ls
    return [d for _, d in sorted(out, key=lambda t: (t[0], t[1].span[0]))]


def search_dels(body: str) -> list:
    """delsearch's candidates on a body, keyed: simple simp-list arguments by position, then standalone single-line tactics."""
    mask = _mask(body); pairs = _pairs(body, mask); fb = _first_by(body, mask)
    if fb < 0:
        return []
    return _keyed(body, mask, _arg_dels(body, mask, pairs, fb) + _line_dels(body, mask, pairs, fb))


                                                                                                                                           
def _probe_layout(row: dict, version: str) -> tuple:
    """(file lines before the declaration in an unmeasured compile, the options the probe may set, the column of the declaration's first

"""
    from scorer.compile import file_prefix, split_modifiers
    if row["source"] == "putnambench":
        return (row["header"].rstrip() + "\n\n").count("\n"), LINT_OPTS, 0
    core, mods = split_modifiers(file_prefix(row, version))
    return (core.rstrip("\n") + "\n\n" + mods).count("\n"), (() if mods.strip() else LINT_OPTS), len(mods) - (mods.rfind("\n") + 1)


def delete_proof(name: str, decl: str, *, base: dict | None = None, evaluate_fn=None, compile_fn=None, head_lines: int | None = None,
                 statement: str | None = None, opts=None, max_compiles: int = MAX_COMPILES, ops=OPS, deadline: float | None = None,
                 clock=time.monotonic, min_gain: float = MIN_GAIN, head_col: int = 0, opt_key=None) -> dict:
    """The report of one proof: status (improved / no sites / no gain / input does not compile / input not fully scored / statement










"""
    if evaluate_fn is None or statement is None or ("lint" in ops and (compile_fn is None or head_lines is None)):
        from harness.leantools import ROWS, comp
        from harness.normalize import evaluate
        from probe.verify_candidates import newest_first
        row = ROWS[name]; versions = newest_first(row["version_info"])
        evaluate_fn = evaluate_fn or (lambda d, full: evaluate(name, d, versions, full))
        compile_fn = compile_fn or (lambda d: comp(row, d, versions[0], count=False))
        statement = statement or row["statement"]
        if "lint" in ops and head_lines is None:
            head_lines, lay_opts, head_col = _probe_layout(row, versions[0])
            opts = lay_opts if opts is None else opts
            opt_key = opt_key or (row["source"], versions[0])
    opts = LINT_OPTS if opts is None else tuple(opts)
    if opt_key is not None:
        opts = tuple(o for o in opts if o not in _UNKNOWN_OPTS.get(opt_key, ()))
    decl = decl.rstrip(); body0 = split_declaration(decl, statement)
    if body0 is None:
        return {"problem": name, "status": "statement differs", "compiles": 0}
    head = decl[:len(decl) - len(body0)]; n = [0]

    def ev(d: str, full: bool) -> dict:
        n[0] += 1
        return evaluate_fn(d, full) or {}
    stored = base if (base and base.get("ok") and base.get("score") is not None and base.get("Z") is not None) else None
    first = search_dels(body0) if "delsearch" in ops else []
    res = {"problem": name, "candidates": {"delsearch": len(first)}, "applied": {}, "compiles": 0, "stopped": None}
    if stored is not None:
        res["stored"] = _pick(stored)
    if "lint" not in ops and not first:
        res.update(status="no sites", before=_pick(stored) if stored else None, proof=decl); res["after"] = res["before"]; return res
    if stored is not None:                                                                                 
        fresh = ev(decl, False); b0 = dict(fresh)
        if fresh.get("ok"):
            Z0 = float(stored["Z"]); b0.update(Z=Z0, score=round(prov(fresh) - (100.0 - Z0) / 3, 2))
            floor = max(float(stored["score"]), b0["score"])
    else:
        b0 = ev(decl, True)
    res["before"] = _pick(b0); res["compiles"] = n[0]
    if not b0.get("ok"):
        res.update(status="input does not compile", after=res["before"], proof=decl); return res
    if b0.get("score") is None or b0.get("Z") is None:
        res.update(status="input not fully scored", after=res["before"], proof=decl); return res
    if stored is None:
        Z0 = float(b0["Z"]); floor = float(b0["score"])
    cur, cur_p = body0, prov(b0); cache: dict = {}; fcache: dict = {}; failed: set = set(); steps: list = []; offered = len(first)
    why_none = "no deletion raised the score"

    def trial(b: str) -> dict:
        if b not in cache:
            cache[b] = ev(head + b, False)
        return cache[b]

    def full(b: str) -> dict:
        if b not in fcache:
            fcache[b] = ev(head + b, True)
        return fcache[b]

    def z_of(e: dict):
        return None if e.get("Z") is None else float(e["Z"])

    def pins_ok(e: dict) -> bool:
        return bool(e.get("ok")) and z_of(e) is not None and z_of(e) >= Z0 - EPS

    def full_ok(e: dict) -> bool:
        return pins_ok(e) and e.get("score") is not None and float(e["score"]) > floor + min_gain

    def stop_reason():
        if n[0] >= max_compiles - 1:
            return "max-compiles"
        if deadline is not None and clock() >= deadline:
            return "deadline"
        return None

    def pays(e: dict, p0: float) -> bool:
        return bool(e.get("ok")) and prov(e) > p0 + min_gain
    if "lint" in ops:
        lint = {"probe": "skipped"}
        if stop_reason() is None:
            def cfn(text: str):
                n[0] += 1
                return compile_fn(text)
            unknown: set = set()
            r, pre = lint_probe(decl, cfn, opts, lambda: stop_reason() is None, unknown)
            if opt_key is not None and unknown:
                _UNKNOWN_OPTS.setdefault(opt_key, set()).update(unknown)
            if r is None:
                lint["probe"] = "failed"; why_none = "lint probe failed; no deletion raised the score"
            else:
                lint["probe"] = "ok" if pre else "plain"
                dels, cnt = lint_dels(body0, len(head), len(pre), pre + decl, getattr(r, "messages", []), head_lines or 0, head_col)
                lint.update(cnt); offered += len(dels)
                chosen: list = []; p_start = cur_p
                txt, kept = render_kept(body0, dels)
                if len(kept) >= 2 and stop_reason() is None and pays(trial(txt), cur_p):
                    chosen, cur_p = kept, prov(trial(txt))
                    for d in [x for x in kept if x.kind == "arg" and x.note.lstrip().startswith(("←", "<-", "-"))]:
                        if len(chosen) < 2 or stop_reason():
                            break
                        txt2, kept2 = render_kept(body0, [x for x in chosen if x != d])
                        if pays(trial(txt2), cur_p):                                                                         
                            chosen, cur_p = kept2, prov(trial(txt2)); failed.add(d.key)
                if not chosen:
                    p0 = cur_p
                    for d in dels:
                        txt, kept = render_kept(body0, chosen + [d])
                        if d not in kept:                                                                          
                            failed.add(d.key); continue
                        why = stop_reason()
                        if why:
                            res["stopped"] = why; break
                        e = trial(txt)
                        if pays(e, p0):
                            chosen = kept; p0 = prov(e)
                        else:
                            failed.add(d.key)
                    cur_p = p0
                if chosen:
                    cur = render(body0, chosen); steps.append(("lint", cur, [d.kind for d in chosen], [d.note for d in chosen]))
                    if "delsearch" in ops and stop_reason() is None and any(d.key not in failed for d in search_dels(cur)):
                        if pins_ok(full(cur)):
                            lint["pins"] = "ok"
                        else:                                                                                                  
                            lint["pins"] = "broke"; steps.pop(); cur, cur_p = body0, p_start
                            why_none = "lint deletions broke a pin; no other deletion raised the score"
                            if len(chosen) == 1:
                                failed.add(chosen[0].key)
        else:
            res["stopped"] = stop_reason()
        res["lint"] = lint
    if "delsearch" in ops and not res["stopped"]:                                                                              
        while True:
            promoted = False
            for d in search_dels(cur):
                if d.key in failed:
                    continue
                why = stop_reason()
                if why:
                    res["stopped"] = why; break
                b = render(cur, [d]); e = trial(b)
                if pays(e, cur_p):
                    cur, cur_p, promoted = b, prov(e), True
                    steps.append(("delsearch", b, [d.kind], [d.note])); break
                failed.add(d.key)
            if not promoted or res["stopped"]:
                break
    res["compiles"] = n[0]
    if not steps:
        if not offered and res.get("lint", {}).get("probe") in (None, "ok", "plain"):
            res.update(status="no sites", after=res["before"], proof=decl); return res
        res.update(status="no gain", reason=why_none, after=res["before"], proof=decl); return res
    k_ok = len(steps); fin = full(steps[-1][1])
    if not full_ok(fin):                                                                                                                    
        k_ok = 0; lo, hi = 1, len(steps) - 1; best_e = None
        while lo <= hi:
            mid = (lo + hi) // 2
            if steps[mid - 1][1] not in fcache and (n[0] >= max_compiles or (deadline is not None and clock() >= deadline)):
                res["stopped"] = res["stopped"] or ("max-compiles" if n[0] >= max_compiles else "deadline"); break
            e = full(steps[mid - 1][1])
            if full_ok(e):
                k_ok, best_e, lo = mid, e, mid + 1
            elif pins_ok(e):
                lo = mid + 1                                                     
            else:
                hi = mid - 1
        if k_ok:
            fin = best_e
    res["compiles"] = n[0]
    if not k_ok:
        why = ("final check does not compile" if not fin.get("ok") else "final check reported no Z" if z_of(fin) is None else
               "pins broke" if z_of(fin) < Z0 - EPS else "not strictly better on the full check")
        res.update(status="no gain", reason=why, after=res["before"], tried=_pick(fin), proof=decl); return res
    deleted = []
    for op, _b, kinds, notes in steps[:k_ok]:
        for kd in kinds:
            res["applied"][f"{op}-{kd}"] = res["applied"].get(f"{op}-{kd}", 0) + 1
        deleted += [f"{op}: {x}" for x in notes]
    proof = head + steps[k_ok - 1][1]
    res.update(status="improved", after=_pick(fin), gain=round(float(fin["score"]) - float(b0["score"]), 2), proof=proof, deleted=deleted,
               dtok=count_tokens(steps[k_ok - 1][1]) - count_tokens(body0))
    if k_ok < len(steps):
        res["steps_dropped"] = len(steps) - k_ok
    if stored is not None:
        res["gain_vs_stored"] = round(float(fin["score"]) - float(stored["score"]), 2)
    return res


                                                                                                                                           
def _bank(w: Path, name: str, proof: str, run_id: str, kind: str = "closed-dev-only", lock_wait: float = 1700.0) -> dict:
    from harness.inrun import locked_check
    return locked_check(w, name, proof, {"kind": kind, "model": "lint-delete@cpu", "run_id": run_id, "mode": "lint-delete"},
                        ROOT / "probe/runs" / run_id / "verified.jsonl", lock_wait=lock_wait)


def _stored_score(st: Path, fallback) -> float:
    try:
        return float(json.loads(st.read_text())["best"]["score"])
    except Exception:                
        return float(fallback or 0)


def delete_work_root(work_root: Path, run_id: str, problems=None, deadline_s: float = 3000.0, max_compiles: int = MAX_COMPILES, ops=OPS,
                     delete_fn=None, check_fn=None, clock=time.monotonic, kind: str = "closed-dev-only", min_gain: float = MIN_GAIN) -> dict:
    """Every stored best of a line through the deletion pass; a strictly better proof is banked through the normal check path as run

"""
    if not valid_run_id(run_id):
        raise ValueError("run id: letters, digits, '.', '_', '-' only, no '..'")
    if kind not in KINDS:
        raise ValueError(f"kind must be one of {KINDS}")
    from harness.leantools import ROWS
    t0 = clock(); dl = t0 + deadline_s
    delete_fn = delete_fn or delete_proof
    check_fn = check_fn or (lambda w, name, proof: _bank(w, name, proof, run_id, kind=kind, lock_wait=max(60.0, dl - clock())))
    c = {"problems": 0, "improved": 0, "banked": 0, "gain": 0.0, "compiles": 0, "skipped_deadline": 0, "errors": 0, "bank_errors": 0,
         "rows": []}
    k = 0
    for st in sorted(Path(work_root).glob("*/state.json")):
        try:
            s = json.loads(st.read_text())
        except (OSError, ValueError):
            continue
        name = s.get("problem"); b = s.get("best") or {}
        if (problems and name not in problems) or not b.get("proof") or name not in ROWS:
            continue
        k += 1
        if clock() >= dl:
            c["skipped_deadline"] += 1; c["rows"].append({"row": k, "status": "skipped (deadline)"}); continue
        base = ({"ok": True, "score": b["score"], "Z": b["Z"], "L": b.get("L"), "H": b.get("H"), "tokens": b.get("tokens"), "heartbeats": b.get("heartbeats")}
                if b.get("Z") is not None and b.get("score") is not None else None)
        try:
            r = delete_fn(name, b["proof"], base=base, max_compiles=max_compiles, ops=ops, deadline=dl, min_gain=min_gain)
        except Exception as ex:                                                                                                      
            c["errors"] += 1; c["rows"].append({"row": k, "status": f"error {type(ex).__name__}"}); continue
        c["problems"] += 1; c["compiles"] += r.get("compiles") or 0
        row = {"row": k, "status": r.get("status"), "compiles": r.get("compiles"), "applied": r.get("applied") or {}, "banked": False}
        if r.get("status") == "improved":
            c["improved"] += 1
            prev = _stored_score(st, b.get("score"))                                                                     
            try:
                chk = check_fn(st.parent, name, r["proof"]) or {}
            except Exception as ex:                                                                                        
                c["bank_errors"] += 1; row["status"] = f"bank error {type(ex).__name__}"; c["rows"].append(row); continue
            if chk.get("new_best"):
                g = float(chk.get("score") or 0) - prev
                c["banked"] += 1; c["gain"] += g; row.update(banked=True, gain=round(g, 2))
        c["rows"].append(row)
    c["gain"] = round(c["gain"], 2)
    return c


def _ops_arg(s: str | None) -> tuple:
    if not s:
        return OPS
    got = tuple(o.strip() for o in s.split(",") if o.strip())
    bad = [o for o in got if o not in OPS]
    if bad:
        raise SystemExit(f"unknown operator(s) {bad}; known: {','.join(OPS)}")
    return tuple(o for o in OPS if o in got)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem"); ap.add_argument("--file"); ap.add_argument("--out")
    ap.add_argument("--work-root", help="a line's work root (relative to the checkout, or absolute): every stored best")
    ap.add_argument("--run-id", help="with --work-root: the run id its banked records go under")
    ap.add_argument("--problems", nargs="*", default=None); ap.add_argument("--deadline-s", type=float, default=3000.0)
    ap.add_argument("--max-compiles", type=int, default=MAX_COMPILES)
    ap.add_argument("--min-gain", type=float, default=MIN_GAIN, help="the score rise a deletion and the final proof must exceed (noise margin)")
    ap.add_argument("--kind", choices=KINDS, default="closed-dev-only",
                    help="provenance kind of banked records: closed-dev-only (never imported into the bank) or api-dev-only (an open / API line)")
    ap.add_argument("--ops", default=None, help=f"comma-separated subset of {','.join(OPS)}")
    a = ap.parse_args(argv)
    ops = _ops_arg(a.ops)
    if a.problem and a.file:
        r = delete_proof(a.problem, Path(a.file).read_text(), max_compiles=a.max_compiles, ops=ops, deadline=time.monotonic() + a.deadline_s,
                         min_gain=a.min_gain)
        print(json.dumps({k: v for k, v in r.items() if k != "proof"}, indent=1, ensure_ascii=False))
        if a.out and r.get("status") == "improved":
            Path(a.out).write_text(r["proof"].rstrip() + "\n")
        return 0
    if not (a.work_root and a.run_id):
        ap.error("--problem with --file, or --work-root with --run-id")
    if not valid_run_id(a.run_id):
        ap.error("--run-id: letters, digits, '.', '_', '-' only, no '..'")
    c = delete_work_root(ROOT / a.work_root, a.run_id, set(a.problems) if a.problems else None, a.deadline_s, a.max_compiles, ops,
                         kind=a.kind, min_gain=a.min_gain)
    for r in c["rows"]:
        ap_s = ",".join(f"{k}:{v}" for k, v in sorted((r.get("applied") or {}).items()))
        print(f"row#{r['row']} {r['status']}" + (f" compiles {r['compiles']}" if r.get("compiles") is not None else "")
              + (f" applied {ap_s}" if ap_s else "") + (f" banked {r['gain']:+.2f}" if r.get("banked") else ""))
    print(f"lint_delete: {c['problems']} stored best(s) searched, {c['improved']} strictly better, {c['banked']} banked as new bests "
          f"(summed gain {c['gain']:+.2f}), {c['compiles']} compiles, {c['skipped_deadline']} left for the deadline, {c['errors']} errors, "
          f"{c['bank_errors']} bank errors; run {a.run_id}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
