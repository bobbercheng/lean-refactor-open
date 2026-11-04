#!/usr/bin/env python3
"""Heartbeat micro-normalizer (docs/competitor_rma.md, 'Measured heartbeat techniques' and the $0 plan; 2026-10-13): a deterministic, model-free

































"""
from __future__ import annotations

import argparse, json, re, sys, time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs, apply, OPEN, CLOSE              
from harness.hb_polish import prov, _pick              
from scorer.tokenize import count_tokens, split_declaration              

OPS = ("repeatrw", "rw2rewrite", "simponly2dsimp", "simprw2only", "withreducible", "exists2refine", "use2refine")                   
                                                                                                                                         
                                                                                                                                            
TOKEN_OPS = ("nilarg", "anyiftry", "anonhave", "case2bullet", "bulletdrop", "exact2assumption", "intromerge", "nthrw")
                                                                                                                                             
B_OPS = ("specialize", "firstorder")
                                                                                                                                        
                                                                                                                     
C_OPS = ("simpmerge", "rwsimpfold", "simpafold")
                                                                                                                                             
                                                                                                                                    
                                                                                                                    
V_OPS = ("lemmavariant",)
_CTX: dict = {}                                                                                                  
VARIANT_CAP = 6                                         
VARIANT_SITES = 40                                                                              
                                                                                                                                             
                                                                     
                                                                                                                                          
                                                                                          
D_OPS = ("preorder", "clearhyp")
ALL_OPS = OPS + B_OPS + V_OPS + C_OPS + D_OPS + TOKEN_OPS
                                                                                                                                             
                                                                                                                                    
DEFAULT_OPS = OPS + B_OPS + TOKEN_OPS
TOKEN_ONLY = ("nilarg", "anyiftry", "anonhave", "case2bullet", "bulletdrop", "exact2assumption", "intromerge",
              "simpmerge", "rwsimpfold", "simpafold")                                   
MONOTONE = ("rw2rewrite",)                                                                                             
MAX_COMPILES = 24
MIN_GAIN = 0.05                                                                                               
EPS = 1e-9
KINDS = ("closed-dev-only", "api-dev-only")
RUN_ID_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")

                                                           
TAC_PREV_SYMS = {"\n", "<;>", "<|>", "=>", "·", ";", "|", "(", "{", "focus."}
TAC_PREV_WORDS = {"by", "all_goals", "any_goals", "try", "repeat", "repeat'", "iterate", "focus", "with_reducible",
                  "with_reducible_and_instances", "with_unfolding_all", "then", "else", "classical"}
LOC_RE = re.compile(r"[ \t]+at(?:[ \t]+(?:⊢|\*|[^\s;()<|\[\]⟨⟩{},]+))+")
CFG_RE = re.compile(r"\(\s*[A-Za-z_]+\s*:=")


def _word_re(w: str) -> re.Pattern:
    return re.compile(r"(?<![\w.'?!])" + w + r"(?![\w'?!])")


RW_RE, SIMPRW_RE, REPEAT_RE, FIRST_RE = _word_re("rw"), _word_re("simp_rw"), _word_re("repeat"), _word_re("first")
CONV_RE = re.compile(r"(?<![\w.'?!])conv(?:_lhs|_rhs)?(?![\w'?!])")
SIMPONLY_RE = re.compile(r"(?<![\w.'?!])simp[ \t]+only(?![\w'?!])")
USE_RE = re.compile(r"(?<![\w.'?!])(use|exists)(?![\w'?!])")
BY_RE = _word_re("by")
BY_END_RE = re.compile(r"(?<![\w.'?!])by$")
FUN_RE = re.compile(r"(?<![\w.'?!])(?:fun|λ)(?![\w'?!])|λ")
ARROW_HDR_RE = re.compile(r"(?:^|[\s·.;(])(?:case'?|next|on_goal)(?![\w'?!])|(?:^|\s)\|(?=\s)")
OPEN_TAIL_RE = re.compile(r"(?:(?<![\w.'?!])(?:by|fun)|=>|λ)\s*$")


@dataclass
class Site:
    op: str
    edits: tuple                                                                                  
    span: tuple                                                                                                                         
    note: str
    variant: int = 0
    dtok: int = 0                                         
    late: bool = False                                                                


                                                                                                                                           
def _ls(body: str, i: int) -> int:
    return body.rfind("\n", 0, i) + 1


def _col(body: str, i: int) -> int:
    return i - _ls(body, i)


def _indent_at(body: str, ls: int) -> int:
    k = ls
    while k < len(body) and body[k] in " \t":
        k += 1
    return k - ls


def _skip_ws(body: str, k: int, newlines: bool = True) -> int:
    while k < len(body) and (body[k] in " \t" or (newlines and body[k] == "\n")):
        k += 1
    return k


def _line_end(body: str, k: int) -> int:
    j = body.find("\n", k)
    return len(body) if j < 0 else j


def _code(body: str, mask: list, a: int, b: int) -> str:
    """The unmasked text of body[a:b] (comments and strings dropped)."""
    return "".join(ch for p, ch in enumerate(body[a:b], a) if not mask[p])


def _rest(body: str, mask: list, k: int) -> str:
    """The code (comments and their text dropped) on the rest of the line from k."""
    return "".join(ch for p, ch in enumerate(body[k:_line_end(body, k)], k) if not mask[p] or ch == '"').strip()


def _next_code_line(body: str, mask: list, k: int):
    """(line start, indent) of the first line after position k's line holding unmasked code; None at the end of the body."""
    ls = _line_end(body, k) + 1
    while ls < len(body):
        le = _line_end(body, ls)
        if any(not body[p].isspace() and not mask[p] for p in range(ls, le)):
            return ls, _indent_at(body, ls)
        ls = le + 1
    return None


def _parent_line(body: str, mask: list, ls: int):
    """Start of the nearest earlier line holding code that is less indented than the line at ls; None when there is none."""
    ind = _indent_at(body, ls); e = ls - 1
    while e >= 0:
        q = body.rfind("\n", 0, e) + 1
        if _code(body, mask, q, e).strip() and _indent_at(body, q) < ind:
            return q
        e = q - 1
    return None


def _prev_token(body: str, mask: list, i: int) -> str:
    j = i - 1
    while j >= 0 and (body[j] in " \t" or (mask[j] and body[j] != "\n")):
        j -= 1
    if j < 0 or body[j] == "\n":
        return "\n"
    ch = body[j]
    if ch.isalnum() or ch in "_'!?":
        k = j
        while k >= 0 and (body[k].isalnum() or body[k] in "_.'!?"):
            k -= 1
        w = body[k + 1:j + 1]
        if w.isdigit():                       
            return "iterate" if _prev_token(body, mask, k + 1) == "iterate" else w
        return w
    for sym in ("<;>", "<|>", "=>"):
        if body.startswith(sym, j + 1 - len(sym)):
            return sym
    if ch == "|":
        if j > 0 and body[j - 1] == "<":
            return "<|"                                       
        return "||" if j > 0 and body[j - 1] == "|" else "|"
    if ch == ".":
        return "focus." if j == 0 or body[j - 1] in " \t\n" else "."
    return ch


def _tac_pos(body: str, mask: list, i: int, first_by: int) -> bool:
    if mask[i] or first_by < 0 or i <= first_by:
        return False
    p = _prev_token(body, mask, i)
    return p in TAC_PREV_SYMS or p in TAC_PREV_WORDS


def _first_by(body: str, mask: list) -> int:
    for m in BY_RE.finditer(body):
        if not mask[m.start()]:
            return m.start()
    return -1


def _call_rules(body: str, pairs: dict, k: int, allow_cfg: bool = True):
    """From k (after a head): (config span or None, '[' index, index after its ']') or None."""
    k = _skip_ws(body, k); cfg = None
    if allow_cfg and k < len(body) and body[k] == "(" and k in pairs and CFG_RE.match(body, k):
        cfg = (k, pairs[k] + 1); k = _skip_ws(body, pairs[k] + 1)
    if k >= len(body) or body[k] != "[" or k not in pairs:
        return None
    return cfg, k, pairs[k] + 1


def _loc_end(body: str, mask: list, k: int) -> int:
    """End of an `at l ..` clause starting at k (k itself when there is none); never runs into a comment."""
    e = k
    while e < len(body) and not mask[e] and body[e] != "\n":
        e += 1
    m = LOC_RE.match(body, k, e)
    return m.end() if m else k


def _note(body: str, a: int, b: int) -> str:
    return re.sub(r"\s+", " ", body[a:b])[:48]


def _split_args(body: str, mask: list, pairs: dict, a: int, b: int) -> list[str]:
    """The depth-0 comma-separated pieces of body[a:b], each verbatim (stripped): commas in strings, comments and brackets do not split."""
    out, s, p = [], a, a
    while p < b:
        if mask[p]:
            p += 1; continue
        ch = body[p]
        if ch in OPEN and p in pairs:
            p = pairs[p] + 1; continue
        if ch == ",":
            out.append(body[s:p].strip()); s = p + 1
        p += 1
    out.append(body[s:b].strip())
    return out


def _top_seq(body: str, mask: list, pairs: dict, a: int, b: int) -> bool:
    """Does body[a:b] hold a depth-0 `;` (also `<;>`), i.e. more than one tactic?"""
    p = a
    while p < b:
        if mask[p]:
            p += 1; continue
        if body[p] in OPEN and p in pairs:
            p = pairs[p] + 1; continue
        if body[p] == ";":
            return True
        p += 1
    return False


def _args_end(body: str, mask: list, pairs: dict, k: int):
    """End of a comma-separated term list starting at k (the arguments of use / exists): the line end unless the line ends with `,`;
"""
    n, start = len(body), k
    while k < n:
        if mask[k]:
            if body[k] == '"':
                while k < n and mask[k]:
                    k += 1
                continue
            break
        ch = body[k]
        if ch in OPEN:
            if k not in pairs:
                return None
            k = pairs[k] + 1; continue
        if ch in CLOSE or ch == ";" or body.startswith("<;>", k) or body.startswith("<|>", k):
            break
        if ch == "|" and not (k > 0 and body[k - 1] in "<|") and not body.startswith("|>", k) and not body.startswith("||", k):
            break                                                                             
        if ch == "\n":
            if body[start:k].rstrip().endswith(","):
                k += 1; continue
            break
        k += 1
    while k > start and body[k - 1] in " \t\n":
        k -= 1
    return k


def _block_col(body: str, mask: list, i: int) -> int:
    """The column of the tactic block holding the tactic at i: the line's indent when only comments precede it on its line."""
    ls = _ls(body, i)
    return _indent_at(body, ls) if not _code(body, mask, ls, i).strip() else i - ls


def _is_final(body: str, mask: list, i: int, end: int) -> bool:
    """Is the tactic at [i, end) the last one of its block (nothing after it on the line but closers; next code line less indented)?"""
    r = _rest(body, mask, end)
    if r:
        return all(c in ")]}⟩ " for c in r)
    nx = _next_code_line(body, mask, end)
    return nx is None or nx[1] < _block_col(body, mask, i)


def _block_must_close(body: str, mask: list, i: int) -> bool:
    """Must the tactic block holding the tactic at i close its goals? True for a `by` block, a `·` bullet and a `=>` alternative / case;
"""
    ls = _ls(body, i)
    if _code(body, mask, ls, i).strip():
        return _prev_token(body, mask, i) in ("by", "·", "focus.", "=>")
    q = _parent_line(body, mask, ls)
    if q is None:
        return False
    pc = _code(body, mask, q, _line_end(body, q)).rstrip()
    if BY_END_RE.search(pc) or pc.endswith("=>"):
        return True
    st = q + _indent_at(body, q)
    if body[st] == "·" or (body[st] == "." and body[st + 1:st + 2] in (" ", "\t")):
        return _skip_ws(body, st + 1, newlines=False) - q == _indent_at(body, ls)                           
    return False


def _conv_arrow(body: str, mask: list, a: int, b: int):
    """Column (from a) of the `=>` of a conv header in body[a:b], or None."""
    for m in CONV_RE.finditer(body, a, b):
        if mask[m.start()]:
            continue
        j = body.find("=>", m.end(), b)
        while j >= 0 and mask[j]:
            j = body.find("=>", j + 2, b)
        if j >= 0:
            return j - a
    return None


def _in_conv(body: str, mask: list, i: int) -> bool:
    """Is the tactic at i inside a conv block (`conv ... => tac` on its line, or under a conv header line)?"""
    ls = _ls(body, i)
    if _conv_arrow(body, mask, ls, i) is not None:
        return True
    ind, q = _indent_at(body, ls), _parent_line(body, mask, ls)
    while q is not None:
        le = _line_end(body, q); pc = _code(body, mask, q, le).rstrip(); col = _conv_arrow(body, mask, q, le)
        if col is not None and (pc.endswith("=>") or ind > col):
            return True
        if BY_END_RE.search(pc):
            return False
        ind, q = _indent_at(body, q), _parent_line(body, mask, q)
    return False


def _tactic_arrow(body: str, mask: list, i: int) -> bool:
    """Is the `=>` just before i the arrow of a tactic alternative (case / next / on_goal / `| pat =>`), not of a `fun`?"""
    pre = _code(body, mask, _ls(body, i), i)
    head = pre[:pre.rfind("=>")]
    return not FUN_RE.search(head) and bool(ARROW_HDR_RE.search(head))


def _in_first(body: str, mask: list, i: int) -> bool:
    """Is the `|` just before i an alternative bar of `first` (on this line, or a bar line under a `first` line)?"""
    ls = _ls(body, i); pre = _code(body, mask, ls, i)
    if FIRST_RE.search(pre):
        return True
    if pre.strip() != "|":
        return False
    e = ls - 1
    while e >= 0:                                                        
        q = body.rfind("\n", 0, e) + 1; c = _code(body, mask, q, e).strip()
        if c and not c.startswith("|"):
            return bool(FIRST_RE.search(c))
        e = q - 1
    return False


                                                                                                                                           
def _repeatrw(body, mask, pairs, fb):
    out = []
    for m in REPEAT_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):
            continue
        k = _skip_ws(body, m.end(), newlines=False); close = None; block = False
        if k < len(body) and body[k] == "(" and k in pairs:
            close = pairs[k]; r = _skip_ws(body, k + 1)
        elif k >= len(body) or body[k] == "\n" or mask[k]:
            nx = _next_code_line(body, mask, i)
            if nx is None or nx[1] <= _col(body, i):
                continue
            r = nx[0] + nx[1]; block = True
        else:
            r = k
        mr = RW_RE.match(body, r)
        if not mr:
            continue
        got = _call_rules(body, pairs, mr.end(), allow_cfg=False)
        if not got:
            continue
        _cfg, lb, rb = got; end = _loc_end(body, mask, rb)
        if close is not None:
            if body[end:close].strip():
                continue
            span_end = close + 1
            if _rest(body, mask, span_end):
                continue
        else:
            if _rest(body, mask, end):
                continue
            span_end = end
            nx2 = _next_code_line(body, mask, end)
            if block and nx2 is not None and nx2[1] > _col(body, i):                                      
                continue
            if not block and nx2 is not None and nx2[1] >= _col(body, r):                                                           
                continue
        repl = "simp only " + body[lb:rb] + body[rb:end]
        out.append(Site("repeatrw", ((i, span_end - i, repl),), (i, span_end), _note(body, i, span_end)))
    return out


def _rw2rewrite(body, mask, pairs, fb):
    out = []
    for m in RW_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):                                          
            continue
        got = _call_rules(body, pairs, m.end())
        if not got:
            continue
        end = _loc_end(body, mask, got[2]); late = False
        if _is_final(body, mask, i, end):
            if _block_must_close(body, mask, i):                                                                                
                continue
            late = True
        out.append(Site("rw2rewrite", ((i, 2, "rewrite"),), (i, end), _note(body, i, end), late=late))
    return out


def _simponly2dsimp(body, mask, pairs, fb):
    out = []
    for m in SIMPONLY_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        k = _skip_ws(body, m.end(), newlines=False)
        end = pairs[k] + 1 if k < len(body) and body[k] == "[" and k in pairs else m.end()
        end = _loc_end(body, mask, end)
        out.append(Site("simponly2dsimp", ((i, 4, "dsimp"),), (i, end), _note(body, i, end)))
    return out


def _simprw2only(body, mask, pairs, fb):
    out = []
    for m in SIMPRW_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        got = _call_rules(body, pairs, m.end())
        if not got:
            continue
        cfg, _lb, rb = got; end = _loc_end(body, mask, rb)
        edits = ((i, 7, "simp"), (cfg[1], 0, " only")) if cfg else ((i, 7, "simp only"),)
        out.append(Site("simprw2only", edits, (i, end), _note(body, i, end)))
    return out


def _alt_end(body: str, mask: list, pairs: dict, a: int) -> int:
    """End of the `first` alternative starting at a: the next depth-0 `|` on the line, a closer, or the line end."""
    j, n = a, len(body)
    while j < n and body[j] != "\n":
        if mask[j] and body[j] != '"':
            j = _line_end(body, j) if body.startswith("--", j) else j + 1; continue
        if body[j] in OPEN and j in pairs:
            j = pairs[j] + 1; continue
        if body[j] in CLOSE or (body[j] == "|" and not body.startswith("||", j) and not body.startswith("|>", j)
                                and not body.startswith("<|", j - 1)):
            break
        j += 1
    return j


def _withreducible(body, mask, pairs, fb):
    out = []
    n = len(body)
    for m in FIRST_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        base_col = _indent_at(body, _ls(body, i)); k = m.end(); bar_col = None
        while True:
            k = _skip_ws(body, k, newlines=False)
            if k < n and (body[k] == "\n" or (mask[k] and body[k] != '"')):
                                                                                                                                       
                                                                                                          
                nx = _next_code_line(body, mask, k)
                if nx is None or body[nx[0] + nx[1]] != "|" or nx[1] < (base_col if bar_col is None else bar_col):
                    break
                k = nx[0] + nx[1]
            if k >= n or body[k] != "|" or body.startswith("||", k) or body.startswith("|>", k):
                break
            if bar_col is None:
                bar_col = _col(body, k)
            a = _skip_ws(body, k + 1, newlines=False)
            j = _alt_end(body, mask, pairs, a)
            mw = re.match(r"(apply|exact)(?![\w'?!])", body[a:a + 8])
            if mw and not mask[a] and not _top_seq(body, mask, pairs, a, j):
                cont = False
                if j >= n or body[j] == "\n":                                                                             
                    nx = _next_code_line(body, mask, a)
                    cont = nx is not None and nx[1] > bar_col and body[nx[0] + nx[1]] != "|"
                if not cont:
                    out.append(Site("withreducible", ((a, 0, "with_reducible "),), (a, a + len(mw.group(1))), _note(body, a, _line_end(body, a))))
            if j < n and body[j] in CLOSE:
                break
            k = j
    return out


def _use_exists(body, mask, pairs, fb, want):
    out = []
    for m in USE_RE.finditer(body):
        head, i = m.group(1), m.start()
        if head not in want or not _tac_pos(body, mask, i, fb):
            continue
        if m.end() >= len(body) or body[m.end()] not in " \t":
            continue
        p = _prev_token(body, mask, i)
        if p in ("(", "{") or (p == "=>" and not _tactic_arrow(body, mask, i)) or (p == "|" and not _in_first(body, mask, i)):
            continue                                                                           
        k = _skip_ws(body, m.end(), newlines=False)
        if head == "use" and re.match(r"\(\s*disch", body[k:k + 12]):
            continue
        end = _args_end(body, mask, pairs, k)
        if end is None or end <= k:
            continue
        if OPEN_TAIL_RE.search(body[k:end]):
            continue                                                        
        nxt = _skip_ws(body, end, newlines=False)
        if nxt < len(body) and body[nxt] in ")}" and p != "by":
            continue                                
        if not _rest(body, mask, end):
            nx = _next_code_line(body, mask, end)
            if nx is not None and nx[1] > _block_col(body, mask, i):
                continue                                           
        args = _split_args(body, mask, pairs, k, end)
        if not all(args):
            continue
        a = ", ".join(args); final = _is_final(body, mask, i, end); op = "use2refine" if head == "use" else "exists2refine"
        ref, ex_rfl = f"refine ⟨{a}, ?_⟩", f"exact ⟨{a}, rfl⟩"
        if head == "use":
            variants = [f"exact ⟨{a}⟩", ex_rfl, f"exists {a}", ref] if final else [ref, f"exists {a}", f"exact ⟨{a}⟩", ex_rfl]
        else:
            variants = [ex_rfl, ref] if final else [ref, ex_rfl]
        for v, rep in enumerate(variants):
            out.append(Site(op, ((i, end - i, rep),), (i, end), _note(body, i, end), variant=v))
    return out


                                                                                                                                            
NIL_RE = re.compile(r"\[[ \t]*\]")
ANYTRY_RE = re.compile(r"(?<![\w.'?!])all_goals[ \t]+try[ \t]+")
HAVE_NAME_RE = re.compile(r"(?<![\w.'?!])have[ \t]+([^\W\d][\w'!?₀-₉]*)[ \t]*(?=:=|:)")
CASE_TAG_RE = re.compile(r"(?<![\w.'?!])case[ \t]+([^\W\d][\w.'!?₀-₉]*)[ \t]*=>")
EXACT_ID_RE = re.compile(r"(?<![\w.'?!])exact[ \t]+([^\W\d][\w'!?₀-₉]*)(?=[ \t]*(?:\n|$|<;>|;|\)|\]|\}))", re.M)
INTRO_LINE_RE = re.compile(r"[ \t]*intro((?:[ \t]+[^\W\d][\w'!?₀-₉]*|[ \t]+_)+)[ \t]*$")
NTHRW_RE = re.compile(r"(?<![\w.'?!])nth_rw(?![\w'?!])")
_NIL_SKIP = {"simp", "only", "simp_all", "dsimp", "rw", "rewrite", "erw", "at", "with", "using", "exact", "apply", "refine", "use", "exists",
             "show", "from", "have", "let", "fun", "λ", "by", "=>", "intro", "cases", "induction", "obtain", "rcases", "match", "if", "then", "else"}


def _nilarg(body, mask, pairs, fb):
    """`f a []` -> `f a .nil` (bounty: "h .nil instead of h []"): `[]` in argument position, after an identifier or a closing bracket."""
    out = []
    for m in NIL_RE.finditer(body):
        i = m.start()
        if mask[i] or fb < 0 or i <= fb:
            continue
        pt = _prev_token(body, mask, i)
        if not pt or pt in _NIL_SKIP or pt in TAC_PREV_SYMS or not (pt[-1].isalnum() or pt[-1] in "_'!?)]⟩"):
            continue
        out.append(Site("nilarg", ((i, m.end() - i, ".nil"),), (i, m.end()), _note(body, i, m.end())))
    return out


def _anyiftry(body, mask, pairs, fb):
    """`all_goals try T` -> `any_goals T` (bounty: "all_goals try solve_by_elim -> any_goals solve_by_elim", -1 token)."""
    out = []
    for m in ANYTRY_RE.finditer(body):
        i = m.start()
        if _tac_pos(body, mask, i, fb):
            out.append(Site("anyiftry", ((i, m.end() - i, "any_goals "),), (i, _line_end(body, i)), _note(body, i, _line_end(body, i))))
    return out


def _anonhave(body, mask, pairs, fb):
    """`have h : T := e` ... h ... -> `have : T := e` ... this ... (bounty: anonymous have, -1 token), when `this` is not used after it."""
    out = []
    for m in HAVE_NAME_RE.finditer(body):
        i = m.start(); name = m.group(1)
        if name == "this" or not _tac_pos(body, mask, i, fb):
            continue
        after = body[m.end(1):]
        if re.search(r"(?<![\w.'?!])this(?![\w'?!])", _code(body, mask, m.end(1), len(body))):
            continue
        refs = [m.end(1) + r.start() for r in re.finditer(r"(?<![\w.'?!])" + re.escape(name) + r"(?![\w'?!])", after)
                if not mask[m.end(1) + r.start()]]
        edits = [(m.start(1), m.end(1) - m.start(1) + (1 if body[m.end(1):m.end(1) + 1] in (" ", "\t") else 0), "")]
        edits += [(r, len(name), "this") for r in refs]
        out.append(Site("anonhave", tuple(edits), (i, len(body)), _note(body, i, _line_end(body, i))))
    return out


def _case2bullet(body, mask, pairs, fb):
    """`case tag => tac` -> `· tac` (bounty: "case var => contradiction -> · contradiction"): a single tag, no binders; correct when the
"""
    out = []
    for m in CASE_TAG_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        out.append(Site("case2bullet", ((i, m.end() - i, "·"),), (i, m.end()), _note(body, i, _line_end(body, i))))
    return out


def _bulletdrop(body, mask, pairs, fb):
    """Drop a focusing bullet and dedent its block (bounty: "V3 without the two focusing bullets"): `· tac` lines -> `tac` at the bullet's
"""
    out = []
    for m in re.finditer(r"(?m)^([ \t]*)·[ \t]+", body):
        i = m.start() + len(m.group(1))
        if mask[i] or fb < 0 or i <= fb:
            continue
        col = len(m.group(1)); width = m.end() - i
        edits = [(i, width, "")]
        ls = _line_end(body, i) + 1; end = _line_end(body, i)
        while ls < len(body):
            le = _line_end(body, ls)
            line = body[ls:le]
            if line.strip():
                ind = _indent_at(body, ls)
                if ind <= col:
                    break
                if ind < col + width:
                    edits = None; break                                                   
                edits.append((ls, width, ""))
            end = le; ls = le + 1
        if edits:
            out.append(Site("bulletdrop", tuple(edits), (i, end), _note(body, i, _line_end(body, i))))
    return out


def _exact2assumption(body, mask, pairs, fb):
    """`exact h` (a bare identifier) -> `assumption`; `exact rfl` -> `rfl`; `exact trivial` -> `trivial` (-1 token each)."""
    out = []
    for m in EXACT_ID_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        name = m.group(1)
        rep = name if name in ("rfl", "trivial") else "assumption"
        out.append(Site("exact2assumption", ((i, m.end() - i, rep),), (i, m.end()), _note(body, i, m.end())))
    return out


def _intromerge(body, mask, pairs, fb):
    """Consecutive `intro a` / `intro b` lines at one indent -> `intro a b` (-1 token per merge)."""
    out = []
    lines = []; ls = 0
    while ls <= len(body):
        le = _line_end(body, ls); lines.append((ls, le)); ls = le + 1
        if le >= len(body):
            break
    for (a0, a1), (b0, b1) in zip(lines, lines[1:]):
        ma, mb = INTRO_LINE_RE.fullmatch(body[a0:a1]), INTRO_LINE_RE.fullmatch(body[b0:b1])
        if not (ma and mb) or a0 <= fb or _indent_at(body, a0) != _indent_at(body, b0) or any(mask[p] for p in range(a0, b1)):
            continue
        k = b0 + _indent_at(body, b0) + len("intro")
        out.append(Site("intromerge", ((a1, k - a1, ""),), (a0, b1), _note(body, a0, b1)))
    return out


def _nthrw(body, mask, pairs, fb):
    """`nth_rw` -> `nth_rewrite` (bounty: "nth_rw -> nth_rewrite"; nth_rw tries rfl like rw), not as the last tactic of a closing block."""
    out = []
    for m in NTHRW_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        end = _line_end(body, i)
        if _is_final(body, mask, i, end) and _block_must_close(body, mask, i):
            continue
        out.append(Site("nthrw", ((i, len("nth_rw"), "nth_rewrite"),), (i, end), _note(body, i, end)))
    return out


                                                                                                                                               
                                                                                                                                             
                                                                                                                                             
                                                                                                                                      
                                                                                                                                          
                                                                                                                                             
                                                                                                                                      
                                                                                                                        
SPEC_CAP = 4
SPEC_TABLE = ROOT / "harness/tools/tables/bundled_homs.json"
TABLES = {"bundled_homs": {"rule": "bundled homs = Mathlib structures with a `map_<x>'` field; generics = root-namespace `map_*` theorems; "
                                   "S.g is a variant of g when Lean's apply of g closes S.g's conclusion on every Mathlib pin; ordered by "
                                   "S's namespace size; the specialize op uses the first SPEC_CAP variants of each generic",
                           "query": "python3 harness/tools/tables/gen_bundled_homs.py (harness/tools/tables/bundled_homs_query.lean)",
                           "path": "harness/tools/tables/bundled_homs.json", "ops": ("specialize",)}}


def specialize_map(table: dict, cap: int = SPEC_CAP) -> dict:
    """generic lemma -> its first cap variants, from a bundled_homs table (its "specialize" field, ordered by the table's rule)."""
    spec = table.get("specialize") if isinstance(table, dict) else None
    return {g: tuple(v[:cap]) for g, v in sorted((spec or {}).items()) if isinstance(v, list) and v}


def spec_regex(spec: dict):
    """The site pattern of a specialize map: any of its generics as a whole identifier (longest first); None for an empty map."""
    if not spec:
        return None
    return re.compile(r"(?<![\w.'?!])(" + "|".join(re.escape(k) for k in sorted(spec, key=len, reverse=True)) + r")(?![\w'?!])")


def _load_table(path: Path) -> dict:
    """The table at path, or {} with a warning on stderr (R2 review 2026-10-22: a missing table must not pass silently; harness/sweep
"""
    try:
        return json.loads(Path(path).read_text())
    except (OSError, ValueError) as e:
        print(f"[hb_rewrite] WARNING: table {path} unreadable ({type(e).__name__}); its ops propose nothing", file=sys.stderr, flush=True)
        return {}


SPECIALIZE = specialize_map(_load_table(SPEC_TABLE))
SPEC_RE = spec_regex(SPECIALIZE)
FIRST_RE = re.compile(r"(?<![\w.'?!])first(?![\w'?!])")


def _specialize(body, mask, pairs, fb):
    """A generic lemma name -> each of its specialized variants (one Site per variant; variants of one name share its span)."""
    out = []
    if SPEC_RE is None:
        return out
    for m in SPEC_RE.finditer(body):
        i = m.start()
        if mask[i] or fb < 0 or i <= fb:
            continue
        for v, rep in enumerate(SPECIALIZE[m.group(1)]):
            out.append(Site("specialize", ((i, m.end() - i, rep),), (i, m.end()), f"{m.group(1)} -> {rep}", variant=v))
    return out


def _first_alts(body: str, mask: list, pairs: dict, k: int):
    """[(start, end)] of the depth-0 `|` alternatives of a one-line `first | A | B ...` whose `|` starts at k; None when not one line or
"""
    end = _line_end(body, k); alts = []; a = None; d = 0; j = k
    while j < end:
        c = body[j]
        if mask[j]:
            j += 1; continue
        if c in "([{⟨":
            d += 1
        elif c in ")]}⟩":
            d -= 1
            if d < 0:
                end = j; break
        elif d == 0 and c == "|" and body[j - 1:j] not in ("<", "|") and body[j + 1:j + 2] not in ("|", ">"):
            if a is not None:
                alts.append((a, j))
            a = j + 1
        elif d == 0 and body.startswith("<;>", j):
            return None
        j += 1
    if a is not None:
        alts.append((a, end))
    alts = [(x, y) for x, y in alts if body[x:y].strip()]
    return alts if len(alts) >= 2 else None


def _firstorder(body, mask, pairs, fb):
    """`first | A | B | C` -> each other alternative moved to the front (the one that usually succeeds first: no failed attempts)."""
    out = []
    for m in FIRST_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        k = _skip_ws(body, m.end(), newlines=False)
        if k >= len(body) or body[k] != "|":
            continue
        alts = _first_alts(body, mask, pairs, k)
        if not alts:
            continue
        texts = [body[x:y].strip() for x, y in alts]
        a0, a1 = alts[0][0], alts[-1][1]
        for v in range(1, len(texts)):
            order = [texts[v]] + texts[:v] + texts[v + 1:]
            rep = " " + " | ".join(order) + (" " if body[a1 - 1:a1] == " " else "")
            out.append(Site("firstorder", ((a0, a1 - a0, rep),), (i, a1), f"first: alternative {v + 1} first", variant=v - 1))
    return out


SIMPFAM_RE = re.compile(r"(?<![\w.'?!])(simp_all|simp|dsimp)(?:[ \t]+(only))?(?![\w'?!])")
RWHEAD_RE = re.compile(r"(?<![\w.'?!])(rw|rewrite)(?![\w'?!])")


def _line_call(body, mask, pairs, fb, i, head_re):
    """A call matched by head_re at i that starts its line (only indentation before it), has no config / discharger, and is the only code
"""
    m = head_re.match(body, i)
    if not m or mask[i] or not _tac_pos(body, mask, i, fb) or _code(body, mask, _ls(body, i), i).strip():
        return None
    k = _skip_ws(body, m.end(), newlines=False); items = []; e = m.end()
    if k < len(body) and body[k] == "[" and k in pairs:
        items = [x for x in _split_args(body, mask, pairs, k + 1, pairs[k]) if x]; e = pairs[k] + 1
    elif k < len(body) and body[k] == "(":
        return None
    le = _loc_end(body, mask, e)
    if _rest(body, mask, le):
        return None
    return {"head": m.group(1), "only": bool(m.lastindex and m.lastindex >= 2 and m.group(2)), "items": items,
            "loc": re.sub(r"\s+", " ", body[e:le]).strip(), "start": i, "end": le, "indent": _col(body, i)}


def _next_call(body, mask, pairs, fb, c, head_re):
    """The call right after call c in the same block (next code line at the same indent), parsed with head_re, or None."""
    nx = _next_code_line(body, mask, c["end"])
    if nx is None or nx[1] != c["indent"]:
        return None
    return _line_call(body, mask, pairs, fb, nx[0] + nx[1], head_re)


def _render(head, only, items, loc):
    return head + (" only" if only else "") + (f" [{', '.join(items)}]" if items else "") + (f" {loc}" if loc else "")


def _simpmerge(body, mask, pairs, fb):
    """Two adjacent simp-family calls on the same location -> one call with both lists (bounty: "W1 crAnTimeOrderList into first simp",
"""
    out = []
    for m in SIMPFAM_RE.finditer(body):
        a = _line_call(body, mask, pairs, fb, m.start(), SIMPFAM_RE)
        if not a:
            continue
        b = _next_call(body, mask, pairs, fb, a, SIMPFAM_RE)
        if not b or a["loc"] != b["loc"]:
            continue
        items = a["items"] + [x for x in b["items"] if x not in a["items"]]
        heads = [(b["head"], b["only"]), (a["head"], a["only"])]
        for v, (h, o) in enumerate(dict.fromkeys(heads)):
            if h == "dsimp" and "simp" in (a["head"], b["head"]) and (a["head"], b["head"]) != ("dsimp", "dsimp"):
                continue                                                                          
            rep = _render(h, o, items, a["loc"])
            out.append(Site("simpmerge", ((a["start"], b["end"] - a["start"], rep),), (a["start"], b["end"]), _note(body, a["start"], b["end"]), variant=v))
    return out


def _rwsimpfold(body, mask, pairs, fb):
    """`rw [R]` + the next simp-family call on the same location -> that call with R in front of its list (bounty: "fold hg in the big
"""
    out = []
    for m in RWHEAD_RE.finditer(body):
        a = _line_call(body, mask, pairs, fb, m.start(), RWHEAD_RE)
        if not a or not a["items"]:
            continue
        b = _next_call(body, mask, pairs, fb, a, SIMPFAM_RE)
        if not b or a["loc"] != b["loc"] or b["head"] == "dsimp":
            continue
        rep = _render(b["head"], b["only"], a["items"] + [x for x in b["items"] if x not in a["items"]], b["loc"])
        out.append(Site("rwsimpfold", ((a["start"], b["end"] - a["start"], rep),), (a["start"], b["end"]), _note(body, a["start"], b["end"])))
    return out


EXACT_LINE_RE = re.compile(r"[ \t]*exact[ \t]+([^\W\d][\w'!?₀-₉]*)[ \t]*$")


def _simpafold(body, mask, pairs, fb):
    """`simp [only] [L] at h` + `exact h` -> `simpa [only] [L] using h` (-2 tokens)."""
    out = []
    for m in SIMPFAM_RE.finditer(body):
        a = _line_call(body, mask, pairs, fb, m.start(), SIMPFAM_RE)
        if not a or a["head"] != "simp" or not re.fullmatch(r"at [^\W\d][\w'!?₀-₉]*", a["loc"]):
            continue
        h = a["loc"][3:]
        nx = _next_code_line(body, mask, a["end"])
        if nx is None or nx[1] != a["indent"]:
            continue
        le = _line_end(body, nx[0]); mm = EXACT_LINE_RE.fullmatch(body[nx[0]:le])
        if not mm or mm.group(1) != h:
            continue
        rep = _render("simpa", a["only"], a["items"], "") + f" using {h}"
        out.append(Site("simpafold", ((a["start"], le - a["start"], rep),), (a["start"], le), _note(body, a["start"], le)))
    return out


_TACTIC_WORDS = set("""apply exact refine intro intros introv rintro obtain cases rcases induction simp simp_all dsimp rw rewrite erw nth_rewrite
nth_rw show from have let calc constructor econstructor use exists assumption contradiction exfalso trivial decide norm_num ring ring_nf field_simp
linarith nlinarith positivity omega grind aesop tauto unfold delta congr ext funext gcongr rotate_left rotate_right iterate repeat first try
all_goals any_goals case next fun by at with using only generalizing specialize subst injection clear rename_i exact_mod_cast push_cast""".split())
IDENT_RE = re.compile(r"(?<![\w.'!?])((?:[^\W\d][\w'!?₀-₉ₛₗ]*\.)*[^\W\d][\w'!?₀-₉ₛₗ]*)")


def _row():
    """The row of _CTX: its "row" object when the caller passes one (the open-track family adapter harness/tools/hr_variant.py), else
"""
    if isinstance(_CTX.get("row"), dict):
        return _CTX["row"]
    name = _CTX.get("name")
    if not name:
        return None
    from harness.leantools import ROWS
    return ROWS.get(name)


def _env_index():
    row = _row()
    if not row:
        return None
    from harness.leantools import _name_index
    from scorer.compile import project_env_dir, env_dir
    from probe.verify_candidates import newest_first
    primary = newest_first(row["version_info"])[0]
    root = env_dir(primary) if row["source"] == "putnambench" else project_env_dir(row["source"], primary)
    return _name_index(root)


def _lemmavariant(body, mask, pairs, fb):
    """Every global lemma name in the proof -> up to VARIANT_CAP variants from the row's environment: the same final name in another

"""
    idx = _env_index()
    if not idx:
        return []
    from harness.lemma_search import bound_names
    from harness.architect import _KW
    row = _row()
    stmt = row["statement"] if row else ""
    local = bound_names(stmt + "\n" + body) | {"this", "h", "rfl", "trivial"} | _KW | _TACTIC_WORDS
    occ = []
    for m in IDENT_RE.finditer(body):
        i = m.start(); w = m.group(1)
        if mask[i] or fb < 0 or i <= fb or w.split(".")[0] in local or w in TAC_PREV_WORDS:
            continue
        seg = w.split(".")[-1]
        if seg not in idx or len(seg) < 4:
            continue
        occ.append((i, w, seg))
    used_ns = {w.rsplit(".", 1)[0].split(".")[-1] for _, w, _ in occ if "." in w}
    sites_out = []
    for i, w, seg in occ:
        own_ns = w.rsplit(".", 1)[0] if "." in w else ""
        forms = (seg + "_of_tower", seg + "ₛₗ", seg + "'", "fun_" + seg) + ((seg[4:],) if seg.startswith("fun_") else ())
        cands = []
        for n, _ in idx.get(seg, []):                                                                                       
            ns = n.rsplit(".", 1)[0].split(".")[-1] if "." in n else ""
            if n != w and not n.endswith("." + w) and ns in used_ns and ns != own_ns.split(".")[-1]:
                cands.append((0, len(n), n))
        for f in forms:                                                                                                          
            for n, _ in idx.get(f, []):
                ns = n.rsplit(".", 1)[0] if "." in n else ""
                if ns.split(".")[-1] == own_ns.split(".")[-1] or (not own_ns and ns.split(".")[-1] in used_ns):
                    cands.append((0, len(n), n))
        cands = sorted({c[2]: c for c in cands if not (c[2].startswith("_private") or ".proof_" in c[2])}.values())
        if not cands:
            continue
        rank = 0
        for v, (_, _, n) in enumerate(cands[:VARIANT_CAP]):
            sites_out.append((rank, i, Site("lemmavariant", ((i, len(w), n),), (i, i + len(w)), f"{w} -> {n}", variant=v)))
    sites_out.sort(key=lambda x: (x[0], x[1], x[2].variant))
    keep_spans = []
    for rank, i, st in sites_out:
        if st.span not in keep_spans:
            if len(keep_spans) >= VARIANT_SITES:
                continue
            keep_spans.append(st.span)
    return [st for rank, i, st in sites_out if st.span in keep_spans]



                                                                                                                                              
SIMPCALL_RE = re.compile(r"(?<![\w.'?!])(simp_all|simp|dsimp|simpa|simp_arith)(?![\w'?!])")
PREORDER_CAP = 8                                                                                               
PREORDER_HINT = re.compile(r"map_|forall|exists|funext|_apply\b|_comp\b|fun_|_sum\b|sum_|_cons\b")


def _arg_spans(body: str, mask: list, pairs: dict, a: int, b: int) -> list[tuple]:
    """(start, end) of each depth-0 comma-separated piece of body[a:b], whitespace trimmed."""
    out, s, p = [], a, a
    def trim(x, y):
        while x < y and body[x].isspace(): x += 1
        while y > x and body[y - 1].isspace(): y -= 1
        return x, y
    while p < b:
        if mask[p]:
            p += 1; continue
        if body[p] in OPEN and p in pairs:
            p = pairs[p] + 1; continue
        if body[p] == ",":
            out.append(trim(s, p)); s = p + 1
        p += 1
    out.append(trim(s, b))
    return [(x, y) for x, y in out if y > x]


def _preorder(body, mask, pairs, fb):
    """A simp argument -> its pre-order form `↓arg` (rewrite a parent before descent destroys its pattern: Wick `↓List.forall_mem_cons`,

"""
    out = []
    for m in SIMPCALL_RE.finditer(body):
        i = m.start()
        if mask[i] or not _tac_pos(body, mask, i, fb):
            continue
        k = _skip_ws(body, m.end(), newlines=False)
        if k < len(body) and body[k] == "(" and k in pairs and CFG_RE.match(body, k):
            k = _skip_ws(body, pairs[k] + 1, newlines=False)
        if body.startswith("only", k) and not re.match(r"[\w'?!]", body[k + 4:k + 5] or " "):
            k = _skip_ws(body, k + 4, newlines=False)
        if k >= len(body) or body[k] != "[" or k not in pairs:
            continue
        spans = [(x, y) for x, y in _arg_spans(body, mask, pairs, k + 1, pairs[k]) if body[x] not in "↓↑-*" and not body.startswith("<-", x)]
        def prio(sp):
            t = body[sp[0]:sp[1]].lstrip("← ")
            return (0 if re.fullmatch(r"[hH][\w'₀-₉]*", t) else 1 if PREORDER_HINT.search(t) else 2, sp[0])
        for v, (x, y) in enumerate(sorted(spans, key=prio)[:PREORDER_CAP]):
            out.append(Site("preorder", ((x, 0, "↓"),), (x, y), "↓" + _note(body, x, y), variant=v))
    return out


AUTO_RE = re.compile(r"(?<![\w.'?!])(grind|simp_all|aesop|linarith|nlinarith|positivity|tauto|omega|norm_num|solve_by_elim|field_simp|simpa|"
                     r"polyrith|bound)(?![\w'?!])")
HYP_RE = re.compile(r"(?<![\w.'₀-₉])[hH][\w'₀-₉]*(?![\w'₀-₉])")
CLEAR_INTRO_RE = re.compile(r"\s*(?:·\s*)?(intro|intros|rintro|obtain|rcases|have|haveI|cases|induction|refine|constructor|choose|set)\b")
CLEAR_CAP = 4                                         
HYP_KEYWORDS = {"have", "haveI", "hiding", "hint", "h.1", "h.2"}


def _clearhyp(body, mask, pairs, fb):
    """`clear h` before costly automation, for a hypothesis-named binder (statement binders and names introduced earlier in an enclosing

"""
    if fb < 0:
        return []
    out = []
    hdr = body[:fb]
    stmt = []
    for m in re.finditer(r"\(([^():]+):", hdr):
        stmt += [n for n in m.group(1).split() if re.fullmatch(r"[hH][\w'₀-₉]*", n)]
    lines = body.split("\n"); starts = []; pos = 0
    for ln in lines:
        starts.append(pos); pos += len(ln) + 1
    ind = [len(ln) - len(ln.lstrip()) if ln.strip() else None for ln in lines]
    intros = []                         
    for li, ln in enumerate(lines):
        if starts[li] <= fb or ind[li] is None or not CLEAR_INTRO_RE.match(ln):
            continue
        bul = re.match(r"\s*·\s*", ln)                                                                         
        eff = bul.end() if bul else ind[li]
        for m in HYP_RE.finditer(ln):
            if m.group(0) not in HYP_KEYWORDS:
                intros.append((m.group(0), li, eff))
    for m in AUTO_RE.finditer(body):
        i = m.start()
        if mask[i] or i <= fb or not _tac_pos(body, mask, i, fb):
            continue
        li = body.count("\n", 0, i); ls = starts[li]
        if body[ls:i].strip():                                     
            continue
        d = ind[li]; later = set(HYP_RE.findall(body[i:]))
        cands = []
        for name, il, idt in reversed(intros):                      
            if il < li and idt <= d and all(ind[j] is None or ind[j] >= idt for j in range(il + 1, li + 1)) and name not in later and name not in cands:
                cands.append(name)
        cands += [n for n in stmt if n not in later and n not in cands]
        for v, name in enumerate(cands[:CLEAR_CAP]):
            out.append(Site("clearhyp", ((ls, 0, " " * d + f"clear {name}\n"),), (ls, ls), f"clear {name} before {m.group(1)}", variant=v))
    return out

_TOKEN_FINDERS = {"preorder": _preorder, "clearhyp": _clearhyp, "lemmavariant": _lemmavariant, "simpmerge": _simpmerge, "rwsimpfold": _rwsimpfold, "simpafold": _simpafold, "specialize": _specialize, "firstorder": _firstorder, "nilarg": _nilarg, "anyiftry": _anyiftry, "anonhave": _anonhave, "case2bullet": _case2bullet, "bulletdrop": _bulletdrop,
                  "exact2assumption": _exact2assumption, "intromerge": _intromerge, "nthrw": _nthrw}


def sites(body: str, ops=DEFAULT_OPS) -> list[Site]:
    """Every site of the selected operators in the proof body, ordered by operator priority, position, variant; dtok filled in."""
    mask = _mask(body); pairs = _pairs(body, mask); fb = _first_by(body, mask); out: list[Site] = []
    for op in ALL_OPS:
        if op not in ops:
            continue
        if op in _TOKEN_FINDERS: got = _TOKEN_FINDERS[op](body, mask, pairs, fb)
        elif op == "repeatrw": got = _repeatrw(body, mask, pairs, fb)
        elif op == "rw2rewrite": got = _rw2rewrite(body, mask, pairs, fb)
        elif op == "simponly2dsimp": got = _simponly2dsimp(body, mask, pairs, fb)
        elif op == "simprw2only": got = _simprw2only(body, mask, pairs, fb)
        elif op == "withreducible": got = _withreducible(body, mask, pairs, fb)
        elif op == "exists2refine": got = _use_exists(body, mask, pairs, fb, ("exists",))
        else: got = _use_exists(body, mask, pairs, fb, ("use",))
        out += sorted(got, key=lambda s: (s.span[0], s.variant))
    t0 = count_tokens(body); seen = set(); uniq = []
    for s in out:
        if s.edits in seen:
            continue
        seen.add(s.edits); s.dtok = count_tokens(apply(body, [s])) - t0
        if s.op in TOKEN_ONLY and s.dtok >= 0:                                                    
            continue
        uniq.append(s)
    return uniq


def conflicts(s: Site, kept: list[Site]) -> bool:
    a, b = s.span
    return any((a < k.span[1] and k.span[0] < b) or a == k.span[0] for k in kept)


                                                                                                                                           
def rewrite_proof(name: str, decl: str, *, base: dict | None = None, evaluate_fn=None, statement: str | None = None,
                  max_compiles: int = MAX_COMPILES, ops=DEFAULT_OPS, deadline: float | None = None, clock=time.monotonic,
                  all_at_once: bool = True, min_gain: float = MIN_GAIN) -> dict:
    """The report of one proof: status (improved / no sites / no gain / input does not compile / input not fully scored / statement



"""
    if evaluate_fn is None or statement is None:
        from harness.leantools import ROWS
        from harness.normalize import evaluate
        from probe.verify_candidates import newest_first
        row = ROWS[name]; versions = newest_first(row["version_info"])
        evaluate_fn = evaluate_fn or (lambda d, full: evaluate(name, d, versions, full))
        statement = statement or row["statement"]
    decl = decl.rstrip(); body = split_declaration(decl, statement)
    if body is None:
        return {"problem": name, "status": "statement differs", "compiles": 0}
    head = decl[:len(decl) - len(body)]; n = [0]
    _CTX["name"] = name

    def ev(d: str, full: bool) -> dict:
        n[0] += 1
        return evaluate_fn(d, full) or {}
    stored = base if (base and base.get("ok") and base.get("score") is not None and base.get("Z") is not None) else None
    ss = sites(body, ops)
    calls: dict = {}
    for s in ss:
        calls.setdefault(s.op, set()).add(s.span)
    res = {"problem": name, "sites": {op: len(v) for op, v in calls.items()}, "candidates": len(ss), "applied": {}, "compiles": 0,
           "stopped": None}
    if stored is not None:
        res["stored"] = _pick(stored)
    if not ss:
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
    kept: list[Site] = []; cur_p = prov(b0); cache: dict = {}

    def trial(chosen: list[Site]) -> dict:
        cand = head + apply(body, chosen)
        if cand not in cache:
            cache[cand] = ev(cand, False)
        return cache[cand]

    def stop_reason():
        if n[0] >= max_compiles - 1:
            return "max-compiles"
        if deadline is not None and clock() >= deadline:
            return "deadline"
        return None
    groups = [(op, [s for s in ss if s.op == op and not s.late], True) for op in ALL_OPS] + [("late", [s for s in ss if s.late], False)]
    for op, group, aao in groups:
        if not group or res["stopped"]:
            continue
        done: set = set()
        free: list[Site] = []
        for s in group:
            if not conflicts(s, kept) and not conflicts(s, free):
                free.append(s)
        if aao and all_at_once and len(free) >= 2 and n[0] + len(free) + 1 < max_compiles - 1 and stop_reason() is None:
            e = trial(kept + free)
            if e.get("ok") and prov(e) > cur_p + min_gain:
                kept += free; cur_p = prov(e); done |= {id(s) for s in free}
                if op not in MONOTONE:                                                                  
                    for s in free:
                        why = stop_reason()
                        if why:
                            res["stopped"] = why; break
                        e2 = trial([x for x in kept if x is not s])
                        if e2.get("ok") and prov(e2) >= cur_p - EPS:
                            kept = [x for x in kept if x is not s]; cur_p = prov(e2)
        for s in group:
            if res["stopped"]:
                break
            if id(s) in done or conflicts(s, kept):
                continue
            why = stop_reason()
            if why:
                res["stopped"] = why; break
            e = trial(kept + [s])
            if e.get("ok") and prov(e) > cur_p + min_gain:
                kept.append(s); cur_p = prov(e)
    res["compiles"] = n[0]
    if not kept:
        res.update(status="no gain", reason="no site raised the score", after=res["before"], proof=decl); return res

    def z_of(e: dict):
        return None if e.get("Z") is None else float(e["Z"])

    def full_ok(e: dict) -> bool:
        return (bool(e.get("ok")) and z_of(e) is not None and z_of(e) >= Z0 - EPS and e.get("score") is not None
                and float(e["score"]) > floor + min_gain)
    fin = ev(head + apply(body, kept), True)
    if fin.get("ok") and z_of(fin) is not None and z_of(fin) < Z0 - EPS:                                                     
        for op in [o for o in OPS if any(s.op == o for s in kept)]:
            if n[0] >= max_compiles or (deadline is not None and clock() >= deadline):
                res["stopped"] = res["stopped"] or ("max-compiles" if n[0] >= max_compiles else "deadline"); break
            trial_k = [s for s in kept if s.op != op]
            if not trial_k:
                continue
            e = ev(head + apply(body, trial_k), True)
            if full_ok(e):
                kept, fin = trial_k, e; break
    res["compiles"] = n[0]
    if not full_ok(fin):
        why = ("final check does not compile" if not fin.get("ok") else "final check reported no Z" if z_of(fin) is None else
               "pins broke" if z_of(fin) < Z0 - EPS else "not strictly better on the full check")
        res.update(status="no gain", reason=why, after=res["before"], tried=_pick(fin), proof=decl); return res
    for s in kept:
        res["applied"][s.op] = res["applied"].get(s.op, 0) + 1
    res.update(status="improved", after=_pick(fin), gain=round(float(fin["score"]) - float(b0["score"]), 2), proof=head + apply(body, kept),
               kept=[{"op": s.op, "note": s.note, "dtok": s.dtok} for s in kept])
    if stored is not None:
        res["gain_vs_stored"] = round(float(fin["score"]) - float(stored["score"]), 2)
    return res


                                                                                                                                           
def valid_run_id(run_id) -> bool:
    return isinstance(run_id, str) and bool(RUN_ID_RE.fullmatch(run_id)) and ".." not in run_id


def _bank(w: Path, name: str, proof: str, run_id: str, kind: str = "closed-dev-only", lock_wait: float = 1700.0) -> dict:
    from harness.inrun import locked_check
    return locked_check(w, name, proof, {"kind": kind, "model": "hb-rewrite@cpu", "run_id": run_id, "mode": "hb-rewrite"},
                        ROOT / "probe/runs" / run_id / "verified.jsonl", lock_wait=lock_wait)


def _stored_score(st: Path, fallback) -> float:
    try:
        return float(json.loads(st.read_text())["best"]["score"])
    except Exception:                
        return float(fallback or 0)


def rewrite_work_root(work_root: Path, run_id: str, problems=None, deadline_s: float = 3000.0, max_compiles: int = MAX_COMPILES, ops=DEFAULT_OPS,
                      rewrite_fn=None, check_fn=None, clock=time.monotonic, kind: str = "closed-dev-only", min_gain: float = MIN_GAIN) -> dict:
    """Every stored best of a line rewritten; a strictly better proof is banked through the normal check path as run `run_id`. Stops

"""
    if not valid_run_id(run_id):
        raise ValueError("run id: letters, digits, '.', '_', '-' only, no '..'")
    if kind not in KINDS:
        raise ValueError(f"kind must be one of {KINDS}")
    from harness.leantools import ROWS
    t0 = clock(); dl = t0 + deadline_s
    rewrite_fn = rewrite_fn or rewrite_proof
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
            r = rewrite_fn(name, b["proof"], base=base, max_compiles=max_compiles, ops=ops, deadline=dl, min_gain=min_gain)
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
        return DEFAULT_OPS
    got: tuple = ()
    for o in (o.strip() for o in s.split(",") if o.strip()):
        got += (TOKEN_OPS if o == "tokens" else B_OPS if o == "b" else C_OPS if o == "c" else D_OPS if o == "d" else V_OPS if o == "v" else ALL_OPS if o == "all" else OPS if o == "classic"
                else DEFAULT_OPS if o == "default" else (o,))
    bad = [o for o in got if o not in ALL_OPS]
    if bad:
        raise SystemExit(f"unknown operator(s) {bad}; known: {','.join(ALL_OPS)} (aliases: tokens, b, c, d, v, all, classic, default)")
    return tuple(dict.fromkeys(got))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem"); ap.add_argument("--file"); ap.add_argument("--out")
    ap.add_argument("--work-root", help="a line's work root (relative to the checkout, or absolute): rewrite every stored best")
    ap.add_argument("--run-id", help="with --work-root: the run id its banked records go under")
    ap.add_argument("--problems", nargs="*", default=None); ap.add_argument("--deadline-s", type=float, default=3000.0)
    ap.add_argument("--max-compiles", type=int, default=MAX_COMPILES)
    ap.add_argument("--min-gain", type=float, default=MIN_GAIN, help="the score rise a site and the final proof must exceed (noise margin)")
    ap.add_argument("--kind", choices=KINDS, default="closed-dev-only",
                    help="provenance kind of banked records: closed-dev-only (never imported into the bank) or api-dev-only (an open / API line)")
    ap.add_argument("--ops", default=None, help=f"comma-separated subset of {','.join(OPS)}")
    a = ap.parse_args(argv)
    ops = _ops_arg(a.ops)
    if a.problem and a.file:
        r = rewrite_proof(a.problem, Path(a.file).read_text(), max_compiles=a.max_compiles, ops=ops, deadline=time.monotonic() + a.deadline_s,
                          min_gain=a.min_gain)
        print(json.dumps({k: v for k, v in r.items() if k != "proof"}, indent=1, ensure_ascii=False))
        if a.out and r.get("status") == "improved":
            Path(a.out).write_text(r["proof"].rstrip() + "\n")
        return 0
    if not (a.work_root and a.run_id):
        ap.error("--problem with --file, or --work-root with --run-id")
    if not valid_run_id(a.run_id):
        ap.error("--run-id: letters, digits, '.', '_', '-' only, no '..'")
    c = rewrite_work_root(ROOT / a.work_root, a.run_id, set(a.problems) if a.problems else None, a.deadline_s, a.max_compiles, ops,
                          kind=a.kind, min_gain=a.min_gain)
    for r in c["rows"]:
        ap_s = ",".join(f"{k}:{v}" for k, v in sorted((r.get("applied") or {}).items()))
        print(f"row#{r['row']} {r['status']}" + (f" compiles {r['compiles']}" if r.get("compiles") is not None else "")
              + (f" applied {ap_s}" if ap_s else "") + (f" banked {r['gain']:+.2f}" if r.get("banked") else ""))
    print(f"hb_rewrite: {c['problems']} stored best(s) rewritten, {c['improved']} strictly better, {c['banked']} banked as new bests "
          f"(summed gain {c['gain']:+.2f}), {c['compiles']} compiles, {c['skipped_deadline']} left for the deadline, {c['errors']} errors, "
          f"{c['bank_errors']} bank errors; run {a.run_id}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
