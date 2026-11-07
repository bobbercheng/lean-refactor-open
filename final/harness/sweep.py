#!/usr/bin/env python3
"""Generic single-edit sweep (B62b end stage; ported 2026-10-21 from the golf93 $0 sweep, probe/golf93/sweep/sweep.py, under










































"""
from __future__ import annotations

import argparse, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs, apply, OPEN, CLOSE              
import harness.hb_rewrite as HR              
import harness.lint_delete as LD              
from scorer.tokenize import split_declaration, count_tokens              

                                                                                                                                      
                                                                                                                                        
SAVE_OPS = ("byexact", "parendrop", "paren2dollar", "namedarg", "dots", "armdrop", "combdrop", "rwargdrop", "ld:arg", "ld:tac", "nth2plain",
            "at2star", "cleararg", "gendrop", "flagdrop", "ctorshort", "bycontra", "substhoist", "hr:nilarg", "hr:anyiftry", "hr:anonhave",
            "hr:case2bullet", "hr:bulletdrop", "hr:exact2assumption", "hr:intromerge", "hr:nthrw", "hr:simpmerge", "hr:rwsimpfold",
            "hr:simpafold")
SWAP_OPS = ("swap", "refine", "refine'", "deltaunfold", "assumpswap", "erw", "letI", "hr:rw2rewrite", "hr:simponly2dsimp", "hr:repeatrw",
            "hr:specialize", "hr:firstorder", "hr:preorder", "hr:use2refine")
ADD_OPS = ("rwa2rewrite", "rwfinal", "addonly", "simpall2at", "hr:simprw2only", "hr:exists2refine", "hr:withreducible", "hr:clearhyp", "addwr")
HR_SKIP = ("lemmavariant",)                                                                                                 
HR_OPS = tuple(o for o in HR.ALL_OPS if o not in HR_SKIP)
OPS = SAVE_OPS + SWAP_OPS + ADD_OPS + tuple(f"hr:{o}" for o in HR_OPS if f"hr:{o}" not in SAVE_OPS + SWAP_OPS + ADD_OPS)
                                                                                                                                          
                                                                                                                                        
                                                                                                                           
HB_CAP: dict = {}
MAX_PER_OP = 40
_W = r"(?<![\w.'?!])"                                                                                      
                                                                                                                                         
                                                                                                                
WRAPPER_TABLE = ROOT / "harness/tools/tables/transparency_wrappers.json"
TABLES = {"transparency_wrappers": {"rule": "the leading tactic tokens whose run changes the transparency setting a wrapped tactic sees, "
                                            "measured on every installed core toolchain; addwr inserts the least common one",
                                    "query": "python3 harness/tools/tables/gen_transparency.py (harness/tools/tables/transparency_query.lean)",
                                    "path": "harness/tools/tables/transparency_wrappers.json", "ops": ("addwr",)},
          **{k: dict(v, ops=tuple("hr:" + o for o in v.get("ops", ()))) for k, v in HR.TABLES.items()}}


def _least_wrapper(path: Path) -> str | None:
    try:
        common = json.loads(Path(path).read_text()).get("common") or []
        return common[0]["token"] if common and isinstance(common[0].get("token"), str) else None
    except (OSError, ValueError, AttributeError, KeyError, TypeError):
        return None


ADDWR_WRAPPER = _least_wrapper(WRAPPER_TABLE)


def table_status(root: Path = ROOT) -> dict:
    """{table: {"path", "ok", "sha256" (first 16 hex of the file) or None, "ops", "error"?}} for TABLES: ok when the file reads, parses and
"""
    import hashlib
    out = {}
    for name, meta in TABLES.items():
        p = Path(root) / meta["path"]
        rec = {"path": meta["path"], "ok": False, "sha256": None, "ops": list(meta.get("ops") or ())}
        try:
            raw = p.read_bytes()
            rec["sha256"] = hashlib.sha256(raw).hexdigest()[:16]
            data = json.loads(raw.decode())
            if name == "transparency_wrappers":
                rec["ok"] = _least_wrapper(p) is not None
            elif name == "bundled_homs":
                rec["ok"] = bool(HR.specialize_map(data))
            else:
                rec["ok"] = bool(data)
            if not rec["ok"]:
                rec["error"] = "parsed, but gives its ops nothing to propose"
        except (OSError, ValueError, UnicodeDecodeError) as e:
            rec["error"] = f"{type(e).__name__}: {str(e)[:120]}"
        out[name] = rec
    return out


def warn_tables(status: dict, out=None) -> list[str]:
    """One warning line per table of `status` (table_status()) that is not ok, printed to `out` (default stderr); the lines."""
    lines = [f"[sweep] WARNING: table {n} ({s['path']}): {s.get('error')}; ops {', '.join(s['ops'])} propose nothing"
             for n, s in status.items() if not s.get("ok")]
    for l in lines:
        print(l, file=out or sys.stderr, flush=True)
    return lines


TABLES_STATUS = table_status()
warn_tables(TABLES_STATUS)


def _wordch(c: str) -> bool:
    return c.isalnum() or c in "_.'"


def _depth0(inner: str, ch: str) -> bool:
    """Does inner hold ch outside nested brackets (a type ascription `:` not part of `:=` / `::`, a tuple comma)?"""
    d = 0
    for i, c in enumerate(inner):
        if c in OPEN: d += 1
        elif c in CLOSE: d -= 1
        elif c == ch and d == 0:
            if ch != ":" or (inner[i + 1:i + 2] not in ("=", ":") and inner[i - 1:i] != ":"):
                return True
    return False


def _prev_nonspace(body: str, i: int) -> int:
    j = i - 1
    while j >= 0 and body[j] in " \t":
        j -= 1
    return j


def _next_nonspace(body: str, i: int) -> int:
    j = i
    while j < len(body) and body[j] in " \t":
        j += 1
    return j


def _line_start_tac(c, i: int) -> bool:
    return not HR._code(c.body, c.mask, HR._ls(c.body, i), i).strip()


def _code_end(c, i: int) -> int:
    """End of the code on i's line before its first comment, trailing blanks excluded (a string literal is code, not a comment)."""
    e = HR._line_end(c.body, i); p = i
    while p < e and not (c.mask[p] and (p == 0 or not c.mask[p - 1]) and c.body.startswith(("--", "/-"), p)):
        p += 1
    while p > i and c.body[p - 1] in " \t":
        p -= 1
    return p


def _depth0_at(c, a: int, b: int, pat: str) -> list[int]:
    """Positions in body[a:b] where the regex pat matches outside brackets, comments and strings."""
    out = []; d = 0; k = a
    while k < b:
        ch = c.body[k]
        if c.mask[k]:
            k += 1; continue
        if ch in OPEN: d += 1
        elif ch in CLOSE: d -= 1
        elif d == 0 and re.match(pat, c.body[k:b]) and (k == a or not _wordch(c.body[k - 1])):
            out.append(k)
        k += 1
    return out


def _drop_span(body: str, a: int, b: int) -> tuple:
    """The edit deleting body[a:b] with its blanks: the leading ones mid-line; when it starts its line, the trailing ones, or the whole line
"""
    ls = HR._ls(body, a)
    if body[ls:a].strip():
        while a > ls and body[a - 1] in " \t":
            a -= 1
        return (a, b - a, "")
    while b < len(body) and body[b] in " \t":
        b += 1
    if b >= len(body) or body[b] == "\n":
        return (ls, min(b + 1, len(body)) - ls, "")
    return (a, b - a, "")


class _Ctx:
    def __init__(self, body: str):
        self.body = body; self.mask = _mask(body); self.pairs = _pairs(body, self.mask); self.fb = HR._first_by(body, self.mask)


                                                                                                                                            
def _parens(c) -> list[tuple]:
    body, mask, out = c.body, c.mask, []
    for i, j in sorted(c.pairs.items()):
        if body[i] != "(" or mask[i]:
            continue
        inner = body[i + 1:j]
        if re.match(r"\s*[^\W\d][\w.'₀-₉]*\s*:=", inner):                                         
            out.append(("namedarg", inner[:30], (_drop_span(body, i, j + 1),)))
            continue
                                                                                                                                          
        if not inner.strip() or _depth0(inner, ":") or _depth0(inner, ",") or inner.lstrip().startswith("·"):
            continue
        lo = "" if (i == 0 or not _wordch(body[i - 1]) or not _wordch(body[i + 1:i + 2] or " ")) else " "
        ro = "" if (j + 1 >= len(body) or not _wordch(body[j + 1]) or not _wordch(body[j - 1])) else " "
        out.append(("parendrop", inner[:30], ((i, 1, lo), (j, 1, ro))))
        k = _next_nonspace(body, j + 1)
        nxt_ok = k >= len(body) or body[k] in "\n)]}⟩," or body.startswith("<;>", k) or mask[k]
        p = _prev_nonspace(body, i)
        prv_ok = 0 <= p < i - 1 and (_wordch(body[p]) or body[p] in ")]}⟩")
        if nxt_ok and prv_ok:
            out.append(("paren2dollar", inner[:30], ((i, 1, "$ "), (j, 1, ""))))
    return out


def _byexact(c) -> list[tuple]:
    out = []
    for m in re.finditer(_W + r"by[ \t]+exact[ \t]+", c.body):
        if not c.mask[m.start()]:
            out.append(("byexact", c.body[m.start():m.start() + 30], ((m.start(), m.end() - m.start(), ""),)))
    if c.fb >= 0:                                                                                               
        m = re.compile(r"by[ \t]*\n[ \t]*exact[ \t]+").match(c.body, c.fb)
        if m and not c.mask[m.end() - 1]:
            out.append(("byexact", "by / exact", ((c.fb, m.end() - c.fb, ""),)))
    return out


_DOTS_END = re.compile(r"[ \t]*(?:\)|\n|$|,|⟩|\$|<;>|\]|\}|;|=>|\|)")


def _dots(c) -> list[tuple]:
    """A run of >= 2 `_` arguments that ends its application (`..` fills every remaining explicit argument, so nothing may follow it)."""
    out = []
    for m in re.finditer(r"(?:[ \t]+_(?![\w'₀-₉])){2,}", c.body):
        if not c.mask[m.start() + 1] and _DOTS_END.match(c.body, m.end()):
            out.append(("dots", m.group(0).strip(), ((m.start(), m.end() - m.start(), " .."),)))
    return out


def _armdrop(c) -> list[tuple]:
    """` <;> arm` dropped: the arm runs to the next depth-0 `<;>` or the end of its logical line."""
    body, mask, out = c.body, c.mask, []
    for m in re.finditer(r"<;>", body):
        i = m.start()
        if mask[i]:
            continue
        a = i
        while a > 0 and body[a - 1] in " \t":
            a -= 1
        k = m.end(); d = 0
        while k < len(body):
            if mask[k]:
                k += 1; continue
            ch = body[k]
            if ch in OPEN: d += 1
            elif ch in CLOSE:
                if d == 0: break
                d -= 1
            elif d == 0 and (body.startswith("<;>", k) or ch == "\n"):
                break
            k += 1
        e = k
        while e > a and body[e - 1] in " \t\n":
            e -= 1
        out.append(("armdrop", re.sub(r"\s+", " ", body[i:e])[:40], ((a, e - a, ""),)))
    return out


def _combdrop(c) -> list[tuple]:
    out = []
    for m in re.finditer(_W + r"(any_goals|all_goals|repeat'|repeat|try|with_reducible)[ \t]+(?=\S)", c.body):
        i = m.start()
        if HR._tac_pos(c.body, c.mask, i, c.fb) and not c.mask[m.end()]:
            out.append(("combdrop", m.group(1), ((i, m.end() - i, ""),)))
    return out


def _rwargdrop(c) -> list[tuple]:
    body, out = c.body, []
    for m in re.finditer(_W + r"(rw|rwa|rewrite|erw|nth_rewrite[ \t]+\d+|nth_rw[ \t]+\d+|simp_rw)(?![\w'?!])", body):
        if c.mask[m.start()]:
            continue
        k = _next_nonspace(body, m.end())
        if k >= len(body) or body[k] != "[" or k not in c.pairs:
            continue
        items = LD._list_items(body, c.mask, c.pairs, k)
        if not items or len(items) < 2:
            continue
        for n, (s, e) in enumerate(items):
            edit = (s, items[1][0] - s, "") if n == 0 else (items[n - 1][1], e - items[n - 1][1], "")
            out.append(("rwargdrop", body[s:e][:40], (edit,)))
    return out


def _lint_delete(c) -> list[tuple]:
    """harness/lint_delete.py delsearch: each simp-list argument and each standalone tactic line deleted alone."""
    out = []
    for d in LD.search_dels(c.body):
        nb = LD.render(c.body, [d])
        if nb != c.body:
            out.append(("ld:" + d.kind, d.note, (diff_edit(c.body, nb),)))
    return out


def _shorthands(c) -> list[tuple]:
    body, mask, fb, out = c.body, c.mask, c.fb, []
    for m in re.finditer(_W + r"(nth_rewrite|nth_rw)[ \t]+\d+[ \t]*", body):
        if HR._tac_pos(body, mask, m.start(), fb):
            out.append(("nth2plain", m.group(0).strip(), ((m.start(), m.end() - m.start(), "rewrite " if m.group(1) == "nth_rewrite" else "rw "),)))
    for m in re.finditer(_W + r"at((?:[ \t]+(?:⊢|(?!(?:with|using|generalizing|from)(?![\w'₀-₉]))[^\W\d][\w.'₀-₉]*))+)", body):                       
        if len(m.group(1).split()) >= 2 and not mask[m.start()]:
            out.append(("at2star", m.group(0), ((m.start(1), len(m.group(1)), " *"),)))
    for m in re.finditer(_W + r"clear((?:[ \t]+[^\W\d][\w'₀-₉]*){2,})", body):
        if mask[m.start()]:
            continue
        for w in re.finditer(r"[ \t]+[^\W\d][\w'₀-₉]*", m.group(1)):
            out.append(("cleararg", w.group(0).strip(), ((m.start(1) + w.start(), w.end() - w.start(), ""),)))
    for m in re.finditer(r"[ \t]+generalizing(?:[ \t]+(?!(?:with|using)(?![\w'₀-₉]))[^\W\d][\w'₀-₉]*)+", body):                               
        if not mask[m.start() + 1]:
            out.append(("gendrop", m.group(0).strip(), ((m.start(), m.end() - m.start(), ""),)))
    for m in re.finditer(r"(?<=[ \t])([+-])[^\W\d]\w*", body):                                                                               
        i = m.start()
        if mask[i]:
            continue
        pre = body[HR._ls(body, i):i]
        if re.search(_W + r"(simp|simp_all|dsimp|simpa|grind)(?![\w'?!])", pre) and "[" not in pre:
            a = i
            while a > 0 and body[a - 1] in " \t":
                a -= 1
            out.append(("flagdrop", m.group(0), ((a, m.end() - a, ""),)))
    short = {"Or.inl": "left", "Or.inr": "right", "And.intro": "constructor", "Iff.intro": "constructor", "Exists.intro": "constructor"}
    for m in re.finditer(_W + r"(apply|exact)[ \t]+([^\W\d][\w.'₀-₉]*)(?=[ \t]*(?:\n|$|<;>))", body):
        i = m.start(); w = m.group(2)
        if not HR._tac_pos(body, mask, i, fb):
            continue
        last = w.split(".")[-1]; reps = [short[w]] if w in short else []
        if last in ("refl", "rfl"):
            reps.append("rfl")
        elif "." in w and w[:1].isupper() and w not in short:                                                                            
            reps.append("constructor")                                                                                    
        for r in reps:
            if r != m.group(0).strip():
                out.append(("ctorshort", f"{m.group(0).strip()} -> {r}", ((i, m.end() - i, r),)))
    for m in re.finditer(_W + r"false_or_by_contra[ \t]*\n[ \t]*rename_i[ \t]+([^\W\d][\w'₀-₉]*)", body):
        if not mask[m.start()]:
            out.append(("bycontra", m.group(1), ((m.start(), m.end() - m.start(), "by_contra " + m.group(1)),)))
    subs = [mm for mm in re.finditer(r"(?m)^[ \t]*subst[ \t]+([^\W\d][\w'₀-₉]*)[ \t]*\n", body) if not mask[mm.start(1)]]
    if len(subs) >= 2 and len({mm.group(1) for mm in subs}) == 1:                                                                         
        first = next((mm for mm in re.finditer(r"(?m)^[ \t]*(intro)[^\n]*\n", body) if not mask[mm.start(1)]), None)
        if first and first.end() < subs[0].start():
            ind = re.match(r"[ \t]*", body[first.start():]).group(0)
            edits = [(first.end(), 0, f"{ind}subst {subs[0].group(1)}\n")] + [(mm.start(), mm.end() - mm.start(), "") for mm in subs]
            out.append(("substhoist", subs[0].group(1), tuple(edits)))
    return out


                                                                                                                                            
SWAPS = {"apply": ("exact",), "exact": ("apply",), "cases": ("rcases", "induction"), "induction": ("cases",), "intro": ("intros",),
         "intros": ("intro",), "any_goals": ("all_goals",), "all_goals": ("any_goals",), "constructor": ("econstructor", "apply And.intro"),
         "econstructor": ("constructor",), "simp_all": ("simp at *",), "ring1": ("ring",), "rintro": ("intro",), "subst": ("cases",),
         "repeat": ("repeat'",), "repeat'": ("repeat",)}
_SWAP_RE = re.compile(_W + r"(apply|exact|rcases|cases|induction|obtain|intros|intro|any_goals|all_goals|constructor|econstructor|simp_all|"
                      r"ring1|rintro|subst|repeat'|repeat)(?![\w'?!])")


def _swaps(c) -> list[tuple]:
    body, mask, out = c.body, c.mask, []
    for m in _SWAP_RE.finditer(body):
        i = m.start(); w = m.group(1)
        if not HR._tac_pos(body, mask, i, c.fb):
            continue
        rest = HR._rest(body, mask, m.end())                                                          
        has_with = re.search(_W + r"with(?![\w'?!])", rest) is not None
        if w in ("obtain", "rcases"):
            out += _obtain_rcases(c, i, m.end(), w)
            if w == "rcases" and not has_with:                                                                   
                out.append(("swap", "rcases -> cases", ((i, len(w), "cases"),)))
            continue
        if w == "simp_all" and rest:                                                                           
            continue
        if w in ("intro", "intros") and rest:
            continue
        if w == "rintro" and not re.fullmatch(r"[^\W\d][\w'₀-₉]*(?:[ \t]+[^\W\d][\w'₀-₉]*)*", rest):
            continue
        for v in SWAPS[w]:
            if w == "cases" and v == "rcases" and has_with:                                        
                continue
            out.append(("swap", f"{w} -> {v}", ((i, len(w), v),)))
    return out


def _obtain_rcases(c, i: int, k: int, w: str) -> list[tuple]:
    """`obtain pat := e` <-> `rcases e with pat` for a one-line call (no type ascription, one target, no `<;>` / `;` after it); 2026-10-21:
"""
    le = HR._line_end(c.body, i); e = _code_end(c, i); nx = HR._next_code_line(c.body, c.mask, i)
    if e <= k or '"' in c.body[i:le] or HR._code(c.body, c.mask, e, le).strip() or _depth0_at(c, k, e, r"<;>|;"):
        return []
    if nx and nx[1] > HR._col(c.body, i):                                      
        return []
    if w == "obtain":
        ce = _depth0_at(c, k, e, r":=")
        if len(ce) != 1 or _depth0(c.body[k:ce[0]], ":"):
            return []
        pat, tgt = c.body[k:ce[0]].strip(), c.body[ce[0] + 2:e].strip()
        if not tgt or _depth0(tgt, ","):
            return []
        new = f"rcases {tgt}" + (f" with {pat}" if pat else "")
        return [("swap", "obtain -> rcases", ((i, e - i, new),))]
    ws = _depth0_at(c, k, e, r"with(?![\w'?!])")
    if len(ws) > 1:
        return []
    tgt = c.body[k:ws[0] if ws else e].strip(); pat = c.body[ws[0] + 4:e].strip() if ws else ""
    if not tgt or _depth0(tgt, ",") or _depth0(tgt, ":"):
        return []
    new = "obtain " + (pat + " " if pat else "") + ":= " + tgt
    return [("swap", "rcases -> obtain", ((i, e - i, new),))]


def _small_swaps(c) -> list[tuple]:
    body, mask, fb, out = c.body, c.mask, c.fb, []
    for m in re.finditer(_W + r"(apply|exact)(?![\w'?!])", body):
        if HR._tac_pos(body, mask, m.start(), fb):
            out.append(("refine", m.group(1) + " -> refine", ((m.start(), len(m.group(1)), "refine"),)))
    for m in re.finditer(_W + r"refine'(?![\w'?!])", body):
        if not mask[m.start()]:
            for v in ("refine", "exact"):
                out.append(("refine'", v, ((m.start(), 7, v),)))
    for m in re.finditer(_W + r"(delta|unfold)(?![\w'?!])", body):
        if HR._tac_pos(body, mask, m.start(), fb):
            out.append(("deltaunfold", m.group(1), ((m.start(), len(m.group(1)), "unfold" if m.group(1) == "delta" else "delta"),)))
    for m in re.finditer(_W + r"assumption('?)(?![\w?!])", body):
        if HR._tac_pos(body, mask, m.start(), fb):
            out.append(("assumpswap", m.group(0), ((m.start(), len(m.group(0)), "assumption" if m.group(1) else "assumption'"),)))
    for m in re.finditer(_W + r"erw(?![\w'?!])", body):
        if HR._tac_pos(body, mask, m.start(), fb):
            for v in ("rewrite", "rw"):
                out.append(("erw", v, ((m.start(), 3, v),)))
    for m in re.finditer(_W + r"letI(?![\w'?!])", body):
        if not mask[m.start()]:
            out.append(("letI", "haveI", ((m.start(), 4, "haveI"),)))
    return out


                                                                                                                                            
_ADDWR_RE = re.compile(r"(?m)^[ \t]*(apply|exact|assumption|constructor|econstructor|rcases|cases|simp|refine|use|exists|rewrite|rw|rwa|"
                       r"intro|obtain|induction|any_goals|all_goals)(?![\w'?!])")


def _heartbeat_adds(c) -> list[tuple]:
    body, mask, fb, out = c.body, c.mask, c.fb, []
    for m in re.finditer(_W + r"(rwa|rw)(?![\w'?!])", body):                                                                   
        i = m.start(); w = m.group(1)
        if not HR._tac_pos(body, mask, i, fb) or not _line_start_tac(c, i) or HR._in_conv(body, mask, i):
            continue
        got = HR._call_rules(body, c.pairs, m.end())
        if not got:
            continue
        end = HR._loc_end(body, mask, got[2]); ind = " " * HR._col(body, i)
        if HR._rest(body, mask, end):                                                                                        
            continue
        if w == "rwa":
            out.append(("rwa2rewrite", HR._note(body, i, end), ((i, 3, "rewrite"), (end, 0, "\n" + ind + "assumption"))))
        elif HR._is_final(body, mask, i, end) and HR._block_must_close(body, mask, i):                                                  
            for tail in ("rfl", "with_reducible rfl", "exact rfl"):
                out.append(("rwfinal", tail, ((i, 2, "rewrite"), (end, 0, "\n" + ind + tail))))
    for m in re.finditer(_W + r"(simp_all|simp|dsimp)(?![\w'?!])", body):                                                 
        i = m.start()
        if not HR._tac_pos(body, mask, i, fb):
            continue
        k = _next_nonspace(body, m.end())
        if body.startswith("only", k) or body[k:k + 1] in ("(", "+", "-", "?", "!"):
            continue
        out.append(("addonly", HR._note(body, i, HR._line_end(body, i)), ((m.end(), 0, " only"),)))
    for m in re.finditer(_W + r"simp_all[ \t]+only[ \t]*(\[)", body):
        lb = m.start(1)
        if not mask[m.start()] and lb in c.pairs and not re.match(r"[ \t]*at(?![\w'?!])", body[c.pairs[lb] + 1:]):
            out.append(("simpall2at", "at *", ((m.start(), 8, "simp"), (c.pairs[lb] + 1, 0, " at *"))))
    for m in (_ADDWR_RE.finditer(body) if ADDWR_WRAPPER else ()):
        i = m.start(1)
        if HR._tac_pos(body, mask, i, fb):
            out.append(("addwr", HR._note(body, i, HR._line_end(body, i)), ((i, 0, ADDWR_WRAPPER + " "),)))
    return out


def _hb_rewrite(c) -> list[tuple]:
    """harness/hb_rewrite.py: every site of every operator but HR_SKIP, each alone (its variants are separate candidates)."""
    return [("hr:" + s.op, s.note, s) for s in HR.sites(c.body, HR_OPS)]


FINDERS = (_byexact, _parens, _dots, _armdrop, _combdrop, _rwargdrop, _lint_delete, _shorthands, _swaps, _small_swaps, _heartbeat_adds,
           _hb_rewrite)


                                                                                                                                            
def diff_edit(a: str, b: str) -> tuple:
    """The single (pos, delete_len, insert) edit turning a into b (common prefix and suffix stripped)."""
    p = 0
    while p < len(a) and p < len(b) and a[p] == b[p]:
        p += 1
    s = 0
    while s < len(a) - p and s < len(b) - p and a[len(a) - 1 - s] == b[len(b) - 1 - s]:
        s += 1
    return (p, len(a) - p - s, b[p:len(b) - s])


def apply_edits(body: str, edits) -> str:
    """(pos, delete_len, insert) edits on the original body, applied from the end; at one position the deletion goes before the insertion."""
    for pos, dl, ins in sorted(edits, key=lambda e: (-e[0], -e[1])):
        body = body[:pos] + ins + body[pos + dl:]
    return body


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = MAX_PER_OP) -> list[dict]:
    """Every single-site edit of the declaration by every operator: [{"op", "decl", "note"}] in OPS order, then by position."""
    body = split_declaration(proof, statement)
    if body is None:
        return []
    head = proof[:len(proof) - len(body)]; c = _Ctx(body)
    newline0 = bool(re.match(r"[ \t]*\n", body)); t0 = None
    by_op: dict = {}
    for find in FINDERS:
        for op, note, edits in find(c):
            nb = apply(body, [edits]) if isinstance(edits, HR.Site) else apply_edits(body, edits)
            by_op.setdefault(op, []).append((nb, note))
    out, seen = [], {proof, proof.rstrip()}
    for op in OPS + tuple(o for o in by_op if o not in OPS):                                                                   
        n = 0
        for nb, note in sorted(by_op.get(op, ()), key=lambda x: diff_edit(body, x[0])[0]):
            decl = head + nb
            if n >= max_per_op or decl in seen or decl.rstrip() in seen:
                continue
            if not newline0 and re.match(r"[ \t]*\n", nb):                                                                  
                continue
            if split_declaration(decl, statement) != nb:
                continue
            if exchange is not None and op in HB_CAP:
                t0 = count_tokens(body) if t0 is None else t0
                dtok = count_tokens(nb) - t0
                if dtok > 0 and dtok * float(exchange) > HB_CAP[op]:                                                                  
                    continue
            seen.add(decl); seen.add(decl.rstrip()); n += 1
            pos = diff_edit(body, nb)[0]
            out.append({"op": op, "decl": decl, "note": f"{note} @L{decl.count(chr(10), 0, len(head) + pos) + 1}"})
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="single-edit sweep candidates of one declaration (no compile)")
    ap.add_argument("--file", required=True, help="the declaration (statement := body)")
    ap.add_argument("--statement-file", required=True, help="the exact statement text")
    ap.add_argument("--exchange", type=float, default=None, help="heartbeats per token of the row (ref hb / ref tokens)")
    ap.add_argument("--max-per-op", type=int, default=MAX_PER_OP)
    a = ap.parse_args(argv)
    proof = Path(a.file).read_text(); stmt = Path(a.statement_file).read_text().rstrip("\n")
    t0 = count_tokens(split_declaration(proof, stmt) or "")
    for d in candidates(proof, stmt, exchange=a.exchange, max_per_op=a.max_per_op):
        print(json.dumps({"op": d["op"], "note": d["note"], "dtok": count_tokens(split_declaration(d["decl"], stmt)) - t0}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
