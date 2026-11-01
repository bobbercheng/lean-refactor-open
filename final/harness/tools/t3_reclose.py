#!/usr/bin/env python3
"""T3 delete-and-reclose (R1): delete a span of a tactic proof and close the goal it leaves with a closer from a generated grammar.





























































"""
from __future__ import annotations

import argparse, heapq, json, re, sys
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask              
from harness.tools import t3_suggest as _SG                                                                                       
from scorer.tokenize import count_tokens, split_declaration              

OPS = ("t3:d1", "t3:d2")                                        
OP_HINT = "t3:hint"                                                                                               
ALL_OPS = (OP_HINT,) + OPS
ORDER = None                                                                                                                              
TABLE_PATH = ROOT / "harness/tools/tables/closers.json"
TOP_SPANS = 20
MAX_SUFFIX = 4
D2_TOTAL = 200
MAX_OWN_TOKENS = 16
MIN_TIMEOUT_S = 20
TIMEOUT_MULT = 3.0
DEFAULT_TIMEOUT_S = 60
OPENERS_ARM = ("|", "case ", "next ", "next=>")                                                                                        
_IDCH = re.compile(r"[\w.'!?]")


def _load_table() -> dict:
    try:
        return json.loads(TABLE_PATH.read_text())
    except (OSError, ValueError):
        return {}


_TABLE = _load_table()
TABLES = {"closers": {"rule": _TABLE.get("rule", "missing: run harness/tools/tables/gen_closers.py"),
                      "query": _TABLE.get("query", "python3 harness/tools/tables/gen_closers.py (inside a 16G systemd unit)"),
                      "generated_at": _TABLE.get("generated_at"),
                      "path": "harness/tools/tables/closers.json"}}


                                                                                                                                      
@dataclass
class Step:
    start: int                                                                 
    end: int                                                                                                     
    l0: int                                                                  
    l1: int                                    
    children: list = field(default_factory=list)


@dataclass
class Block:
    col: int
    inline: bool
    steps: list
    top: bool = False


class _Doc:
    def __init__(self, decl: str, body_off: int):
        self.decl = decl
        self.mask = _mask(decl)
        self.lines = decl.split("\n")
        self.off, o = [], 0
        for ln in self.lines:
            self.off.append(o)
            o += len(ln) + 1
        self.code = []
        for i, ln in enumerate(self.lines):
            o = self.off[i]
            self.code.append("".join(" " if self.mask[o + j] else ch for j, ch in enumerate(ln)).rstrip())
        self.body_off = body_off
        self.body_line = decl.count("\n", 0, body_off)

    def blank(self, k: int) -> bool:
        return not self.code[k].strip()

    def indent(self, k: int) -> int:
        c = self.code[k]
        return len(c) - len(c.lstrip(" "))

    def line_end(self, k: int) -> int:
        return self.off[k] + len(self.code[k])

    @staticmethod
    def delta(s: str) -> int:
        return sum(1 for ch in s if ch in "([{⟨") - sum(1 for ch in s if ch in ")]}⟩")


def _is_cont(head: str) -> bool:
    if head.startswith(("<;>", "<|>", ")", "]", "}", "⟩", ",", ":=", "|", "_")):
        return True
    w = head.split(" ", 1)[0]
    return w in ("then", "else", "with", "using", "at", "from", "generalizing")


def _parse_block(d: _Doc, k0: int, p0: int, col: int, last: int, inline: bool) -> tuple[Block, int]:
    """The block whose first step starts at offset p0 on line k0 (column col), within lines k0..last. Returns (block, its last line)."""
    steps, cur_start, cur_l0, cur_l1 = [], p0, k0, k0
    depth = _Doc.delta(d.code[k0][p0 - d.off[k0]:])
    k = k0 + 1
    while k <= last:
        if d.blank(k):
            k += 1
            continue
        ind, head = d.indent(k), d.code[k].strip()
        if depth > 0 or ind > col or (ind == col and _is_cont(head)):
            cur_l1 = k
            depth += _Doc.delta(d.code[k])
            k += 1
            continue
        if ind == col:
            steps.append(Step(cur_start, d.line_end(cur_l1), cur_l0, cur_l1))
            cur_start, cur_l0, cur_l1 = d.off[k] + ind, k, k
            depth = _Doc.delta(d.code[k])
            k += 1
            continue
        break
    steps.append(Step(cur_start, d.line_end(cur_l1), cur_l0, cur_l1))
    blk = Block(col, inline, steps)
    for st in steps:
        st.children = _children(d, st)
    return blk, cur_l1


def _find_opener(seg: str, depth0: int) -> int | None:
    """End column (within seg) of the first tactic-block opener at bracket depth 0 of the segment seg (a step's text on one line, from the
"""
    s = seg.lstrip(" ")
    lead = len(seg) - len(s)
    if depth0 == 0 and (s.startswith("· ") or s == "·" or s.startswith(". ")):
        return lead + 1
    arm = s.startswith(OPENERS_ARM) or s.split(" ", 1)[0] in ("case", "next")
    depth, i = depth0, lead
    while i < len(seg):
        ch = seg[i]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0:
            if seg.startswith("by", i) and (i == 0 or not _IDCH.match(seg[i - 1])) and (i + 2 == len(seg) or not _IDCH.match(seg[i + 2])):
                return i + 2
            if arm and seg.startswith("=>", i):
                pre = seg[lead:i]
                if not re.search(r"(?<![\w.'])(fun|λ|match)(?![\w'])", pre):
                    return i + 2
        i += 1
    return None


def _children(d: _Doc, st: Step) -> list:
    out, k, depth = [], st.l0, 0
    while k <= st.l1:
        if d.blank(k):
            k += 1
            continue
        c0 = (st.start - d.off[k]) if k == st.l0 else d.indent(k)
        seg = d.code[k][c0:]
        e = _find_opener(seg, depth)
        if e is None:
            depth += _Doc.delta(seg)
            k += 1
            continue
        rest = seg[e:]
        if rest.strip():
            ccol = c0 + e + (len(rest) - len(rest.lstrip(" ")))
            blk, last = _parse_block(d, k, d.off[k] + ccol, ccol, st.l1, True)
        else:
            m = k + 1
            while m <= st.l1 and d.blank(m):
                m += 1
            if m > st.l1 or d.indent(m) <= d.indent(k):
                depth += _Doc.delta(seg)
                k += 1
                continue
            blk, last = _parse_block(d, m, d.off[m] + d.indent(m), d.indent(m), st.l1, False)
        out.append(blk)
        depth = 0
        k = last + 1
    return out


def parse(proof: str, statement: str) -> tuple[_Doc, Block] | None:
    """(document, top block) of a tactic proof `statement := by ...`, else None (term-mode proofs are out of scope in R1)."""
    body = split_declaration(proof, statement)
    if body is None:
        return None
    off = len(proof) - len(body)
    d = _Doc(proof, off)
    m = re.match(r"[ \t]*by(?![\w'])", body)
    if not m or d.mask[off + m.end() - 1]:
        return None
    k = d.body_line
    after = off + m.end()
    rest = d.code[k][after - d.off[k]:]
    if rest.strip():
        col = (after - d.off[k]) + (len(rest) - len(rest.lstrip(" ")))
        blk, _ = _parse_block(d, k, d.off[k] + col, col, len(d.lines) - 1, True)
    else:
        m2 = k + 1
        while m2 < len(d.lines) and d.blank(m2):
            m2 += 1
        if m2 >= len(d.lines):
            return None
        blk, _ = _parse_block(d, m2, d.off[m2] + d.indent(m2), d.indent(m2), len(d.lines) - 1, False)
    blk.top = True
    return d, blk


def _blocks(blk: Block):
    yield blk
    for st in blk.steps:
        for ch in st.children:
            yield from _blocks(ch)


                                                                                                                                     
def _scope(proof: str, ctx: dict | None) -> str:
    ctx = ctx or {}
    if ctx.get("scope") in ("core", "mathlib"):
        return ctx["scope"]
    src = str(ctx.get("source") or "").lower()
    if src:
        return "core" if src == "strata" else "mathlib"
    imp = ctx.get("imports")
    if imp:
        return "mathlib" if "Mathlib" in (imp if isinstance(imp, str) else " ".join(imp)) else "core"
    scopes = _TABLE.get("scopes", {})
    core = {c["tactic"] for c in scopes.get("core", {}).get("closers", []) + scopes.get("core", {}).get("progress", [])}
    ml = {c["tactic"] for c in scopes.get("mathlib", {}).get("closers", []) + scopes.get("mathlib", {}).get("progress", [])}
    words = set(re.findall(r"(?<![\w.'])[A-Za-z_][\w'!]*", proof))
    return "mathlib" if words & (ml - core) else "core"


def _table_lists(scope: str) -> tuple[list[dict], list[dict]]:
    sc = _TABLE.get("scopes", {}).get(scope) or {}
    return list(sc.get("closers", [])), [c for c in sc.get("closers", []) + sc.get("progress", []) if c.get("progress")]


def _ntok(s: str) -> int:
    return count_tokens(s)


def _own_terminals(d: _Doc, top: Block) -> list[str]:
    out, seen = [], set()
    for blk in _blocks(top):
        st = blk.steps[-1]
        if st.children or st.l0 != st.l1 or any(d.mask[st.start:st.end]):
            continue
        txt = " ".join(d.decl[st.start:st.end].split())
        if not txt or txt.startswith(("·", ".")) or "?" in txt.split(" ", 1)[0] or _ntok(txt) > MAX_OWN_TOKENS:
            continue
        if txt not in seen:
            seen.add(txt)
            out.append(txt)
    return out


def _closer_lists(own: list[str], scope: str) -> tuple[list[dict], list[dict]]:
    """(d1 closers, d2 closers) as dicts {"text", "cost", "rank"}; see the module docstring for the order."""
    table, prog = _table_lists(scope)
    info = {c["tactic"]: c for c in table}
    d1 = []
    for i, t in enumerate(own):
        head = t.split(" ", 1)[0]
        cost = info[head]["cost"] if head in info else "unknown"
        d1.append({"text": t, "cost": cost, "own": True, "key": (_ntok(t), 0, cost == "expensive", 0, 0, i, t)})
    seen_sets: set = set()
    for c in sorted(table, key=lambda c: (-len(c["closes"]), c["cost"] != "cheap", c["tactic"])):
        fs = frozenset(c["closes"])
        alias = fs in seen_sets
        seen_sets.add(fs)
        if c["tactic"] in own:
            continue
        d1.append({"text": c["tactic"], "cost": c["cost"], "own": False, "closes": fs,
                   "key": (_ntok(c["tactic"]), 1, c["cost"] != "cheap", alias, -len(fs), 0, c["tactic"])})
    d1.sort(key=lambda x: x["key"])
    for r, x in enumerate(d1):
        x["rank"] = r
    pinfo = {c["tactic"]: c for c in prog}
    porder = sorted(pinfo, key=lambda t: (_ntok(t), pinfo[t].get("cost") != "cheap", -len(pinfo[t]["progress"]), t))
    prank = {t: i for i, t in enumerate(porder)}                                                                                   
    ptok = {t: _ntok(t) for t in porder}
    for x in d1:
        x["ntok"] = x["key"][0]
    pairs = (_TABLE.get("scopes", {}).get(scope) or {}).get("pairs")
    if pairs is not None:                                                                                                  
        splitters = sorted({p["t1"] for p in pairs if p["t1"] in pinfo}, key=lambda t: prank[t])
        allowed = {(p["t1"], p["t2"]): len(p["adds"]) for p in pairs if p["t1"] in pinfo}
        combos = [(t1, x, allowed.get((t1, x["text"]))) for t1 in splitters for x in d1
                  if (t1, x["text"]) in allowed or (x["own"] and x["text"] != t1)]
    else:                                                                                                
        combos = [(t1, x, None) for t1 in porder for x in d1 if x["text"] != t1]

    def worst(*cs):
        return "expensive" if "expensive" in cs else ("unknown" if "unknown" in cs else "cheap")

    def gen():                                                                                                                       
        for t1, x, adds in combos:
            txt = f"{t1} <;> {x['text']}"
            yield (ptok[t1] + 1 + x["ntok"], -(adds or 0), prank[t1] + x["rank"], txt), txt, worst(pinfo[t1].get("cost"), x["cost"])
        for i, a in enumerate(d1):
            for b in d1[i + 1:]:
                if not a["own"] and not b["own"] and (a["closes"] <= b["closes"] or b["closes"] <= a["closes"]):
                    continue
                txt = f"first | {a['text']} | {b['text']}"
                yield (3 + a["ntok"] + b["ntok"], 0, a["rank"] + b["rank"], txt), txt, worst(a["cost"], b["cost"])

    out2, seen = [], set()
    for key, txt, cost in heapq.nsmallest(2 * D2_TOTAL, gen(), key=lambda g: g[0]):
        if txt not in seen and len(out2) < D2_TOTAL:
            seen.add(txt)
            out2.append({"text": txt, "cost": cost, "key": key})
    for r, x in enumerate(out2):
        x["rank"] = r
    return d1, out2


                                                                                                                                   
def _profile_lines(profile, nlines: int) -> list[float] | None:
    if not profile:
        return None
    hb = [0.0] * (nlines + 2)
    blocks = profile.get("blocks") if isinstance(profile, dict) and "blocks" in profile else profile
    try:
        if isinstance(blocks, dict):
            for k, v in blocks.items():
                i = int(k)
                if 1 <= i <= nlines and v:
                    hb[i] = max(hb[i], float(v))
        else:
            for b in blocks or []:
                h = b.get("heartbeats")
                if not h or h <= 0:
                    continue
                rng = str(b["lines"]) if b.get("lines") is not None else f"{b['line']}-{b['line']}"
                a, z = (int(x) for x in rng.split("-"))
                n = max(1, z - a + 1)
                for i in range(max(1, a), min(nlines, z) + 1):
                    hb[i] = max(hb[i], float(h) / n)
    except (TypeError, ValueError, AttributeError):
        return None
    return hb if sum(hb) > 0 else None


def _goal_counts(ctx: dict | None) -> dict:
    """{declaration line (1-based): goals open before it} from ctx["goals"] = [{"line", "n_goals"}] (harness/goals.py, as T2 reads it)."""
    out = {}
    for g in (ctx or {}).get("goals") or []:
        try:
            out[int(g["line"])] = int(g["n_goals"])
        except (KeyError, TypeError, ValueError):
            continue
    return out


def _spans(d: _Doc, top: Block, own: list[str], closer_heads: set, line_hb, goals: dict | None = None) -> list[dict]:
    body_tok = max(1, _ntok(d.decl[d.body_off:]))
    heads = {t.split(" ", 1)[0] for t in own} | closer_heads
    total_hb = sum(line_hb) if line_hb else 0.0
    out, seen = [], set()

    def add(a: Step, z: Step, kind: str, blk: Block):
        s, e = a.start, z.end
        if (s, e) in seen or s < d.body_off:
            return
        txt = d.decl[s:e]
        if any(d.mask[s:e]) or "@[" in txt or not txt.strip():
            return
        seen.add((s, e))
        tok = _ntok(txt)
        hb = sum(line_hb[i + 1] for i in range(a.l0, z.l1 + 1)) if line_hb else 0.0
        score = tok / body_tok + (hb / total_hb if total_hb else 0.0)
        out.append({"start": s, "end": e, "l0": a.l0 + 1, "l1": z.l1 + 1, "kind": kind, "tokens": tok, "hb": hb, "score": score,
                    "text": txt, "top": blk.top and a is blk.steps[0]})

    for blk in _blocks(top):
        n = len(blk.steps)
        ks = list(range(1, min(MAX_SUFFIX, n) + 1)) + ([n] if n > MAX_SUFFIX else [])
        for k in ks:
            add(blk.steps[n - k], blk.steps[-1], "suffix" if k < n else "block", blk)
        for st in blk.steps[:-1]:
            if not st.children and st.l0 == st.l1:
                w = d.decl[st.start:st.end].split(" ", 1)[0]
                if w in heads:
                    add(st, st, "leaf", blk)
        if goals:                                                                                                             
            for i in range(n - 1):
                for j in range(i, min(n - 1, i + MAX_SUFFIX)):
                    g0, g1 = goals.get(blk.steps[i].l0 + 1), goals.get(blk.steps[j + 1].l0 + 1)
                    if g0 is not None and g1 is not None and g0 - g1 == 1:
                        add(blk.steps[i], blk.steps[j], "closes1", blk)
    out.sort(key=lambda x: (-x["score"], x["kind"] in ("leaf", "closes1"), x["start"], -x["end"]))
    return out[:TOP_SPANS]


                                                                                                                                        
def _timeout(cost: str, ctx: dict | None):
    if cost == "cheap":
        return None
    cs = (ctx or {}).get("compile_s")
    try:
        return max(MIN_TIMEOUT_S, round(TIMEOUT_MULT * float(cs))) if cs else DEFAULT_TIMEOUT_S
    except (TypeError, ValueError):
        return DEFAULT_TIMEOUT_S


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = 40, ctx: dict | None = None) -> list[dict]:
    if not isinstance(proof, str) or not isinstance(statement, str):
        return []
    parsed = parse(proof, statement)
    if parsed is None:
        return []
    d, top = parsed
    body0 = d.decl[d.body_off:]
    tok0 = _ntok(body0)
    own = _own_terminals(d, top)
    scope = _scope(proof, ctx)
    d1, d2 = _closer_lists(own, scope)
    line_hb = _profile_lines((ctx or {}).get("profile"), len(d.lines))
    spans = _spans(d, top, own, {c["tactic"] for c in _table_lists(scope)[0]}, line_hb, _goal_counts(ctx))
    sugg = _suggestions(proof, ctx)
    info = {c["tactic"]: c for c in _table_lists(scope)[0]}
    out, seen = [], {proof.rstrip()}
    for op in _op_order(ctx, bool(sugg)):
        if op == OP_HINT:                                                                                                         
            per = [[{"text": t, "cost": info[t.split(" ", 1)[0]]["cost"] if t.split(" ", 1)[0] in info else "unknown"}
                    for t in sugg.get((sp["start"], sp["end"]), [])] for sp in spans]
        else:
            per = [d1 if op == "t3:d1" else d2] * len(spans)
        grid = [(si + ci, -(sp["tokens"] - _ntok(c["text"])), si, ci) for si, sp in enumerate(spans) for ci, c in enumerate(per[si])]
        grid.sort()
        n = 0
        for _, _, si, ci in grid:
            if n >= max_per_op:
                break
            sp, c = spans[si], per[si][ci]
            if " ".join(sp["text"].split()) == c["text"]:
                continue
            new = proof[:sp["start"]] + c["text"] + proof[sp["end"]:]
            if new.rstrip() in seen:
                continue
            body = split_declaration(new, statement)
            if body is None:
                continue
            dt = tok0 - _ntok(body)
            if dt < 1:
                if not (sp["hb"] > 0 and c["cost"] == "cheap" and (dt == 0 or (exchange and -dt * float(exchange) < sp["hb"]))):
                    continue
            seen.add(new.rstrip())
            n += 1
            out.append({"op": op, "decl": new, "cost": c["cost"], "timeout_s": _timeout(c["cost"], ctx),
                        "span": [sp["l0"], sp["l1"]], "closer": c["text"],
                        "note": f"{sp['kind']} L{sp['l0']}-{sp['l1']} ({sp['tokens']} tok) -> {c['text']} [{c['cost']}, {-dt:+d} tok]"
                                + (" (Lean's suggestion)" if op == OP_HINT else "")})
    return out


def _op_names(v) -> list[str]:
    """Op names from a list / tuple / set or a comma-separated string, each with the "t3:" prefix."""
    if isinstance(v, str):
        v = v.split(",")
    return [x if x.startswith("t3:") else f"t3:{x}" for x in (str(y).strip() for y in (v or ())) if x]


def _op_order(ctx: dict | None, has_suggestions: bool) -> tuple:
    """The ops in run order (module docstring, "Goal-aware closers"); unknown names are ignored."""
    c = ctx or {}
    order = c.get("t3_ops") or ORDER
    if order:
        out = tuple(o for o in dict.fromkeys(_op_names(order)) if o in ALL_OPS)
    else:
        out = ((OP_HINT,) if has_suggestions else ()) + OPS
    if c.get("ops") is not None:                                                                                                     
        allow = set(_op_names(c["ops"]))
        out = tuple(o for o in out if o in allow)
    return out


def ops_for(ctx: dict | None = None, has_suggestions: bool = False) -> tuple:
    """The ops a candidates() call with this ctx runs, in run order (module docstring, "Goal-aware closers"); has_suggestions: ctx will
"""
    return _op_order(ctx, has_suggestions)


def _suggestions(proof: str, ctx: dict | None) -> dict:
    """{(start, end): [tactic, ...]} from ctx["suggestions"] when ctx["suggestions_for"] says they were made for this proof ({}
"""
    c = ctx or {}
    raw = c.get("suggestions")
    if not isinstance(raw, dict) or not raw:
        return {}
    if c.get("suggestions_for") != _SG.proof_key(proof):                                                               
        return {}
    out = {}
    for k, v in raw.items():
        try:
            a, b = (int(x) for x in (k.split(":") if isinstance(k, str) else k))
        except (TypeError, ValueError):
            continue
        tacs = [" ".join(t.split()) for t in (v or []) if isinstance(t, str) and t.strip()]
        if tacs:
            out[(a, b)] = list(dict.fromkeys(tacs))
    return out


def ranked_spans(proof: str, statement: str, ctx: dict | None = None) -> list[dict]:
    """T3's ranked spans of `proof` (the top TOP_SPANS; module docstring, "Neighbourhoods"): [{"start", "end", "l0", "l1", "kind", "tokens",
"""
    if not isinstance(proof, str) or not isinstance(statement, str):
        return []
    parsed = parse(proof, statement)
    if parsed is None:
        return []
    d, top = parsed
    own = _own_terminals(d, top)
    scope = _scope(proof, ctx)
    line_hb = _profile_lines((ctx or {}).get("profile"), len(d.lines))
    return _spans(d, top, own, {c["tactic"] for c in _table_lists(scope)[0]}, line_hb, _goal_counts(ctx))


def suggest(proof: str, statement: str, spans, compile_batch, *, ctx: dict | None = None, tactic=None, mode: str | None = "rule",
            max_spans: int | None = None, stats: dict | None = None, log=None) -> dict:
    """{(start, end): [tactic, ...]}: Lean's closing suggestions at each span (harness/tools/t3_suggest.py). spans: T3 span dicts or



"""
    if spans is None:
        spans = ranked_spans(proof, statement, ctx)
    tac = tactic or _SG.probe_tactics(_scope(proof, ctx), mode)
    return _SG.suggest(proof, statement, spans, compile_batch, tactic=tac, max_spans=max_spans, stats=stats, log=log)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--file", required=True)
    ap.add_argument("--statement-file", required=True)
    ap.add_argument("--max-per-op", type=int, default=40)
    ap.add_argument("--scope", choices=("core", "mathlib"))
    a = ap.parse_args(argv)
    proof = Path(a.file).read_text()
    stmt = Path(a.statement_file).read_text().rstrip("\n")
    for c in candidates(proof, stmt, max_per_op=a.max_per_op, ctx={"scope": a.scope} if a.scope else None):
        print(json.dumps({"op": c["op"], "note": c["note"], "cost": c["cost"], "tokens": count_tokens(split_declaration(c["decl"], stmt))},
                         ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
