#!/usr/bin/env python3
"""T7 joint operators "defer side goals", "let-collapse" and the specialised bundled-map swaps (opt-in end-stage family "t7"; b63






































"""
from __future__ import annotations

import hashlib, json, re, sys, threading, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.tools import famkit as K              
from harness.tools import t5_joint as T5              
from harness.tools.t5_joint import Edit, Src, apply_edits, disjoint, split_items              
from scorer.accept import HB_EPS, decide              
from scorer.tokenize import count_tokens, split_declaration              

OPS = ("t7:defer", "t7:letc", "t7:swap", "t7:chain")
TABLES: dict = {}                                                                                                                                             
SEARCH_SECONDS = 240.0                                                                                                  
MAX_CHECKS = 400                                            
STAGE_CAPS = {"defer": 80, "letc": 60, "swap": 160, "chain": 40}
CHAIN_CAP = 40
N_OUT = 6
FALLBACK_PER_OP = 3
DEFER_CLOSERS = 12                                    
BARE_CLOSERS = 3                                                                                                                   
LETC_LEMMAS = 3                                                                            
LETC_EXPLICIT_TOKENS = 40                                                                                        
SWAP_SITE_MAX = 8                                                                 
SWAP_LIST_MAX = 24                                                                    
SWAP_SPEC_SINGLES = 2                                                                                                         
SWAP_PAIR_OWNERS = 10                                                                                                           
SWAP_TOTAL = 160
MIN_TIMEOUT_S = 10.0
TIMEOUT_MULT = 4.0
RW_HEADS = ("rw", "rewrite", "erw", "nth_rewrite", "nth_rw")
DEFER_HEADS = RW_HEADS + ("apply", "refine", "refine'", "exact", "have", "haveI", "obtain", "use", "calc")
SIMP_HEADS = ("simp", "simp_all", "simpa", "dsimp", "simp_arith", "field_simp", "norm_num", "simp?", "simp_rw")
ATOMS = ("nofun", "trivial")
NAME = T5.NAME
IDENT = T5.IDENT
_WORD = r"(?<![\w'.₀-₉])%s(?![\w'₀-₉])"


def proof_key(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def _ops(ctx: dict | None) -> set:
    allow = (ctx or {}).get("ops")
    if not allow:
        return set(OPS)
    return {a if a.startswith("t7:") else "t7:" + a for a in allow}


                                                                                                                                       
def _head(S: Src, st) -> str:
    m = re.match(r"(?:[·.]\s+)?([^\s\[(]+)", S.code[st.start:st.end])
    return m.group(1) if m else ""


def _blocks(S: Src):
    """(block, parent step or None) for every block of the tree, in source order."""
    if not S.tree:
        return
    _augment(S)
    _, top = S.tree
    stack = [(top, None)]
    while stack:
        blk, par = stack.pop(0)
        yield blk, par
        for st in blk.steps:
            for ch in st.children:
                stack.append((ch, st))


def _augment(S: Src) -> None:
    """T3's tree misses a `by` block whose opener line is indented deeper than the block (a calc step's continuation line `.. := by`):
"""
    if not S.tree or getattr(S, "_t7_aug", False):
        return
    S._t7_aug = True
    from harness.tools import t3_reclose as T3
    d, top = S.tree
    for blk in list(T3._blocks(top)):
        for st in blk.steps:
            covered = set()
            for ch in st.children:
                for cs in ch.steps:
                    covered.update(range(cs.l0, cs.l1 + 1))
            col0 = st.start - d.off[st.l0]
            k = st.l0
            while k <= st.l1:
                line = d.code[k]
                if k in covered or not re.search(r"(?<![\w'.])by\s*$", line) or d.mask[d.off[k] + len(line.rstrip()) - 1]:
                    k += 1
                    continue
                m = k + 1
                while m <= st.l1 and d.blank(m):
                    m += 1
                if m > st.l1 or m in covered or d.indent(m) <= col0:
                    k += 1
                    continue
                try:
                    nb, last = T3._parse_block(d, m, d.off[m] + d.indent(m), d.indent(m), st.l1, False)
                except Exception:                
                    k += 1
                    continue
                if any(cs.l0 in covered for cs in nb.steps):
                    k += 1
                    continue
                st.children.append(nb)
                st.children.sort(key=lambda b: b.steps[0].start if b.steps else 0)
                for cs in nb.steps:
                    covered.update(range(cs.l0, cs.l1 + 1))
                k = last + 1


def _block_end(blk) -> int:
    return max(st.end for st in blk.steps) if blk.steps else 0


def _depth_end(S: Src, a: int, lim: int) -> int:
    """Offset where the term starting at a ends: the first depth-0 `,` (relative to a) or the bracket closing a's group, else lim."""
    d0 = S.depth[a]
    k = a
    while k < lim:
        if S.depth[k] < d0:
            return k
        if S.depth[k] == d0 and k > a and (S.code[k] == "," or S.code[k] in ")]}⟩"):
            return k
        k += 1
    return lim


def _names_in(S: Src, a: int, e: int) -> set:
    return {m.group(0) for m in IDENT.finditer(S.code[a:e])}


def _trim(S: Src, a: int, e: int) -> tuple[int, int]:
    while a < e and S.proof[a].isspace():
        a += 1
    while e > a and S.proof[e - 1].isspace():
        e -= 1
    return a, e


class _WhyTL(threading.local):
    """The collector of skipped constructs, per thread (the end stage searches several rows at once in one process): None when off."""
    def __init__(self):
        self.cur: list | None = None


_Why = _WhyTL()


def _why(op: str, S: Src, pos: int, what: str, reason: str):
    cur = _Why.cur
    if cur is not None:
        cur.append({"op": op, "line": S.line(pos) + 1, "what": what.strip()[:80], "reason": reason})


                                                                                                                                    
def defer_sites(S: Src) -> list[dict]:
    """Per block with deferrable argument proofs: {"block", "sites": [{"a", "e", "body", "kind", "step"}], "heads": {step start: head}}."""
    out = []
    if not S.tree:
        return out
    for blk, _par in _blocks(S):
        sites, heads = [], {}
        if blk.inline:
            continue
        for st in blk.steps:
            if st.start < S.off0:
                continue
            h = _head(S, st)
            seg_end = st.end
            if st.children:                                                                
                seg_end = min(seg_end, min(c.steps[0].start for c in st.children if c.steps))
            text = S.code[st.start:seg_end]
            bys = [(m.start(), m.end()) for m in re.finditer(r"(?<![\w'.])by(?![\w'])", text)]
            for b0, b1 in bys:
                p = st.start + b0
                q = st.start + b1
                if S.mask[p]:
                    continue
                i = p - 1
                while i > st.start and S.proof[i] in " \t":
                    i -= 1
                pre = S.code[max(st.start, i - 1):i + 1]
                kind = None
                if pre.endswith("$") or pre.endswith("<|"):
                    kind = "pipe"
                    a = i - (2 if pre.endswith("<|") else 1)
                    while a > st.start and S.proof[a - 1] in " \t":
                        a -= 1
                    e = _depth_end(S, q, seg_end)
                elif S.code[i] == "(" and i in S.pairs:
                    kind = "paren"
                    a, e = i, S.pairs[i] + 1
                elif S.code[i] in "⟨," and _in_ctor(S, i) or S.code[i] == "▸":
                    kind = "item"                                                                                                 
                    a, e = q - 2, _depth_end(S, q, seg_end)
                else:
                    if S.code[max(0, i - 1):i + 1] == ":=" or S.code[max(0, i - 1):i + 1] == "=>":
                        continue                                          
                    _why("t7:defer", S, p, S.proof[st.start:min(seg_end, st.start + 60)], "an inline `by` that is not an argument "
                         "(after `$`, `<|` or `(`)")
                    continue
                if h not in DEFER_HEADS:
                    _why("t7:defer", S, p, S.proof[st.start:min(seg_end, st.start + 60)],
                         "simp-family lemma argument" if h in SIMP_HEADS else f"head `{h}` is not a deferrable step")
                    continue
                body = S.proof[q:e if kind == "pipe" else e - 1].strip()
                if "\n" in body or not body:
                    _why("t7:defer", S, p, body[:60], "multi-line argument proof")
                    continue
                if S.depth[p] == S.depth[st.start] and kind == "pipe" and h in RW_HEADS:
                    _why("t7:defer", S, p, body[:60], "a `by` at the step's own depth (the rewrite's `at`/config, not a lemma argument)")
                    continue
                sites.append({"a": a, "e": e, "body": body, "kind": kind, "step": st.start})
                heads[st.start] = h
            if h in RW_HEADS or h in ("apply", "refine", "exact", "have"):
                for at in ATOMS:
                    for m in re.finditer(_WORD % re.escape(at), text):
                        p = st.start + m.start()
                        if S.mask[p] or S.depth[p] <= S.depth[st.start]:
                            continue
                        sites.append({"a": p, "e": p + len(at), "body": at, "kind": "atom", "step": st.start})
                        heads[st.start] = h
        if sites:
            out.append({"block": blk, "sites": sites, "heads": heads})
    return out


def _in_ctor(S: Src, i: int) -> bool:
    """Is the `⟨` or `,` at i a component separator of an anonymous constructor (the innermost open bracket is `⟨`)?"""
    if S.code[i] == "⟨":
        return i in S.pairs
    d = S.depth[i]
    k = i - 1
    while k >= 0:
        if S.depth[k] == d - 1 and S.code[k] in "([{⟨" and k in S.pairs:
            return S.code[k] == "⟨"
        k -= 1
    return False


def _closer_list(S: Src, bodies: list[str], ctx: dict | None) -> list[str]:
    out: list[str] = []

    def add(t):
        t = " ".join(t.split())
        if t and t not in out:
            out.append(t)
    uniq = list(dict.fromkeys(bodies))
    simp_lists = []
    for b in uniq:
        m = re.match(r"(simp|simp_all|simpa)(?:\s+only)?\s*\[(.*)\]\s*$", b)
        if m:
            simp_lists.append(split_items(m.group(2)))
    if len(uniq) == 1:
        add(uniq[0])
    if simp_lists and len(simp_lists) == len(uniq):
        items = []
        for L in simp_lists:
            for it in L:
                if it not in items:
                    items.append(it)
        add("simp [" + ", ".join(items) + "]")
        add("simp [" + ", ".join(items + ["*"]) + "]")
    add("simp [*]")
    add("simp_all")
    add("simp")
    try:
        for c in T5.closers(S, [[b] for b in uniq], ctx=ctx):
            if c.get("expensive") or len(c["lines"]) != 1:
                continue
            add(c["lines"][0])
    except Exception:                
        pass
    return out[:DEFER_CLOSERS]


def defer_variants(S: Src, ctx: dict | None = None) -> list[dict]:
    """Candidates: {"op", "group", "edits", "note", "tok"} per block x closer x site selection."""
    out = []
    for k, site in enumerate(defer_sites(S)):
        blk, sites, heads = site["block"], site["sites"], site["heads"]
        last = blk.steps[-1]
        ins = _block_end(blk)
        col = blk.col
        selections = [("all", sites)]
        bys = [s for s in sites if s["kind"] != "atom"]
        if bys and len(bys) < len(sites):
            selections.append(("by-only", bys))
        for sel, ss in selections:
            edits = []
            for s in ss:
                edits.append(Edit(s["a"], s["e"], "?_" if s["kind"] != "pipe" else " ?_"))                                         
            for st0, h in heads.items():
                if h == "exact" and any(s["step"] == st0 for s in ss):
                    edits.append(Edit(st0, st0 + len("exact"), "refine"))
            bodies = [s["body"] for s in ss if s["kind"] != "atom"]
            cl = _closer_list(S, bodies, ctx) if bodies else ["simp", "simp [*]", "simp_all"]
            forms = [(ci, c, "all_goals " + c) for ci, c in enumerate(cl)]
            forms += [(ci, c, c) for ci, c in enumerate(cl[:BARE_CLOSERS])]                                                         
            for ci, c, line in forms:
                tail_text = "\n" + " " * col + line
                es_ = list(edits)
                touch = next((i for i, x in enumerate(es_) if x.e == ins), None)
                if touch is None:
                    es_.append(Edit(ins, ins, tail_text))
                else:                                                                     
                    es_[touch] = Edit(es_[touch].a, es_[touch].e, es_[touch].new + tail_text)
                es = tuple(sorted(es_, key=lambda x: (x.a, x.e)))
                if any(not disjoint(x, y) for i, x in enumerate(es) for y in es[i + 1:]):
                    continue
                out.append({"op": "t7:defer", "group": f"defer@{blk.steps[0].start}", "edits": es,
                            "note": f"defer {len(ss)} site(s) of block L{S.line(blk.steps[0].start) + 1} ({sel}); closer {ci}"
                                    f"{'' if line.startswith('all_goals') else ' bare'}: {c[:40]}",
                            "tok": S.dtok(es)})
    return out


                                                                                                                                    
_LET_RE = re.compile(r"let\s+(" + NAME + r")\s*((?:\([^)]*\)\s*)*)(?::\s*(.*?))?\s*:=\s*", re.S)


def _parse_have(S: Src, st) -> dict | None:
    text = S.code[st.start:st.end]
    m = re.match(r"have\s+(" + NAME + r")", text)
    if not m:
        return None
    p = st.start + m.end()
    cols = [c for c in T5._depth0(S, p, st.end, ":") if not S.code.startswith(":=", c)]
    asg = T5._depth0(S, p, st.end, ":=")
    if not cols or not asg or cols[0] > asg[0]:
        return None
    binders = S.proof[p:cols[0]].strip()
    typ = " ".join(S.proof[cols[0] + 1:asg[0]].split())
    val = S.proof[asg[0] + 2:st.end].strip()
    return {"name": m.group(1), "binders": binders, "type": typ, "value": val, "val_pos": asg[0] + 2}


def _binder_groups(b: str) -> list[dict]:
    """`l (hl : H) {x : X}` -> [{"text", "names", "type", "kind"}]."""
    out = []
    i = 0
    m_ = T5._mask(b)
    pairs = T5._pairs(b, m_)
    while i < len(b):
        if b[i].isspace():
            i += 1
            continue
        if b[i] in "({[⦃" and i in pairs:
            g = b[i:pairs[i] + 1]
            inner = g[1:-1]
            k = inner.find(":")
            names = inner[:k].split() if k >= 0 else inner.split()
            out.append({"text": g, "names": names, "type": inner[k + 1:].strip() if k >= 0 else None, "kind": g[0]})
            i = pairs[i] + 1
        else:
            m = re.match(NAME, b[i:])
            if not m:
                return []
            out.append({"text": m.group(0), "names": [m.group(0)], "type": None, "kind": "bare"})
            i += m.end()
    return out


def letc_sites(S: Src) -> list[dict]:
    out = []
    if not S.tree:
        return out
    for blk, _par in _blocks(S):
        steps = blk.steps
        i = 0
        while i < len(steps):
            if steps[i].start >= S.off0 and _head(S, steps[i]) == "let":
                j = i
                lets = []
                while j < len(steps) and _head(S, steps[j]) == "let":
                    m = _LET_RE.match(S.code[steps[j].start:steps[j].end])
                    if not m:
                        lets = None
                        break
                    v0 = steps[j].start + m.end()
                    lets.append({"name": m.group(1), "binders": (m.group(2) or "").strip(), "type": (m.group(3) or "").strip() or None,
                                 "value": S.proof[v0:steps[j].end].strip(), "step": steps[j]})
                    j += 1
                if lets is None:
                    _why("t7:letc", S, steps[i].start, S.proof[steps[i].start:steps[i].start + 60], "a `let` the parser does not read")
                    i = max(j, i + 1)
                    continue
                if j >= len(steps) or _head(S, steps[j]) != "have":
                    _why("t7:letc", S, steps[i].start, S.proof[steps[i].start:steps[i].start + 60],
                         "the let run is not followed by a `have`" if j < len(steps) else "the let run ends its block")
                    i = j
                    continue
                hv = _parse_have(S, steps[j])
                if hv is None:
                    _why("t7:letc", S, steps[j].start, S.proof[steps[j].start:steps[j].start + 60], "a `have` without a name or a stated type")
                    i = j + 1
                    continue
                names = [l["name"] for l in lets]
                in_type = [n for n in names if re.search(_WORD % re.escape(n), hv["type"])]
                if not in_type:
                    _why("t7:letc", S, steps[i].start, S.proof[steps[i].start:steps[i].start + 60], "no let occurs in the have's statement")
                    i = j + 1
                    continue
                later = S.code[steps[j].end:_block_end(blk)]
                used_later = [n for n in names if n not in in_type and re.search(_WORD % re.escape(n), later)]
                if used_later:
                    _why("t7:letc", S, steps[i].start, S.proof[steps[i].start:steps[i].start + 60],
                         f"{len(used_later)} let(s) outside the statement used after the have")
                    i = j + 1
                    continue
                if any(l["binders"] for l in lets):
                    _why("t7:letc", S, steps[i].start, S.proof[steps[i].start:steps[i].start + 60], "a let with binders (a local function)")
                    i = j + 1
                    continue
                out.append({"block": blk, "lets": lets, "in_type": in_type, "have": hv, "have_step": steps[j], "first": steps[i]})
                i = j + 1
                continue
            i += 1
    return out


def _strip_items(items: list[str], names: list[str]) -> list[str]:
    return [it for it in items if re.sub(r"^[←↓↑]\s*", "", it).strip() not in names]


def _proof_forms(S: Src, site: dict) -> list[tuple[str, str]]:
    """(P, label) alternatives for the have's value with hole witnesses; P closes `∀ binders, T` as a term."""
    hv, names = site["have"], [l["name"] for l in site["lets"]]
    bs = _binder_groups(hv["binders"])
    lam = ""
    if bs:
        lam = "λ " + " ".join(n for g in bs for n in g["names"]) + " => "
    V = hv["value"]
    out: list[tuple[str, str]] = []

    def add(p, lab):
        p = " ".join(p.split())
        if all(p != q for q, _ in out):
            out.append((lam + p, lab))
    uses_let = any(re.search(_WORD % re.escape(n), V) for n in names)
    m = re.match(r"by\s+simpa(\s+only)?\s*(?:\[(.*?)\])?\s+using\s+(.*)$", V, re.S)
    if m:
        only, L, X = bool(m.group(1)), split_items(m.group(2) or ""), " ".join(m.group(3).split())
        L2 = _strip_items(L, names)
        lemmas = [re.sub(r"^[←↓↑]\s*", "", it) for it in L2 if re.fullmatch(r"[^\W\d][\w'!?₀-₉.]*", re.sub(r"^[←↓↑]\s*", "", it))][:LETC_LEMMAS]
        xa = X if T5._atomic(X) else f"({X})"
        add(X, "X")
        for Lk in lemmas:
            add(f"{Lk} .. ▸ {X}", "L ▸ X")
            add(f"{xa}.trans ({Lk} ..)", "X.trans L")
            add(f"({Lk} .. ▸ {X}).trans ({Lk} ..)", "(L ▸ X).trans L")
            add(f"({Lk} ..).symm ▸ {X}", "L.symm ▸ X")
        if len(lemmas) >= 2:
            add(f"({lemmas[0]} .. ▸ {X}).trans ({lemmas[1]} ..)", "(L1 ▸ X).trans L2")
            add(f"({lemmas[1]} .. ▸ {X}).trans ({lemmas[0]} ..)", "(L2 ▸ X).trans L1")
        if L2:
            add(f"by rw [{', '.join(L2)}]; exact {X}", "rw; exact")
            add(f"by simpa{' only' if only else ''} [{', '.join(L2)}] using {X}", "simpa L'")
        else:
            add(f"by simpa using {X}", "simpa")
    elif V.startswith("by"):
        add(_drop_list_names(V, names), "by-block")
    else:
        if not uses_let:
            add(V, "term")
        else:
            add(V, "term (let names free)")
    return out


def _drop_list_names(v: str, names: list[str]) -> str:
    """The let names dropped from the simp / rw lists of a tactic text (unfold hints are meaningless once the lets are gone)."""
    for n in names:
        v = re.sub(r"(?<=[\[,])\s*" + re.escape(n) + r"\s*(?=[,\]])", "", v)
    v = re.sub(r"\[\s*,", "[", re.sub(r",\s*,", ",", re.sub(r",\s*\]", "]", v)))
    v = re.sub(r"\b(simp|dsimp|simp_all|simpa)\s+only\s*\[\s*\]", r"\1 only", v)
    return v


def letc_variants(S: Src, ctx: dict | None = None) -> list[dict]:
    out = []
    for site in letc_sites(S):
        blk, lets, hv = site["block"], site["lets"], site["have"]
        names = site["in_type"]
        a = S.line_start(site["first"].start)
        e = site["have_step"].end
        col = blk.col
        bs = _binder_groups(hv["binders"])
        later_names = set()
        quant = []
        for gi, g in enumerate(bs):
            tail = " ".join(x["text"] for x in bs[gi + 1:]) + " " + hv["type"]
            if g["kind"] == "bare":
                quant.append(("∀", g["text"]))
            elif g["kind"] == "(" and g["type"] and not any(re.search(_WORD % re.escape(n), tail) for n in g["names"]) and len(g["names"]) == 1:
                quant.append(("→", g["type"]))
            else:
                quant.append(("∀", g["text"]))
                                                                             
        stmt = hv["type"]
        parts = []
        i = len(quant) - 1
        body = stmt
        while i >= 0:
            kind, t = quant[i]
            if kind == "→":
                body = f"{t if T5._atomic(t) else '(' + t + ')'} → {body}"
            else:
                names_run = [t]
                while i - 1 >= 0 and quant[i - 1][0] == "∀":
                    i -= 1
                    names_run.insert(0, quant[i][1])
                body = f"∀ {' '.join(names_run)}, {body}"
            i -= 1
        del parts
        ex_plain = "∃ " + " ".join(names) + ", " + body
        typed = [l for l in lets if l["name"] in names and l["type"]]
        ex_typed = None
        if typed:
            ex_typed = "∃ " + " ".join(f"({l['name']} : {l['type']})" if l["type"] else l["name"] for l in lets if l["name"] in names) + ", " + body
        pat = "⟨" + ", ".join(names + [hv["name"]]) + "⟩"
        holes = ", ".join("_" for _ in names)
        forms = _proof_forms(S, site)
        for fi, (P, lab) in enumerate(forms):
            for ex, exlab in ((ex_plain, "holes"), (ex_typed, "typed")):
                if ex is None:
                    continue
                new = f"{' ' * col}obtain {pat} : {ex} := ⟨{holes}, {P}⟩"
                es = (Edit(a, e, new),)
                out.append({"op": "t7:letc", "group": f"letc@{a}", "edits": es, "tok": S.dtok(es),
                            "note": f"let-collapse {len(lets)} let(s) + have L{S.line(a) + 1} -> obtain ∃ ({exlab}; P {fi}: {lab})"})
                                                                                                      
        vals = {l["name"]: l["value"] for l in lets}
        def inline(v, depth=0):
            if depth > 6:
                return v
            for n, w in vals.items():
                if re.search(_WORD % re.escape(n), v):
                    v = re.sub(_WORD % re.escape(n), lambda m_: f"({inline(w, depth + 1)})", v)
            return v
        wit = [inline(vals[n]) for n in names]
        wtok = sum(count_tokens(w) for w in wit)
        if wtok <= LETC_EXPLICIT_TOKENS:
            V = _drop_list_names(hv["value"], [l["name"] for l in lets])
            lam = ("λ " + " ".join(n for g in bs for n in g["names"]) + " => ") if bs else ""
            new = f"{' ' * col}obtain {pat} : {ex_plain} := ⟨{', '.join(wit)}, {lam}{' '.join(V.split())}⟩"
            es = (Edit(a, e, new),)
            out.append({"op": "t7:letc", "group": f"letc@{a}", "edits": es, "tok": S.dtok(es),
                        "note": f"let-collapse {len(lets)} let(s) + have L{S.line(a) + 1} -> obtain ∃ (explicit witnesses, {wtok} tok)"})
        else:
            _why("t7:letc", S, a, S.proof[a:a + 60], "explicit-witness variant skipped: the let values are too long to inline (LETC_EXPLICIT_TOKENS)")
    return out


                                                                                                                                    
_QUAL_CACHE: dict = {}
_NS_RE = re.compile(r"^\s*(?:(namespace)\s+([\w'.₀-₉!?ₛₗ]+)|(section)(?:\s+[\w'.₀-₉!?]+)?|(noncomputable\s+section)(?:\s+[\w'.]+)?|(end)(?:\s+([\w'.₀-₉!?ₛₗ]+))?\s*$)")
_DECL_LINE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec|noncomputable|public)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+([^\s:({\[]+)")


def _env_root(ctx: dict | None, wb=None) -> Path | None:
    row = (ctx or {}).get("row") or getattr(wb, "row", None)
    version = (ctx or {}).get("pin") or getattr(wb, "version", None) or (((ctx or {}).get("pins") or [None])[0])
    if not isinstance(row, dict) or not version:
        return None
    try:
        from scorer.compile import project_env_dir, env_dir
        root = env_dir(version) if row.get("source") == "putnambench" else project_env_dir(row["source"], version)
        return Path(root) if Path(root).exists() else None
    except Exception:                
        return None


def _qualified(root: Path, seg: str) -> list[str]:
    """Fully qualified declared names whose last segment is `seg`, from the declaring files' namespace stacks (library-general)."""
    key = (str(root), seg)
    if key in _QUAL_CACHE:
        return _QUAL_CACHE[key]
    from harness.leantools import _name_index
    idx = _name_index(root)
    files = sorted({f for _, f in idx.get(seg, [])})[:12]
    out: list[str] = []
    for rel in files:
        try:
            lines = (root / rel).read_text(errors="replace").split("\n")
        except OSError:
            continue
        stack: list[str] = []                                  
        kinds: list[str] = []
        for ln in lines:
            m = _NS_RE.match(ln)
            if m:
                if m.group(1):
                    stack.append(m.group(2)); kinds.append("ns")
                elif m.group(3) or m.group(4):
                    stack.append(""); kinds.append("sec")
                elif m.group(5):
                    if stack:
                        stack.pop(); kinds.pop()
                continue
            d = _DECL_LINE.match(ln)
            if d:
                nm = d.group(1)
                if nm.split(".")[-1] != seg:
                    continue
                if nm.startswith("_root_."):
                    out.append(nm[len("_root_."):])
                    continue
                ns = ".".join(s for s in stack if s)
                out.append(f"{ns}.{nm}" if ns else nm)
    out = list(dict.fromkeys(out))
    _QUAL_CACHE[key] = out
    return out


def _struct_rank(ctx: dict | None, S: Src) -> dict:
    """Structure namespace -> rank: those the text names first, then by the bundled-hom table's namespace size (largest first)."""
    text = S.proof + "\n" + str((ctx or {}).get("prefix") or "")
    tbl = K.load_table("bundled_homs")
    sizes = {}
    for s, v in ((tbl.get("structures") or {}).items() if isinstance(tbl.get("structures"), dict) else []):
        sz = v.get("size") if isinstance(v, dict) else None
        sizes[s] = max((sz or {}).values(), default=0) if isinstance(sz, dict) else 0
    rank = {}
    for s in set(sizes) | set(re.findall(r"\b([A-Z][A-Za-z]+(?:Hom|Equiv|Map|Iso))\b", text)):
        rank[s] = (0 if re.search(_WORD % re.escape(s), text) else 1, -sizes.get(s, 0))
    return rank


def swap_variants(S: Src, ctx: dict | None = None, wb=None) -> list[dict]:
    out: list[dict] = []
    per_site: dict = {}
    _merge_sites(S, per_site)
    root = _env_root(ctx, wb)
    if root is None:
        _why("t7:swap", S, S.off0, "", "no environment root (ctx row / pin): name forms not generated")
        for span in sorted(per_site):
            out.extend(per_site[span])
        return out
    from harness.leantools import _name_index
    try:
        from harness.hb_rewrite import SPECIALIZE
    except Exception:                
        SPECIALIZE = {}
    idx = _name_index(root)
    if not idx:
        _why("t7:swap", S, S.off0, "", "empty name index")
        return out
    rank = _struct_rank(ctx, S)
    local = set(T5._locals(S)) if hasattr(T5, "_locals") else set()
    body0 = S.off0

    joint: dict = {}                                                                                                                  

    def add(span, rep, note, kind, ident=None, cap=SWAP_SITE_MAX):
        es = (Edit(span[0], span[1], rep),)
        lst = per_site.setdefault(span, [])
        if ident is not None:                                                                                            
            joint.setdefault((ident, kind), []).append((span, rep))
        if len(lst) >= cap or any(x["edits"][0].new == rep for x in lst):
            return
        lst.append({"op": "t7:swap", "group": f"swap@{span[0]}", "edits": es, "tok": S.dtok(es), "note": f"{kind}: {note}"})

                                                                                              
    occ = [(m.start(), m.end(), m.group(0), False) for m in IDENT.finditer(S.code)]
    occ += [(m.start(1), m.end(1), m.group(1), True) for m in re.finditer(r"(?<=[)\]⟩])\.(" + NAME + r")", S.code)]                  
    for i, j, w, dot in sorted(occ):
        if i < body0 or S.mask[i]:
            continue
        seg = w.split(".")[-1]
        if w.split(".")[0] in local or len(seg) < 3 or w in T5.KEYWORDS:
            continue
        span = (i, j)
        if seg not in idx:
            continue
        for suf in ("ₛₗ", "_of_tower"):
            if seg + suf in idx:
                add(span, w + suf, f"{w} -> {w + suf}", "form", ident=(seg, suf))
        if "." in w and not dot:
            q = _qualified(root, seg)
            if seg in q:
                add(span, seg, f"{w} -> {seg}", "dequalify", ident=(seg, ""))
                                                                                                       
    for blk, _par in _blocks(S):
        for st in blk.steps:
            h = _head(S, st)
            if h not in RW_HEADS and h not in SIMP_HEADS:
                continue
            seg_end = st.end
            if st.children:
                seg_end = min(seg_end, min(c.steps[0].start for c in st.children if c.steps))
            lb = S.code.find("[", st.start, seg_end)
            if lb < 0 or lb not in S.pairs:
                continue
            rb = S.pairs[lb]
            for a, e, it in T5._item_spans(S, lb, rb):
                core = re.sub(r"^[←↓↑]\s*", "", it).strip()
                if not re.fullmatch(r"[^\W\d][\w'!?₀-₉.]*", core) or core not in SPECIALIZE:
                    continue
                arrow = it[:len(it) - len(it.lstrip("←↓↑ "))]
                singles = list(SPECIALIZE[core][:SWAP_SPEC_SINGLES])
                for s_ in singles:
                    add((a, e), arrow + s_, f"{core} -> {s_}", "specialise", cap=SWAP_LIST_MAX)
                owners = [q for q in _qualified(root, core + "_of_tower") if "." in q]
                owners.sort(key=lambda q: rank.get(q.rsplit(".", 1)[0], (2, 0)) + (q.count("."), q))
                for s_ in singles:
                    for o in owners[:SWAP_PAIR_OWNERS]:
                        if o.rsplit(".", 1)[0] == s_.rsplit(".", 1)[0]:
                            continue
                        add((a, e), f"{arrow}{s_}, {arrow}{o}", f"{core} -> {s_} + {o}", "pair", cap=SWAP_LIST_MAX)
            if h in RW_HEADS:
                pass
    for (ident, kind), spans in joint.items():
        spans = sorted(dict(spans).items())
        if len(spans) < 2:
            continue
        es = tuple(Edit(a, e, rep) for (a, e), rep in spans)
        out.append({"op": "t7:swap", "group": f"swapall@{ident[0]}{ident[1]}", "edits": es, "tok": S.dtok(es),
                    "note": f"{kind} x{len(spans)}: {ident[0]} -> {ident[0] + ident[1] if ident[1] else 'unqualified'} at every occurrence"})
    for span in sorted(per_site):
        out.extend(per_site[span])
    if len(out) > SWAP_TOTAL:
        _why("t7:swap", S, S.off0, "", f"{len(out) - SWAP_TOTAL} swap variant(s) beyond SWAP_TOTAL dropped (lists first)")
        out = sorted(out, key=lambda c: (0 if c["note"].startswith(("pair", "specialise", "merge")) else 1))[:SWAP_TOTAL]
    return out


def _merge_sites(S: Src, per_site: dict) -> None:
    """(c) two consecutive rewrite-family steps of a block merged into one call."""
    for blk, _par in _blocks(S):
        for k in range(len(blk.steps) - 1):
            s1, s2 = blk.steps[k], blk.steps[k + 1]
            h1, h2 = _head(S, s1), _head(S, s2)
            if h1 not in ("rw", "rewrite", "erw") or h2 not in ("rw", "rewrite", "erw") or s1.children or s2.children:
                continue
            t1, t2 = S.code[s1.start:s1.end], S.code[s2.start:s2.end]
            if not re.fullmatch(r"\w+\s*\[.*\]\s*", t1, re.S) or not re.fullmatch(r"\w+\s*\[.*\]\s*", t2, re.S):
                continue                                      
            l1, l2 = S.code.find("[", s1.start), S.code.find("[", s2.start)
            if l1 not in S.pairs or l2 not in S.pairs or S.pairs[l1] != s1.end - 1 or S.pairs[l2] != s2.end - 1:
                continue
            head = "erw" if "erw" in (h1, h2) else ("rw" if "rw" in (h1, h2) else "rewrite")
            inner1, inner2 = S.proof[l1 + 1:S.pairs[l1]].strip(), S.proof[l2 + 1:S.pairs[l2]].strip()
            new = f"{head} [{inner1}, {inner2}]"
            es = (Edit(s1.start, s2.end, new),)
            per_site.setdefault((s1.start, s2.end), []).append({"op": "t7:swap", "group": f"merge@{s1.start}", "edits": es, "tok": S.dtok(es),
                                                               "note": f"merge: {h1} + {h2} -> {head} (L{S.line(s1.start) + 1})"})


                                                                                                                                     
def generate(proof: str, statement: str, ctx: dict | None = None, wb=None) -> dict:
    S = Src(proof, statement)
    gen = {"defer": [], "letc": [], "swap": [], "ok": S.ok and bool(S.tree)}
    if not S.ok:
        return gen | {"skip": "statement differs / no body"}
    if not S.tree:
        return gen | {"skip": "term-mode proof or unparsed tactic block"}
    ops = _ops(ctx)
    if "t7:defer" in ops:
        gen["defer"] = [c for c in defer_variants(S, ctx) if c["tok"] is not None]
    if "t7:letc" in ops:
        gen["letc"] = [c for c in letc_variants(S, ctx) if c["tok"] is not None]
    if "t7:swap" in ops:
        gen["swap"] = [c for c in swap_variants(S, ctx, wb) if c["tok"] is not None]
    gen["S"] = S
    return gen


def _timeout(ctx: dict | None) -> float:
    cs = (ctx or {}).get("compile_s")
    return max(MIN_TIMEOUT_S, TIMEOUT_MULT * float(cs) + 4.0) if isinstance(cs, (int, float)) else MIN_TIMEOUT_S * 3


def _gain(r: dict) -> bool:
    return r.get("status") == "ok" and ((r.get("d_score") or 0) > 0 or ((r.get("d_heartbeats") or 0) <= -HB_EPS and (r.get("d_score") or 0) >= 0))


def search(proof: str, statement: str, wb, *, meter_reading: dict | None = None, exchange=None, ctx: dict | None = None,
           stats: dict | None = None, log=None, deadline: float | None = None, max_checks: int = MAX_CHECKS, n_out: int = N_OUT,
           stage_caps: dict | None = None, trace: list | None = None) -> dict:
    t0 = time.time()
    st = stats if stats is not None else {}
    log = log or (lambda *a: None)
    for k_, v_ in (("sites", {}), ("variants", {}), ("readings", 0), ("compiled", 0), ("survivors", 0), ("skips", {}), ("errors", {}),
                   ("budget_out", False), ("searches", 0), ("best", {}), ("chain", {})):
        st.setdefault(k_, v_ if not isinstance(v_, dict) else dict(v_))
    st["searches"] += 1
    ctx = dict(ctx or {})
    ctx.setdefault("row", getattr(wb, "row", None))
    ctx.setdefault("pin", getattr(wb, "version", None))
    if "prefix" not in ctx:
        try:
            core = getattr(getattr(wb, "_lay", None), "core", None)
            if isinstance(core, str):
                ctx["prefix"] = core
        except Exception:                
            pass
    caps = dict(STAGE_CAPS)
    caps.update({k: v for k, v in (stage_caps or {}).items() if k in caps})
    _Why.cur = []
    try:
        gen = generate(proof, statement, ctx, wb)
    finally:
        why, _Why.cur = (_Why.cur or []), None
    for w in why:
        key = f"{w['op'][3:]}: {w['reason']}"
        st["skips"][key] = st["skips"].get(key, 0) + 1
    if gen.get("skip"):
        st["skips"][gen["skip"]] = st["skips"].get(gen["skip"], 0) + 1
        st["seconds"] = round(st.get("seconds", 0.0) + time.time() - t0, 2)
        return {}
    S = gen["S"]
    for op in ("defer", "letc", "swap"):
        st["sites"][op] = st["sites"].get(op, 0) + len({c["group"] for c in gen[op]})
        st["variants"][op] = st["variants"].get(op, 0) + len(gen[op])
    todo = []
    for op in ("letc", "defer", "swap"):
        cs = sorted(gen[op], key=lambda c: -(c["tok"] or 0))
        if len(cs) > caps[op]:
            st["skips"][f"{op}: variants beyond the stage cap"] = st["skips"].get(f"{op}: variants beyond the stage cap", 0) + len(cs) - caps[op]
        todo.extend(cs[:caps[op]])
    if not todo:
        st["seconds"] = round(st.get("seconds", 0.0) + time.time() - t0, 2)
        return {"t7_found": [], "t7_found_for": proof_key(proof)}
    dl = deadline if deadline is not None else time.time() + SEARCH_SECONDS
    scr = K.Screen(wb, proof, meter_reading=meter_reading, deadline=dl, max_checks=max_checks, timeout=_timeout(ctx), log=log)
    decls = []
    for c in todo:
        c["decl"] = S.decl(c["edits"])
        decls.append(c["decl"])
    rs = scr.read(decls)
    by = {}
    for c, r in zip(todo, rs):
        c["r"] = r
        if trace is not None:
            trace.append({"op": c["op"], "note": c["note"][:120], "status": r.get("status"), "error": str(r.get("error") or "")[:160],
                          "d_score": r.get("d_score"), "d_heartbeats": r.get("d_heartbeats"), "tokens": r.get("tokens")})
        if r.get("status") == "ok":
            cur = by.get(c["group"])
            if cur is None or (r.get("d_score") or 0) > (cur["r"].get("d_score") or 0):
                by[c["group"]] = c
    for c in todo:
        if "r" not in c:
            c["r"] = {"status": "unread"}
    for op in ("defer", "letc", "swap"):
        best = max((c["r"].get("d_score") or -9 for c in gen[op] if c.get("r", {}).get("status") == "ok"), default=None)
        if best is not None:
            st["best"][op] = round(max(best, st["best"].get(op, -9)), 4)
                                                        
    pool = sorted((c for c in by.values() if _gain(c["r"])), key=lambda c: -(c["r"].get("d_score") or 0))
    chain_info = {"pool": len(pool), "read": 0, "members": 0, "est": None}
    chain = None
    if len(pool) >= 2 and scr.left():
        cur_edits, cur_best, members = [], None, []
        for c in pool:
            if chain_info["read"] >= min(caps["chain"], CHAIN_CAP) or not scr.left():
                break
            es = list(cur_edits) + list(c["edits"])
            if any(not disjoint(x, y) for i, x in enumerate(es) for y in es[i + 1:]):
                continue
            if not members:                                     
                cur_edits, members, cur_best = list(c["edits"]), [c], c["r"]
                continue
            d = apply_edits(proof, es)
            r = scr.read([d])
            chain_info["read"] += 1
            if not r:
                break
            r = r[0]
            if trace is not None:
                trace.append({"op": "t7:chain", "note": "+" + c["note"][:100], "status": r.get("status"), "error": str(r.get("error") or "")[:160],
                              "d_score": r.get("d_score"), "d_heartbeats": r.get("d_heartbeats"), "tokens": r.get("tokens")})
            if r.get("status") == "ok" and (r.get("d_score") or -9) > (cur_best.get("d_score") or -9):
                cur_edits, cur_best, members = es, r, members + [c]
        if len(members) >= 2:
            chain = {"op": "t7:chain", "decl": apply_edits(proof, cur_edits), "r": cur_best, "members": members,
                     "note": "chain of " + " + ".join(m["op"][3:] for m in members) + ": " + "; ".join(m["note"][:50] for m in members)}
            chain_info.update(members=len(members), est=round(cur_best.get("d_score") or 0, 4))
    if (chain_info["est"] or -9) >= ((st["chain"] or {}).get("est") or -9) or not st["chain"]:
        st["chain"] = dict(chain_info, searches_with_chain=(st["chain"] or {}).get("searches_with_chain", 0) + (1 if chain else 0))
    else:
        st["chain"]["searches_with_chain"] = st["chain"].get("searches_with_chain", 0) + (1 if chain else 0)
               
    inc_tok = count_tokens(split_declaration(proof, statement) or "")
    inc_hb = (meter_reading or {}).get("heartbeats") or (scr.wb and None)
    inc_score = scr._inc_est
    found = []

    def passes(c):
        r = c["r"]
        if inc_score is None or r.get("score_exact") is None:
            return (r.get("d_score") or 0) > 0
        ok, _ = decide({"score": inc_score, "tokens": inc_tok, "heartbeats": inc_hb if inc_hb is not None else (r.get("heartbeats_est") or 0) - (r.get("d_heartbeats") or 0), "Z": 100.0},
                       {"score": r["score_exact"], "tokens": r.get("tokens"), "heartbeats": r.get("heartbeats_est"), "Z": 100.0})
        return ok
    if chain and passes(chain):
        found.append(chain)
    for c in sorted(by.values(), key=lambda c: -(c["r"].get("d_score") or 0)):
        if passes(c):
            found.append(c)
    out = []
    for c in found[:n_out]:
        r = c["r"]
        out.append({"op": c["op"], "decl": c["decl"], "note": c["note"][:260] + f"; est {r.get('d_score') or 0:+.3f}, hb {r.get('d_heartbeats') or 0:+d}",
                    "est": round(r.get("d_score") or 0, 6), "tokens": r.get("tokens"), "heartbeats_est": r.get("heartbeats_est")})
    for k_ in ("readings", "compiled", "timeouts", "calls"):
        st[k_] = st.get(k_, 0) + scr.stats[k_]
    st["budget_out"] = st["budget_out"] or scr.stats["budget_out"]
    for k_, v_ in scr.stats["errors"].items():
        st["errors"][k_] = st["errors"].get(k_, 0) + v_
    st["survivors"] += len(out)
    st["wb_seconds"] = round(st.get("wb_seconds", 0.0) + scr.stats["seconds"], 2)
    st["peak_rss_mb"] = getattr(wb, "peak_rss_mb", None)
    st["seconds"] = round(st.get("seconds", 0.0) + time.time() - t0, 2)
    log(f"t7: {len(out)} survivor(s) of {len(todo)} variant(s) ({sum(len(gen[o]) for o in ('defer', 'letc', 'swap'))} generated; "
        f"defer {len(gen['defer'])}, letc {len(gen['letc'])}, swap {len(gen['swap'])}), {scr.stats['compiled']} compiled, "
        f"chain {chain_info['members']} ({st['seconds']} s)")
    return {"t7_found": out, "t7_found_for": proof_key(proof)}


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = N_OUT, ctx: dict | None = None) -> list[dict]:
    ctx = ctx or {}
    if ctx.get("t7_found_for") == proof_key(proof) and isinstance(ctx.get("t7_found"), list):
        return [{"op": c.get("op") or "t7:chain", "decl": c["decl"], "note": str(c.get("note") or "")[:300]}
                for c in ctx["t7_found"][:max_per_op] if isinstance(c, dict) and isinstance(c.get("decl"), str) and c["decl"].strip() != proof.strip()]
    if ctx.get("t7_found_for") is not None:
        return []
    gen = generate(proof, statement, ctx)
    if gen.get("skip"):
        return []
    S = gen["S"]
    out = []
    for op in ("letc", "defer", "swap"):
        for c in sorted(gen[op], key=lambda c: -(c["tok"] or 0))[:FALLBACK_PER_OP]:
            out.append({"op": c["op"], "decl": S.decl(c["edits"]), "note": c["note"][:300]})
    return out


def explain(proof: str, statement: str, ctx: dict | None = None) -> dict:
    _Why.cur = []
    try:
        gen = generate(proof, statement, ctx)
    finally:
        why, _Why.cur = (_Why.cur or []), None
    if gen.get("skip"):
        return {"ok": False, "skip": gen["skip"], "skipped": why}
    S = gen["S"]
    return {"ok": True,
            "sites": {op: sorted({c["group"] for c in gen[op]}) for op in ("defer", "letc", "swap")},
            "n_variants": {op: len(gen[op]) for op in ("defer", "letc", "swap")},
            "variants": {op: [{"note": c["note"], "d_tokens": c["tok"]} for c in gen[op]] for op in ("defer", "letc", "swap")},
            "skipped": why, "tokens": S.tok0}


def main(argv=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(description="t7 defer / let-collapse / swaps: sites and variants without Lean")
    ap.add_argument("--file", required=True)
    ap.add_argument("--statement-file", required=True)
    ap.add_argument("--explain", action="store_true")
    ap.add_argument("--variants", action="store_true", help="print every variant's declaration as JSON lines")
    ap.add_argument("--source", default=None)
    ap.add_argument("--pin", default=None)
    a = ap.parse_args(argv)
    proof = Path(a.file).read_text()
    stmt = Path(a.statement_file).read_text().strip()
    ctx = {}
    if a.source and a.pin:
        ctx = {"row": {"source": a.source}, "pin": a.pin}
    if a.variants:
        gen = generate(proof, stmt, ctx)
        if gen.get("skip"):
            print(json.dumps({"skip": gen["skip"]}))
            return 0
        for op in ("defer", "letc", "swap"):
            for c in gen[op]:
                print(json.dumps({"op": c["op"], "note": c["note"], "d_tokens": c["tok"], "decl": gen["S"].decl(c["edits"])}, ensure_ascii=False))
        return 0
    print(json.dumps(explain(proof, stmt, ctx), ensure_ascii=False, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
