#!/usr/bin/env python3
"""T8 instance pin (b63, docs/adaptive_plan_93.md §4.1 item 10; B §3 "interleaved" row, T10 pretest): for every type-class binder a
































"""
from __future__ import annotations

import hashlib, re, time

from harness.tools import famkit as K

OPS = ("t8:pin", "t8:transp", "t8:bridge", "t8:stack")
_T_instances = K.load_table("instances")
_T_relations = K.load_table("relations")
TABLES = {                                                                                                         
    "instances": {"rule": _T_instances.get("rule", "missing: run harness/tools/tables/gen_relations.py"), "query": _T_instances.get("query", "python3 harness/tools/tables/gen_relations.py (inside a capped systemd unit)"),
            "generated_at": _T_instances.get("generated_at"), "path": "harness/tools/tables/instances.json"},
    "relations": {"rule": _T_relations.get("rule", "missing: run harness/tools/tables/gen_relations.py"), "query": _T_relations.get("query", "python3 harness/tools/tables/gen_relations.py (inside a capped systemd unit)"),
            "generated_at": _T_relations.get("generated_at"), "path": "harness/tools/tables/relations.json"},
}
TRANSP_WRAPS = ("with_reducible_and_instances", "with_reducible")
TRANSP_CLOSERS = ("assumption", "rfl", "trivial", "decide", "exact", "apply")
TRANSP_MAX_SITES = 12
BRIDGE_MAX = 16
BRIDGE_MAX_SITES = 3
JOINT_PINS = 4
STACK_READS = 4
BRIDGE_HEADS = {"Subtype", "Prod", "PProd", "Sigma", "PSigma", "And", "Exists", "Set.Elem", "Fin", "SetLike"}                             
                                                                                                                         
PER_BINDER = 12
MAX_BINDERS = 8
MAX_CANDIDATES = 96
DERIVED_MAX = 40
PINS_UNSCREENED = 4
SEARCH_SECONDS = 150.0
MAX_CHECKS = 160
N_OUT = 4
BAR = 0.02
MIN_HB_DROP = 0.05
MIN_TIMEOUT_S = 10.0
TIMEOUT_MULT = 4.0
CLASSICAL = {                                                                                                                
    "DecidableEq": ["Classical.decEq _"], "Decidable": ["Classical.propDecidable _"], "DecidablePred": ["Classical.decPred _"],
    "DecidableRel": ["Classical.decRel _"],
}


def proof_key(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def _tbl() -> dict:
    return K.load_table("instances")


def _in_env(rec: dict, source: str | None) -> bool:
    if not source:
        return True
    return any(f"/{source}-" in e for e in rec.get("envs") or [])


def _is_type_var(t: str) -> bool:
    """A bare identifier that reads as a type variable: no dot, and either not capitalised or at most two characters (`F`, `A`, `ι`, `𝔽`)."""
    return bool(re.fullmatch(r"[^\W\d][\w'!?₀-₉]*", t)) and "." not in t and (not t[:1].isupper() or len(t) <= 2)


def _class_of(bt: str) -> str | None:
    t = bt.strip()
    while t.startswith("(") and t.endswith(")"):
        t = t[1:-1].strip()
    m = re.match(r"^([A-Za-z_][\w'!?₀-₉.]*)(\s|$)", t)
    if not m or t.startswith(("∀", "Π", "fun")):
        return None
    return m.group(1)


def _prefix_variables(statement: str, ctx: dict | None) -> list[dict]:
    """Instance binders of `variable` lines in ctx["prefix"] (the file prefix, when the caller gives it) that mention an identifier of
"""
    pre = (ctx or {}).get("prefix")
    if not isinstance(pre, str) or not pre:
        return []
    ids = set(m.group(0) for m in K.IDENT.finditer(statement))
    out = []
    for m in re.finditer(r"(?m)^\s*variable\b(.*(?:\n[ \t]+.*)*)", pre):
        for a, b in K._groups(m.group(1)):
            g = m.group(1)[a:b]
            if g[0] != "[":
                continue
            inner = g[1:-1].strip()
            cp = [p for p, _ in K.depth0_positions(inner, [":"]) if not inner.startswith(":=", p)]
            bt = inner[cp[0] + 1:].strip() if cp and re.fullmatch(r"[\w'!?₀-₉\s]+", inner[:cp[0]]) else inner
            if set(K.IDENT.findall(bt)) - {_class_of(bt) or ""} & ids:
                out.append({"kind": "inst", "text": g, "name": None, "type": bt, "from": "variable"})
    return out


def binders(statement: str, ctx: dict | None = None) -> list[dict]:
    P = K.statement_parts(statement)
    if not P.get("ok"):
        return []
    out = [dict(b, **{"from": "statement"}) for b in P["binders"] if b["kind"] == "inst"]
    out += _prefix_variables(statement, ctx)
    seen, uniq = set(), []
    for b in out:
        c = _class_of(b["type"])
        if c is None or b["type"] in seen:
            continue
        seen.add(b["type"])
        uniq.append(dict(b, cls=c))
    return uniq[:MAX_BINDERS]


def present_classes(statement: str, ctx: dict | None, source: str | None) -> set:
    """The classes in scope for the statement: its own instance binders and the prefix `variable` ones, closed under the index's own

"""
    T = _tbl()
    present = {b["cls"] for b in binders(statement, ctx)}
    present |= {c.split(".")[-1] for c in present}
    edges: dict = {}
    for cls, recs in (T.get("classes") or {}).items():
        for r in recs:
            if r.get("carrier") == "var" and r.get("explicit", 0) == 0 and len(r.get("needs") or []) == 1 and _in_env(r, source):
                edges.setdefault(r["needs"][0], set()).add(cls)
                edges.setdefault(r["needs"][0].split(".")[-1], set()).add(cls)
    frontier = list(present)
    while frontier:
        c = frontier.pop()
        for d in edges.get(c, ()):
            if d not in present:
                present.add(d)
                present.add(d.split(".")[-1])
                frontier.append(d)
    return present


def pins_for(binder: dict, source: str | None, present: set | None = None) -> list[str]:
    """`letI` lines for one binder: named instances of its class whose carrier fits the binder (over any type, or the binder's type

"""
    T = _tbl()
    cls = binder["cls"]
    short = cls.split(".")[-1]
    recs = []
    for key in {cls, short} | {k for k in (T.get("classes") or {}) if k.split(".")[-1] == short}:
        recs += [r for r in (T.get("classes") or {}).get(key) or [] if _in_env(r, source) and r.get("explicit", 1) == 0]
    arg = binder["type"].split(" ", 1)[1].strip() if " " in binder["type"].strip() else ""
    while arg.startswith("(") and arg.endswith(")"):
        arg = arg[1:-1].strip()
    head = arg.split(" ", 1)[0] if arg else ""
    bare = " " not in arg and _is_type_var(head)
    carriers = {"var"} if bare or not head else {"var", head, head.split(".")[-1]}
    recs = [r for r in recs if r.get("carrier", "var") in carriers or r.get("carrier", "").split(".")[-1] in carriers]
    if present is not None:                                                                                                     
        recs = [r for r in recs if all(n in present or n.split(".")[-1] in present for n in (r.get("needs") or [])) and r["name"] != cls]
    recs.sort(key=lambda r: (0 if r.get("inst", 0) > 0 else 1, r.get("inst", 0), r.get("implicit", 0), len(r["name"]), r["name"]))
    names, seen = [], set()
    for r in recs:
        if r["name"] in seen or r["name"].endswith(("inferInstance", "inferInstanceAs")):
            continue
        seen.add(r["name"])
        names.append(r["name"])
        if len(names) >= PER_BINDER:
            break
    names += [c for c in CLASSICAL.get(short, []) if c not in names]
    return [f"letI : {binder['type']} := {n}" for n in names]


def derived_pins(statement: str, ctx: dict | None, source: str | None) -> list[tuple[str, str]]:
    """Pins for classes the statement does NOT bind but the proof's lemmas synthesize on the way (B §3: `[Nonempty F]` in 7 lemma


"""
    T = _tbl()
    classes = T.get("classes") or {}
    per_var: dict = {}
    for b in binders(statement, ctx):
        arg = b["type"].split(" ", 1)[1].strip() if " " in b["type"].strip() else ""
        if _is_type_var(arg):
            per_var.setdefault(arg, set()).add(b["cls"])
    edges: dict = {}
    for cls, recs in classes.items():
        for r in recs:
            if r.get("carrier") == "var" and r.get("explicit", 0) == 0 and len(r.get("needs") or []) == 1 and _in_env(r, source):
                edges.setdefault(r["needs"][0], set()).add(cls)
    out = []
    for var, bound in per_var.items():
        clo = set(bound) | {c.split(".")[-1] for c in bound}
        frontier = list(clo)
        while frontier:
            c = frontier.pop()
            for d in edges.get(c, ()):
                if d not in clo:
                    clo.add(d); clo.add(d.split(".")[-1]); frontier.append(d)
        cands = []
        for cls in clo - set(bound):                                                                         
            if "." not in cls and cls in {c.split(".")[-1] for c in clo if "." in c}:
                continue                                           
            for r in classes.get(cls) or []:
                needs = r.get("needs") or []
                                                                                                                                  
                if (r.get("carrier") == "var" and r.get("explicit", 0) == 0 and len(needs) == 1 and r.get("implicit", 0) == 1
                        and _in_env(r, source) and all(n in clo for n in needs)):
                    cands.append((len(needs), -len(classes.get(cls) or []), len(r["name"]), r["name"], cls))
        cands.sort()
        seen_cls = set()
        for _, _, _, name, cls in cands:
            if cls in seen_cls:
                continue
            seen_cls.add(cls)
            out.append((f"letI : {cls} {var} := {name}", f"derived for {var}"))
    out.sort(key=lambda t: -len(classes.get(t[0].split(" ")[2]) or []))                                                   
    return out[:DERIVED_MAX]



                                                                                                                                    
                                                                                                                      
                                                                                                                                    
_PLAIN = r"[^\W\d][\w'!?₀-₉]*"
_CTX_TAIL = re.compile(r"(?:^|.*?(?:<;>|(?<![\w'])(?:all_goals|any_goals|repeat'?|try|iterate\s+\d+|focus)|first\s*\||\||;|=>|·))\s*$", re.S)
_COMBI = re.compile(r"(?:<;>|(?<![\w'])(?:all_goals|any_goals|repeat'?|iterate\s+\d+))\s*(?:first\s*\|\s*|\(\s*)?$")


def _body_start(decl: str, statement: str) -> int | None:
    body = K.body_of(decl, statement)
    return None if body is None else len(decl) - len(body)


def _lines(decl: str, start: int) -> list[tuple[int, int, str]]:
    """(offset, end, text) of every line of decl[start:]."""
    out, pos = [], start
    for ln in decl[start:].split("\n"):
        out.append((pos, pos + len(ln), ln))
        pos += len(ln) + 1
    return out


def _balanced(t: str) -> bool:
    d = 0
    for c in t:
        if c in K.OPEN:
            d += 1
        elif c in K.CLOSE:
            d -= 1
            if d < 0:
                return False
    return d == 0


def _tactic_context(pre: str, line: str) -> bool:
    """`pre` (the line's text before the closer) ends where a tactic may start."""
    ps = pre.strip()
    if ps == "" or ps == "·":
        return True
    if not _CTX_TAIL.match(pre):
        return False
    if ps.endswith("=>"):                                                               
        return line.lstrip().startswith(("|", "case", "next")) and "fun" not in ps
    if ps.endswith("|") and not re.search(r"first\s*\|$", ps):
        return line.lstrip().startswith("|") or "first" in ps
    return True


def transp_sites(decl: str, statement: str) -> tuple[list[dict], dict]:
    """Closer sites: [{"start", "end", "seg", "closer", "combi", "line"}] and {reason: count} of the skipped occurrences."""
    bs = _body_start(decl, statement)
    skips: dict = {}
    if bs is None:
        return [], {"body not found": 1}
    sites = []
    pat = re.compile(r"(?<![\w'.])(" + "|".join(TRANSP_CLOSERS) + r")(?![\w'!?])")
    for off, end, ln in _lines(decl, bs):
        for m in pat.finditer(ln):
            pre = ln[:m.start()]
            if re.search(r"with_reducible(?:_and_instances)?\s*$", pre):
                skips["already reducible"] = skips.get("already reducible", 0) + 1
                continue
            if not _tactic_context(pre, ln):
                skips["closer not at a tactic position"] = skips.get("closer not at a tactic position", 0) + 1
                continue
            word = m.group(1)
            rest = ln[m.end():]
            if word in ("exact", "apply"):
                cut = len(rest)
                for pcut, sep in K.depth0_positions(rest, ["<;>", ";", "|"]):
                    cut = pcut
                    break
                dpt = 0
                for i, c in enumerate(rest[:cut]):                                                                    
                    if c in K.OPEN:
                        dpt += 1
                    elif c in K.CLOSE:
                        dpt -= 1
                        if dpt < 0:
                            cut = i
                            break
                seg = rest[:cut].rstrip()
                if not seg.strip():
                    skips["closer without a term"] = skips.get("closer without a term", 0) + 1
                    continue
                if not _balanced(seg):
                    skips["closer term spans several lines"] = skips.get("closer term spans several lines", 0) + 1
                    continue
                seg_full = word + seg
                span_end = off + m.end() + len(seg)
            else:
                if rest[:1] not in ("", " ", ")", ";", "\t") and not rest.startswith(("<;>", "|")):
                    skips["closer followed by arguments"] = skips.get("closer followed by arguments", 0) + 1
                    continue
                seg_full = word
                span_end = off + m.end()
            sites.append({"start": off + m.start(), "end": span_end, "seg": seg_full, "closer": word,
                          "combi": bool(_COMBI.search(pre)), "line": ln.strip()[:80]})
    if len(sites) > TRANSP_MAX_SITES:
        skips["closer sites beyond the cap"] = len(sites) - TRANSP_MAX_SITES
        sites = sites[:TRANSP_MAX_SITES]
    return sites, skips


def transp_variants(site: dict) -> list[tuple[str, str]]:
    """(replacement text, label) for one closer site."""
    seg = site["seg"]
    out = [(f"{w} {seg}", w) for w in TRANSP_WRAPS]
    if site["combi"]:
        out.append((f"first | with_reducible_and_instances {seg} | {seg}", "first|reducible|bare"))
    return out


def bridges_for(source: str | None) -> list[dict]:
    """The relation table's forall binder bridges with a structure binder on one side and its components on the other, available in the
"""
    T = K.load_table("relations")
    recs = [b for b in (T.get("binder_bridge") or []) if b.get("kind") == "forall" and _in_env(b, source)
            and (b.get("lhs") == "[anonymous]") != (b.get("rhs") == "[anonymous]")
            and (b.get("lhs") in BRIDGE_HEADS or b.get("rhs") in BRIDGE_HEADS)]
    recs.sort(key=lambda b: (-len(b.get("envs") or []), 0 if b.get("root") == "Init" else 1, len(b["thm"]), b["thm"]))
    seen, out = set(), []
    for b in recs:
        if b["thm"] in seen:
            continue
        seen.add(b["thm"])
        out.append({"thm": b["thm"], "struct_side": "lhs" if b.get("lhs") != "[anonymous]" else "rhs", "lhs": b.get("lhs"), "rhs": b.get("rhs")})
        if len(out) >= BRIDGE_MAX:
            break
    return out


def _args(term: str) -> list[str]:
    return [a for a in K.depth0_split(term.strip(), [" "]) if a]


def bridge_sites(decl: str, statement: str) -> tuple[list[dict], dict]:
    """`intro`/`rintro` line followed by a one-line `exact`/`apply` closer whose argument list ends with the introduced components:

"""
    bs = _body_start(decl, statement)
    skips: dict = {}
    if bs is None:
        return [], {"body not found": 1}
    L = _lines(decl, bs)
    sites = []
    for i, (off, end, ln) in enumerate(L):
        m = re.match(r"^(\s*)(intro|rintro)\s+(.+?)\s*$", ln)
        if not m:
            continue
        if i + 1 >= len(L):
            skips["intro at the end of the proof"] = skips.get("intro at the end of the proof", 0) + 1
            continue
        off2, end2, ln2 = L[i + 1]
        m2 = re.match(r"^(\s*)(exact|apply)\s+(.+?)\s*$", ln2)
        if not m2 or len(m2.group(1)) != len(m.group(1)):
            skips["intro not followed by a one-line closer"] = skips.get("intro not followed by a one-line closer", 0) + 1
            continue
        if not _balanced(m2.group(3)):
            skips["closer term spans several lines"] = skips.get("closer term spans several lines", 0) + 1
            continue
        pat = m.group(3).strip()
        args = _args(m2.group(3))
        T = None
        two = re.fullmatch(r"(" + _PLAIN + r")\s+(" + _PLAIN + r")", pat)
        one = re.fullmatch(_PLAIN, pat)
        anon = re.fullmatch(r"⟨\s*(" + _PLAIN + r")\s*,\s*(" + _PLAIN + r")\s*⟩", pat)
        if two and m.group(2) == "intro" and args and re.fullmatch(r"⟨\s*" + re.escape(two.group(1)) + r"\s*,\s*" + re.escape(two.group(2)) + r"\s*⟩", args[-1]):
            T, d, shape = args[:-1], ".1", "intro a h; exact T ⟨a, h⟩"
        elif anon and len(args) >= 3 and args[-2:] == [anon.group(1), anon.group(2)]:
            T, d, shape = args[:-2], ".2", "rintro ⟨a, h⟩; exact T a h"
        elif one and len(args) >= 3 and args[-2:] in ([f"{pat}.1", f"{pat}.2"], [f"{pat}.val", f"{pat}.property"]):
            T, d, shape = args[:-2], ".2", "intro x; exact T x.1 x.2"
        if not T:
            skips["intro/closer pair not a binder-bridge shape"] = skips.get("intro/closer pair not a binder-bridge shape", 0) + 1
            continue
        sites.append({"start": off, "end": end2, "indent": m.group(1), "T": " ".join(T), "dir": d, "shape": shape, "line": ln.strip()[:60]})
    if len(sites) > BRIDGE_MAX_SITES:
        skips["bridge sites beyond the cap"] = len(sites) - BRIDGE_MAX_SITES
        sites = sites[:BRIDGE_MAX_SITES]
    return sites, skips


def bridge_variants(site: dict, source: str | None) -> list[tuple[str, str]]:
    """(replacement text for the two lines, label): every bridge in the site's direction, the other direction for the first few."""
    out = []
    T = site["T"]
    for k, b in enumerate(bridges_for(source)):
        d0 = site["dir"] if b["struct_side"] == "lhs" else (".2" if site["dir"] == ".1" else ".1")                                                 
        dirs = [d0] + ([".2" if d0 == ".1" else ".1"] if k < 4 else [])
        for d in dirs:
            term = f"{b['thm']}{d} $ {T}" if " " in T else f"{b['thm']}{d} {T}"
            out.append((f"{site['indent']}exact {term}", f"{b['thm']}{d}"))
    return out


def apply_edits(decl: str, edits: list[dict]) -> str:
    """Replace each edit's [start, end) by its "text"; edits must not overlap."""
    out = decl
    for e in sorted(edits, key=lambda e: -e["start"]):
        out = out[:e["start"]] + e["text"] + out[e["end"]:]
    return out


def _overlap(a: dict, b: dict) -> bool:
    return not (a["end"] <= b["start"] or b["end"] <= a["start"])


def replace_classical(decl: str, statement: str, line: str) -> str | None:
    """The declaration with its leading `classical` tactic replaced by `line`, or None when the proof does not start with one."""
    bs = _body_start(decl, statement)
    if bs is None:
        return None
    m = re.match(r"(\s*:=)?\s*by[ \t]*\n?([ \t]*)classical[ \t]*(?=\n|$)", decl[bs:])
    if not m:
        return None
    a, b = bs + m.start(0) + m.group(0).rindex("classical"), bs + m.end(0)
    return decl[:a] + line + decl[b:]


def has_classical(decl: str, statement: str) -> bool:
    bs = _body_start(decl, statement)
    return bs is not None and re.match(r"(\s*:=)?\s*by[ \t]*\n?[ \t]*classical[ \t]*(?=\n|$)", decl[bs:]) is not None


def generate(proof: str, statement: str, *, ctx: dict | None = None) -> list[dict]:
    """[{"op", "decl", "note", "binder"}] pure: one candidate per (binder, instance), the pin inserted as the first tactic; then the
"""
    source = (ctx or {}).get("source")
    out, seen = [], {proof.strip()}
    present = present_classes(statement, ctx, source)
    items = [(line, b["from"], b["type"]) for b in binders(statement, ctx) for line in pins_for(b, source, present)]
    items += [(line, why, line.split(":=")[0][7:].strip()) for line, why in derived_pins(statement, ctx, source)]
    classical = has_classical(proof, statement)
    for line, why, btype in items:
        forms = [("insert", K.first_tactic_insert(proof, statement, line))]
        if classical:                                                                                                
            forms.insert(0, ("replace classical", replace_classical(proof, statement, line)))
        for how, d in forms:
            if d is None or d.strip() in seen:
                continue
            seen.add(d.strip())
            out.append({"op": "t8:pin", "decl": d, "note": f"{line[:120]} ({why}; {how})", "binder": btype, "line": line, "how": how})
        if len(out) >= MAX_CANDIDATES:
            break
    return out


def _timeout(ctx: dict | None) -> float:
    cs = (ctx or {}).get("compile_s")
    return max(MIN_TIMEOUT_S, TIMEOUT_MULT * float(cs) + 4.0) if isinstance(cs, (int, float)) else MIN_TIMEOUT_S * 3


def _bump(d: dict, k: str, n: int = 1) -> None:
    d[k] = d.get(k, 0) + n


def _op_stats(st: dict, op: str) -> dict:
    return st.setdefault("ops", {}).setdefault(op, {"sites": 0, "variants": 0, "compiled": 0, "survivors": 0})


def _survivor(r: dict, c: dict, inc_hb_warm: int | None) -> dict | None:
    """The found-entry for an ok reading that clears the bar (estimated score > BAR, or a heartbeat drop >= MIN_HB_DROP with a positive
"""
    if r.get("status") != "ok":
        return None
    dhb = r.get("d_heartbeats") or 0
    hb_warm = (r.get("heartbeats") or 0) - dhb
    drop = (-dhb / hb_warm) if hb_warm else 0.0
    est = r.get("d_score") or 0.0
    if est > BAR or (drop >= MIN_HB_DROP and est > 0):                                                                                             
        return {"op": c["op"], "decl": c["decl"], "note": c["note"] + f"; hb {dhb:+d} ({drop:+.1%}); est {est:+.3f}", "est": est,
                "hb_drop": round(drop, 4), "tokens": r.get("tokens"), "heartbeats_est": r.get("heartbeats_est"),
                "edits": c.get("edits"), "line": c.get("line"), "how": c.get("how")}
    return None


def search(proof: str, statement: str, wb, *, meter_reading: dict | None = None, exchange=None, ctx: dict | None = None,
           stats: dict | None = None, log=None, deadline: float | None = None, max_checks: int = MAX_CHECKS, n_out: int = N_OUT,
           stage_caps: dict | None = None, trace: list | None = None) -> dict:
    t0 = time.time()
    st = stats if stats is not None else {}
    log = log or (lambda *a: None)
    for k_, v_ in (("sites", 0), ("variants", 0), ("readings", 0), ("compiled", 0), ("survivors", 0), ("skips", {}), ("errors", {}),
                   ("budget_out", False), ("searches", 0), ("ops", {}), ("stack", {"read": 0, "better": 0})):
        st.setdefault(k_, v_ if not isinstance(v_, dict) else dict(v_))
    st["searches"] += 1
    ctx = dict(ctx or {})
    ctx.setdefault("source", (getattr(wb, "row", None) or {}).get("source"))
    source = ctx.get("source")
    if "prefix" not in ctx:
        try:                                                                                         
            lay = getattr(wb, "_lay", None)
            core = getattr(lay, "core", None)
            if isinstance(core, str):
                ctx["prefix"] = core
        except Exception:                
            pass
                                                                                                                               
    bs = binders(statement, ctx)
    st["binders"] = [b["type"][:60] for b in bs]
    pins = generate(proof, statement, ctx=ctx) if bs else []
    if not bs:
        _bump(st["skips"], "no instance binder")
    elif not pins:
        _bump(st["skips"], "no named instance for the binders' classes")
    tsites, tsk = transp_sites(proof, statement)
    bsites, bsk = bridge_sites(proof, statement)
    for k_, v_ in list(tsk.items()) + list(bsk.items()):
        _bump(st["skips"], k_, v_)
    if not tsites:
        _bump(st["skips"], "no closer site")
    if not bsites:
        _bump(st["skips"], "no intro/closer bridge site")
    tcands = []
    for i, site in enumerate(tsites):
        for text, lab in transp_variants(site):
            e = {"start": site["start"], "end": site["end"], "text": text}
            tcands.append({"op": "t8:transp", "decl": apply_edits(proof, [e]), "note": f"{lab} @ `{site['line'][:50]}`", "edits": [e], "site": i})
    bcands = []
    brs = bridges_for(source) if bsites else []
    if bsites and not brs:
        _bump(st["skips"], "no binder bridge in the row's environment")
    for i, site in enumerate(bsites):
        for text, lab in bridge_variants(site, source):
            e = {"start": site["start"], "end": site["end"], "text": text}
            bcands.append({"op": "t8:bridge", "decl": apply_edits(proof, [e]), "note": f"{lab} ({site['shape']})", "edits": [e], "site": i})
    for op, nsites, cands in (("t8:pin", len(bs), pins), ("t8:transp", len(tsites), tcands), ("t8:bridge", len(bsites), bcands)):
        o = _op_stats(st, op)
        o["sites"] = max(o["sites"], nsites)
        o["variants"] += len(cands)
    st["sites"] = max(st["sites"], len(bs) + len(tsites) + len(bsites))
    st["variants"] += len(pins) + len(tcands) + len(bcands)
    st["site_lines"] = {"transp": [x["line"] for x in tsites][:12], "bridge": [x["shape"] for x in bsites]}
    if not (pins or tcands or bcands):
        st["seconds"] = round(time.time() - t0, 2)
        return {}
    dl = deadline if deadline is not None else time.time() + SEARCH_SECONDS
    scr = K.Screen(wb, proof, meter_reading=meter_reading, deadline=dl, max_checks=max_checks, timeout=_timeout(ctx), log=log)
    found: list = []
    compiled_pins: list = []

    def read(cands: list[dict]) -> list[dict]:
        """Read candidates on the workbench; survivors appended to `found`; returns the readings paired with their candidates."""
        if not cands or not scr.left():
            return []
        rs = scr.read([c["decl"] for c in cands])
        by = {c["decl"]: c for c in cands}
        out = []
        for r in rs:
            c = by[r["decl"]]
            out.append((r, c))
            if trace is not None:
                trace.append({"op": c["op"], "src": c["note"], "status": r.get("status"), "error": str(r.get("error") or "")[:160],
                              "d_score": r.get("d_score"), "d_heartbeats": r.get("d_heartbeats")})
            o = _op_stats(st, c["op"])
            if r.get("status") == "ok":
                o["compiled"] += 1
                st.setdefault("compiled_readings", [])
                if len(st["compiled_readings"]) < 32:                                                  
                    st["compiled_readings"].append({"op": c["op"], "note": c["note"][:80], "d_hb": r.get("d_heartbeats"),
                                                    "d_score": r.get("d_score"), "tokens": r.get("tokens")})
            f = _survivor(r, c, None)
            if f is not None:
                o["survivors"] += 1
                found.append(f)
        return out

                   
    for r, c in read(pins):
        if r.get("status") == "ok":
            compiled_pins.append((r.get("d_heartbeats") or 0, c))
    compiled_pins.sort(key=lambda t: t[0])
                                              
    read(tcands)
                                                                                                                            
    bread = read(bcands)
    if bcands:
        joint_pins = [c for c in pins if c.get("how") == "replace classical"][:2]
        joint_pins += [c for _, c in compiled_pins if c not in joint_pins]
        joint_pins = joint_pins[:JOINT_PINS]
        jc = []
        for _, bc in bread[:6]:
            for pc in joint_pins:
                d = replace_classical(bc["decl"], statement, pc["line"]) if pc.get("how") == "replace classical" else K.first_tactic_insert(bc["decl"], statement, pc["line"])
                if d:
                    jc.append({"op": "t8:bridge", "decl": d, "note": f"{bc['note']} + {pc['line'][:60]} ({pc['how']})", "edits": bc["edits"],
                               "line": pc["line"], "how": pc["how"]})
        _op_stats(st, "t8:bridge")["variants"] += len(jc)
        st["variants"] += len(jc)
        read(jc)
                                                                                                                                         
    best_single = max((f["est"] for f in found), default=None)
    per_site: dict = {}
    for f in found:
        if f.get("edits") and f["op"] in ("t8:transp", "t8:bridge") and not f.get("line"):
            key = (f["edits"][0]["start"], f["edits"][0]["end"])
            if key not in per_site or f["est"] > per_site[key]["est"]:
                per_site[key] = f
    chosen: list = []
    for f in sorted(per_site.values(), key=lambda f: -f["est"]):
        if all(not _overlap(f["edits"][0], g["edits"][0]) for g in chosen):
            chosen.append(f)
    pin_best = next((f for f in sorted(found, key=lambda f: -f["est"]) if f["op"] == "t8:pin"), None)
    stacks = []
    if len(chosen) >= 2:
        edits = [f["edits"][0] for f in chosen]
        stacks.append({"op": "t8:stack", "decl": apply_edits(proof, edits), "note": f"stack of {len(chosen)} closer/bridge edits", "edits": edits})
    if chosen and pin_best is not None:
        edits = [f["edits"][0] for f in chosen]
        base = apply_edits(proof, edits)
        d = replace_classical(base, statement, pin_best["line"]) if pin_best.get("how") == "replace classical" else K.first_tactic_insert(base, statement, pin_best["line"])
        if d:
            stacks.append({"op": "t8:stack", "decl": d, "note": f"stack of {len(chosen)} edit(s) + {pin_best['line'][:60]}", "edits": edits,
                           "line": pin_best["line"], "how": pin_best["how"]})
    if len(compiled_pins) >= 2 and pin_best is not None:                                                                        
        second = next((c for _, c in compiled_pins if c["line"] != pin_best["line"]), None)
        if second is not None:
            d = K.first_tactic_insert(pin_best["decl"], statement, second["line"])
            if d:
                stacks.append({"op": "t8:stack", "decl": d, "note": f"{pin_best['line'][:50]} + {second['line'][:50]}", "line": pin_best["line"], "how": pin_best["how"]})
    stacks = stacks[:STACK_READS]
    if stacks:
        _op_stats(st, "t8:stack")["variants"] += len(stacks)
        st["variants"] += len(stacks)
        st["stack"]["read"] += len(stacks)
        n_before = len(found)
        read(stacks)
        st["stack"]["better"] += sum(1 for f in found[n_before:] if best_single is None or f["est"] > best_single)
    found.sort(key=lambda c: (-c["est"], -c["hb_drop"]))
    for k_ in ("readings", "compiled", "timeouts", "calls"):
        st[k_] = st.get(k_, 0) + scr.stats[k_]
    st["budget_out"] = st["budget_out"] or scr.stats["budget_out"]
    for k_, v_ in scr.stats["errors"].items():
        st["errors"][k_] = st["errors"].get(k_, 0) + v_
    st["survivors"] += len(found)
    best = max((c["hb_drop"] for c in found), default=None)
    st["best_hb_drop"] = max(st.get("best_hb_drop") or 0, best) if best is not None else st.get("best_hb_drop")
    st["best_est"] = max(st.get("best_est") or 0, max((c["est"] for c in found), default=0))
    st["survivor_ops"] = {op: sum(1 for f in found if f["op"] == op) for op in OPS if any(f["op"] == op for f in found)}
    st["wb_seconds"] = round(scr.stats["seconds"], 2)
    st["peak_rss_mb"] = getattr(wb, "peak_rss_mb", None)
    st["seconds"] = round(time.time() - t0, 2)
    log(f"t8: {len(found)} survivor(s) of {len(pins)} pin(s) / {len(tcands)} closer variant(s) / {len(bcands)} bridge variant(s) on "
        f"{len(bs)}+{len(tsites)}+{len(bsites)} site(s), {scr.stats['compiled']} compiled ({st['seconds']} s)")
    out = [{k: v for k, v in f.items() if k != "edits"} for f in found[:n_out]]
    return {"t8_found": out, "t8_found_for": proof_key(proof)}                                           


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = N_OUT, ctx: dict | None = None) -> list[dict]:
    ctx = ctx or {}
    if ctx.get("t8_found_for") == proof_key(proof) and isinstance(ctx.get("t8_found"), list):
        return [{"op": c.get("op") or "t8:pin", "decl": c["decl"], "note": str(c.get("note") or "")[:300]}
                for c in ctx["t8_found"][:max_per_op] if isinstance(c, dict) and isinstance(c.get("decl"), str) and c["decl"].strip() != proof.strip()]
    if ctx.get("t8_found_for") is not None:
        return []
    out = [{"op": c["op"], "decl": c["decl"], "note": c["note"]} for c in generate(proof, statement, ctx=ctx)[:PINS_UNSCREENED]]
    sites, _ = transp_sites(proof, statement)
    for site in sites[:PINS_UNSCREENED]:
        text, lab = transp_variants(site)[0]
        out.append({"op": "t8:transp", "decl": apply_edits(proof, [{"start": site["start"], "end": site["end"], "text": text}]),
                    "note": f"{lab} @ `{site['line'][:50]}`"})
    return out


def explain(proof: str, statement: str, ctx: dict | None = None) -> dict:
    """Sites generated and every skipped construct with its reason (no Lean): pin binders with their candidate counts, closer sites
"""
    bs = binders(statement, ctx)
    source = (ctx or {}).get("source")
    present = present_classes(statement, ctx, source)
    per = {b["type"]: pins_for(b, source, present) for b in bs}
    derived = derived_pins(statement, ctx, source) if bs else []
    tsites, tsk = transp_sites(proof, statement)
    bsites, bsk = bridge_sites(proof, statement)
    brs = bridges_for(source) if bsites else []
    skips = dict(tsk)
    for k, v in bsk.items():
        skips[k] = skips.get(k, 0) + v
    if not bs:
        skips["no instance binder"] = 1
    if bsites and not brs:
        skips["no binder bridge in the row's environment"] = 1
    n_pin = sum(len(v) for v in per.values()) + len(derived)
    n_tr = sum(len(transp_variants(x)) for x in tsites)
    n_br = len(bsites) * sum(2 if k < 4 else 1 for k in range(len(brs)))
    return {"ok": True, "fire": bool(n_pin or n_tr or n_br),
            "binders": [{"type": b["type"], "cls": b["cls"], "from": b["from"], "pins": len(per[b["type"]])} for b in bs],
            "derived_pins": len(derived), "classical": has_classical(proof, statement),
            "closer_sites": [{"closer": x["closer"], "combi": x["combi"], "variants": len(transp_variants(x))} for x in tsites],
            "bridge_sites": [{"shape": x["shape"], "dir": x["dir"], "bridges": len(brs)} for x in bsites],
            "n_candidates": n_pin + n_tr + n_br, "per_op": {"t8:pin": n_pin, "t8:transp": n_tr, "t8:bridge": n_br},
            "skips": skips, "first": (per[bs[0]["type"]] or [None])[0] if bs else None}
