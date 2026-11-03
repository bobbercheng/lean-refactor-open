#!/usr/bin/env python3
"""Measurement-range settings of the open-track re-derivation (docs/open_tools_rederive.md 2.4): the wide caps, the R4 (a) tables built















"""
from __future__ import annotations

import hashlib, json, re, threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TABLES = ROOT / "harness/tools/tables"
FULL_PROJECTIONS = ROOT / "probe/open_rederive/tables/projections_full.json"

WIDE = {
    "harness.sweep": {"MAX_PER_OP": 80},
    "harness.hb_rewrite": {"SPEC_CAP": 8, "PREORDER_CAP": 16, "CLEAR_CAP": 8, "VARIANT_CAP": 12, "VARIANT_SITES": 80, "MAX_COMPILES": 48},
    "harness.hb_polish": {"MAX_COMPILES": 24},
    "harness.tools.t1_compress": {"MAX_PER_OP": 80, "PER_SITE": 4, "PAIR_TOP": 16, "MAX_USES": 6},
    "harness.tools.t2_schedule": {"MAX_PER_OP": 80, "SITE_CAP": 300, "MAX_ROT": 24, "MAX_EITHER": 8},
    "harness.tools.t3_reclose": {"TOP_SPANS": 40, "MAX_SUFFIX": 8, "D2_TOTAL": 400, "MAX_OWN_TOKENS": 32},
    "harness.tools.t3_suggest": {"PROBE_K": 20, "PROBE_MAX_FILES": 4, "PROBE_EXTRA_S": 40, "PROBE_HB_SEARCH": 40000},
    "harness.tools.t4_nameless": {"MAX_PER_OP": 80, "PROBE_MAX_SITES": 24, "PROBE_MAX_FILES": 4},
}
WIDE_MAX_PER_OP = 80
GR_WIDE_FACTOR = 2                              

                                                                                                                                          
OLD_ADDWR_HEADS = ("apply", "exact", "assumption", "constructor", "econstructor", "rcases", "cases", "simp", "refine", "use", "exists",
                   "rewrite", "rw", "rwa", "intro", "obtain", "induction", "any_goals", "all_goals")
OLD_AUTO = ("grind", "simp_all", "aesop", "linarith", "nlinarith", "positivity", "tauto", "omega", "norm_num", "solve_by_elim", "field_simp",
            "simpa", "polyrith", "bound")
OLD_HP_HEADS = ("simp_all", "simpa", "simp", "dsimp", "grind")
_IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!]*$")
_LOCK = threading.RLock()
_APPLIED: dict | None = None


def _load(p: Path) -> dict:
    try:
        return json.loads(Path(p).read_text())
    except (OSError, ValueError):
        return {}


def r4a() -> dict:
    """The R4 (a) tables from the Lean-generated files (t2_closers.json `present`: Lean core's tactic token table on every installed core

"""
    t2 = _load(TABLES / "t2_closers.json")
    cl = _load(TABLES / "closers.json")
    present = list((t2.get("present") or {}).keys())
    out: dict = {}
                                                                                                                            
    heads = [w for w in present if _IDENT.match(w) and not w.endswith("!")]
    out["addwr_heads"] = [(w, "lean") for w in heads] + [(w, "old") for w in OLD_ADDWR_HEADS if w not in heads]
                                                                               
    auto = []
    for sc in ("core", "mathlib"):
        for c in ((cl.get("scopes") or {}).get(sc) or {}).get("closers") or []:
            if c.get("cost") == "expensive" and _IDENT.match(c.get("tactic") or "") and c["tactic"] not in auto:
                auto.append(c["tactic"])
    out["auto"] = [(w, "lean") for w in auto] + [(w, "old") for w in OLD_AUTO if w not in auto]
                                                                          
    qh = [w[:-1] for w in present if w.endswith("?") and _IDENT.match(w[:-1])]
    out["hp_heads"] = [(w, "lean") for w in qh] + [(w, "old") for w in OLD_HP_HEADS if w not in qh]
                                                                                                                                   
    from harness import gap_rules as GR
    out["single_closers"], out["multi_closers"] = {}, {}
    for sc in ("core", "mathlib"):
        S = (cl.get("scopes") or {}).get(sc) or {}
        singles = [c["tactic"] for c in S.get("closers") or [] if c.get("tactic")]
        multis = [f"{p['t1']} <;> {p['t2']}" for p in S.get("pairs") or [] if p.get("t1") and p.get("t2")]
        multis += [f"all_goals {c}" for c in singles]
        out["single_closers"][sc] = [(c, "lean") for c in singles] + [(c, "old") for c in GR.SINGLE_CLOSERS if c not in singles]
        out["multi_closers"][sc] = [(c, "lean") for c in dict.fromkeys(multis)] + [(c, "old") for c in GR.MULTI_CLOSERS if c not in multis]
    return out


def scope_of(row_or_source) -> str:
    """T3's scope rule (harness/tools/t3_reclose._scope by source): strata rows are core, every other source imports Mathlib."""
    src = row_or_source.get("source") if isinstance(row_or_source, dict) else row_or_source
    return "core" if src == "strata" else "mathlib"


def gr_closers(scope: str, tabs: dict | None = None) -> tuple:
    """gap_rules CLOSERS for a scope under R4 (a): singles and multis interleaved the way gap_rules interleaves its own lists."""
    t = tabs or r4a()
    s = [c for c, _ in t["single_closers"][scope]]
    m = [c for c, _ in t["multi_closers"][scope]]
    return tuple(c for pair in zip(s, m) for c in pair) + tuple(s[len(m):]) + tuple(m[len(s):])


                                                                                                                                         
_BINDER = re.compile(r"[(\{⦃]([^():{}⦃⦄]+?):")
_NAME = re.compile(r"(?<![\w.'₀-₉])([^\W\d][\w'₀-₉]*)(?![\w'₀-₉])")
_HEADS_BIND = re.compile(r"^\s*(?:·\s*)?(intro|intros|rintro|obtain|rcases|have|haveI|cases|induction|choose|set)\b(.*)$")
_KW = {"with", "at", "using", "only", "fun", "by", "this", "_", "rfl", "from", "show", "generalizing", "in", "if", "then", "else"}


def structural_names(stmt_head: str, line: str | None = None) -> list[str]:
    """Names bound by the statement's binders (stmt_head) or, with `line`, by that intro / obtain / rcases / have / cases line."""
    out = []
    if line is None:
        for m in _BINDER.finditer(stmt_head):
            out += [n for n in m.group(1).split() if _NAME.fullmatch(n) and n not in _KW]
        return list(dict.fromkeys(out))
    m = _HEADS_BIND.match(line)
    if not m:
        return []
    head, rest = m.group(1), m.group(2)
    if head in ("have", "haveI", "set"):
        mm = re.match(r"\s*([^\W\d][\w'₀-₉]*)", rest)
        return [mm.group(1)] if mm and mm.group(1) not in _KW else []
    if head in ("obtain",):
        rest = rest.split(":=", 1)[0]
    elif head in ("rcases", "cases", "induction"):
        rest = rest.split("with", 1)[1] if "with" in rest else ""
    return [n for n in dict.fromkeys(_NAME.findall(rest)) if n not in _KW]


def _structural_clearhyp(HR):
    """hb_rewrite._clearhyp with T31's structural rule in place of the h/H naming rule (same sites, same caps, same edit)."""
    def clearhyp(body, mask, pairs, fb):
        if fb < 0:
            return []
        out = []
        stmt = structural_names(body[:fb])
        lines = body.split("\n"); starts = []; pos = 0
        for ln in lines:
            starts.append(pos); pos += len(ln) + 1
        ind = [len(ln) - len(ln.lstrip()) if ln.strip() else None for ln in lines]
        intros = []
        for li, ln in enumerate(lines):
            if starts[li] <= fb or ind[li] is None:
                continue
            names = structural_names("", ln)
            if not names:
                continue
            bul = re.match(r"\s*·\s*", ln)
            eff = bul.end() if bul else ind[li]
            intros += [(n, li, eff) for n in names]
        for m in HR.AUTO_RE.finditer(body):
            i = m.start()
            if mask[i] or i <= fb or not HR._tac_pos(body, mask, i, fb):
                continue
            li = body.count("\n", 0, i); ls = starts[li]
            if body[ls:i].strip():
                continue
            d = ind[li]
            later = set(_NAME.findall(body[i:]))
            cands = []
            for name, il, idt in reversed(intros):
                if il < li and idt <= d and all(ind[j] is None or ind[j] >= idt for j in range(il + 1, li + 1)) and name not in later \
                        and name not in cands:
                    cands.append(name)
            cands += [n for n in stmt if n not in later and n not in cands]
            for v, name in enumerate(cands[:HR.CLEAR_CAP]):
                out.append(HR.Site("clearhyp", ((ls, 0, " " * d + f"clear {name}\n"),), (ls, ls), f"clear {name} before {m.group(1)}", variant=v))
        return out
    return clearhyp


def _position_preorder(HR):
    """hb_rewrite._preorder with position order (T29: PREORDER_HINT and the h/H naming priority dropped; same sites, same cap, same
"""
    def preorder(body, mask, pairs, fb):
        out = []
        for m in HR.SIMPCALL_RE.finditer(body):
            i = m.start()
            if mask[i] or not HR._tac_pos(body, mask, i, fb):
                continue
            k = HR._skip_ws(body, m.end(), newlines=False)
            if k < len(body) and body[k] == "(" and k in pairs and HR.CFG_RE.match(body, k):
                k = HR._skip_ws(body, pairs[k] + 1, newlines=False)
            if body.startswith("only", k) and not re.match(r"[\w'?!]", body[k + 4:k + 5] or " "):
                k = HR._skip_ws(body, k + 4, newlines=False)
            if k >= len(body) or body[k] != "[" or k not in pairs:
                continue
            spans = [(x, y) for x, y in HR._arg_spans(body, mask, pairs, k + 1, pairs[k]) if body[x] not in "↓↑-*" and not body.startswith("<-", x)]
            for v, (x, y) in enumerate(sorted(spans)[:HR.PREORDER_CAP]):
                out.append(HR.Site("preorder", ((x, 0, "↓"),), (x, y), "↓" + HR._note(body, x, y), variant=v))
        return out
    return preorder


def _set_tables(heads, auto, hp_heads, gr_by_scope, structural: bool, projections: Path | None, preorder_position: bool = False) -> dict:
    """Set the table-driven module state (the census's measurement range and the open package's shipped tables share this)."""
    from harness import sweep as SW, hb_rewrite as HR, hb_polish as HP
    from harness.tools import gr_rules as GRA, t1_compress as T1
    rec: dict = {}
    if heads is not None:                                                             
        SW._ADDWR_RE = re.compile(r"(?m)^[ \t]*(" + "|".join(re.escape(w) for w in sorted(heads, key=len, reverse=True)) + r")(?![\w'?!])") \
            if heads else re.compile(r"(?!x)x")
        rec["addwr_heads"] = len(heads)
    if auto is not None:                                           
        HR.AUTO_RE = re.compile(r"(?<![\w.'?!])(" + "|".join(re.escape(w) for w in sorted(auto, key=len, reverse=True)) + r")(?![\w'?!])") \
            if auto else re.compile(r"(?!x)x")
        rec["auto"] = len(auto)
    if structural:                                          
        HR._TOKEN_FINDERS["clearhyp"] = _structural_clearhyp(HR)
        rec["clearhyp_rule"] = "structural (statement binders, intro / obtain / rcases / have / cases lines)"
    if preorder_position:                                                                     
        HR._TOKEN_FINDERS["preorder"] = _position_preorder(HR)
        rec["preorder_rule"] = "position (PREORDER_HINT and the h/H naming priority dropped)"
    if hp_heads is not None:                        
        HP.HEADS = tuple(hp_heads)
        HP.SITE_RE = re.compile(r"(?<![\w.'?!])(" + "|".join(re.escape(w) for w in sorted(hp_heads, key=len, reverse=True)) + r")(?![\w'?!])") \
            if hp_heads else re.compile(r"(?!x)x")
        rec["hp_heads"] = len(hp_heads)
    if gr_by_scope is not None:                                                                                                        
        GRA.CLOSERS_BY_SCOPE = {sc: tuple(v) for sc, v in gr_by_scope.items()}
        rec["gr_closers"] = {sc: len(v) for sc, v in gr_by_scope.items()}
    if projections is not None:                                                                            
        p = Path(projections)
        if p.exists():
            T1._T = _load(p)
            T1.BY_NAME, T1.BY_IDX, T1.PROJFN, T1.SHARE = T1._index_table(T1._T)
            rec["projections"] = {"path": str(p.relative_to(ROOT)) if p.is_relative_to(ROOT) else str(p),
                                  "structures": len(T1._T.get("structures") or {}), "regenerated": True,
                                  "sha256": hashlib.sha256(p.read_bytes()).hexdigest()[:16]}
        else:
            rec["projections"] = {"path": "harness/tools/tables/projections.json", "regenerated": False,
                                  "structures": len(T1._T.get("structures") or {})}
    return rec


def apply(projections: Path | None = None) -> dict:
    """Set the census / miner measurement range on the imported modules (module docstring). Returns the record (idempotent)."""
    global _APPLIED
    with _LOCK:
        if _APPLIED is not None:
            return _APPLIED
        import importlib
        rec: dict = {"wide": {}, "tables": {}}
        for mod, consts in WIDE.items():
            M = importlib.import_module(mod)
            for k, v in consts.items():
                rec["wide"].setdefault(mod, {})[k] = {"old": getattr(M, k, None), "new": v}
                setattr(M, k, v)
        tabs = r4a()
        from harness import hb_rewrite as HR, gap_rules as GR
                                                                          
        HR.SPECIALIZE = HR.specialize_map(HR._load_table(HR.SPEC_TABLE), cap=HR.SPEC_CAP)
        HR.SPEC_RE = HR.spec_regex(HR.SPECIALIZE)
        GR.DEFAULT_CAPS = {k: v * GR_WIDE_FACTOR for k, v in GR.DEFAULT_CAPS.items()}
        rec["wide"]["harness.gap_rules"] = {"DEFAULT_CAPS": f"x{GR_WIDE_FACTOR}"}
        got = _set_tables([w for w, _ in tabs["addwr_heads"]], [w for w, _ in tabs["auto"]], [w for w, _ in tabs["hp_heads"]],
                          {sc: gr_closers(sc, tabs) for sc in ("core", "mathlib")}, True, Path(projections) if projections else FULL_PROJECTIONS,
                          preorder_position=True)
        rec["tables"] = {k: v for k, v in got.items()}
        for name in ("addwr_heads", "auto", "hp_heads"):
            rec["tables"][name] = {"lean": sum(o == "lean" for _, o in tabs[name]), "old": sum(o == "old" for _, o in tabs[name])}
        rec["tables"]["gr_closers"] = {sc: {"single": len(tabs["single_closers"][sc]), "multi": len(tabs["multi_closers"][sc])}
                                       for sc in ("core", "mathlib")}
        rec["_tabs"] = tabs
        _APPLIED = rec
        return rec


def apply_shipped(path: Path) -> dict:
    """The open package's re-derived tables (probe/open_rederive/refit.py writes them): only the kept entries are set."""
    t = _load(Path(path))
    if not t:
        raise ValueError(f"opentables: no shipped tables in {path}")
    rec = _set_tables(t.get("addwr_heads"), t.get("auto"), t.get("hp_heads"), t.get("gr_closers"), t.get("clearhyp_rule") == "structural",
                      (ROOT / t["projections"]) if t.get("projections") else None, preorder_position=t.get("preorder_rule") == "position")
    rec["file"] = str(Path(path).relative_to(ROOT)) if Path(path).is_relative_to(ROOT) else str(path)
    rec["sha256"] = hashlib.sha256(Path(path).read_bytes()).hexdigest()
    return rec


def record_of(rec: dict | None) -> dict | None:
    return None if rec is None else {k: v for k, v in rec.items() if not k.startswith("_")}


def record() -> dict | None:
    """What apply() set, without the raw tables (for end_config.json and the provenance records)."""
    return None if _APPLIED is None else {k: v for k, v in _APPLIED.items() if not k.startswith("_")}


                                                                                                                                       
_CTOR_SHORT = {"Or.inl": "left", "Or.inr": "right", "And.intro": "constructor", "Iff.intro": "constructor", "Exists.intro": "constructor"}


def entry_of(fop: str, note: str | None, closer: str | None = None) -> str | None:
    """The table entry behind a candidate (its op's hand table, R4 (b)/(c) counts per entry), or None for an op without one."""
    n = (note or "").split(" @L", 1)[0].strip()
    if fop in ("sweep:swap", "swap"):
        return n
    if fop in ("sweep:combdrop", "combdrop"):
        return n
    if fop in ("sweep:rwfinal", "rwfinal"):
        return n
    if fop in ("sweep:ctorshort", "ctorshort"):
        m = re.match(r"(?:apply|exact)\s+(\S+)\s*->\s*(\S+)", n)
        if not m:
            return n
        name, rep = m.group(1), m.group(2)
        if name in _CTOR_SHORT and _CTOR_SHORT[name] == rep:
            return f"{name} -> {rep}"
        return "rule: .refl / .rfl -> rfl" if rep == "rfl" else "rule: Type.ctor -> constructor"
    if fop in ("sweep:addwr", "addwr"):
        return (n.split() or [""])[0]
    if fop in ("sweep:hr:clearhyp", "hr:clearhyp"):
        m = re.search(r"before (\S+)", n)
        return m.group(1) if m else None
    if fop.startswith("gr:tail-closer") or fop == "gr:tail-closer":
        m = re.search(r"`([^`]*)`", n)
        return m.group(1) if m else closer
    if fop.startswith("hp:"):
        m = re.match(r"(\S+)", n)
        return m.group(1) if m else None
    if fop in ("hr:lemmavariant", "sweep:hr:lemmavariant"):
        return lemmavariant_form(n)
    return None


LEMMAVARIANT_LEAN = ("namespace",)                                                                 


def lemmavariant_form(note: str) -> str | None:
    """The variant form of a lemmavariant candidate note `<old name> -> <new name>` (hb_rewrite._lemmavariant): "namespace" (same final
"""
    if " -> " not in (note or ""):
        return None
    w, n = (x.strip() for x in note.split(" -> ", 1))
    seg, last = w.split(".")[-1], n.split(".")[-1]
    if last == seg:
        return "namespace"
    for form, name in (("_of_tower", seg + "_of_tower"), ("ₛₗ", seg + "ₛₗ"), ("'", seg + "'"), ("fun_", "fun_" + seg)):
        if last == name:
            return form
    if seg.startswith("fun_") and last == seg[4:]:
        return "-fun_"
    return "other"


TABLE_OPS = ("swap", "combdrop", "rwfinal", "ctorshort", "addwr", "hr:clearhyp", "gr:tail-closer", "hp:cert", "hp:prune", "hr:lemmavariant")
