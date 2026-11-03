#!/usr/bin/env python3
# Vendored, unchanged except for this comment and the `harness.post` imports, from the closed line's bet D4 code (branch closed-bets-d4 402c44d2, harness/tools/d4_inlineeq.py) for the open post-step harness/open_post.py (2026-11-03).
"""Bet D4, rule R2 "inlineeq" (docs/closed_run2.md, research wins W3 / W4 distilled; bet D4 2026-11-02): an end-stage family
("inlineeq", registered only by harness/end_d4.register(), never by default) with the harness/sweep.candidates contract and an ENV QUERY
(harness/endstage.py QUERY_FAMILIES; without an answer the query ops propose nothing, the pure ops still run).

The rule: an equation proved inline and used as a rewrite rule inside a simp-family lemma list (`show A = B by TAC [h, ...]`,
`show A = B from by TAC [...]`, `(by TAC [h, ...] : A = B)`, optionally after `←` / `↓`) costs the equation's tokens. When one of TAC's own
hints h (or a sibling of h in the row's environment) instantiated at the literal's components proves it after simp's normalisation, the
item can be `← by simpa using h ARGS` (or one of the forms below): the equation's text disappears.

  sites     the items of a simp-family lemma list (simp / simp only / simp_all / simpa / dsimp / norm_num / field_simp / rw / ...; the list
            head on the `[`'s line, harness/tools/d3_simpconst.LIST_HEAD_RE) of the forms above with ONE top-level `=` in the equation and
            a hint list `[h, ...]` of plain names in TAC. At most MAX_SITES items per proof.
  query     one Lean text: d3_simpconst's literal query (QUERY, unchanged) on the anonymous-constructor literals `f ⟨..⟩` inside those
            items (the named constants of the literal's type that Lean finds equal to it), then one `#eval` that resolves each hint h in
            the row's own environment and lists the theorems (or axioms: an imported theorem under Lean's module system) of h's
            namespace whose last name component starts with h's stem (h's last component without trailing primes / subscript digits)
            and whose rest may only be primes / subscript digits (the exact rule applied in Lean before the cap of 64 per hint, so a
            common stem cannot crowd the real siblings out), each with its count of explicit binders, and each through the AXIOM GATE
            (harness/tools/d4_kit.axiom_ok: every axiom Lean.collectAxioms finds for it in AXIOM_ALLOW; a real `axiom` or a sorried
            theorem is reported as LRAD4SIBAX and never written). Names come only from the proof's own hint lists and the environment's
            answer.
  generate  (query ops, every candidate saving tokens, shortest first)
    inlineeq:simpa      the item -> `← by simpa using s ARGS` and `by simpa using s ARGS` (the arrow combined with the item's own), s a
                        sibling of a hint (h itself included), ARGS by s's explicit binder count k: k = the literal's component count:
                        the components (`0 1`; a negative one in parentheses; also every component negated, for an equation whose other
                        side is a negation that another item of the same list moves outward); k = 1: the literal itself, each named
                        constant equal to it (query), each identifier argument of A or B; k = 0: nothing. The literal's side picks the
                        arrow tried first (literal on the right: `←` first).
    inlineeq:bare       `← s ARGS` / `s ARGS` (the same s, ARGS)
    inlineeq:consthint  the equation kept, the literal replaced by a named constant equal to it AND the hint h replaced by a sibling
                        (d3_simpconst's simpconst alone keeps h; with h's sibling the simp set can still prove it)
            (pure ops, no query)
    inlineeq:showform   `(by TAC : T)` item -> `show T by TAC` (two tokens fewer in a list)
    inlineeq:ascdrop    `show T by simpa ... using e` / `(by simpa ... using e : T)` item -> `by simpa ... using e`
    inlineeq:fromby     `show T from by tac` -> `show T by tac` (anywhere)
    inlineeq:haveinline a one-line `have h : T := by TAC` whose name is used exactly once afterwards, as an item `h` / `← h` of a simp-family
                        list (and no `assumption` / `simp_all` / `*` / automation that could use it unnamed after it) -> the line dropped,
                        the item `show T by TAC` (the next pass may apply inlineeq:simpa to it)
The caller measures every candidate back to back with its incumbent (batch screen, paired decide, all-pin confirmation); the query runs on
the primary pin only. No harm: no site, no answer, a timeout or a budget stop proposes nothing from the query ops and never changes the
final. Generic by construction: no row names, lemma names, proof fragments or tables."""
from __future__ import annotations

import argparse, json, re, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs, OPEN  # noqa: E402
from harness.lint_delete import _list_items  # noqa: E402
from harness.post import d3_simpconst as SC  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402

FAMILY = "inlineeq"
OPS = ("inlineeq:simpa", "inlineeq:bare", "inlineeq:consthint", "inlineeq:showform", "inlineeq:ascdrop", "inlineeq:fromby",
       "inlineeq:haveinline")
ALL_OPS = OPS
OPT_IN_OPS: tuple = ()
DEFAULT_OPS = OPS
QUERY_OPS = ("inlineeq:simpa", "inlineeq:bare", "inlineeq:consthint")
TABLES: dict = {}
MAX_PER_OP = 24
MAX_SITES = 8
MAX_HINTS = 8
MAX_SIBS = 6
MAX_ATOMS = 3
QUERY_TIMEOUT = 300

BY_RE = re.compile(r"(?<![\w.'])by(?![\w'!?])")
FROM_RE = re.compile(r"(?<![\w.'])from(?![\w'!?])")
EQ_RE = re.compile(r"(?<![=:<>≠!≤≥])=(?![=>])")
COLON_RE = re.compile(r":(?!=)")
MOD_RE = re.compile(r"^((?:↓\s*|↑\s*)*)(←\s*|<-\s*)?")
TAC_HEAD_RE = re.compile(r"^(simp_all|simp_arith|simpa|simp|norm_num|field_simp|dsimp|rw|rwa|rewrite|simp_rw|push_cast)!?(?![\w'])")
STEM_TAIL_RE = re.compile(r"['₀-₉]+$")
LIT_RE = re.compile(r"⟨([^⟨⟩]*)⟩")
NUM_RE = re.compile(r"^-?\d+$")
APP_ARG_RE = re.compile(r"(?<![\w.'])(%s)[ \t]+(%s)(?![\w'.])" % (K.IDENT, K.IDENT))
HAVE_RE = re.compile(r"^([ \t]*)have[ \t]+([^\W\d][\w'₀-₉]*)[ \t]*:[ \t]*(.+?)[ \t]*:=[ \t]*by[ \t]+(.+?)[ \t]*$")
UNNAMED_USE_RE = re.compile(r"(?<![\w.'])(assumption|simp_all|aesop|omega|linarith|nlinarith|tauto|grind|positivity|simpa|trivial|"
                            r"solve_by_elim|exact\?|apply\?|decide|norm_num|field_simp|polyrith|bound|gcongr|assumption_mod_cast|"
                            r"exact_mod_cast|this)(?![\w'])|\[\s*\*|,\s*\*\s*[\],]|\bat\s*\*")
KEYWORDS = SC.KW | {"using", "only", "at", "with", "fun", "λ", "from", "show", "by"}

SIB_QUERY = r'''
set_option maxHeartbeats 2000000 in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let hints : List (String × String) := [LRAD4HINTS]
  let env ← Lean.getEnv
  let mut out : String := ""
  let mut i : Nat := 0
  for (h, stem) in hints do
    let r ← Lean.Elab.Command.liftTermElabM do
      try
        let n ← Lean.resolveGlobalConstNoOverload (Lean.mkIdent h.toName)
        pure (some n)
      catch _ => pure none
    match r with
    | none => pure ()
    | some n =>
      let pre := n.getPrefix
      let sibs := env.constants.fold (fun (acc : Array (Lean.Name × Nat)) (c : Lean.Name) (ci : Lean.ConstantInfo) =>
          let thm := match ci with
            | .thmInfo _ => true
            | .axiomInfo _ => true
            | _ => false
          match c with
          | .str p s =>
            if thm && p == pre && acc.size < 64 && s.startsWith stem &&
                (s.toList.drop stem.length).all (fun ch => ch == '\'' || ('₀' ≤ ch && ch ≤ '₉')) then
              acc.push (c, Id.run do
                let mut t := ci.type
                let mut k : Nat := 0
                for _ in [0:256] do
                  match t with
                  | .forallE _ _ b bi =>
                    if bi.isExplicit then
                      k := k + 1
                    t := b
                  | _ => break
                return k)
            else acc
          | _ => acc) #[]
      out := out ++ s!"LRAD4HINT\t{i}\t{n}\n"
      for (c, k) in sibs do
        if (← Lean.collectAxioms c).all (fun a => LRAD4AXOK) then
          out := out ++ s!"LRAD4SIB\t{i}\t{c}\t{k}\n"
        else
          out := out ++ s!"LRAD4SIBAX\t{i}\t{c}\n"
    i := i + 1
  Lean.logInfo (Lean.toMessageData ("LRAD4SBEGIN\n" ++ out ++ "LRAD4SEND"))
'''


# ------------------------------------------------------------------------------------------------------------------ text helpers
def _top(s: str, rx: re.Pattern) -> list[tuple[int, int]]:
    """Matches of rx in s at bracket depth 0 (outside comments and strings)."""
    mask = _mask(s)
    pairs = _pairs(s, mask)
    out, i = [], 0
    while i < len(s):
        if mask[i]:
            i += 1; continue
        if s[i] in OPEN and i in pairs:
            i = pairs[i] + 1; continue
        m = rx.match(s, i)
        if m and m.end() > m.start():
            out.append((m.start(), m.end())); i = m.end(); continue
        i += 1
    return out


def stem_of(name: str) -> str:
    last = name.rsplit(".", 1)[-1]
    return STEM_TAIL_RE.sub("", last) or last


def _arg(c: str) -> str:
    c = c.strip()
    return f"({c})" if c.startswith("-") or " " in c else c


def _neg(c: str) -> str:
    c = c.strip()
    if c.startswith("-"):
        return c[1:].strip()
    return c if c in ("0",) else "-" + c


def parse_tac(tac: str) -> dict | None:
    """{"head", "hints": [names], "using": e or None} of a simp-family call `head [only] [list] [using e]`, else None."""
    t = tac.strip()
    m = TAC_HEAD_RE.match(t)
    if not m:
        return None
    rest = t[m.end():].lstrip()
    if rest.startswith("only"):
        rest = rest[4:].lstrip()
    hints = []
    if rest.startswith("["):
        mask = _mask(rest); pairs = _pairs(rest, mask)
        if 0 not in pairs:
            return None
        items = _list_items(rest, mask, pairs, 0) or []
        for a, b in items:
            it = re.sub(r"^(?:←|<-)\s*", "", rest[a:b].strip())
            if K.IDENT_RE.match(it) and it not in hints:
                hints.append(it)
        rest = rest[pairs[0] + 1:].lstrip()
    use = None
    mu = re.match(r"^using\s+(.+)$", rest, re.S)
    if mu:
        use = mu.group(1).strip()
    elif rest.strip():
        return None
    return {"head": m.group(1), "hints": hints, "using": use}


def parse_item(item: str) -> dict | None:
    """An inline-equation item (module docstring, "sites"): {"mods", "arrow", "kind" (show / paren), "T", "A", "B", "tac", "from"}."""
    m = MOD_RE.match(item)
    mods, arrow = (m.group(1) or ""), bool(m.group(2))
    core = item[m.end():].strip()
    out = {"mods": mods, "arrow": arrow}
    if core.startswith("show") and re.match(r"show(?![\w'])", core):
        rest = core[4:]
        bys = _top(rest, BY_RE)
        if not bys:
            return None
        a, b = bys[0]
        T = rest[:a].rstrip()
        fr = _top(T + " ", FROM_RE)
        frm = False
        if fr and T[fr[-1][0]:].strip() == "from":
            T, frm = T[:fr[-1][0]].rstrip(), True
        out.update(kind="show", T=T.strip(), tac=rest[b:].strip(), frm=frm)
    elif core.startswith("(") and core.endswith(")"):
        mask = _mask(core); pairs = _pairs(core, mask)
        if pairs.get(0) != len(core) - 1:
            return None
        inner = core[1:-1].strip()
        if not BY_RE.match(inner):
            return None
        cs = _top(inner, COLON_RE)
        if not cs:
            return None
        c = cs[-1][0]
        out.update(kind="paren", T=inner[c + 1:].strip(), tac=inner[2:c].strip(), frm=False)
    else:
        return None
    eqs = _top(out["T"], EQ_RE)
    if len(eqs) != 1:
        return None
    out["A"], out["B"] = out["T"][:eqs[0][0]].strip(), out["T"][eqs[0][1]:].strip()
    if not out["A"] or not out["B"] or not out["tac"]:
        return None
    return out


def list_items(body: str) -> list[tuple[int, int]]:
    """The item spans of every simp-family lemma list of the body (list head on the `[`'s line), text order."""
    mask = _mask(body)
    pairs = _pairs(body, mask)
    out = []
    for lb in sorted(pairs):
        if body[lb] != "[" or mask[lb]:
            continue
        ls = body.rfind("\n", 0, lb) + 1
        if not SC.LIST_HEAD_RE.search(body[ls:lb]):
            continue
        out += list(_list_items(body, mask, pairs, lb) or [])
    return sorted(set(out))


def sites(body: str) -> list[dict]:
    """[{"a", "b": the item's span, "item", "p": parse_item, "tac": parse_tac, "lits": [(lo, hi, components)] in the item}]."""
    out = []
    for a, b in list_items(body):
        it = body[a:b]
        p = parse_item(it)
        if p is None:
            continue
        t = parse_tac(p["tac"])
        if t is None:
            continue
        lits = []
        for side in ("A", "B"):
            for m in LIT_RE.finditer(p[side]):
                comps = [x.strip() for x in m.group(1).split(",")]
                if len(comps) >= 2 and all(x and SC.LIT_INNER_RE.match(x) for x in comps):
                    lits.append({"side": side, "lit": m.group(0), "comps": comps})
        atoms = []
        for side in ("A", "B"):
            for m in APP_ARG_RE.finditer(p[side]):
                x = m.group(2)
                if x not in KEYWORDS and m.group(1) not in KEYWORDS and x not in atoms and len(atoms) < MAX_ATOMS:
                    atoms.append(x)
        out.append({"a": a, "b": b, "item": it, "p": p, "tac": t, "lits": lits, "atoms": atoms})
        if len(out) >= MAX_SITES:
            break
    return out


def _lit_sites(body: str, ss: list[dict]) -> list[dict]:
    """d3_simpconst's literal sites that lie inside the R2 items."""
    return [s for s in SC.sites(body) if any(x["a"] <= s["lo"] and s["hi"] <= x["b"] for x in ss)]


def _hints(ss: list[dict]) -> list[str]:
    out = []
    for s in ss:
        for h in s["tac"]["hints"]:
            if h not in out and len(out) < MAX_HINTS:
                out.append(h)
    return out


# ------------------------------------------------------------------------------------------------------------------ the query
def query_text(proof: str, statement: str) -> str | None:
    body = split_declaration(proof, statement)
    if body is None:
        return None
    ss = [s for s in sites(body) if s["tac"]["hints"]]
    if not ss:
        return None
    lits = _lit_sites(body, ss)
    q1 = (SC.QUERY.replace("[SITES]", "[" + ", ".join(f"({K.lean_str(s['f'])}, {K.lean_str(s['ty'])}, {K.lean_str(s['lit'])})"
                                                       for s in lits) + "]")
          .replace("[0:UNFOLDS]", f"[0:{SC.UNFOLDS}]").replace("MAXC", str(SC.MAX_CONSTS)))
    hl = ", ".join(f"({K.lean_str(h)}, {K.lean_str(stem_of(h))})" for h in _hints(ss))
    return q1.rstrip() + "\n" + SIB_QUERY.replace("[LRAD4HINTS]", "[" + hl + "]").replace("LRAD4AXOK", K.axiom_ok("a"))


def parse_query(messages, hints: list[str]) -> dict:
    """{"answered", "resolved": {hint: full name}, "sibs": {hint: [(name, k)]}, "axioms": [siblings the axiom gate dropped]} from the
    sibling #eval."""
    out = {"answered": False, "resolved": {}, "sibs": {}, "axioms": []}
    for m in messages or []:
        d = K.msg_text(m)
        if "LRAD4SBEGIN" not in d or "LRAD4SEND" not in d:
            continue
        out["answered"] = True
        for ln in d.split("\n"):
            p = ln.split("\t")
            if len(p) < 3 or not p[1].strip().isdigit() or int(p[1]) >= len(hints):
                continue
            h = hints[int(p[1])]
            if p[0] == "LRAD4HINT" and len(p) == 3:
                out["resolved"][h] = p[2].strip()
            elif p[0] == "LRAD4SIBAX" and len(p) == 3:
                out["axioms"].append(p[2].strip())
            elif p[0] == "LRAD4SIB" and len(p) == 4 and p[3].strip().isdigit():
                nm = p[2].strip()
                last = nm.rsplit(".", 1)[-1]
                st = stem_of(h)
                if K.IDENT_RE.match(nm) and last.startswith(st) and re.fullmatch(r"['₀-₉]*", last[len(st):]):
                    lst = out["sibs"].setdefault(h, [])
                    if nm not in [x[0] for x in lst]:
                        lst.append((nm, int(p[3])))
        break
    return out


def query(proof: str, statement: str, run, *, versions=None, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict | None:
    """The env query (module docstring). Always returns {"inlineeq_query": {...}, "inlineeq_query_for": key}: without a site no compile
    and no answer (the pure ops still run)."""
    st = stats if stats is not None else {}
    log = log or (lambda *a: None)
    t0 = time.time()
    key = K.proof_key(proof)
    body = split_declaration(proof, statement)
    ss = [s for s in (sites(body) if body is not None else []) if s["tac"]["hints"]]
    q = {"answered": False, "hints": [], "lits": [], "consts": {}, "resolved": {}, "sibs": {}}
    text = query_text(proof, statement) if ss else None
    if text is None:
        q["skip"] = "no inline equation with a hint list in a simp-family lemma list"
        st["query"] = {"ids": 0, "used": 0, "vars": 0, "class_vars": 0, "skip": q["skip"]}
        return {"inlineeq_query": q, "inlineeq_query_for": key}
    hints = _hints(ss)
    lits = _lit_sites(body, ss)
    vs = list(versions or [None])
    r = run(text, vs[0])
    msgs = getattr(r, "messages", None)
    pq = parse_query(msgs, hints)
    pc = SC.parse_query(msgs)
    q.update(answered=pq["answered"], hints=hints, resolved=pq["resolved"], sibs={h: [list(x) for x in v] for h, v in pq["sibs"].items()},
             lits=[s["lit"] for s in lits], lit_spans=[[s["lo"], s["hi"]] for s in lits],
             consts={str(k): v for k, v in pc["found"].items()})
    if not pq["answered"]:
        q["skip"] = "the primary pin did not answer: " + str((getattr(r, "errors", None) or ["?"])[0])[:160]
    q["seconds"] = round(time.time() - t0, 2)
    nsib = sum(len(v) for v in pq["sibs"].values())
    st["query"] = {"ids": len(hints), "used": len(pq["resolved"]), "vars": nsib, "class_vars": 0, "seconds": q["seconds"],
                   **({"skip": q["skip"]} if q.get("skip") else {})}
    log(f"inlineeq: env query {len(ss)} site(s), {len(hints)} hint(s): {len(pq['resolved'])} resolved, {nsib} sibling(s), "
        f"{sum(len(v) for v in pc['found'].values())} named constant(s) in {q['seconds']} s"
        + (f"; dropped by the axiom gate: {pq['axioms']}" if pq["axioms"] else ""))
    return {"inlineeq_query": q, "inlineeq_query_for": key}


# ------------------------------------------------------------------------------------------------------------------ generation
def _replace(body: str, a: int, b: int, new: str) -> str:
    return body[:a] + new + body[b:]


def _arrowed(arrow: bool, mods: str, term: str) -> str:
    return mods + ("← " if arrow else "") + term


def _sib_text(written: str, full: str) -> str:
    """The sibling `full` spelled like the written hint (its written prefix kept, the last component swapped)."""
    pre = written.rsplit(".", 1)[0] + "." if "." in written else ""
    return pre + full.rsplit(".", 1)[-1]


def _args(k: int, s: dict, consts_of) -> list[str]:
    out = []
    for L in s["lits"][:2]:
        if k == len(L["comps"]):
            out.append(" " + " ".join(_arg(c) for c in L["comps"]))
            if any(c.strip().startswith("-") for c in L["comps"]):
                out.append(" " + " ".join(_arg(_neg(c)) for c in L["comps"]))
        if k == 1:
            out.append(" " + L["lit"])
            out += [" " + c for c in consts_of(L)]
    if k == 1:
        out += [" " + x for x in s["atoms"]]
    if k == 0:
        out.append("")
    return list(dict.fromkeys(out))


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int | None = None,
               ctx: dict | None = None) -> list[dict]:
    ctx = ctx or {}
    ops = K.ops_for(FAMILY, OPS, DEFAULT_OPS, OPT_IN_OPS, ctx)
    hb = K.head_body(proof, statement)
    if hb is None or not ops:
        return []
    head, body = hb
    em = K.Emitter(proof, statement, head, body, int(max_per_op) if max_per_op else MAX_PER_OP)
    q = ctx.get("inlineeq_query")
    answered = bool(q) and ctx.get("inlineeq_query_for") == K.proof_key(proof) and bool(q.get("answered"))
    ss = sites(body)
    gen: list[tuple[str, str, str]] = []
    if answered and any(o in QUERY_OPS for o in ops):
        lit_spans = [tuple(x) for x in q.get("lit_spans") or []]
        consts = q.get("consts") or {}

        def consts_of(L, s=None):
            out = []
            for i, (lo, hi) in enumerate(lit_spans):
                if s is not None and not (s["a"] <= lo and hi <= s["b"]):
                    continue
                if body[lo:hi] == L["lit"]:
                    out += [c for c in consts.get(str(i)) or [] if c not in out]
            return out[:4]
        for s in ss:
            if not s["tac"]["hints"]:
                continue
            p = s["p"]
            rev_first = any(L["side"] == "B" for L in s["lits"][:1])
            for h in s["tac"]["hints"]:
                sibs = [tuple(x) for x in (q.get("sibs") or {}).get(h) or []]
                full = (q.get("resolved") or {}).get(h)
                sibs.sort(key=lambda x: (x[0] != full, len(x[0]), x[0]))
                for full_s, k in sibs[:MAX_SIBS]:
                    stext = _sib_text(h, full_s)
                    cfun = lambda L, s=s: consts_of(L, s)   # noqa: E731
                    for args in _args(k, s, cfun):
                        for rev in ((True, False) if rev_first else (False, True)):
                            arr = rev != p["arrow"]
                            for op, term in (("inlineeq:simpa", f"by simpa using {stext}{args}"), ("inlineeq:bare", f"{stext}{args}")):
                                gen.append((op, _replace(body, s["a"], s["b"], _arrowed(arr, p["mods"], term)),
                                            f"`{s['item'][:50]}` -> `{_arrowed(arr, p['mods'], term)[:60]}`"))
                    if full_s != full and "inlineeq:consthint" in ops:
                        for L in s["lits"][:2]:
                            for c in cfun(L):
                                it2 = s["item"].replace(L["lit"], c, 1)
                                it2 = re.sub(r"(?<![\w.'])%s(?![\w'.])" % re.escape(h), stext.replace("\\", "\\\\"), it2, count=1)
                                if it2 != s["item"]:
                                    gen.append(("inlineeq:consthint", _replace(body, s["a"], s["b"], it2),
                                                f"`{L['lit']}` -> `{c}`, `{h}` -> `{stext}`"))
    for s in ss:   # pure ops on the parsed items
        p, t = s["p"], s["tac"]
        if p["kind"] == "paren":
            new = p["mods"] + ("← " if p["arrow"] else "") + f"show {p['T']} by {p['tac']}"
            gen.append(("inlineeq:showform", _replace(body, s["a"], s["b"], new), f"`(by .. : T)` -> `show T by ..`"))
        if t["head"] == "simpa" and t["using"]:
            new = p["mods"] + ("← " if p["arrow"] else "") + f"by {p['tac']}"
            gen.append(("inlineeq:ascdrop", _replace(body, s["a"], s["b"], new), "ascription dropped"))
    mask = _mask(body)
    for m in re.finditer(r"(?<![\w.'])from[ \t]+by(?![\w'])", body):
        ls = body.rfind("\n", 0, m.start()) + 1
        if not mask[m.start()] and re.search(r"(?<![\w.'])show(?![\w'])", body[ls:m.start()]):
            gen.append(("inlineeq:fromby", body[:m.start()] + "by" + body[m.end():], f"`from by` -> `by` @L{K.line_of(body, m.start())}"))
    gen += _haveinline(body, mask)
    order = {o: i for i, o in enumerate(OPS)}
    qgen = sorted([g for g in gen if g[0] in QUERY_OPS], key=lambda g: (count_tokens(g[1]), order[g[0]]))
    pgen = [g for g in gen if g[0] not in QUERY_OPS]
    for op, nb, note in qgen + pgen:
        if op in ops:
            em.add(op, nb, note)
    return em.out


def _haveinline(body: str, mask) -> list[tuple[str, str, str]]:
    out = []
    items = list_items(body)
    lines = body.split("\n")
    pos = 0
    for ln in lines:
        start, end = pos, pos + len(ln)
        pos = end + 1
        m = HAVE_RE.match(ln)
        if not m or mask[start + len(m.group(1))]:
            continue
        name, T, tac = m.group(2), m.group(3), m.group(4)
        if ":=" in T or ";" in tac or "<;>" in tac or not _top(T, EQ_RE):
            continue
        rest = body[end:]
        uses = [u for u in re.finditer(r"(?<![\w.'])%s(?![\w'₀-₉])" % re.escape(name), rest) if not mask[end + u.start()]]
        if len(uses) != 1:
            continue
        u = end + uses[0].start()
        it = [(a, b) for a, b in items if a <= u < b]
        if not it:
            continue
        a, b = it[0]
        mi = re.fullmatch(r"(←\s*|<-\s*)?%s" % re.escape(name), body[a:b])
        if not mi:
            continue
        if UNNAMED_USE_RE.search(body[end:a]) or UNNAMED_USE_RE.search(body[b:]):
            continue
        new_item = ("← " if mi.group(1) else "") + f"show {T} by {tac}"
        nb = body[:a] + new_item + body[b:]
        nb = nb[:start] + nb[min(end + 1, len(nb)):] if end < len(body) else nb[:max(0, start - 1)]
        out.append(("inlineeq:haveinline", nb, f"`have {name}` inlined into its simp list"))
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="inlineeq: the sites of one declaration and its env query text (no compile)")
    ap.add_argument("--file", required=True); ap.add_argument("--statement-file", required=True)
    ap.add_argument("--query", action="store_true", help="print the query text")
    a = ap.parse_args(argv)
    proof = Path(a.file).read_text(); stmt = Path(a.statement_file).read_text().rstrip("\n")
    body = split_declaration(proof, stmt) or ""
    for s in sites(body):
        print(json.dumps({k: s[k] for k in ("a", "b", "item", "lits", "atoms")} | {"hints": s["tac"]["hints"]}, ensure_ascii=False))
    for c in candidates(proof, stmt):
        print(json.dumps({"op": c["op"], "note": c["note"]}, ensure_ascii=False))
    if a.query:
        print(query_text(proof, stmt) or "(no site)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
