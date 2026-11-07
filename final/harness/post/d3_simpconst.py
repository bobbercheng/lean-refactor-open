#!/usr/bin/env python3
# Vendored, unchanged except for this comment and the `harness.post` imports, from the closed line's bet D4 code (branch closed-bets-d4 402c44d2, harness/tools/d3_simpconst.py) for the open post-step harness/open_post.py (2026-11-03).
"""Bet D3, literal to named constant in simp arguments (docs/closed_plus5_per_problem.md, "End-stage ops"; bet-backend-replay 2026-11-02):
an end-stage family ("simpconst", registered only by harness/end_ops.register(), never by default) with the harness/sweep.candidates
contract and an ENV QUERY (harness/endstage.py QUERY_FAMILIES: the query runs first, plain compiles after the row's file prefix through the
meter's path, charged to the tool phase and the family's cap; without an answer the family proposes nothing).

  sites     an anonymous-constructor literal `⟨a, b, ...⟩` (no nested bracket; numerals, `-`, identifiers) inside the lemma list `[...]` of a
            simp-family tactic (simp / simp only / simp_all / simpa / dsimp / norm_num / field_simp / rw / ...; also inside a term of that
            list, e.g. `show x = f ⟨0, 1⟩ by ...`) that is the first argument of an identifier `f` right before it (`f ⟨..⟩`), or ascribed
            `(⟨..⟩ : T)`. At most MAX_SITES per proof.
  query     one Lean `#eval` (QUERY) in the declaration's own context: for each site, the literal's type T (f's first explicit binder's
            type, or the ascription elaborated), the literal elaborated at T, then the constants of the row's own environment in the
            namespace of T's head constant or of a type it unfolds to (at most UNFOLDS unfoldings), definitions whose binders are all
            implicit, whose type is T and whose value is definitionally equal to the literal (default transparency; each check in its own
            state, a failure is no match). Nothing is guessed and no name comes from a table: the names are the environment's answer.
  generate  op simpconst:name: the literal's text replaced by one found constant's full name (one candidate per site and constant, the
            shorter names first), kept only when it saves tokens (scorer/tokenize.py).
The caller measures every candidate back to back with its incumbent (batch screen, paired decide, all-pin confirmation); the query runs on
the primary pin only (a constant missing on another pin fails that pin's confirmation compile). No harm: a query that does not answer, a
timeout or a budget stop proposes nothing."""
from __future__ import annotations

import argparse, hashlib, json, re, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs  # noqa: E402
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402

FAMILY = "simpconst"
OP = f"{FAMILY}:name"
OPS = (OP,)
ALL_OPS = OPS
OPT_IN_OPS: tuple = ()
DEFAULT_OPS = OPS
TABLES: dict = {}
MAX_PER_OP = 24
MAX_SITES = 12
UNFOLDS = 4
MAX_CONSTS = 4000      # candidate constants checked per site (the namespace filter keeps this small)
QUERY_TIMEOUT = 300

IDENT = r"[^\W\d][\w'!?₀-₉]*(?:\.(?:\d+|[^\W\d][\w'!?₀-₉]*))*"
IDENT_END_RE = re.compile(r"(%s)\s*$" % IDENT)
LIT_INNER_RE = re.compile(r"^[\s\w'.,₀-₉-]*$")
LIST_HEAD_RE = re.compile(r"(?:^|[\s;(])(?:simp_all|simp_arith|simpa|simp|dsimp|field_simp|norm_num|rw|rwa|rewrite|erw|simp_rw|nth_rewrite"
                          r"(?:\s+\d+)+|nth_rw(?:\s+\d+)+|push_cast)[!?]?(?:\s+only)?\s*$")
KW = frozenset({"by", "at", "only", "with", "using", "in", "from", "then", "else", "if", "do", "fun", "have", "show", "let", "this", "exact",
                "apply", "intro", "simp", "rw", "norm_num", "decide", "rfl", "λ"})

QUERY = r'''theorem lraD3QueryDummy : True := trivial

set_option maxHeartbeats 2000000 in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let sites : List (String × String × String) := [SITES]
  let mut out : String := ""
  let mut i : Nat := 0
  for (f, ty, lit) in sites do
    let r ← Lean.Elab.Command.liftTermElabM do
      try
        let env ← Lean.getEnv
        let src := if ty != "" then s!"({lit} : {ty})" else s!"{f} {lit}"
        match Lean.Parser.runParserCategory env `term src with
        | .error _ => pure #[]
        | .ok stx =>
            let e ← Lean.Elab.Term.elabTerm stx none
            Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
            let e ← Lean.instantiateMVars e
            let args := e.getAppArgs
            let v := if ty != "" then e else if args.size == 0 then Lean.mkConst `lraD3None else args[args.size - 1]!
            let T ← Lean.instantiateMVars (← Lean.Meta.inferType v)
            if v.isConstOf `lraD3None || v.hasMVar || T.hasMVar || v.hasFVar then pure #[] else
            let mut heads : Array Lean.Name := #[]
            let mut t := T
            for _ in [0:UNFOLDS] do
              match t.getAppFn.constName? with
              | some n => if !(heads.contains n) then heads := heads.push n
              | none => pure ()
              match ← Lean.Meta.unfoldDefinition? t with
              | some t' => t := t'
              | none => break
            let cands := env.constants.fold (fun (acc : Array Lean.Name) (n : Lean.Name) (c : Lean.ConstantInfo) =>
                match c with
                | .defnInfo _ => if !n.isInternal && heads.contains n.getPrefix && acc.size < MAXC then acc.push n else acc
                | _ => acc) #[]
            let mut found : Array Lean.Name := #[]
            for c in cands do
              let ok ← Lean.withoutModifyingState do
                try
                  let cinfo ← Lean.getConstInfo c
                  let us ← cinfo.levelParams.mapM fun _ => Lean.Meta.mkFreshLevelMVar
                  let cty := cinfo.type.instantiateLevelParams cinfo.levelParams us
                  let (mvs, bis, body) ← Lean.Meta.forallMetaTelescopeReducing cty
                  if bis.any (fun b => b.isExplicit) then pure false else
                  if !(← Lean.Meta.isDefEq body T) then pure false else
                  Lean.Meta.withTransparency .default (Lean.Meta.isDefEq (Lean.mkAppN (Lean.mkConst c us) mvs) v)
                catch _ => pure false
              if ok then found := found.push c
            pure found
      catch _ => pure #[]
    for c in r do
      out := out ++ s!"LRAD3CONST\t{i}\t{c}\n"
    i := i + 1
  Lean.logInfo (Lean.toMessageData ("LRAD3BEGIN\n" ++ out ++ "LRAD3END"))
'''


def proof_key(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def _in_simp_list(body: str, mask, pairs, i: int) -> bool:
    """Is position i inside the `[...]` of a simp-family tactic (at any depth)?"""
    for lb, rb in pairs.items():
        if body[lb] == "[" and lb < i < rb and not mask[lb]:
            ls = body.rfind("\n", 0, lb) + 1
            if LIST_HEAD_RE.search(body[ls:lb]):
                return True
    return False


def sites(body: str) -> list[dict]:
    """[{"lo", "hi": the literal's span, "lit", "f", "ty"}] in text order (module docstring, "sites")."""
    mask = _mask(body)
    pairs = _pairs(body, mask)
    out = []
    for lo in sorted(pairs):
        if body[lo] != "⟨" or mask[lo]:
            continue
        hi = pairs[lo] + 1
        inner = body[lo + 1:hi - 1]
        if not inner.strip() or not LIT_INNER_RE.match(inner) or "," not in inner:
            continue
        if not _in_simp_list(body, mask, pairs, lo):
            continue
        f, ty = "", ""
        m = IDENT_END_RE.search(body[max(0, lo - 200):lo])
        if m and m.group(1) not in KW and not body[max(0, lo - 200):lo].endswith(("(", "[", ",")):
            f = m.group(1)
        else:   # `(⟨..⟩ : T)`
            j = lo - 1
            while j >= 0 and body[j] in " \t":
                j -= 1
            if j >= 0 and body[j] == "(" and j in pairs:
                rest = body[hi:pairs[j]]
                mt = re.match(r"\s*:\s*(.+?)\s*$", rest, re.S)
                if mt and "⟨" not in mt.group(1):
                    ty = mt.group(1)
        if not f and not ty:
            continue
        out.append({"lo": lo, "hi": hi, "lit": body[lo:hi], "f": f, "ty": ty})
        if len(out) >= MAX_SITES:
            break
    return out


def query_text(proof: str, statement: str) -> str | None:
    body = split_declaration(proof, statement)
    if body is None:
        return None
    ss = sites(body)
    if not ss:
        return None
    lst = ", ".join(f"({lean_str(s['f'])}, {lean_str(s['ty'])}, {lean_str(s['lit'])})" for s in ss)
    return QUERY.replace("[SITES]", "[" + lst + "]").replace("[0:UNFOLDS]", f"[0:{UNFOLDS}]").replace("MAXC", str(MAX_CONSTS))


def parse_query(messages) -> dict:
    found, answered = {}, False
    for m in messages or []:
        d = str((m or {}).get("data", "")) if isinstance(m, dict) else str(m)
        if "LRAD3BEGIN" not in d:
            continue
        answered = True
        for ln in d.split("\n"):
            p = ln.split("\t")
            if p[0] == "LRAD3CONST" and len(p) == 3 and p[1].strip().isdigit():
                found.setdefault(int(p[1]), [])
                if p[2].strip() not in found[int(p[1])]:
                    found[int(p[1])].append(p[2].strip())
    return {"found": found, "answered": answered}


def query(proof: str, statement: str, run, *, versions=None, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict | None:
    """The env query (module docstring). run(text, version) -> a CompileResult-like (messages, ...), charged by the end stage. Returns
    {"simpconst_query": {...}, "simpconst_query_for": key}; no site: an empty answer (nothing proposed) without a compile."""
    st = stats if stats is not None else {}
    log = log or (lambda *a: None)
    t0 = time.time()
    key = proof_key(proof)
    body = split_declaration(proof, statement)
    ss = sites(body) if body is not None else []
    q = {"sites": [{k: s[k] for k in ("lo", "hi", "lit", "f", "ty")} for s in ss], "found": {}, "answered": False}
    if not ss:
        q["skip"] = "no literal site in a simp-family lemma list"
        st["query"] = {"ids": 0, "used": 0, "vars": 0, "class_vars": 0, "skip": q["skip"]}
        return {"simpconst_query": q, "simpconst_query_for": key}
    vs = list(versions or [None])
    r = run(query_text(proof, statement), vs[0])
    pq = parse_query(getattr(r, "messages", None))
    q["answered"] = pq["answered"]
    q["found"] = {str(k): v for k, v in pq["found"].items()}
    if not pq["answered"]:
        q["skip"] = "the primary pin did not answer: " + str((getattr(r, "errors", None) or ["?"])[0])[:160]
    q["seconds"] = round(time.time() - t0, 2)
    nconst = sum(len(v) for v in pq["found"].values())
    st["query"] = {"ids": len(ss), "used": len(pq["found"]), "vars": nconst, "class_vars": 0, "seconds": q["seconds"],
                   **({"skip": q["skip"]} if q.get("skip") else {})}
    log(f"simpconst: env query {len(ss)} literal site(s): {len(pq['found'])} with a named constant ({nconst} name(s)) in {q['seconds']} s")
    return {"simpconst_query": q, "simpconst_query_for": key}


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int | None = None,
               ctx: dict | None = None) -> list[dict]:
    ctx = ctx or {}
    if ctx.get("ops") is not None and OP not in {o if ":" in o else f"{FAMILY}:{o}" for o in ctx["ops"]}:
        return []
    q = ctx.get("simpconst_query")
    if not q or ctx.get("simpconst_query_for") != proof_key(proof) or not q.get("answered"):
        return []
    body = split_declaration(proof, statement)
    if body is None:
        return []
    head = proof[:len(proof) - len(body)]
    t0 = count_tokens(body)
    cap = int(max_per_op) if max_per_op else MAX_PER_OP
    out, seen = [], {proof.rstrip()}
    for k, s in enumerate(q.get("sites") or []):
        if body[s["lo"]:s["hi"]] != s["lit"]:
            continue
        for name in sorted(q.get("found", {}).get(str(k)) or [], key=lambda x: (len(x), x)):
            if len(out) >= cap:
                return out
            nb = body[:s["lo"]] + name + body[s["hi"]:]
            decl = head + nb
            if decl.rstrip() in seen or split_declaration(decl, statement) != nb or count_tokens(nb) >= t0:
                continue
            seen.add(decl.rstrip())
            line = decl.count("\n", 0, len(head) + s["lo"]) + 1
            out.append({"op": OP, "decl": decl, "note": f"`{s['lit']}` -> `{name}` @L{line}"})
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="simpconst: the literal sites of one declaration and its env query text (no compile)")
    ap.add_argument("--file", required=True); ap.add_argument("--statement-file", required=True)
    ap.add_argument("--query", action="store_true", help="print the query text")
    a = ap.parse_args(argv)
    proof = Path(a.file).read_text(); stmt = Path(a.statement_file).read_text().rstrip("\n")
    body = split_declaration(proof, stmt)
    for s in sites(body or ""):
        print(json.dumps(s, ensure_ascii=False))
    if a.query:
        print(query_text(proof, stmt) or "(no site)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
