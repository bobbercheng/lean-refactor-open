#!/usr/bin/env python3
# Vendored, unchanged except for this comment and the `harness.post` imports, from the closed line's bet D4 code (branch closed-bets-d4 402c44d2, harness/tools/d4_implied.py) for the open post-step harness/open_post.py (2026-11-03).
"""Bet D4, rule R1 "implied" (docs/closed_run2.md, research wins W1 / W2 distilled; bet D4 2026-11-02): an end-stage family ("implied",
registered only by harness/end_d4.register(), never by default) with the harness/sweep.candidates contract and an ENV QUERY
(harness/endstage.py QUERY_FAMILIES: the query runs first, plain compiles after the row's file prefix through the meter's path, charged to
the tool phase and the family's cap; without an answer the family proposes nothing).

The rule: a proof whose last tactic is a decide-family closer C (`decide` with `+flag` / `-flag` options, never `+native`) makes the
kernel decide the goal P. When the row's own environment holds a theorem L whose conclusion is P and whose one explicit hypothesis is a
DECIDABLE proposition Q (or an iff `P ↔ Q` / `Q ↔ P` with no explicit argument), the closer can decide Q instead and L carries it to P:
the kernel may do much less work. Whether it does (and pays for its tokens) is the end stage's paired measurement.

  sites     the proof's last line ends in C (after its last `;`, `<;>` or `by`), and the statement is a `theorem` / `lemma`.
  query     one Lean text (QUERY) placed where the declaration goes: a dummy theorem (it takes the declaration's modifiers), then an
            `example` with the row's own statement whose `run_tac` reads the goal exactly as the proof sees it (binders before the colon
            in context): its Pi binders xs (no unfolding) and the head constant P of its body; the environment's theorems whose
            conclusion (after their own binders, no unfolding) has head P, or is an iff with P on one side (a theorem, or an axiom: under
            Lean's module system an imported theorem is an axiom to the importer; at most MAX_CONSTS such theorems, else no answer: the
            head is too common); for each, in its own state, with its own heartbeat allowance (CAND_HEARTBEATS, withCurrHeartbeats) and
            every exception caught (tryCatchRuntimeEx: a heartbeat or recursion limit ends that theorem's check, never the query):
            exactly one explicit binder (an iff: none), the conclusion unified with the body under xs (instances transparency: the head
            already matches), the remaining instance arguments synthesized, the hypothesis Q fully determined, a Prop, not the body
            itself, `Decidable (∀ xs, Q)` synthesized, and the AXIOM GATE: every axiom Lean.collectAxioms finds for the theorem and for
            the constants of that Decidable instance is in AXIOM_ALLOW (harness/tools/d4_kit.py; a real library `axiom Q → P` or a
            sorried theorem is dropped and reported, LRAD4AX). The header (goal, head, count) is logged first and each theorem found in
            its own message, so the answer read so far survives a failure. At most MAX_LEMMAS names. It also reports xs (count, explicit
            count) and whether `Function.dcomp` exists. Names come only from the environment.
  generate  whole-body candidates from the statement, the closer and the found names L (nothing else of the proof is kept):
    implied:apply      (no Pi binder) `by apply L; C`, `by refine L ?_; C`, ` L $ by C`
    implied:intro      (Pi binders) `by intro; apply L; C +revert` (`intros` for several binders); one binder: `by apply forall_imp λ_ => L; C`
                       and the `fun _ =>` spelling
    implied:iff        an iff L: `by rw [L]; C` / `by simp only [L]; C` (`← L` when P is the right side), `by apply L.2; C` (`L.1`), ` L.2 $ by C`,
                       under Pi binders `by intro; apply L.2; C +revert` and `by apply forall_imp λ_ => L.2; C`
    implied:search     OPT-IN (bet D4S, review 2026-11-02: no ruling covers writing a search tactic into a final, and whether the
                       official worker reads its heartbeats as our meter does is unchecked; the launcher decides): (one Pi binder, at
                       least one L found) `by apply forall_imp; exact?; C`: Lean's library search supplies the bridge at elaboration (no
                       name written; the search may pick any library theorem, which the axiom gate above does not see)
    implied:pointfree  OPT-IN (bet D4P: a Nov 1 decision put dependent composition in future packages; the launcher decides shipping):
                       one explicit Pi binder and `Function.dcomp` in the environment: ` L ∘'by C` (the lexer reads `'by` as one token),
                       ` L ∘' by C`, `by apply Function.dcomp L; C`; an iff: ` L.2 ∘'by C` (`L.1`)
            The closer: C as written; on a closed goal also C without `+revert`; after `intro` C with `+revert` added. Every term body sits
            on the `:=` line (the official worker counts `:=` + a line break as one more token). No token filter: a heartbeat gain can
            pay for tokens, the paired decision prices it.
The caller measures every candidate back to back with its incumbent (batch screen with the heartbeat bound, paired decide, all-pin
confirmation); the query runs on the primary pin only. No harm: no site, a query that does not answer, a timeout or a budget stop proposes
nothing and never changes the final. Generic by construction: no row names, lemma names, proof fragments or tables; P, Q, L and C come
from the statement, the proof and the environment."""
from __future__ import annotations

import argparse, json, re, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402

FAMILY = "implied"
OPS = ("implied:apply", "implied:intro", "implied:iff", "implied:search", "implied:pointfree")
ALL_OPS = OPS
OPT_IN_OPS = ("implied:search", "implied:pointfree")
DEFAULT_OPS = tuple(o for o in OPS if o not in OPT_IN_OPS)
TABLES: dict = {}
MAX_PER_OP = 12
MAX_LEMMAS = 6
MAX_CONSTS = 300
CAND_HEARTBEATS = 1000000   # each candidate theorem's own allowance (withCurrHeartbeats: one costly check never ends the query)
QUERY_TIMEOUT = 300

CLOSER_RE = re.compile(r"^decide(?:\s+[+-][A-Za-z][\w.]*)*$")
DECL_RE = re.compile(r"\A(?P<pre>(?:\s+|/--(?:(?!-/).)*-/|@\[[^\]]*\]|(?:private|protected|noncomputable|nonrec)\b)*)"
                     r"(?P<kw>theorem|lemma)\s+(?P<name>[^\s(:{\[⦃]+(?:\{[^}]*\})?)", re.S)

QUERY = r'''theorem lraD4QueryDummy : True := trivial

set_option maxHeartbeats LRAD4HB in
LRAD4EXAMPLE := by
  run_tac do
    let g ← Lean.Elab.Tactic.getMainGoal
    g.withContext do
      let T ← Lean.instantiateMVars (← g.getType)
      let env ← Lean.getEnv
      let say : String → Lean.MetaM Unit := fun s => Lean.logInfo (Lean.toMessageData ("LRAD4BEGIN\n" ++ s ++ "LRAD4END"))
      Lean.Meta.forallTelescope T fun xs body => do
        let mut s : String := s!"LRAD4DCOMP\t{if env.contains `Function.dcomp then 1 else 0}\n"
        let mut nexp : Nat := 0
        for x in xs do
          if (← x.fvarId!.getBinderInfo).isExplicit then
            nexp := nexp + 1
        s := s ++ s!"LRAD4GOAL\t{xs.size}\t{nexp}\n"
        match body.getAppFn.constName? with
        | none => say (s ++ "LRAD4SKIP\tthe goal has no head constant\n")
        | some P =>
          let isHead : Lean.Expr → Bool := fun b =>
            b.getAppFn.isConstOf P || (b.isAppOfArity ``Iff 2 &&
              (b.appFn!.appArg!.getAppFn.isConstOf P || b.appArg!.getAppFn.isConstOf P))
          let (cnt, cands) := env.constants.fold (fun (acc : Nat × Array Lean.Name) (n : Lean.Name) (c : Lean.ConstantInfo) =>
              let thm := match c with
                | .thmInfo _ => true
                | .axiomInfo _ => true
                | _ => false
              if thm && !n.isInternal && isHead c.type.getForallBody then
                (acc.1 + 1, if acc.2.size < LRAD4MAXC then acc.2.push n else acc.2)
              else acc) (0, #[])
          s := s ++ s!"LRAD4HEAD\t{P}\t{cnt}\n"
          if cnt > LRAD4MAXC then
            say (s ++ "LRAD4SKIP\ttoo many theorems with this head\n")
          else
            say s
            let mut found : Nat := 0
            for c in cands do
              if found ≥ LRAD4MAXL then
                break
              let (k, bad) ← Lean.withCurrHeartbeats (Lean.withoutModifyingState (Lean.tryCatchRuntimeEx (do
                  let ci ← Lean.getConstInfo c
                  let us ← ci.levelParams.mapM fun _ => Lean.Meta.mkFreshLevelMVar
                  let cty := ci.type.instantiateLevelParams ci.levelParams us
                  let (mvs, bis, concl) ← Lean.Meta.forallMetaTelescope cty
                  let mut kind := "imp"
                  let mut tgt := concl
                  let mut q := concl
                  if concl.isAppOfArity ``Iff 2 && !concl.getAppFn.isConstOf P then
                    if concl.appFn!.appArg!.getAppFn.isConstOf P then
                      kind := "iffl"
                      tgt := concl.appFn!.appArg!
                      q := concl.appArg!
                    else
                      kind := "iffr"
                      tgt := concl.appArg!
                      q := concl.appFn!.appArg!
                  let nex := (bis.filter (fun b => b.isExplicit)).size
                  if (kind == "imp" && nex != 1) || (kind != "imp" && nex != 0) then
                    return ("", "")
                  if !(← Lean.Meta.withTransparency Lean.Meta.TransparencyMode.instances (Lean.Meta.isDefEq tgt body)) then
                    return ("", "")
                  for i in [0:mvs.size] do
                    if bis[i]!.isInstImplicit then
                      let m := mvs[i]!.mvarId!
                      if !(← m.isAssigned) then
                        match ← Lean.Meta.synthInstance? (← Lean.Meta.inferType mvs[i]!) with
                        | some inst => m.assign inst
                        | none => pure ()
                  if kind == "imp" then
                    for i in [0:mvs.size] do
                      if bis[i]!.isExplicit then
                        q ← Lean.Meta.inferType mvs[i]!
                  q ← Lean.instantiateMVars q
                  if q.hasExprMVar then
                    return ("", "")
                  if !(← Lean.Meta.isProp q) then
                    return ("", "")
                  if q == (← Lean.instantiateMVars body) then
                    return ("", "")
                  let gq ← Lean.Meta.mkForallFVars xs q
                  match ← Lean.Meta.synthInstance? (Lean.mkApp (Lean.mkConst ``Decidable) gq) with
                  | none => return ("", "")
                  | some inst =>
                    let mut axs : Array Lean.Name := ← Lean.collectAxioms c
                    for d in (← Lean.instantiateMVars inst).getUsedConstants do
                      axs := axs ++ (← Lean.collectAxioms d)
                    let bad := axs.filter fun a => !(LRAD4AXOK)
                    if bad.isEmpty then
                      return (kind, "")
                    return ("", toString bad.toList)
                  : Lean.MetaM (String × String)) (fun _ => pure ("", ""))))
              if bad != "" then
                say s!"LRAD4AX\t{c}\t{bad}\n"
              else if k != "" then
                say s!"LRAD4LEM\t{c}\t{k}\n"
                found := found + 1
  exact sorry
'''


def closer(body: str) -> str | None:
    """The decide-family closer C ending the proof (module docstring, "sites"), whitespace-normalised, else None."""
    mask = _mask(body)
    clean = "".join(" " if mask[i] and body[i] != "\n" else body[i] for i in range(len(body)))
    lines = [ln for ln in clean.split("\n") if ln.strip()]
    if not lines:
        return None
    seg = re.split(r"<;>|;|(?:(?<![\w.'])|(?<=[^\w.']'))by(?![\w'])", lines[-1])[-1].strip()   # (`∘'by`: the prime ends a token)
    seg = re.sub(r"\s+", " ", seg)
    if not CLOSER_RE.match(seg) or "native" in seg:
        return None
    return seg


def example_decl(statement: str) -> str | None:
    """The statement as an anonymous `example` (keyword and name dropped, with the modifiers before them), else None (not a theorem)."""
    m = DECL_RE.match(statement)
    if not m or ".{" in m.group("name"):
        return None
    return "example" + statement[m.end():]


def _flag_add(c: str, f: str) -> str:
    w = c.split()
    return c if f in w else " ".join([w[0], f] + w[1:])


def _flag_drop(c: str, f: str) -> str:
    return " ".join(x for x in c.split() if x != f)


def query_text(proof: str, statement: str) -> str | None:
    body = split_declaration(proof, statement)
    if body is None or closer(body) is None:
        return None
    ex = example_decl(statement)
    if ex is None:
        return None
    return (QUERY.replace("LRAD4EXAMPLE", ex.rstrip()).replace("LRAD4MAXC", str(MAX_CONSTS))
            .replace("LRAD4MAXL", str(MAX_LEMMAS)).replace("LRAD4HB", str(CAND_HEARTBEATS))
            .replace("LRAD4AXOK", K.axiom_ok("a")))


def parse_query(messages) -> dict:
    """The query's answer: every LRAD4BEGIN..LRAD4END message read in order (the header first, then one message per theorem found, so
    the theorems found before a failure are kept). "axioms": [(name, its axioms outside AXIOM_ALLOW)] of the theorems the gate dropped."""
    out = {"answered": False, "lemmas": [], "binders": None, "explicit": None, "dcomp": False, "head": None, "count": None, "skip": None,
           "axioms": []}
    for m in messages or []:
        d = K.msg_text(m)
        if "LRAD4BEGIN" not in d or "LRAD4END" not in d:
            continue
        for ln in d.split("\n"):
            p = ln.split("\t")
            if p[0] == "LRAD4DCOMP" and len(p) == 2:
                out["dcomp"] = p[1].strip() == "1"
            elif p[0] == "LRAD4GOAL" and len(p) == 3 and p[1].strip().isdigit() and p[2].strip().isdigit():
                out["binders"], out["explicit"] = int(p[1]), int(p[2])
                out["answered"] = True   # the header (it precedes every theorem's message)
            elif p[0] == "LRAD4HEAD" and len(p) == 3:
                out["head"] = p[1].strip()
                out["count"] = int(p[2]) if p[2].strip().isdigit() else None
            elif p[0] == "LRAD4SKIP" and len(p) >= 2:
                out["skip"] = p[1].strip()
            elif p[0] == "LRAD4AX" and len(p) == 3:
                out["axioms"].append((p[1].strip(), p[2].strip()))
            elif p[0] == "LRAD4LEM" and len(p) == 3 and p[2].strip() in ("imp", "iffl", "iffr") and out["answered"]:
                nm = p[1].strip()
                if K.IDENT_RE.match(nm) and nm not in [x[0] for x in out["lemmas"]] and len(out["lemmas"]) < MAX_LEMMAS:
                    out["lemmas"].append((nm, p[2].strip()))
    return out


def query(proof: str, statement: str, run, *, versions=None, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict | None:
    """The env query (module docstring). run(text, version) -> a CompileResult-like (messages, ...), charged by the end stage. Returns
    {"implied_query": {...}, "implied_query_for": key}; no site: an empty answer (nothing proposed) without a compile."""
    st = stats if stats is not None else {}
    log = log or (lambda *a: None)
    t0 = time.time()
    key = K.proof_key(proof)
    q = {"answered": False, "lemmas": []}
    text = query_text(proof, statement)
    if text is None:
        q["skip"] = "no decide-family closer at the end of a theorem's proof"
        st["query"] = {"ids": 0, "used": 0, "vars": 0, "class_vars": 0, "skip": q["skip"]}
        return {"implied_query": q, "implied_query_for": key}
    vs = list(versions or [None])
    r = run(text, vs[0])
    pq = parse_query(getattr(r, "messages", None))
    q.update(pq)
    if not pq["answered"]:
        q["skip"] = "the primary pin did not answer: " + str((getattr(r, "errors", None) or ["?"])[0])[:160]
    q["seconds"] = round(time.time() - t0, 2)
    st["query"] = {"ids": 1, "used": 1 if pq["head"] else 0, "vars": len(pq["lemmas"]), "class_vars": 0, "seconds": q["seconds"],
                   **({"skip": q["skip"]} if q.get("skip") else {})}
    log(f"implied: env query: head {pq['head']} ({pq['count']} theorem(s)), {len(pq['lemmas'])} implication(s) "
        f"{[n for n, _ in pq['lemmas']]}, {pq['binders']} Pi binder(s), dcomp {pq['dcomp']} in {q['seconds']} s"
        + (f"; dropped by the axiom gate: {pq['axioms']}" if pq["axioms"] else ""))
    return {"implied_query": q, "implied_query_for": key}


def forms(lemmas, c: str, binders: int, explicit: int, dcomp: bool, ops) -> list[tuple[str, str, str]]:
    """[(op, new body, note)] in op order, then lemma order (module docstring, "generate")."""
    pi = binders > 0
    closed = [c] + ([_flag_drop(c, "+revert")] if "+revert" in c.split() else [])
    opened = _flag_add(c, "+revert")
    intro = "intro" if binders == 1 else "intros"
    out = []
    for op in ops:
        for L, kind in lemmas:
            iff = kind in ("iffl", "iffr")
            pr = (f"{L}.2" if kind == "iffl" else f"{L}.1") if iff else L
            arrow = "" if kind != "iffr" else "← "
            if op == "implied:apply" and not iff and not pi:
                out += [(op, f" by\n  apply {L}\n  {c}", f"apply {L}"), (op, f" by\n  refine {L} ?_\n  {c}", f"refine {L} ?_"),
                        (op, f" {L} $ by {c}", f"{L} $ by")]
            elif op == "implied:intro" and not iff and pi:
                out.append((op, f" by\n  {intro}\n  apply {L}\n  {opened}", f"{intro}; apply {L}"))
                if binders == 1:
                    for cc in closed:
                        out += [(op, f" by\n  apply forall_imp λ_ => {L}\n  {cc}", f"forall_imp λ_ => {L}"),
                                (op, f" by\n  apply forall_imp fun _ => {L}\n  {cc}", f"forall_imp fun _ => {L}")]
            elif op == "implied:iff" and iff:
                if not pi:
                    out += [(op, f" by\n  rw [{arrow}{L}]\n  {c}", f"rw [{arrow}{L}]"), (op, f" by\n  apply {pr}\n  {c}", f"apply {pr}"),
                            (op, f" {pr} $ by {c}", f"{pr} $ by")]
                else:
                    for cc in closed:
                        out.append((op, f" by\n  simp only [{arrow}{L}]\n  {cc}", f"simp only [{arrow}{L}]"))
                    out.append((op, f" by\n  {intro}\n  apply {pr}\n  {opened}", f"{intro}; apply {pr}"))
                    if binders == 1:
                        for cc in closed:
                            out.append((op, f" by\n  apply forall_imp λ_ => {pr}\n  {cc}", f"forall_imp λ_ => {pr}"))
            elif op == "implied:pointfree" and pi and binders == 1 and explicit == 1 and dcomp:
                for cc in closed:
                    out += [(op, f" {pr} ∘'by {cc}", f"{pr} ∘'by"), (op, f" {pr} ∘' by {cc}", f"{pr} ∘' by")]
                    if not iff:
                        out.append((op, f" by\n  apply Function.dcomp {L}\n  {cc}", f"Function.dcomp {L}"))
        if op == "implied:search" and pi and binders == 1 and any(k == "imp" for _, k in lemmas):
            for cc in closed:
                out.append((op, f" by\n  apply forall_imp\n  exact?\n  {cc}", "forall_imp; exact?"))
    return out


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int | None = None,
               ctx: dict | None = None) -> list[dict]:
    ctx = ctx or {}
    ops = K.ops_for(FAMILY, OPS, DEFAULT_OPS, OPT_IN_OPS, ctx)
    q = ctx.get("implied_query")
    if not ops or not q or ctx.get("implied_query_for") != K.proof_key(proof) or not q.get("answered") or not q.get("lemmas"):
        return []
    hb = K.head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    c = closer(body)
    if c is None or q.get("binders") is None:
        return []
    em = K.Emitter(proof, statement, head, body, int(max_per_op) if max_per_op else MAX_PER_OP)
    lemmas = [(n, k) for n, k in q["lemmas"] if K.IDENT_RE.match(n)][:MAX_LEMMAS]
    for op, nb, note in forms(lemmas, c, int(q["binders"]), int(q.get("explicit") or 0), bool(q.get("dcomp")), ops):
        em.add(op, nb, note, save=False)
    return em.out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="implied: the closer of one declaration and its env query text (no compile)")
    ap.add_argument("--file", required=True); ap.add_argument("--statement-file", required=True)
    ap.add_argument("--query", action="store_true", help="print the query text")
    a = ap.parse_args(argv)
    proof = Path(a.file).read_text(); stmt = Path(a.statement_file).read_text().rstrip("\n")
    body = split_declaration(proof, stmt)
    print(json.dumps({"closer": closer(body or ""), "example": example_decl(stmt), "tokens": count_tokens(body or "")}, ensure_ascii=False))
    if a.query:
        print(query_text(proof, stmt) or "(no site)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
