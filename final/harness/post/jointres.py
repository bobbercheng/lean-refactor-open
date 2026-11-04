#!/usr/bin/env python3
"""Op "jointres" of the open post-step v2 (harness/open_post.py; 2026-11-03): the never-tried residue of the open package's own pure
surface generators, run JOINTLY through the error-localized engine harness/post/joint.py. The run's end stage reads one edit at a time
and stops on its budget (run 2: 141 of 550 end-stage runs), so many token-saving single edits of the export were never compiled; one
joint compile per round reads dozens of them at once, Lean's error positions drop the ones that break, and the survivors go to the
post-step's gate as one candidate (then per rule, halves, singles).

  generators (the open package's existing code, pure, called on the current proof; op names restricted to the open frozen keep set,
              probe/open_rederive/open_frozen.json and the end pipe's probe/open_package/end_r10.json; t4:induction excluded)
    t1        harness/tools/t1_compress: t1:inline, t1:hole
    dialect   harness/dialect: dialect:typehole, dialect:ascription, and (ctx "dialect_more", default on) the dialect pass's other rules
              but combo (DIALECT_MORE)
    gr        harness/gap_rules (the gr family's kinds): wit-underscore, arg-underscore, obtain-proj, eta-lam, and the rest of the frozen gr
              keep set but the table-driven tail-closer (caps GR_CAP per kind)
    golf      harness/tools/golf_ops: golf:trailarg, golf:dot, golf:casewrap (the end pipe's opt-in set)
    sweep     harness/sweep: its token-saving operators that the frozen config keeps (SWEEP_OPS; the table-driven combdrop and
              ctorshort only with the frozen entries; the lint deletions ld:arg / ld:tac only with ctx {"ld": True})
    norm      harness/normalize.sites: dollar, bare, ltri, lam, semi
    t5        harness/tools/t5_joint.elide_atoms (pure): t5:elide
  edits       every candidate that saves a token becomes one joint.Edit (joint.from_decl; normalizer sites and gap rules directly from
              their own edit lists); an edit whose local key failed before on this row (joint cache) is left out.
  engine      joint.run_joint (rounds of one plain compile on the primary pin, a control copy first per row) and joint.candidates.
  screen      when more than SCREEN_MIN candidates come out, one d4_measure file (the incumbent first as control, at most 16 variants)
              orders them by predicted score change (heartbeats saved minus tokens added at the row's exchange rate; only those predicted
              to read higher are kept); a file whose control does not read leaves the engine's order.
  combo       the screened candidates predicted to read higher, joined greedily (joint.combine: best first, a candidate's edits join when
              none conflicts with those chosen), go FIRST when that joins two or more of them (full1 smoke: the adopted candidate of a
              pass was often one rule's subset while other rules' subsets also read higher; they then waited for later passes).
Nothing here decides anything: the caller's gate measures each candidate (exact statement, forbidden list, every pin, paired re-reading,
sorry audit). No row name, table or proof text; every token of a candidate comes from the proof or from the generators above."""
from __future__ import annotations

import re, sys, threading, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.post import joint as J  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "jointres"
T1_OPS = ("t1:inline", "t1:hole")
DIALECT_OPS = ("dialect:typehole", "dialect:ascription")
# the dialect pass's other rules (the open package runs all of them; combo, its own all-sites combinations, is the engine's job here)
DIALECT_MORE = ("dialect:dollar", "dialect:iterate", "dialect:funext", "dialect:bulletdrop", "dialect:casedrop", "dialect:caseor",
                "dialect:samebullets", "dialect:firstmerge", "dialect:altmerge", "dialect:samelines", "dialect:intros", "dialect:introobtain",
                "dialect:ctor", "dialect:rwmerge", "dialect:listdrop", "dialect:firstdrop", "dialect:calctail", "dialect:letinline")
GR_KINDS = ("wit-underscore", "arg-underscore", "obtain-proj", "eta-lam", "inline-have", "by-exact", "bullet-merge", "bullet-hoist", "rwa",
            "simpa", "refine-constructor")   # the frozen gr keep set but its table-driven tail-closer
GOLF_OPS = ("golf:trailarg", "golf:dot", "golf:casewrap")
# harness/sweep.SAVE_OPS kept by the open frozen config (its drop_ops removed); combdrop / ctorshort only with the frozen entries
SWEEP_OPS = ("byexact", "parendrop", "paren2dollar", "namedarg", "dots", "armdrop", "combdrop", "rwargdrop", "at2star", "ctorshort",
             "hr:anonhave", "hr:case2bullet", "hr:bulletdrop", "hr:exact2assumption", "hr:simpmerge", "hr:rwsimpfold", "hr:simpafold")
SWEEP_LD = ("ld:arg", "ld:tac")
SWEEP_ENTRIES = {"combdrop": ("all_goals", "any_goals", "try"),
                 "ctorshort": ("And.intro -> constructor", "Iff.intro -> constructor", "rule: .refl / .rfl -> rfl")}
NORM_KINDS = ("dollar", "bare", "ltri", "lam", "semi")
# The order the engine TESTS edits in (joint.run_joint ctx "prior": expected saving = dtok x prior): a generic prior by the KIND of
# rewrite, not by row. A: layout / notation that keeps the elaborated term (parentheses -> `$`, `fun` -> `λ`, bullets, anonymous `have`);
# B: dropping information the elaborator usually recovers (an ascription, a `have` type, a named argument, an inlined `have`);
# C: dropping information it must infer (a hole, a typehole, a trailing argument, generalized field notation, a parenthesis or a rewrite).
PRIOR_A, PRIOR_B, PRIOR_C = 0.8, 0.4, 0.15
TIER_A = ("norm:", "sweep:paren2dollar", "sweep:dots", "sweep:byexact", "hr:bulletdrop", "hr:case2bullet", "hr:anonhave", "golf:casewrap",
          "dialect:dollar", "dialect:bulletdrop", "dialect:casedrop")
TIER_C = ("t1:hole", "dialect:typehole", "gr:wit-underscore", "gr:arg-underscore", "golf:dot", "golf:trailarg", "sweep:parendrop",
          "sweep:rwargdrop", "sweep:ld:", "dialect:listdrop", "dialect:firstdrop")


def tier_prior(rule: str) -> float:
    if rule.startswith(TIER_A):
        return PRIOR_A
    if rule.startswith(TIER_C):
        return PRIOR_C
    return PRIOR_B


# MEASURED per-rule outcomes of the engine's tests (edits verified in a clean copy, edits dropped by an error), summed over the
# "jointres rates" log lines of one full post-step run (RATES_SOURCE). Generic per rule kind (no row, name or proof): they only order
# which edits a round tests first; a rule with few observations shrinks to its tier prior (RATE_PSEUDO pseudo-observations).
RATES_SOURCE = "full3: open run 2 + post v1 (sub29), 60 rows, PASSES 5, 2026-11-03"
RULE_RATES: dict = {"t1:hole": (36, 1654), "sweep:parendrop": (17, 1338), "dialect:listdrop": (141, 779), "t5:elide": (291, 291),
              "sweep:rwargdrop": (7, 333), "t1:inline": (102, 217), "dialect:typehole": (5, 294), "golf:trailarg": (36, 239),
              "sweep:namedarg": (42, 175), "golf:dot": (14, 199), "sweep:paren2dollar": (26, 122), "gr:obtain-proj": (5, 98),
              "dialect:bulletdrop": (24, 78), "dialect:ascription": (12, 85), "hr:anonhave": (75, 18), "hr:bulletdrop": (50, 0),
              "sweep:dots": (11, 28), "gr:arg-underscore": (0, 26), "gr:eta-lam": (4, 20), "norm:dollar": (0, 22),
              "sweep:at2star": (15, 6), "sweep:armdrop": (0, 21), "dialect:calctail": (4, 15), "hr:rwsimpfold": (4, 11),
              "sweep:combdrop": (2, 13), "hr:exact2assumption": (3, 9), "dialect:firstdrop": (0, 8), "dialect:casedrop": (0, 7),
              "hr:simpmerge": (0, 5), "gr:rwa": (5, 0), "hr:case2bullet": (0, 4), "norm:semi": (0, 4), "gr:by-exact": (4, 0),
              "dialect:letinline": (3, 0), "dialect:ctor": (2, 0), "dialect:intros": (1, 1), "dialect:altmerge": (0, 1),
              "norm:lam": (1, 0), "dialect:rwmerge": (0, 1)}
RATE_PSEUDO = 8.0
LIKELY_MIN = 0.6       # an edit whose prior is at least this joins the round's "likely" group copy (joint.plan); None turns it off


TABLE_CAP = 40.0       # the table counts as at most this many observations of a rule (a soft prior: proof sets differ, see below)


def prior(rule: str) -> float:
    """The expected success rate of an edit of this rule before the row's own outcomes (the engine's test order: expected saving = dtok
    x prior; joint.run_joint then updates it with the row's own verified / dropped counts per rule). RULE_RATES is measured on proofs
    that went through the open end pipeline (sub29), where e.g. dialect:typehole survived 1.7% of its tests; on the run 3 agent snapshot
    (before the end pipeline) it survived 27%: so the table is capped at TABLE_CAP observations and the row's own outcomes take over."""
    t = tier_prior(rule)
    ok, bad = RULE_RATES.get(rule, (0, 0))
    n = ok + bad
    if n > TABLE_CAP:
        ok, bad = ok * TABLE_CAP / n, bad * TABLE_CAP / n
    return (ok + RATE_PSEUDO * t) / (ok + bad + RATE_PSEUDO)


PER_OP = 200           # generator candidates per op at most
GR_CAP = 64
SCREEN_MIN = 2
SCREEN_MAX = 16        # variants per screen file (the control included)


def _sweep_rule(op: str) -> str:
    return op if op.startswith("hr:") else "sweep:" + op


def _entry_ok(op: str, note: str) -> bool:
    if op not in SWEEP_ENTRIES:
        return True
    try:
        from probe.open_rederive.opentables import entry_of
        ent = entry_of("sweep:" + op, note)
    except Exception:  # noqa: BLE001  (no table module: the table-driven op proposes nothing)
        return False
    return ent in SWEEP_ENTRIES[op]


_MEMO: dict = {}
_MEMO_LOCK = threading.Lock()
MEMO_MAX = 64


def edits(proof: str, statement: str, ctx: dict | None = None, stats: dict | None = None) -> list[J.Edit]:
    """Every generator's token-saving candidate on `proof` as a joint.Edit (module docstring); pure (memoized per proof, statement and
    the ctx keys that change the output)."""
    key = (proof.rstrip(), statement, bool((ctx or {}).get("ld")), bool((ctx or {}).get("dialect_more", True)), tuple((ctx or {}).get("skip") or ()))
    with _MEMO_LOCK:
        got = _MEMO.get(key)
    if got is not None and stats is None:
        return list(got)
    out = _edits(proof, statement, ctx, stats)
    with _MEMO_LOCK:
        if len(_MEMO) >= MEMO_MAX:
            _MEMO.pop(next(iter(_MEMO)))
        _MEMO[key] = tuple(out)
    return out


def _edits(proof: str, statement: str, ctx: dict | None = None, stats: dict | None = None) -> list[J.Edit]:
    ctx = ctx or {}
    st = stats if stats is not None else {}
    body = split_declaration(proof, statement)
    if body is None:
        return []
    body = body.rstrip()
    proof = proof.rstrip()
    t0 = count_tokens(body)
    out: list[J.Edit] = []

    def add_decl(cands, rule_of):
        for c in cands or []:
            r = rule_of(c)
            if r is None:
                continue
            e = J.from_decl(proof, c["decl"], r, statement, note=str(c.get("note") or "")[:80], t0=t0)
            if e is not None:
                out.append(e); st[r] = st.get(r, 0) + 1

    def add_raw(raw_edits, rule, note=""):
        hs = sorted((int(p), int(p) + int(dl), str(ins)) for p, dl, ins in raw_edits)
        if not hs:
            return
        try:
            nb = J.apply(body, [J.Edit(s, e, t) for s, e, t in hs]) if len(hs) == 1 else _apply_raw(body, hs)
        except Exception:  # noqa: BLE001
            return
        if nb is None:
            return
        e = J.edit_from_bodies(body, nb, rule, note[:80], t0)
        if e is not None:
            out.append(e); st[rule] = st.get(rule, 0) + 1

    def guard(name, fn):
        try:
            fn()
        except Exception as ex:  # noqa: BLE001  (a generator that trips on odd syntax never blocks the others)
            st.setdefault("errors", []).append(f"{name}: {type(ex).__name__}: {str(ex)[:80]}")

    def g_t1():
        from harness.tools import t1_compress as T1
        add_decl(T1.candidates(proof, statement, max_per_op=PER_OP, ctx={"ops": list(T1_OPS)}),
                 lambda c: c["op"] if c.get("op") in T1_OPS else None)

    def g_dialect():
        from harness import dialect as DI
        for ops in (DIALECT_OPS,) + ((DIALECT_MORE,) if ctx.get("dialect_more", True) else ()):   # separate calls: its max_cands cap
            add_decl(DI.candidates(proof, statement, max_per_op=PER_OP, ctx={"ops": list(ops)}),
                     lambda c, ops=ops: c["op"] if c.get("op") in ops else None)

    def g_gr():
        from harness import gap_rules as GR
        for r in GR.candidates(body, {k: GR_CAP for k in GR_KINDS}, GR_KINDS):
            if r.kind in GR_KINDS:
                add_raw(r.edits, "gr:" + r.kind, getattr(r, "note", "") or "")

    def g_golf():
        from harness.tools import golf_ops as GO
        add_decl(GO.candidates(proof, statement, max_per_op=PER_OP, ctx={"opt_in": list(GOLF_OPS)}),
                 lambda c: c["op"] if c.get("op") in GOLF_OPS else None)

    def g_sweep():
        from harness import sweep as SW
        allowed = set(SWEEP_OPS) | (set(SWEEP_LD) if ctx.get("ld") else set())
        add_decl(SW.candidates(proof, statement, max_per_op=PER_OP),
                 lambda c: _sweep_rule(c["op"]) if c.get("op") in allowed and _entry_ok(c["op"], c.get("note") or "") else None)

    def g_norm():
        from harness import normalize as NO
        for s in NO.sites(body):
            if s.kind in NORM_KINDS:
                add_raw(s.edits, "norm:" + s.kind, s.note or "")

    def g_t5():
        from harness.tools import t5_joint as T5
        S = T5.Src(proof, statement)
        if not getattr(S, "ok", False):
            return
        for m in T5.elide_atoms(S):
            if getattr(m, "op", "") == "t5:elide":
                add_decl([{"decl": S.decl(m.edits), "note": getattr(m, "src", "")}], lambda c: "t5:elide")

    for name, fn in (("t1", g_t1), ("dialect", g_dialect), ("gr", g_gr), ("golf", g_golf), ("sweep", g_sweep), ("norm", g_norm), ("t5", g_t5)):
        if name in (ctx.get("skip") or ()):
            continue
        guard(name, fn)
    uniq: dict = {}
    for e in out:
        uniq.setdefault(e.key, e)
    return sorted(uniq.values(), key=lambda e: (e.start, e.end, e.rule))


def _apply_raw(body: str, hs) -> str | None:
    """Several (start, end, text) hunks of ONE generator edit applied together (they must not overlap)."""
    prev = -1
    for s, e, _ in hs:
        if s < prev:
            return None
        prev = e
    out, pos = [], 0
    for s, e, t in hs:
        out.append(body[pos:s]); out.append(t); pos = e
    out.append(body[pos:])
    return "".join(out)


def sites(proof: str, statement: str) -> bool:
    """A pure pre-check: some generator edit exists (no compile)."""
    try:
        return bool(edits(proof, statement)) and J.renamed(statement, 0) is not None
    except Exception:  # noqa: BLE001
        return False


# The screen's measuring file: harness/post/d4_measure's protocol (one `#eval` per variant, the variant parsed as a command and
# elaborated between two IO.getNumHeartbeats readings under Lean.withoutModifyingEnv, logged "LRAD4M <i> <ok> <heartbeats / 1000>", read
# back by d4_measure.parse), with three changes for rows whose own file defeats the vendored text: every local of the `#eval` carries
# the `lraJ` prefix and no `s!` interpolation is used (a file's notation token such as a local prefix `s` broke `let s : String`), the
# variant keeps the declaration's namespace prefix and `private` (joint.renamed; the ok check looks the theorem up under that name,
# private-mangled when private), and the row's own `... in` combinators precede each variant (joint.in_mods). A module file whose
# imports do not bring Lean.Elab.Command into reach still cannot run it (the control does not read; the engine's order stays).
SCREEN_VARIANT = r'''
LRAJMODSset_option Elab.async false in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let lraJsrc : String := LRAJSRC
  let lraJidx : Nat := LRAJIDX
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command lraJsrc with
  | .error _ => Lean.logInfo (Lean.toMessageData ("LRAD4M\t" ++ toString lraJidx ++ "\t0\t0\tparse"))
  | .ok lraJstx =>
    let lraJbase := (← Lean.getCurrNamespace) ++ LRAJNS ++ Lean.Name.mkSimple ("lraD4M" ++ toString lraJidx)
    let (lraJok, lraJdh) ← Lean.withoutModifyingEnv do
      let lraJt0 ← IO.getNumHeartbeats
      Lean.Elab.Command.elabCommand lraJstx
      let lraJt1 ← IO.getNumHeartbeats
      let lraJenv ← Lean.getEnv
      let lraJname := if LRAJPRIV then Lean.mkPrivateName lraJenv lraJbase else lraJbase
      let mut lraJgood := false
      if lraJenv.contains lraJname then
        lraJgood := !((← Lean.collectAxioms lraJname).contains ``sorryAx)
      pure (lraJgood, lraJt1 - lraJt0)
    Lean.logInfo (Lean.toMessageData ("LRAD4M\t" ++ toString lraJidx ++ "\t" ++ (if lraJok then "1" else "0") ++ "\t" ++ toString (lraJdh / 1000)))
'''


def _lean_name(ns: str) -> str:
    """A Lean `Name` expression for a dotted namespace prefix ('' -> Lean.Name.anonymous)."""
    out = "Lean.Name.anonymous"
    for comp in [c for c in ns.split(".") if c]:
        out = f"(Lean.Name.mkStr {out} {_lean_str(comp)})"
    return out


def _lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def screen_text(statement: str, bodies: list, mods: str = "") -> str | None:
    """The screen's measuring file for the bodies (variant 0 = the incumbent), SCREEN_VARIANT above; None: not renameable."""
    from harness.post import d4_measure as MS
    rn = J.renamed(statement, 0, stem="lraD4M")
    if rn is None:
        return None
    name = rn[1]
    if name.startswith("_root_"):
        return None
    ns = name.rsplit(".", 1)[0] if "." in name.strip(".") else ""
    priv = "true" if rn[0].startswith("private ") else "false"
    mods = "".join(l.strip() + "\n" for l in (mods or "").split("\n") if l.strip())
    parts = [MS.TEXT]
    for i, b in enumerate(bodies):
        head = J.renamed(statement, i, stem="lraD4M")[0]
        src = head.rstrip() + " :=" + J._rename_body(b.rstrip(), name, i, stem="lraD4M")
        parts.append(SCREEN_VARIANT.replace("LRAJMODS", mods).replace("LRAJSRC", _lean_str(src)).replace("LRAJIDX", str(i))
                     .replace("LRAJNS", _lean_name(ns)).replace("LRAJPRIV", priv))
    return "".join(parts)


def screen(proof: str, statement: str, cands: list, run, exchange, compile_s, log=None, mods: str = "") -> tuple[list, dict]:
    """The candidates ordered by one measuring file (module docstring, screen; screen_text above)."""
    from harness.post import d4_measure as MS
    if len(cands) <= SCREEN_MIN or J.renamed(statement, 0) is None:
        return cands, {"screened": False}
    inc = split_declaration(proof, statement)
    n = min(SCREEN_MAX, MS.budget({"compile_s": compile_s}))
    chunk = cands[:max(1, n - 1)]
    bodies = [split_declaration(c["decl"], statement) for c in chunk]
    text = screen_text(statement, [inc] + bodies, mods)
    if text is None:
        return cands, {"screened": False}
    r = run(text, None)
    rd = MS.parse(getattr(r, "messages", None), len(chunk) + 1)
    ctl = rd.get(0) or {"ok": False}
    if not ctl.get("ok"):
        return cands, {"screened": False, "why": "control did not read"}
    scored = []
    for k, (c, b) in enumerate(zip(chunk, bodies), 1):
        pr = MS.predicted(ctl, inc, b, rd.get(k) or {"ok": False}, exchange)
        if pr is not None and pr > 0:
            scored.append((pr, k, c))
    scored.sort(key=lambda x: (-x[0], x[1]))
    return [c for _, _, c in scored] + cands[len(chunk):], {"screened": True, "predicted_up": len(scored), "of": len(chunk),
                                                           "ranked": [c for _, _, c in scored]}


def generate(proof: str, statement: str, run, versions=None, exchange=None, compile_s=None, log=None, ctx: dict | None = None) -> list[dict]:
    """The op's candidates on `proof` (module docstring): generators -> edits -> joint.run_joint -> joint.candidates -> screen."""
    ctx = dict(ctx or {})
    say = log or (lambda *a: None)
    t0 = time.time()
    body = split_declaration(proof, statement)
    if body is None:
        return []
    es = edits(proof, statement, ctx)
    fresh = [e for e in es if not J.known_failed(statement, body.rstrip(), e)]
    if not fresh:
        say(f"jointres: {len(es)} edit(s), none fresh")
        return []
    jctx = dict(ctx, compile_s=compile_s, prior=prior)
    jctx.setdefault("likely_min", LIKELY_MIN)
    res = J.run_joint(proof, statement, fresh, run, rounds=int(ctx.get("rounds", J.ROUNDS)), ctx=jctx, log=say)
    cands = J.candidates(proof, statement, res, op=FAMILY, max_out=int(ctx.get("max_out", J.MAX_OUT)))
    info = {}
    if cands and ctx.get("screen", True):
        cands, info = screen(proof, statement, cands, run, exchange, compile_s, log, mods=str(ctx.get("in_mods") or ""))
        ranked = info.pop("ranked", None)
        if ranked and ctx.get("combo", True):   # the screened candidates predicted up, joined greedily (their edits verified)
            by_key = {e.key: e for e in list(res.get("verified") or []) + list(res.get("final") or [])}
            cb = J.combine(proof, statement, ranked, by_key, op=FAMILY, bad_sets=res.get("bad_sets") or ())
            if cb is not None and cb["decl"] not in {c["decl"] for c in cands}:
                cands = [cb] + cands
                info["combo"] = cb["note"][:60]
    rules = {}
    for e in res.get("final") or []:
        rules[e.rule] = rules.get(e.rule, 0) + 1
    by_key = {e.key: e for e in fresh}
    ok_r, bad_r = {}, {}   # per rule: edits verified in a clean copy / dropped by an error (the measured success rates)
    for e in res.get("verified") or []:
        ok_r[e.rule] = ok_r.get(e.rule, 0) + 1
    for k in res.get("failed") or {}:
        if k in by_key:
            r = by_key[k].rule
            bad_r[r] = bad_r.get(r, 0) + 1
    say(f"jointres: {len(es)} edit(s) ({len(fresh)} fresh), {res['status']} after {res['compiles']} compile(s) "
        f"[{'; '.join(str(r.get('clean')) + '/' + str(r.get('dropped')) for r in res['rounds'])}], final {len(res.get('final') or [])} "
        f"edit(s) -{sum(e.dtok for e in res.get('final') or [])} tok {rules}, verified {len(res.get('verified') or [])}, "
        f"{len(cands)} candidate(s){' screen ' + str(info) if info else ''}" + (f", why {res['why']}" if res.get("why") else "")
        + f" in {time.time() - t0:.1f} s")
    say(f"jointres rates: ok {ok_r} bad {bad_r}")
    return cands
