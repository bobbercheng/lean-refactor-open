#!/usr/bin/env python3
"""Open post-step (2026-11-03 ~12:15 UTC, "Trio + Q5 kernel-skip"; branch open-post): a $0, model-free, deterministic,
accept-gated pass over a finished open-package export. Input: <out>/proofs.jsonl (the export) and the package's --rows / --heartbeats
files; output: <out>/proofs.post.jsonl (one line per row, in the same order; a row the pass did not improve keeps its input line byte for
byte) and <out>/post_report.json; work files under <out>/post/. <out>/proofs.jsonl is never written.

  ops       (harness/post/; each reads only the proof, the statement and the row's own environment: no row name, table or proof text)
    implied     the closed line's bet D4 rule R1 with its point-free spellings (D4P): a `decide`-family closer decides the hypothesis Q of a
                library theorem `Q -> P` (or `P <-> Q`) found by an env query, instead of the goal P
    inlineeq    bet D4 rule R2: an equation proved inline in a simp-family lemma list -> `← by simpa using h ARGS` from its own hint or
                the hint's environment siblings (env query), plus its pure trims
    closerprep  bet D4C: `conv_rhs => reduce` (or lhs / both) before a `decide`-family closer, alone and jointly with a ddmin drop of
                the simp-family list before it (proposals chosen by a one-file measured query, harness/post/d4_measure.py)
    kskip       (harness/post/kskip.py) a closing `decide +kernel` -> `set_option debug.skipKernelTC true in decide +kernel` in place,
                and ` by` / `unfold P` / that line, P the head predicate of the statement
  v2 ops    (length tools v2, branch open-post-v2, 2026-11-03; generic, model-free, each reads only the proof, the statement and the
            row's own environment; an op runs (sites, queries, readings) only when it is in ORDER; --ops v1 = the four ops above only)
    hintgrind   (harness/post/hintgrind.py + spans.py) a tactic span (case region, arm, have body, block suffix) replaced by the one
                closer Lean prints for it (`grind? [H]`, `simp_all? [H]`, `simp? [H]`, region forms; H = the constants the span writes,
                resolved by an env query), probed on the oldest pin, screened by a one-file heartbeat reading
    projpath    (harness/post/projpath.py) a flat destructuring pattern -> one name + projection paths at its uses, screened by
                one-file single-site compiles on the primary pin, then the joint form
    lexsurf     (harness/post/lexsurf.py) lexer-cheap surface rules (leading-dot constructors, `Classical.em`, multi-line `have`
                ascriptions, binder-form `have`, a small bundle), applied jointly, verified by error-localised plain compiles
    jointres    (harness/post/jointres.py + joint.py) the never-tried residue of the open package's own pure surface generators,
                compiled jointly by an error-localised engine; proposes the best clean edit set, per-rule subsets, halves and singles
    t4ind       (harness/post/t4ind.py) the open package's T4 `t4:induction`: `induction / cases ... with` + named alternatives ->
                the bare tactic + one `·` bullet per goal in Lean's goal order (names from T4's probe)
    ctorsearch  (harness/post/ctorsearch.py) a fixed menu of cheap constructor / assumption closers tried at constructor-term sites
  gate      a candidate is adopted only when ALL hold, against the current proof measured on the same meter (harness/endstage.Meter,
            the end stage's direct path: the scorer's own heartbeat measurement on the primary pin, the official reference heartbeats,
            no local table): it starts with the row's exact statement followed by `:=` (scorer.tokenize.split_declaration); it passes
            scorer/forbidden.check_forbidden (unchanged: `set_option debug.skipKernelTC` is not on the Space list, nothing else is
            allowed); its primary reading scores higher (exact score); it compiles on EVERY pin of the row (Z 100); a fresh paired
            re-reading of the current proof and the candidate, back to back, still passes scorer.accept.decide with the worse candidate
            reading against the better current one and a strictly higher exact score; its rounded score is above the input's stored
            score; and the export's own `#print axioms` sorry audit (harness/open_package.audit_proof) reads it clean. Anything else,
            an exception, a timeout or a budget stop included, leaves the row's current proof as it is (never harm).
  search    per row: a pure pre-check (no op has a site: no compile at all); else the input measured on every pin, then up to PASSES
            passes: every op's candidates on the current proof (env queries on the primary pin), read on the primary pin in op order
            (kskip, implied, closerprep, inlineeq; at most READS[op] each; inlineeq's candidates go through the one-file measured
            screen first when there are more than SCREEN_MIN), the best primary reading that passes is confirmed (pins, paired
            re-reading, audit) and adopted, the next one tried when it fails; a pass that adopts nothing ends the row. Budgets: ROW_COMPILES
            compiles and ROW_SECONDS per row, --seconds for the whole step (no row starts after it; a running row stops at its next
            measurement and keeps what it has confirmed).
    python3 harness/open_post.py --rows R.jsonl --heartbeats H.jsonl --out OUT [--jobs N] [--seconds S] [--problems NAME ...]
Run by harness/open_package.py `post` (and `run --post on`, after the run's export) with the package environment (LRA_LOCAL_REF none,
the sorry guard, compile slots); standalone it sets the same itself."""
from __future__ import annotations

import argparse, hashlib, json, os, statistics, sys, threading, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

V1_ORDER = ("kskip", "implied", "closerprep", "inlineeq")
ORDER = V1_ORDER + ("hintgrind", "projpath", "lexsurf", "jointres", "t4ind", "ctorsearch")
READS = {"kskip": 4, "implied": 12, "closerprep": 3, "inlineeq": 6,   # primary readings per op and pass
         "hintgrind": 8, "projpath": 6, "lexsurf": 6, "jointres": 4, "t4ind": 4, "ctorsearch": 4}
SCREEN_MIN = 6           # inlineeq: more candidates than this are screened in one-file measured batches first
PASSES = 3
ROW_COMPILES = 240       # physical compiles per row (queries, screens, readings, pins, confirmations, audits); v1 120, v2 has 10 ops
ROW_SECONDS = 3600.0     # v1 2400 s
SECONDS = 7200.0         # the whole step's wall (no row starts after it)
QUERY_TIMEOUT = 300
CAND_TIMEOUT_MIN = 120
CAND_TIMEOUT_MULT = 4.0  # a candidate's compile timeout: this many times the input's primary compile seconds (at least the minimum)
IMPLIED_OPT_IN = ("implied:pointfree",)   # D4P on; the library-search bridge (D4S) stays off
POST_FILE, REPORT_FILE, WORK_DIR = "proofs.post.jsonl", "post_report.json", "post"


def log(msg: str) -> None:
    print(f"[{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}] [post] {msg}", flush=True)


def sha16(text: str) -> str:
    return hashlib.sha256(text.rstrip().encode()).hexdigest()[:16]


class _Stop(Exception):
    """A row's (or the step's) compile or wall budget is spent."""


# ------------------------------------------------------------------------------------------------------------------------------ meter
def make_meter(row: dict, ref_hb: dict, scratch: Path | None, log_fn=None):
    """harness/endstage.Meter on the direct path (the end stage's meter) with command(): a plain compile of `text` after the row's file
    prefix (the env queries' path; closed-bets-d4 Meter.command)."""
    from harness.endstage import Meter

    class PostMeter(Meter):
        def command(self, text: str, version: str | None = None, timeout: float | None = None):
            path = self.freeze()
            self._cand_timeout = timeout
            try:
                return self._one(text, version or self.versions[0], False, path)
            finally:
                self._cand_timeout = None
    m = PostMeter(row, ref_hb, prefer="direct", log=log_fn or (lambda *a: None))
    if scratch is not None:
        m.scratch = str(scratch)
    return m


class Budget:
    def __init__(self, meter, compiles: int, deadline: float, now=time.time):
        self.meter, self.max, self.deadline, self.now = meter, int(compiles), float(deadline), now

    def left_s(self) -> float:
        return self.deadline - self.now()

    def need(self, n: int) -> None:
        if self.now() >= self.deadline:
            raise _Stop("row wall budget")
        if self.meter.compiles + int(n) > self.max:
            raise _Stop("row compile budget")


# ------------------------------------------------------------------------------------------------------------------------------ ops
def _mods():
    from harness.post import d4_implied as I, d4_inlineeq as Q, d4_closerprep as CP, d4_measure as MS, kskip as KS
    return I, Q, CP, MS, KS


def sites(proof: str, statement: str) -> dict:
    """Which ops have a site in `proof` (pure: no compile)."""
    from scorer.tokenize import split_declaration
    I, Q, CP, MS, KS = _mods()
    body = split_declaration(proof, statement)
    if body is None:
        return {}
    out = {
        "kskip": lambda: bool(KS.candidates(proof, statement)),
        "implied": lambda: I.query_text(proof, statement) is not None,
        "closerprep": lambda: bool(CP.closer_sites(body)) and MS.renamed(statement, 0) is not None,
        "inlineeq": lambda: Q.query_text(proof, statement) is not None or bool(Q.candidates(proof, statement, ctx={})),
        "hintgrind": lambda: _op("hintgrind").has_sites(proof, statement),
        "projpath": lambda: bool(_op("projpath").sites(proof, statement)),
        "lexsurf": lambda: _op("lexsurf").has_site(proof, statement),
        "jointres": lambda: bool(_op("jointres").sites(proof, statement)),
        "t4ind": lambda: bool(_op("t4ind").sites(proof, statement)),
        "ctorsearch": lambda: _op("ctorsearch").has_sites(proof, statement),
    }
    have = {}
    for k, f in out.items():
        if k not in ORDER:
            continue
        try:
            if f():
                have[k] = True
        except Exception:  # noqa: BLE001  (an op's site detector fault: that op has no site; the others stand)
            pass
    return have


def _op(name: str):
    import importlib
    return importlib.import_module(f"harness.post.{name}")


def generate(proof: str, statement: str, run, versions, exchange, compile_s, log_fn, inc_hb=None, row_ctx: dict | None = None) -> dict:
    """{op: [candidate {"op", "decl", "note"}]} on `proof`; run(text, version) is the charged env-query compile. Only the ops in ORDER;
    a v2 op's own fault proposes nothing for that op (budget stops propagate). row_ctx: per-row facts of the row's own environment
    ({"in_mods": row_mods(row, primary pin)}); inc_hb: the current proof's heartbeats."""
    I, Q, CP, MS, KS = _mods()
    from scorer.tokenize import split_declaration
    body = split_declaration(proof, statement)
    out: dict = {}
    ctx: dict = {}
    if "implied" in ORDER and I.query_text(proof, statement) is not None:
        got = I.query(proof, statement, run, versions=versions, stats={}, log=log_fn) or {}
        ctx.update(got)
        out["implied"] = I.candidates(proof, statement, ctx=dict(got, opt_in=list(IMPLIED_OPT_IN)))
    if "closerprep" in ORDER and body is not None and CP.closer_sites(body) and MS.renamed(statement, 0) is not None:
        cctx = {"compile_s": compile_s, "exchange": exchange}
        got = CP.query(proof, statement, run, versions=versions, ctx=cctx, stats={}, log=log_fn) or {}
        out["closerprep"] = CP.candidates(proof, statement, exchange=exchange, ctx=dict(got, **cctx))
    if "inlineeq" in ORDER:
        qt = Q.query_text(proof, statement)
        got = (Q.query(proof, statement, run, versions=versions, stats={}, log=log_fn) or {}) if qt is not None else {}
        out["inlineeq"] = Q.candidates(proof, statement, exchange=exchange, ctx=got)
    if "kskip" in ORDER:
        out["kskip"] = KS.candidates(proof, statement, ctx=ctx)
    say = log_fn or (lambda *a: None)
    for name, fn in (("hintgrind", lambda: _gen_hintgrind(proof, statement, run, versions, exchange, compile_s, say, inc_hb)),
                     ("projpath", lambda: _gen_projpath(proof, statement, run, versions, exchange, compile_s, say)),
                     ("lexsurf", lambda: _gen_lexsurf(proof, statement, run, versions, exchange, compile_s, say)),
                     ("jointres", lambda: _op("jointres").generate(proof, statement, run, versions, exchange, compile_s, say,
                                                                   ctx=dict(row_ctx or {}))),
                     ("t4ind", lambda: gen_t4ind(proof, statement, run, compile_s, say)),
                     ("ctorsearch", lambda: gen_ctorsearch(proof, statement, run, versions, exchange, compile_s, say).get("ctorsearch"))):
        if name not in ORDER:
            continue
        try:
            got = fn()
            if got:
                out[name] = got
        except _Stop:
            raise
        except Exception as e:  # noqa: BLE001  (this op's fault proposes nothing; the other ops' candidates of this pass stand)
            say(f"{name}: failed ({type(e).__name__}: {str(e)[:200]}); no {name} candidates")
    return {k: v for k, v in out.items() if v}


def _gen_hintgrind(proof, statement, run, versions, exchange, compile_s, log_fn, inc_hb):
    HG = _op("hintgrind")
    if not HG.has_sites(proof, statement):
        return []
    got = HG.query(proof, statement, run, versions=versions,
                   ctx={"compile_s": compile_s, "exchange": exchange, "inc_hb": inc_hb}, stats={}, log=log_fn) or {}
    return HG.candidates(proof, statement, ctx=got)


def _gen_projpath(proof, statement, run, versions, exchange, compile_s, log_fn):
    PP = _op("projpath")
    if not PP.sites(proof, statement):
        return []
    got = PP.query(proof, statement, run, versions=versions, ctx={"compile_s": compile_s}, stats={}, log=log_fn) or {}
    return PP.candidates(proof, statement, exchange=exchange, ctx=got)


def _gen_lexsurf(proof, statement, run, versions, exchange, compile_s, log_fn):
    LS = _op("lexsurf")
    if not LS.has_site(proof, statement):
        return []
    got = LS.query(proof, statement, run, versions=versions, ctx={"compile_s": compile_s, "exchange": exchange}, stats={},
                   log=log_fn) or {}
    return LS.candidates(proof, statement, exchange=exchange, ctx=got)


def row_mods(row: dict, version: str) -> str:
    """jointres (harness/post/joint.in_mods): the `... in` combinators the row's own file prefix attaches to the declaration, one per
    line; '' for a header-only (putnam) row or when the prefix cannot be located."""
    if row.get("source") == "putnambench":
        return ""
    try:
        from scorer import compile as C
        from harness.post import joint as J
        core, tail = C.split_modifiers(C.file_prefix(row, version))
        return J.in_mods(core, tail, C._ATTACHED_IN)
    except Exception:  # noqa: BLE001  (no prefix: the copies go without; the control copy then tells)
        return ""


def gen_t4ind(proof: str, statement: str, run, compile_s, log_fn) -> list:
    """t4ind's candidates on `proof` (harness/post/t4ind.py): its probe (T4's, through `run`; cached per proof) when a site needs one."""
    T = _op("t4ind")
    if not T.sites(proof, statement):
        return []
    st: dict = {}
    got = T.query(proof, statement, run, ctx={"compile_s": compile_s}, stats=st, log=log_fn) or {}
    cs = T.candidates(proof, statement, ctx=got)
    b, p = st.get("batch") or {}, st.get("probe") or {}
    log_fn(f"t4ind: {len(cs)} candidate(s); probe {p.get('sites', 0)} site(s), {p.get('verified', 0)} verified, round 2 {p.get('round2', 0)}, "
           f"{b.get('files', 0)} file(s), {b.get('copies', 0)} cop(ies)" + (" (cached)" if st.get("cached") else ""))
    return cs


def gen_ctorsearch(proof: str, statement: str, run, versions, exchange, compile_s, log_fn) -> dict:
    """ctorsearch's part of generate(): its one-file screen (charged) and its proposals."""
    CT = _op("ctorsearch")
    if not CT.has_sites(proof, statement):
        return {}
    cctx = {"compile_s": compile_s, "exchange": exchange, "attached": attached_in(getattr(run, "meter", None))}
    got = CT.query(proof, statement, run, versions=versions, ctx=cctx, stats={}, log=log_fn) or {}
    return {"ctorsearch": CT.candidates(proof, statement, exchange=exchange, ctx=dict(got, **cctx))}


_ATTACHED: dict = {}


def attached_in(meter) -> str:
    """The `.. in` combinators the row's compile attaches to the declaration: the file prefix's trailing `set_option / omit / include /
    unseal / variable .. in` line (scorer.compile._ATTACHED_IN) and the `open .. in` among its trailing modifiers, one per line ("" when
    there is no meter or no file prefix, e.g. a header row)."""
    if meter is None:
        return ""
    row = getattr(meter, "row", None) or {}
    key = (row.get("name"), (getattr(meter, "versions", None) or [None])[0])
    if key in _ATTACHED:
        return _ATTACHED[key]
    out = ""
    try:
        import re
        from scorer import compile as SC
        if row.get("file_path") and row.get("source") != "putnambench":
            core, mods = SC.split_modifiers(SC.file_prefix(row, key[1]))
            m = SC._ATTACHED_IN.search(core)
            lines = [m.group(0).strip()] if m else []
            lines += [x.group(0).strip() for x in re.finditer(r"open\s+[\w.\s]+?\s+in\b", mods)]
            out = "".join(" ".join(x.split()) + "\n" for x in lines)
    except Exception:  # noqa: BLE001  (no prefix: the screen runs without combinators)
        out = ""
    _ATTACHED[key] = out
    return out


def static_ok(decl: str, statement: str) -> str | None:
    """None when the candidate starts with the exact statement + `:=` and passes the forbidden check, else the reason."""
    from scorer.forbidden import check_forbidden
    from scorer.tokenize import split_declaration
    if split_declaration(decl, statement) is None or not decl.startswith(statement):
        return "statement differs"
    bad = check_forbidden(decl)
    return f"forbidden: {bad}" if bad else None


def screen(cands: list, statement: str, inc_body: str, run, exchange, compile_s, keep: int) -> tuple[list, dict]:
    """inlineeq's candidates through d4_measure's one-file batches (the closed D4C query's measurement): the incumbent first in every
    file as the control; the candidates predicted to read higher (heartbeats saved minus tokens added at the exchange rate), best first,
    at most `keep`. A file whose control does not read leaves its candidates unscreened (they follow the screened ones, in order)."""
    I, Q, CP, MS, KS = _mods()
    from scorer.tokenize import split_declaration
    if MS.renamed(statement, 0) is None:
        return cands[:keep], {"screened": False, "why": "not a theorem / lemma statement"}
    n = MS.budget({"compile_s": compile_s})
    scored, unscreened, files = [], [], 0
    for i in range(0, len(cands), n - 1):
        chunk = cands[i:i + n - 1]
        bodies = [split_declaration(c["decl"], statement) for c in chunk]
        text = MS.text(statement, [inc_body] + bodies)
        if text is None:
            unscreened += chunk
            continue
        r = run(text, None)
        files += 1
        rd = MS.parse(getattr(r, "messages", None), len(chunk) + 1)
        ctl = rd.get(0) or {"ok": False}
        if not ctl.get("ok"):
            unscreened += chunk
            continue
        for k, (c, b) in enumerate(zip(chunk, bodies), 1):
            pr = MS.predicted(ctl, inc_body, b, rd.get(k) or {"ok": False}, exchange)
            if pr is not None and pr > 0:
                scored.append((pr, i + k, c))
    scored.sort(key=lambda x: (-x[0], x[1]))
    picked = [c for _, _, c in scored] + unscreened
    return picked[:keep], {"screened": True, "files": files, "predicted_up": len(scored), "unscreened": len(unscreened)}


# ------------------------------------------------------------------------------------------------------------------------------ gate
def _metric(meter, rd: dict, Z: float) -> dict:
    m = meter.metrics(int(rd["tokens"]), int(rd["heartbeats"]), float(Z))
    return {"score": m["score_exact"], "tokens": int(rd["tokens"]), "heartbeats": int(rd["heartbeats"]), "Z": float(Z), "L": m["L"], "H": m["H"]}


def _ok(rd) -> bool:
    return bool(rd) and bool(rd.get("ok")) and rd.get("heartbeats") is not None and rd.get("tokens") is not None


def improve_row(row: dict, proof: str, stored, meter, budget: Budget, audit=None, log_fn=None) -> dict:
    """The row's search (module docstring). Returns {"status", "proof" (the final one), "before", "after", "chain", "decisions", ...};
    status "adopted" only when the final proof differs from the input and passed the whole gate."""
    from scorer.accept import decide
    from scorer.tokenize import split_declaration
    say = log_fn or (lambda *a: None)
    st = row["statement"]
    decisions: list = []
    res = {"status": "kept", "proof": proof, "decisions": decisions, "chain": []}
    if split_declaration(proof, st) is None:
        res["reason"] = "the input does not start with the statement"; return res
    have = sites(proof, st)
    res["sites"] = sorted(have)
    if not have:
        res["status"] = "no_site"; return res
    budget.need(meter.cost(True))
    r0 = meter.measure(proof, full=True)
    if not _ok(r0):
        res["reason"] = f"the input does not read here: {str(r0.get('error'))[:200]}"; res["status"] = "unreadable"; return res
    Z0 = float(r0["Z"])
    inc = {"proof": proof, "reading": r0, "m": _metric(meter, r0, Z0)}
    res["before"] = dict(inc["m"], compat=r0.get("compat"), seconds=r0.get("seconds"))
    floor = float(stored) if isinstance(stored, (int, float)) else None
    ref_n = row.get("proof_length")
    exchange = (float(meter.ref_hb) / float(ref_n)) if meter.ref_hb and ref_n else None
    compile_s = float(r0.get("seconds") or 0.0) or None
    to = max(CAND_TIMEOUT_MIN, int(CAND_TIMEOUT_MULT * (compile_s or CAND_TIMEOUT_MIN)))

    def run(text, version=None):
        budget.need(1)
        r, _n = meter.command(text, version, timeout=QUERY_TIMEOUT)
        return r
    run.meter = meter   # an op that needs the row's file context (ctorsearch: the combinators attached to the declaration)
    row_ctx = {"in_mods": row_mods(row, meter.versions[0])} if "jointres" in ORDER else {}

    for pas in range(1, PASSES + 1):
        cur = inc["proof"]
        try:
            fam = generate(cur, st, run, list(meter.versions), exchange, compile_s, say, inc_hb=inc["m"]["heartbeats"], row_ctx=row_ctx)
        except _Stop:
            raise
        except Exception as e:  # noqa: BLE001  (a generator / query fault proposes nothing; the row keeps its proof)
            decisions.append({"pass": pas, "op": "generate", "error": f"{type(e).__name__}: {str(e)[:200]}"}); break
        reads = []
        for op in ORDER:
            cs = [dict(c, family=op) for c in fam.get(op) or []]
            seen = set()
            cs2 = []
            for c in cs:
                why = static_ok(c["decl"].rstrip(), st)
                key = sha16(c["decl"])
                if why or key in seen or c["decl"].rstrip() == cur.rstrip():
                    if why:
                        decisions.append({"pass": pas, "op": c["op"], "note": c.get("note", "")[:120], "verdict": why})
                    continue
                seen.add(key); cs2.append(c)
            if op == "inlineeq" and len(cs2) > SCREEN_MIN:
                cs2, info = screen(cs2, st, split_declaration(cur, st), run, exchange, compile_s, READS[op])
                decisions.append({"pass": pas, "op": "inlineeq:screen", **info})
            for c in cs2[:READS[op]]:
                budget.need(meter.cost(False))
                rd = meter.measure(c["decl"].rstrip(), full=False, Z=100.0, timeout=to)
                d = {"pass": pas, "op": c["op"], "note": c.get("note", "")[:160], "tokens": rd.get("tokens"), "hb": rd.get("heartbeats")}
                if not _ok(rd):
                    d["verdict"] = "no compile: " + str(rd.get("error"))[:160]
                else:
                    mc = _metric(meter, rd, 100.0)
                    ok, why = decide(inc["m"], mc)
                    d.update(score=round(mc["score"], 4), verdict=("primary passes: " if ok and mc["score"] > inc["m"]["score"] else "below: ") + why)
                    if ok and mc["score"] > inc["m"]["score"]:
                        reads.append((mc["score"], len(reads), c, rd))
                decisions.append(d)
        adopted = False
        for _s, _k, c, rd in sorted(reads, key=lambda x: (-x[0], x[1])):
            decl = c["decl"].rstrip()
            d = {"pass": pas, "op": c["op"], "confirm": True}
            budget.need(max(0, len(meter.versions) - 1))
            pins = meter.pins(decl, timeout=to)
            if not all(pins["compat"].values()):
                d["verdict"] = f"fails a pin: {sorted(v for v, ok in pins['compat'].items() if not ok)}"; decisions.append(d); continue
            budget.need(2 * meter.cost(False))
            i2 = meter.measure(inc["proof"], full=False, Z=inc["m"]["Z"], timeout=to)
            c2 = meter.measure(decl, full=False, Z=100.0, timeout=to)
            if not (_ok(i2) and _ok(c2)):
                d["verdict"] = "the paired re-reading failed"; decisions.append(d); continue
            ib = inc["reading"] if inc["reading"]["heartbeats"] <= i2["heartbeats"] else i2
            cw = rd if rd["heartbeats"] >= c2["heartbeats"] else c2
            mi, mc = _metric(meter, ib, inc["m"]["Z"]), _metric(meter, cw, 100.0)
            ok, why = decide(mi, mc)
            d.update(inc_hb=[inc["reading"]["heartbeats"], i2["heartbeats"]], cand_hb=[rd["heartbeats"], c2["heartbeats"]],
                     score=round(mc["score"], 4), inc_score=round(mi["score"], 4))
            if not (ok and mc["score"] > mi["score"]):
                d["verdict"] = "paired re-reading: " + why; decisions.append(d); continue
            if floor is not None and round(mc["score"], 2) <= floor:
                d["verdict"] = f"not above the input's stored score {floor}"; decisions.append(d); continue
            if audit is not None:
                budget.need(len(meter.versions))
                ast, awhy = audit(row, decl)
                d["audit"] = ast
                if ast not in ("clean", "skipped"):
                    d["verdict"] = f"audit {ast}: {awhy}"[:200]; decisions.append(d); continue
            d["verdict"] = f"adopted: {why}"; decisions.append(d)
            say(f"{row['name'][:48]}: pass {pas} adopted {c['op']} ({mi['score']:.4f} -> {mc['score']:.4f})")
            inc = {"proof": decl, "reading": dict(cw, compat=pins["compat"]), "m": mc}
            res["chain"].append({"pass": pas, "op": c["op"], "note": c.get("note", "")[:160], "score": round(mc["score"], 4),
                                 "tokens": mc["tokens"], "heartbeats": mc["heartbeats"], "audit": d.get("audit")})
            adopted = True
            break
        if not adopted:
            break
    if inc["proof"].rstrip() != proof.rstrip():
        res.update(status="adopted", proof=inc["proof"], after=dict(inc["m"], compat=inc["reading"].get("compat")),
                   gain=round(inc["m"]["score"] - res["before"]["score"], 4))
    return res


# ------------------------------------------------------------------------------------------------------------------------------ step
def load_inputs(rows_path, hbs_path) -> tuple[dict, dict]:
    rows = {}
    for l in Path(rows_path).read_text().splitlines():
        if l.strip():
            r = json.loads(l); rows[r["name"]] = r
    hbs = {}
    for l in Path(hbs_path).read_text().splitlines():
        if l.strip():
            r = json.loads(l); hbs[r["name"]] = r.get("heartbeat")
    return rows, hbs


def default_audit():
    from harness.open_package import audit_proof
    from probe.verify_candidates import newest_first

    def audit(row, decl):
        return audit_proof(row, decl, newest_first(row["version_info"]), {})
    return audit


def post_out_record(rec: dict, res: dict) -> dict:
    a = res.get("after") or {}
    return {"name": rec["name"], "proof": res["proof"].rstrip() + "\n", "source": "post", "post_from": rec.get("source"),
            "stored_score": round(float(a["score"]), 2), "tokens": a.get("tokens"), "heartbeats": a.get("heartbeats"),
            "post_gain": res.get("gain"), "post_ops": [x["op"] for x in res.get("chain") or []],
            "audit": ((res.get("chain") or [{}])[-1]).get("audit") or rec.get("audit")}


def post_step(rows_path, hbs_path, out, *, jobs: int = 2, seconds: float = SECONDS, row_seconds: float = ROW_SECONDS,
              row_compiles: int = ROW_COMPILES, problems=None, input_path=None, scratch=None, audit="default", meter_factory=None,
              now=time.time) -> dict:
    """The step (module docstring). Returns the report (also written to <out>/post_report.json)."""
    out = Path(out)
    t0 = now()
    deadline = t0 + float(seconds)
    inp = Path(input_path) if input_path else out / "proofs.jsonl"
    raw_lines = [l for l in inp.read_text().splitlines() if l.strip()]
    recs = [json.loads(l) for l in raw_lines]
    rows, hbs = load_inputs(rows_path, hbs_path)
    work = out / WORK_DIR; work.mkdir(parents=True, exist_ok=True)
    scratch = Path(scratch) if scratch else Path(os.environ.get("LRA_HBTOOL_SCRATCH") or
                                                  ROOT / "probe/hbtool/.scratch" / f"post-{hashlib.sha256(str(out.resolve()).encode()).hexdigest()[:10]}")
    aud = default_audit() if audit == "default" else audit
    mk = meter_factory or (lambda row: make_meter(row, {row["name"]: hbs.get(row["name"])}, scratch, None))
    want = set(problems) if problems else None
    results: dict = {}
    lock = threading.Lock()
    rec_path = work / "rows.jsonl"

    def one(k: int):
        rec = recs[k]; n = rec.get("name")
        base = {"row": k, "name": n, "input_sha": sha16(rec.get("proof") or "")}
        try:
            if n not in rows:
                return k, dict(base, status="kept", reason="not in the rows file")
            if want is not None and n not in want:
                return k, dict(base, status="kept", reason="not in --problems")
            row = rows[n]
            if now() >= deadline:
                return k, dict(base, status="skipped", reason="the step's wall budget was spent before this row")
            proof = (rec.get("proof") or "").rstrip()
            if not sites(proof, row["statement"]):
                return k, dict(base, status="no_site")
            meter = mk(row)
            b = Budget(meter, row_compiles, min(deadline, now() + float(row_seconds)), now=now)
            ts = now()
            say = lambda m: log(f"row#{k:02d} {m}")   # noqa: E731
            try:
                r = improve_row(row, proof, rec.get("stored_score"), meter, b, audit=aud, log_fn=say)
            except _Stop as e:
                r = {"status": "stopped", "reason": str(e), "proof": proof}
            r = dict(base, **r, compiles=meter.compiles, seconds=round(now() - ts, 1))
            if r.get("status") == "stopped":
                r["proof"] = proof
            return k, r
        except Exception as e:  # noqa: BLE001  (a row's failure is recorded; the row keeps its input line)
            return k, dict(base, status="error", reason=f"{type(e).__name__}: {str(e)[:300]}")

    def done(k, r):
        with lock:
            results[k] = r
            with rec_path.open("a") as fh:
                fh.write(json.dumps({x: v for x, v in r.items() if x != "decisions"} | {"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())},
                                    ensure_ascii=False) + "\n")
            with (work / "decisions.jsonl").open("a") as fh:
                for d in r.get("decisions") or []:
                    fh.write(json.dumps(dict(d, row=k), ensure_ascii=False) + "\n")
            st = r.get("status")
            if st != "no_site" and r.get("reason") not in ("not in --problems", "not in the rows file"):
                log(f"row#{k:02d} {str(r.get('name'))[:48]}: {st}" + (f" {r.get('gain'):+.4f}" if st == "adopted" else "")
                    + (f" ({r.get('reason')})" if r.get("reason") else "") + (f" {r.get('compiles')} compiles, {r.get('seconds')} s" if r.get("compiles") else ""))

    with ThreadPoolExecutor(max(1, int(jobs)), thread_name_prefix="opk-post") as ex:
        for k, r in ex.map(one, range(len(recs))):
            done(k, r)
    lines, adopted, gain = [], 0, 0.0
    for k, (line, rec) in enumerate(zip(raw_lines, recs)):
        r = results.get(k) or {}
        if r.get("status") == "adopted":
            lines.append(json.dumps(post_out_record(rec, r), ensure_ascii=False))
            adopted += 1; gain += float(r.get("gain") or 0.0)
        else:
            lines.append(line)
    text = "".join(l + "\n" for l in lines)
    tmp = out / (POST_FILE + ".tmp"); tmp.write_text(text); os.replace(tmp, out / POST_FILE)
    before = [float(r["stored_score"]) for r in recs if isinstance(r.get("stored_score"), (int, float))]
    after = [float(json.loads(l)["stored_score"]) for l in lines if isinstance(json.loads(l).get("stored_score"), (int, float))]
    counts: dict = {}
    for r in results.values():
        counts[r.get("status")] = counts.get(r.get("status"), 0) + 1
    rep = {"input": {"path": str(inp), "sha256": hashlib.sha256(inp.read_bytes()).hexdigest(), "rows": len(recs)},
           "output": {"path": str(out / POST_FILE), "sha256": hashlib.sha256(text.encode()).hexdigest()},
           "adopted": adopted, "statuses": counts, "gain_sum_paired": round(gain, 4),
           "stored_mean_before": round(statistics.mean(before), 4) if before else None,
           "stored_mean_after": round(statistics.mean(after), 4) if after else None,
           "seconds": round(now() - t0, 1), "compiles": sum(int(r.get("compiles") or 0) for r in results.values()),
           "config": {"order": list(ORDER), "reads": {k: READS[k] for k in ORDER}, "screen_min": SCREEN_MIN, "passes": PASSES, "row_compiles": int(row_compiles),
                      "row_seconds": float(row_seconds), "seconds": float(seconds), "jobs": int(jobs), "implied_opt_in": list(IMPLIED_OPT_IN),
                      "problems": sorted(want) if want else None},
           "rows": [{x: v for x, v in (results.get(k) or {}).items() if x not in ("decisions", "proof")} for k in range(len(recs))],
           "at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    (out / REPORT_FILE).write_text(json.dumps(rep, indent=1, ensure_ascii=False))
    log(f"done: {adopted} row(s) adopted, paired gain {gain:+.4f}, stored mean {rep['stored_mean_before']} -> {rep['stored_mean_after']}, "
        f"{rep['compiles']} compiles, {rep['seconds']} s -> {out / POST_FILE}")
    return rep


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--rows", required=True); ap.add_argument("--heartbeats", required=True); ap.add_argument("--out", required=True)
    ap.add_argument("--input", default=None, help="the export to post-process (default <out>/proofs.jsonl)")
    ap.add_argument("--jobs", type=int, default=2, help="rows at once")
    ap.add_argument("--seconds", type=float, default=SECONDS, help="the step's wall: no row starts after it")
    ap.add_argument("--row-seconds", type=float, default=ROW_SECONDS)
    ap.add_argument("--row-compiles", type=int, default=ROW_COMPILES)
    ap.add_argument("--problems", nargs="*", default=None)
    ap.add_argument("--keep-local-ref", action="store_true", help="keep the local reference-heartbeat table (dev rows only)")
    ap.add_argument("--ops", default="all", help="'all' (default: v1 + v2 ops), 'v1' (kskip, implied, closerprep, inlineeq only) or a "
                                                 "comma-separated subset of ORDER")
    a = ap.parse_args(argv)
    global ORDER
    if a.ops == "v1":
        ORDER = V1_ORDER
    elif a.ops != "all":
        want = [x.strip() for x in a.ops.split(",") if x.strip()]
        bad = [x for x in want if x not in ORDER]
        if bad:
            ap.error(f"unknown op(s) {bad}; ORDER is {list(ORDER)}")
        ORDER = tuple(x for x in ORDER if x in want)
    from harness.open_package import SORRY_GUARD_ENV, git_trust
    os.environ.update(SORRY_GUARD_ENV)
    git_trust(os.environ)
    if not a.keep_local_ref:
        os.environ["LRA_LOCAL_REF"] = "none"
    post_step(a.rows, a.heartbeats, a.out, jobs=a.jobs, seconds=a.seconds, row_seconds=a.row_seconds, row_compiles=a.row_compiles,
              problems=a.problems, input_path=a.input)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
