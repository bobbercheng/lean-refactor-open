#!/usr/bin/env python3
"""POST-HOC (2026-11-05) v7m executor warm-up for the merged candidate (idea #3; NOT part of any upload). Standalone: pf_worker.py is
NOT edited here (another agent owns it); integration is later (snippet below).

What it warms. With LRA_POST_MERGE=1 the decision code (this dir's code/harness/open_post.py, improve_row) reads ONE more candidate per
round after its reads: the merge of the round's passing readings (open_post.merge_candidate). That read, its pins and its audit sit on
the charged path right before the confirmations, and nothing in pf_worker warms them (the text exists only after the reads). This
module computes the SAME merged text from the round's warmed readings and warms its primary reading, its other pins and its sorry audit,
speculatively (never charged; pf_svc memo draws: the charged merged read consumes the draw this compile leaves).

How the text is matched. warm_merge() replays improve_row's read phase on the round's candidates exactly as pf_worker's own read
warm-up does (open_post.static_ok, sha16 dedup, the incumbent's own text skipped, READS[op] per op, ORDER), then for each planned read
takes its primary reading through the speculative Evaluator (a memo join of the warm-up's compile), judges it with improve_row's
rule (scorer.accept.decide against the incumbent's metric and a strictly higher score), and builds `reads` [(score, k, c, rd)] in
improve_row's order; the merged text is open_post.merge_candidate(proof, reads) - the decision code's own function.
Known divergences (the warmed text then differs from the charged one: the charged merged read is a cold compile, nothing else changes):
  - inlineeq with more than SCREEN_MIN candidates (the charged path screens and reorders them first; those reads are left out here,
    as in pf_worker's read warm-up);
  - a charged reads cut (reserve_hit) that drops later reads;
  - heartbeat draws: a borderline read can pass on one draw and not on another (decide: HB_EPS 3; draws vary by +-1-2);
  - the incumbent metric: read from improve_row's frame (inc["m"], exact); without the frame it is rebuilt from inc_hb and Z 100.

Integration (later; pf_worker.generate(), at the end of its read warm-up `try:` block, after the warm loop):
    if MERGE_WARM and not NOSPEC:          # MERGE_WARM = os.environ.get("LRA_POST_MERGE") == "1"
        import merge_warm as MW
        MW.warm_merge(P, sys.modules[__name__], fam, proof, statement, meter, compile_s,
                      MW.inc_metric(sys._getframe(1), P, meter, proof, inc_hb))
  (sys._getframe(1) there is improve_row's frame: improve_row calls open_post.generate, which pf_worker replaced by its generate.)
W is the pf_worker module: its bound_spec, spec_ev, _compile_with, _to_eff, warm, audit_warm and NOSPEC are used, nothing else.
warm_merge returns at once (one speculative task), never raises, never touches the charged meter or the real op memories.
"""
from __future__ import annotations

import threading

_DONE: set = set()
_LK = threading.Lock()
STATS = {"merge_warm_tasks": 0, "merge_warm_texts": 0, "merge_warm_none": 0, "merge_warm_errors": 0}


def inc_metric(fr, P, meter, proof, inc_hb=None):
    """The incumbent metric improve_row compares the round's readings with: its frame's inc["m"] (read only) when `fr` is improve_row's
    frame; else rebuilt from inc_hb (tokens counted like the meter, Z 100); None when neither is possible."""
    try:
        if fr is not None and fr.f_code is P.improve_row.__code__:
            m = fr.f_locals["inc"]["m"]
            return {k: m[k] for k in ("score", "tokens", "heartbeats", "Z", "L", "H") if k in m}
    except Exception:  # noqa: BLE001
        pass
    if inc_hb is None:
        return None
    try:
        from scorer.tokenize import count_tokens, split_declaration
        tokens = count_tokens(split_declaration(proof, meter.statement))
        m = meter.metrics(tokens, int(inc_hb), 100.0)
        return {"score": m["score_exact"], "tokens": tokens, "heartbeats": int(inc_hb), "Z": 100.0, "L": m["L"], "H": m["H"]}
    except Exception:  # noqa: BLE001
        return None


def read_plan(P, fam: dict, proof: str, statement: str) -> list:
    """improve_row's reads of this round, in order (each candidate tagged family=op as improve_row does), before any reserve cut;
    inlineeq's candidates are left out when its charged screen would reorder them (> SCREEN_MIN)."""
    plan = []
    for op in P.ORDER:
        cs = [dict(c, family=op) for c in fam.get(op) or []]
        seen, cs2 = set(), []
        for c in cs:
            why = P.static_ok(c["decl"].rstrip(), statement)
            key = P.sha16(c["decl"])
            if why or key in seen or c["decl"].rstrip() == proof.rstrip():
                continue
            seen.add(key); cs2.append(c)
        if op == "inlineeq" and len(cs2) > P.SCREEN_MIN:
            continue
        plan += cs2[:P.READS[op]]
    return plan


def judge(P, meter, plan: list, readings: dict, inc_m: dict) -> list:
    """improve_row's `reads` from the planned candidates' primary readings {decl.rstrip(): reading}: _metric(meter, rd, 100.0), decide()
    against inc_m and a strictly higher exact score -> (score, k, c, rd), k the read's index among the passing ones (improve_row's)."""
    from scorer.accept import decide
    reads = []
    for c in plan:
        rd = readings.get(c["decl"].rstrip())
        if not P._ok(rd):
            continue
        mc = P._metric(meter, rd, 100.0)
        ok, _why = decide(inc_m, mc)
        if ok and mc["score"] > inc_m["score"]:
            reads.append((mc["score"], len(reads), c, rd))
    return reads


def merged_text(P, proof: str, statement: str, reads: list):
    """The decision code's merged text for these reads (None: no merge proposal, or it fails the static check)."""
    if len(reads) < 2:
        return None
    c, _why = P.merge_candidate(proof, reads)
    if c is None:
        return None
    decl = c["decl"].rstrip()
    if P.static_ok(decl, statement) or decl == proof.rstrip() or P.sha16(decl) in {P.sha16(x[2]["decl"]) for x in reads}:
        return None
    return decl


def warm_merge(P, W, fam, proof, statement, meter, compile_s, inc_m, *, eager_pins=True, on_text=None):
    """Start the merge warm-up for this round (module docstring); returns the speculative future (None: nothing to do). on_text(text)
    is called with the warmed merged text (tests / logs)."""
    try:
        if not P.merge_on() or getattr(W, "NOSPEC", False) or inc_m is None or meter is None:
            return None
        plan = read_plan(P, fam or {}, proof, statement)
        if len(plan) < 2:
            return None
        key = (getattr(meter, "name", None), P.sha16(proof), tuple(P.sha16(c["decl"]) for c in plan))
        with _LK:
            if key in _DONE:
                return None
            _DONE.add(key)
        to = max(P.CAND_TIMEOUT_MIN, int(P.CAND_TIMEOUT_MULT * (compile_s or P.CAND_TIMEOUT_MIN)))

        def task():
            STATS["merge_warm_tasks"] += 1
            try:
                to_eff = W._to_eff(meter, to)
                ev = W.spec_ev(meter)
                readings = {}
                for c in plan:   # in order; each joins the read warm-up's in-flight compile (or its memo draw)
                    d = c["decl"].rstrip().strip()
                    if meter._check(d) is not None:
                        continue
                    prim, n = W._compile_with(ev, meter, d, meter.versions[0], True, to_eff)
                    readings[c["decl"].rstrip()] = meter._reading(d, prim, None, 100.0, "direct", n)
                text = merged_text(P, proof, statement, judge(P, meter, plan, readings, inc_m))
                if text is None:
                    STATS["merge_warm_none"] += 1
                    return
                STATS["merge_warm_texts"] += 1
                if on_text is not None:
                    on_text(text)
                if eager_pins:   # the confirmation's pins and audit start with the merged primary (idle CPU in the tail)
                    for v in meter.versions[1:]:
                        W.warm(meter, text, v, False, to)
                    W.audit_warm(meter.row, text)
                W._compile_with(ev, meter, text.strip(), meter.versions[0], True, to_eff)
                if not eager_pins:
                    for v in meter.versions[1:]:
                        W.warm(meter, text, v, False, to)
                    W.audit_warm(meter.row, text)
            except Exception:  # noqa: BLE001  (speculation only)
                STATS["merge_warm_errors"] += 1
        return W.bound_spec(task)
    except Exception:  # noqa: BLE001
        STATS["merge_warm_errors"] += 1
        return None
