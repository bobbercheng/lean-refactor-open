#!/usr/bin/env python3
"""Census mode of the end stage (open-track re-derivation, docs/open_tools_rederive.md 2.4, Step 2; branch open-rederive only).




















"""
from __future__ import annotations

import math, re, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _ok(r) -> bool:
    return bool(r) and bool(r.get("ok")) and r.get("heartbeats") is not None and r.get("tokens") is not None


def _site_of(raw: dict, note: str | None) -> str | None:
    if raw.get("site") is not None:
        return str(raw["site"])
    if raw.get("span") is not None:
        return str(raw["span"])
    m = re.search(r"@L(\d+)", note or "")
    if m:
        return "L" + m.group(1)
    m = re.search(r"\bL(\d+)(?:-\d+)?\b", note or "")
    return ("L" + m.group(1)) if m else None


def _raw_dicts(raw) -> list[dict]:
    """The generator's output as dicts {"op", "decl", "note", "site", "timeout_s", "closer", "span"} (sweep_items' accepted forms)."""
    out = []
    for x in raw or []:
        if isinstance(x, dict):
            out.append(x)
        elif hasattr(x, "op") or hasattr(x, "kind"):
            out.append({"op": getattr(x, "op", None) or getattr(x, "kind", None), "decl": getattr(x, "decl", None) or getattr(x, "proof", None),
                        "note": getattr(x, "note", None)})
        elif isinstance(x, str):
            out.append({"decl": x})
    return out


def census_row(name: str, row: dict, final: dict | None, meter, a, cfg: dict, log) -> dict:
    from harness import endstage as ES
    from harness import open_config as OC
    from scorer.accept import decide
    from scorer.compile import CompileResult                                                                         
    from probe.open_rederive.ops import canon
    from probe.open_rederive import opentables as OT
    t_row = time.time()
    statement = row["statement"]
    seed = row["src"].strip()
    inp = ((final or {}).get("proof") or seed).strip()
    group = "seed" if ES.sha(inp) == ES.sha(seed) else "final"
    budgets = dict(cfg["budgets"][group])
    pools = dict(cfg.get("pools") or {})
    n_samples = int(cfg.get("probe_hb_samples", 2))
    acc = OC.accept_values()
    fams = ES.families_for(a.sweep, a.tools)
    spent = [0]
    I = meter.measure(inp, full=True)
    spent[0] += int(I.get("compiles") or 0)
    base = {"problem": name, "group": group, "census": True, "code": None}
    if not _ok(I) or not I.get("compat"):
        log(f"census: the input does not compile on this meter ({(I.get('error') or '?')[:100]})")
        return dict(base, input={"ok": False, "error": (I.get("error") or "")[:300]}, out={"proof": inp, "census": "input does not compile"},
                    end={"stage": "census-no-input"}, delta=None, compiles=spent[0], families={}, candidates=[], seconds=round(time.time() - t_row, 1))
    I = dict(I)
    inp_read = {k: I.get(k) for k in ("score", "score_exact", "tokens", "heartbeats", "Z", "seconds", "L", "H")}
    compile_secs = [I.get("seconds")]
    ex = (meter.ref_hb / row["proof_length"]) if getattr(meter, "ref_hb", None) and row.get("proof_length") else None
    scr = meter.screener(k=getattr(a, "screen_k", ES.SCREEN_K), max_depth=a.screen_depth if getattr(a, "screen_depth", None) is not None
                         else ES.SCREEN_DEPTH, cache={}, log=log) if hasattr(meter, "screener") else None
    from harness.batch_screen import hb_bound
    hbcap = hb_bound(meter.metrics, I)
    pool_left = {}
    decided: dict = {}                                                
    records: list[dict] = []
    fam_out: dict = {}
    probe_samples: list[dict] = []

    class _Stop(Exception):
        pass

    def fam_ctx(fam):
        c = {"source": row.get("source"), "pins": list(getattr(meter, "versions", None) or [])}
        if isinstance(I.get("seconds"), (int, float)) and I["seconds"] > 0:
            c["compile_s"] = I["seconds"]
        if fam == "hr":
            c["row"] = row
        fo = getattr(a, "family_ops", None) or {}
        if fam in fo:
            c["ops"] = list(fo[fam])
        for f, d in (ES.family_ctx_of(a) or {}).items():
            if f == fam:
                c.update(d)
        return c

    def batch_cb(mod, F, deadline, hb_cap, k=None, max_files=None):
        from harness.tools import t3_suggest as SG
        L = scr._lay() if scr is not None else None
        if L is None:
            return None

        def need(n):
            if time.time() > deadline:
                raise _Stop("budget")

        def charge(n):
            spent[0] += int(n)
            F["compiles"] += int(n)
            F["probe_compiles"] = F.get("probe_compiles", 0) + int(n)
        return SG.batch_compiler(statement, scr.compile_fn, L, hb_cap=hb_cap, compile_s=I.get("seconds"), timeout=int(getattr(scr, "timeout", 900) or 900),
                                 k=k or getattr(mod, "PROBE_K", SG.PROBE_K), need=need, charge=charge, stats=F.setdefault("probe", {}),
                                 log=log, max_files=max_files if max_files is not None else getattr(mod, "PROBE_MAX_FILES", SG.PROBE_MAX_FILES))

    def measure(text, full, timeout=None, Z=None):
        r = meter.measure(text, full=full, Z=Z, **({"timeout": timeout} if timeout else {}))
        spent[0] += int(r.get("compiles") or 0)
        return r

    def judge(rec, text, F, deadline):
        """Primary reading, cost guard, paired input reading, decide, confirmation, decide. Fills rec."""
        ts, c0 = time.time(), spent[0]
        try:
            if time.time() > deadline:
                raise _Stop("budget")
            body = ES.split_declaration(text, statement)
            if body is None:
                rec.update(decision="reject", reject="statement")
                return
            z_inc = float(I["Z"])
            c1 = measure(text, False, timeout=rec.get("timeout_s"), Z=z_inc)
            if not _ok(c1):
                err = c1.get("error") or "?"
                rec.update(decision="reject", compiled=False, reject="timeout" if c1.get("timed_out") or err == "timeout" else "no_compile")
                return
            rec["compiled"] = True
            if isinstance(c1.get("seconds"), (int, float)):
                rec["cand_s"] = c1["seconds"]
            if z_inc < 100.0:
                if time.time() > deadline:
                    raise _Stop("budget")
                cp = meter.pins(text, **({"timeout": rec["timeout_s"]} if rec.get("timeout_s") else {}))
                spent[0] += int(cp.get("compiles") or 0)
                zs = ES.compat_pct(cp["compat"]) if cp.get("compat") else z_inc
                c1 = dict(c1, Z=zs, **meter.metrics(c1["tokens"], c1["heartbeats"], zs))
            cand = {"score": c1["score_exact"], "tokens": c1["tokens"], "heartbeats": c1["heartbeats"], "Z": c1.get("Z", z_inc)}
            m = int(acc["screen_hb"]) + math.ceil(float(acc["screen_frac"]) * I["heartbeats"])
            stale = {"score": meter.metrics(I["tokens"], I["heartbeats"] + m, z_inc)["score_exact"], "tokens": I["tokens"],
                     "heartbeats": I["heartbeats"] + m, "Z": z_inc}
            ok, why = decide(stale, cand)
            rec.update(d_score=round(cand["score"] - I["score_exact"], 6), d_tokens=I["tokens"] - cand["tokens"], d_heartbeats=I["heartbeats"] - cand["heartbeats"])
            if not ok:
                rec.update(decision="reject", reject=ES._why(why), at="screen")
                return
            if time.time() > deadline:
                raise _Stop("budget")
            i1 = measure(inp, False, Z=z_inc)
            if not _ok(i1):
                rec.update(decision="reject", reject="meter")
                return
            if isinstance(i1.get("seconds"), (int, float)):
                compile_secs.append(i1["seconds"])
            paired = {"score": i1["score_exact"], "tokens": i1["tokens"], "heartbeats": i1["heartbeats"], "Z": z_inc}
            ok, why = decide(paired, cand)
            rec.update(d_score=round(cand["score"] - paired["score"], 6), d_tokens=paired["tokens"] - cand["tokens"],
                       d_heartbeats=paired["heartbeats"] - cand["heartbeats"], paired=True)
            if not ok:
                rec.update(decision="reject", reject=ES._why(why), at="paired")
                return
            if time.time() > deadline:
                raise _Stop("budget")
            c2 = measure(text, True, timeout=rec.get("timeout_s"))
            if not _ok(c2) or not c2.get("compat"):
                rec.update(decision="reject", reject="timeout" if c2.get("timed_out") else "confirmation_failed", at="confirmation")
                return
            hb = max(int(c1["heartbeats"]), int(c2["heartbeats"]))
            fin = dict(c2, heartbeats=hb, **meter.metrics(c2["tokens"], hb, c2["Z"]))
            final_ = {"score": fin["score_exact"], "tokens": fin["tokens"], "heartbeats": hb, "Z": fin["Z"]}
            ok, why = decide(paired, final_)
            rec.update(d_score=round(final_["score"] - paired["score"], 6), d_tokens=paired["tokens"] - final_["tokens"],
                       d_heartbeats=paired["heartbeats"] - hb, confirmed_hb=(c1["heartbeats"], c2["heartbeats"]), Z=fin["Z"])
            if not ok:
                rec.update(decision="reject", reject=ES._why(why), at="confirmation")
                return
            rec.update(decision="gain", reason=why)
            F["gains"] += 1
            log(f"census: {rec['op']} gain {why} ({(rec.get('note') or '')[:40]})")
        finally:
            rec["compiles"] = spent[0] - c0
            rec["seconds"] = round(time.time() - ts, 2)
            F["compiles"] += rec["compiles"]

    for fam in fams:
        pool = pools.get(fam, fam)
        if pool not in pool_left:
            pool_left[pool] = float(budgets.get(pool) or 0)
        F = fam_out.setdefault(fam, {"generated": 0, "judged": 0, "gains": 0, "censored": 0, "compiles": 0, "seconds": 0.0, "pool": pool,
                                     "budget_s": budgets.get(pool)})
        t_f = time.time()
        deadline = t_f + pool_left[pool]
        if pool_left[pool] <= 0:
            F["skipped"] = "no budget"
            continue
        mod, err = ES._load_family(fam)
        if mod is None or not hasattr(mod, "candidates"):
            F["skipped"] = f"absent ({err})"
            continue
        ctx = fam_ctx(fam)
        try:
                                                                            
            if fam == "t3" and getattr(a, "t3_suggest", False) and hasattr(mod, "suggest"):
                from harness.tools import t3_suggest as SG
                cb = batch_cb(mod, F, deadline, SG.probe_hb_cap(I.get("heartbeats")), k=SG.PROBE_K, max_files=SG.PROBE_MAX_FILES)
                if cb is not None:
                    pst = F.setdefault("probe", {})
                    tp = time.time()
                    sg = mod.suggest(inp, statement, None, cb, ctx=ctx, stats=pst, log=log, mode="rule" if a.t3_suggest is True else a.t3_suggest)
                    F["probe_seconds"] = round(time.time() - tp, 1)
                    if sg:
                        ctx = dict(ctx, suggestions=sg, suggestions_for=SG.proof_key(inp))
                        tac = pst.get("fallback") or pst.get("tactic") or SG.probe_tactic(OT.scope_of(row))
                        for key in list(sg)[:max(0, n_samples)]:                                                                     
                            if time.time() > deadline:
                                break
                            text = SG.probe_text(inp, key, tac if isinstance(tac, str) else SG.probe_tactic(OT.scope_of(row)))
                            r, n = meter._one(text, meter.versions[0], True, meter.freeze())
                            spent[0] += int(n)
                            F["compiles"] += int(n)
                            if getattr(r, "ok", False) and getattr(r, "heartbeats", None) is not None:
                                probe_samples.append({"family": "t3", "hb_extra": int(r.heartbeats) - int(I["heartbeats"]),
                                                      "s_extra": round(float(getattr(r, "seconds", 0.0) or 0.0) - float(I.get("seconds") or 0.0), 2)})
            elif fam in ES.PROBE_FAMILIES and hasattr(mod, "probe"):
                cb = batch_cb(mod, F, deadline, mod.probe_hb_cap(I.get("heartbeats")))
                if cb is not None:
                    tp = time.time()
                    got = mod.probe(inp, statement, cb, ctx=ctx, stats=F.setdefault("probe", {}), log=log)
                    F["probe_seconds"] = round(time.time() - tp, 1)
                    if got:
                        ctx = dict(ctx, **got)
                                                     
            if fam == "sweep":
                raw = mod.candidates(inp, statement, exchange=ex, max_per_op=int(getattr(mod, "MAX_PER_OP", 40)))
            else:
                kw = {"exchange": ex, "ctx": ctx}
                if getattr(a, "max_per_op", None) is not None:
                    kw["max_per_op"] = int(a.max_per_op)
                elif isinstance(getattr(mod, "MAX_PER_OP", None), int):
                    kw["max_per_op"] = int(mod.MAX_PER_OP)
                raw = mod.candidates(inp, statement, **ES._kwargs_for(mod.candidates, kw))
        except _Stop:
            F["censored_probe"] = True
            raw = []
        except Exception as e:                                                                                  
            F["error"] = f"{type(e).__name__}: {str(e)[:160]}"
            raw = []
        items = []
        per_op: dict = {}
        per_site: dict = {}
        allow = set((getattr(a, "family_ops", None) or {}).get(fam) or []) or None
        for x in _raw_dicts(raw):
            text = x.get("decl") or x.get("proof") or x.get("text")
            if not isinstance(text, str) or not text.strip().startswith(statement):
                continue
            fop = ES._fop(fam, x.get("op"))
            if allow is not None and fop not in allow:
                continue
            op = canon(fop)
            note = x.get("note")
            site = _site_of(x, note)
            per_op[op] = per_op.get(op, 0) + 1
            per_site[(op, site)] = per_site.get((op, site), 0) + 1
            to = x.get("timeout_s")
            items.append({"family": fam, "op": op, "entry": OT.entry_of(op, note, x.get("closer")), "rank": per_op[op], "site": site,
                          "rank_in_site": per_site[(op, site)], "note": (note or "")[:200], "text": text.strip(),
                          "timeout_s": to if isinstance(to, (int, float)) and not isinstance(to, bool) and to > 0 else None})
        F["generated"] = len(items)
                                          
        queue = list(items)
        try:
            while queue:
                if time.time() > deadline:
                    raise _Stop("budget")
                chunk = []
                while queue and len(chunk) < max(1, int(getattr(a, "screen_k", ES.SCREEN_K))):
                    it = queue.pop(0)
                    h = ES.sha(it["text"])
                    rec = {k: v for k, v in it.items() if k != "text"}
                    rec["sha"] = h
                    if h == ES.sha(inp):
                        rec.update(decision="reject", reject="identity")
                        records.append(rec)
                        continue
                    if h in decided and decided[h].get("decision") != "censored":
                        first = decided[h]
                        rec.update(decision="dup", dup_of=first.get("op"), **{k: first.get(k) for k in ("d_score", "d_tokens", "d_heartbeats", "reject", "screen")
                                                                              if first.get(k) is not None})
                        rec["dup_decision"] = first.get("decision")
                        records.append(rec)
                        continue
                    chunk.append((it, rec, h))
                    decided[h] = rec
                if not chunk:
                    continue
                verdicts = {}
                if scr is not None and not getattr(scr, "broken", None):
                    def need(n):
                        if time.time() > deadline:
                            raise _Stop("budget")

                    def charge(n):
                        spent[0] += int(n)
                        F["compiles"] += int(n)
                        F["screen_compiles"] = F.get("screen_compiles", 0) + int(n)
                    try:
                        verdicts = scr.screen([{"key": h, "text": it["text"], "timeout_s": it.get("timeout_s")} for it, _, h in chunk], need=need,
                                              charge=charge, hb_cap=hbcap, compile_s=I.get("seconds"), control=inp)
                    except _Stop:
                        for it, rec, h in chunk:
                            rec.update(decision="censored")
                            records.append(rec)
                        raise
                    except Exception as e:                                                                     
                        F["screen_error"] = f"{type(e).__name__}: {str(e)[:120]}"
                        verdicts = {}
                for j, (it, rec, h) in enumerate(chunk):
                    vd = verdicts.get(h) or {"verdict": "unscreened"}
                    rec["screen"] = vd["verdict"]
                    if vd["verdict"] in ES.SCREEN_REJECT:
                        rec.update(decision="reject", compiled=False, reject=ES.SCREEN_REJECT[vd["verdict"]], at="batch")
                        records.append(rec)
                        F["judged"] += 1
                        continue
                    try:
                        judge(rec, it["text"], F, deadline)
                        F["judged"] += 1
                    except _Stop:
                        rec.update(decision="censored")
                        records.append(rec)
                        for it2, rec2, _ in chunk[j + 1:]:
                            rec2.update(decision="censored")
                            records.append(rec2)
                        raise
                    records.append(rec)
        except _Stop:
            left = [it for it in queue]
            for it in left:
                rec = {k: v for k, v in it.items() if k != "text"}
                rec.update(sha=ES.sha(it["text"]), decision="censored")
                records.append(rec)
        F["censored"] = sum(1 for r in records if r.get("family") == fam and r.get("decision") == "censored")
        F["seconds"] = round(time.time() - t_f, 1)
        pool_left[pool] = max(0.0, pool_left[pool] - (time.time() - t_f))
        log(f"census: {fam}: generated {F['generated']}, judged {F['judged']}, gains {F['gains']}, censored {F['censored']} ({F['seconds']:.0f} s)")
    for r in records:                                                                                             
        if r.get("decision") == "dup":
            first = decided.get(r.get("sha"))
            if first is not None and first is not r:
                r["dup_decision"] = first.get("decision")
                r.update({k: first.get(k) for k in ("d_score", "d_tokens", "d_heartbeats", "reject", "screen") if first.get(k) is not None})
    gains = [r for r in records if r.get("decision") == "gain"]
    fsum = {f: {"banked": F["gains"], "d_score": round(sum(float(r.get("d_score") or 0) for r in gains if r["family"] == f), 6),
                "tried": F["judged"], "compiled": sum(1 for r in records if r.get("family") == f and r.get("compiled")),
                "compiles": F["compiles"], **{k: v for k, v in F.items() if k not in ("gains", "judged", "compiles")}} for f, F in fam_out.items()}
    return dict(base, input=inp_read, input_measured={"score_exact": I.get("score_exact")},
                out={"proof": inp, **{k: I.get(k) for k in ("score", "score_exact", "tokens", "heartbeats", "L", "H", "Z", "compat") if I.get(k) is not None},
                     "stage": "census"},
                end={"stage": "census", "score": I.get("score"), "score_exact": I.get("score_exact")}, delta=0.0, compiles=spent[0],
                families=fsum, candidates=records, compile_seconds=[x for x in compile_secs if isinstance(x, (int, float))],
                probe_samples=probe_samples, accept=acc, seconds=round(time.time() - t_row, 1))
