#!/usr/bin/env python3
"""Heartbeat polish (docs/opus_pass2_deep_dive.md R8, docs/cc_driver_v2.md §8-§9; 2026-10-12): a $0 CPU post-pass next to the lexer normalizer












"""
from __future__ import annotations

import argparse, json, re, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))

HEADS = ("simp_all", "simpa", "simp", "dsimp", "grind")
SITE_RE = re.compile(r"(?<![\w.'?!])(simp_all|simpa|simp|dsimp|grind)(?![\w'?!])")
TRY_THIS = re.compile(r"^Try (?:this|these):\s*(?:\[apply\]\s*)?", re.S)
RULES = ("cert", "prune")
MAX_COMPILES = 12


def _mask(s: str) -> list:
    from harness.normalize import _mask as m
    return m(s)


def _items(t: str, i: int):
    from harness.leantools import _bracket_items
    return _bracket_items(t, i)


RULE_CLAUSE = re.compile(r"\s*(?:add|erase|rule_sets|simp_config|config)\b")


def _in_rule_clause(decl: str, mask: list, start: int, pos: int) -> bool:
    """Review 2026-10-12: a `simp` / `grind` word inside an aesop rule clause (`aesop (add simp foo)`, `(add norm simp foo)`, `(erase ...)`) is
"""
    depth = 0
    for i in range(pos - 1, start - 1, -1):
        if mask[i]:
            continue
        if decl[i] == ")":
            depth += 1
        elif decl[i] == "(":
            if depth == 0:
                return bool(RULE_CLAUSE.match(decl, i + 1))
            depth -= 1
    return False


def cert_sites(decl: str, start: int = 0) -> list[dict]:
    """Bare simp-family / grind calls in decl[start:] (the proof body): not in a comment or string, no `only`, no `?`/`!` form, no config,

"""
    mask = _mask(decl); out = []
    for m in SITE_RE.finditer(decl):
        if m.start() < start or mask[m.start()] or _in_rule_clause(decl, mask, start, m.start()):
            continue
        j = m.end(); k = j
        while k < len(decl) and decl[k] in " \t":
            k += 1
        nxt = decl[k:k + 8]
        if re.match(r"only\b", nxt) or nxt[:1] == "(" or re.match(r"[+-][A-Za-z]", nxt):
            continue
        end = j
        if nxt[:1] == "[":
            got = _items(decl, k)
            if got is None:
                continue
            end = got[0]
        out.append({"head": m.group(1), "start": m.start(), "head_end": j, "args_end": end})
    return out


def probe_of(decl: str, sites: list[dict]) -> tuple[str, list[int]]:
    """decl with `?` after every site's head, and each site's head position in that probe (k `?` were inserted before site k)."""
    probe = decl
    for s in sorted(sites, key=lambda s: -s["head_end"]):
        probe = probe[:s["head_end"]] + "?" + probe[s["head_end"]:]
    order = sorted(range(len(sites)), key=lambda k: sites[k]["start"])
    pos = [0] * len(sites)
    for rank, k in enumerate(order):
        pos[k] = sites[k]["start"] + rank
    return probe, pos


def suggestions(probe: str, pos: list[int], messages: list, head_lines: int) -> dict[int, list[str]]:
    """site index -> the union of the lemma lists Lean suggested at that site ("Try this: <tac> only [...]", reported at the tactic's start)."""
    at = {}
    for k, p in enumerate(pos):
        at[(probe.count("\n", 0, p) + 1 + head_lines, p - (probe.rfind("\n", 0, p) + 1))] = k
    out: dict = {}
    for msg in messages or []:
        d = str(msg.get("data", "")); p = msg.get("pos") or {}
        k = at.get((p.get("line"), p.get("column")))
        if k is None or not TRY_THIS.match(d):
            continue
        t = TRY_THIS.sub("", d, count=1).split("\n\n")[0]
        b = t.find("[")
        got = _items(t, b) if b >= 0 else (0, [])
        if got is None:
            continue
        cur = out.setdefault(k, [])
        cur += [x for x in (re.sub(r"\s+", " ", y) for y in got[1]) if x and x not in cur]
    return out


def rewrite(decl: str, sites: list[dict], sugg: dict, chosen) -> str:
    """decl with every chosen site replaced by `<head> only [<its suggested list>]` (the rest of the call, e.g. ` at h` / ` using e`, kept)."""
    for k in sorted(chosen, key=lambda k: -sites[k]["start"]):
        s = sites[k]; items = sugg.get(k) or []
        decl = decl[:s["start"]] + f"{s['head']} only" + (f" [{', '.join(items)}]" if items else "") + decl[s["args_end"]:]
    return decl


def prov(ev: dict) -> float:
    """The provisional score (Z taken as 100) of an evaluation: its own when given, else from L/H, else from score and Z."""
    if ev.get("prov") is not None:
        return float(ev["prov"])
    if ev.get("L") is not None and ev.get("H") is not None:
        return round((float(ev["L"]) + float(ev["H"]) + 100.0) / 3, 2)
    return round(float(ev.get("score") or 0) + (100.0 - float(ev.get("Z", 100.0))) / 3, 2)


def _pick(ev: dict) -> dict:
    return {k: ev.get(k) for k in ("ok", "tokens", "heartbeats", "Z", "score")}


def polish(name: str, decl: str, *, base: dict | None = None, compile_fn=None, evaluate_fn=None, head_lines: int | None = None,
           statement: str | None = None, max_compiles: int = MAX_COMPILES, rules=RULES) -> dict:
    """The polish report of one proof: status (improved / no sites / no gain / pins broke / input does not compile / statement differs),
"""
    from scorer.tokenize import split_declaration
    if compile_fn is None or evaluate_fn is None or head_lines is None or statement is None:
        from harness.leantools import ROWS, comp, head_line_count
        from harness.normalize import evaluate
        from probe.verify_candidates import newest_first
        row = ROWS[name]; versions = newest_first(row["version_info"])
        compile_fn = compile_fn or (lambda d: comp(row, d, versions[0]))
        evaluate_fn = evaluate_fn or (lambda d, full: evaluate(name, d, versions, full))
        head_lines = head_line_count(row, versions[0]) if head_lines is None else head_lines
        statement = statement or row["statement"]
    decl = decl.rstrip(); body = split_declaration(decl, statement)
    if body is None:
        return {"problem": name, "status": "statement differs", "compiles": 0}
    start = len(decl) - len(body); n = [0]

    def ev(d: str, full: bool) -> dict:
        n[0] += 1
        return evaluate_fn(d, full) or {}
    b0 = base if (base and base.get("ok") and base.get("score") is not None) else ev(decl, True)
    res = {"problem": name, "before": _pick(b0), "applied": {}, "compiles": n[0]}
    if not b0.get("ok"):
        res.update(status="input does not compile", after=res["before"], proof=decl); return res
    cur, cur_p = decl, prov(b0); tried = False
    if "cert" in rules:
        sites = cert_sites(cur, start)
        if sites and n[0] < max_compiles:
            tried = True
            sugg = {}
            for subset in ([k for k in range(len(sites))], [k for k in range(len(sites)) if sites[k]["head"] != "grind"]):
                if not subset or n[0] >= max_compiles:
                    break
                sub = [sites[k] for k in subset]
                probe, pos = probe_of(cur, sub); n[0] += 1
                r = compile_fn(probe)
                if getattr(r, "ok", False):                                                                      
                    sugg = {subset[i]: v for i, v in suggestions(probe, pos, getattr(r, "messages", []), head_lines).items()}
                    break
                if len(subset) == len([s for s in sites if s["head"] != "grind"]):
                    break
            ks = sorted(sugg)
            if ks and n[0] < max_compiles:
                base_decl, chosen, best_p = cur, [], cur_p
                cand = rewrite(base_decl, sites, sugg, ks); e = ev(cand, False)
                if e.get("ok") and prov(e) > cur_p + 1e-9:
                    chosen, best_p = ks, prov(e)
                elif len(ks) > 1:
                    for k in ks:
                        if n[0] >= max_compiles:
                            break
                        cand = rewrite(base_decl, sites, sugg, chosen + [k]); e = ev(cand, False)
                        if e.get("ok") and prov(e) > best_p + 1e-9:
                            chosen.append(k); best_p = prov(e)
                if chosen:
                    cur, cur_p = rewrite(base_decl, sites, sugg, chosen), best_p
                    for k in chosen:
                        res["applied"][f"{sites[k]['head']} only"] = res["applied"].get(f"{sites[k]['head']} only", 0) + 1
                                                                                                                     
    if "prune" in rules and n[0] < max_compiles and re.search(r"\b(simp_all|simp|dsimp)\s+only\s*\[", decl[start:]):
        from harness.leantools import simp_prune
        tried = True; n[0] += 1
        pp = simp_prune(cur, compile_fn, head_lines)
        if pp and n[0] < max_compiles:
            e = ev(pp[0], False)
            if e.get("ok") and prov(e) > cur_p + 1e-9:
                cur, cur_p = pp[0], prov(e); res["applied"]["pruned lemmas"] = pp[1]
    res["compiles"] = n[0]
    if cur == decl:
        res.update(status="no gain" if tried else "no sites", after=res["before"], proof=decl); return res
    fin = ev(cur, True); res["compiles"] = n[0]
    if not fin.get("ok") or float(fin.get("Z", 100.0)) < float(b0.get("Z", 100.0)) - 1e-9 or float(fin.get("score") or 0) <= float(b0["score"]) + 1e-9:
        res.update(status="pins broke" if fin.get("ok") and float(fin.get("Z", 100.0)) < float(b0.get("Z", 100.0)) - 1e-9 else "no gain",
                   after=res["before"], proof=decl, tried=_pick(fin)); return res
    res.update(status="improved", after=_pick(fin), gain=round(float(fin["score"]) - float(b0["score"]), 2), proof=cur)
    return res


def polish_work_root(work_root: Path, run_id: str, problems=None, deadline_s: float = 3000.0, max_compiles: int = MAX_COMPILES,
                     polish_fn=None, check_fn=None) -> dict:
    """The ladder's post-pass: every stored best of a line polished; a strictly better proof is banked through the normal check path as run
"""
    from harness.leantools import ROWS
    from harness.inrun import locked_check
    polish_fn = polish_fn or polish
    check_fn = check_fn or (lambda w, name, proof: locked_check(w, name, proof, {"kind": "closed-dev-only", "model": "hb-polish@cpu", "run_id": run_id,
                                                                                 "mode": "hb-polish"}, ROOT / "probe/runs" / run_id / "verified.jsonl"))
    t0 = time.time(); c = {"problems": 0, "improved": 0, "banked": 0, "gain": 0.0, "compiles": 0, "skipped_deadline": 0}
    for st in sorted(Path(work_root).glob("*/state.json")):
        try:
            s = json.loads(st.read_text())
        except (OSError, ValueError):
            continue
        name = s.get("problem"); b = s.get("best") or {}
        if (problems and name not in problems) or not b.get("proof") or name not in ROWS:
            continue
        if time.time() - t0 > deadline_s:
            c["skipped_deadline"] += 1; continue
        base = ({"ok": True, "score": b["score"], "Z": b["Z"], "L": b.get("L"), "H": b.get("H"), "tokens": b.get("tokens"), "heartbeats": b.get("heartbeats")}
                if b.get("Z") is not None and b.get("score") is not None else None)
        try:
            r = polish_fn(name, b["proof"], base=base, max_compiles=max_compiles)
        except Exception:                                                              
            continue
        c["problems"] += 1; c["compiles"] += r.get("compiles") or 0
        if r.get("status") == "improved":
            c["improved"] += 1
            chk = check_fn(st.parent, name, r["proof"])
            if chk.get("new_best"):
                c["banked"] += 1; c["gain"] += float(chk.get("score") or 0) - float(b.get("score") or 0)
    c["gain"] = round(c["gain"], 2)
    return c


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem"); ap.add_argument("--file"); ap.add_argument("--out")
    ap.add_argument("--work-root", help="a line's work root (relative to the checkout, or absolute): polish every stored best")
    ap.add_argument("--run-id", help="with --work-root: the run id its banked records go under (e.g. <prefix>-hx-<arm>-p<round>)")
    ap.add_argument("--problems", nargs="*", default=None); ap.add_argument("--deadline-s", type=float, default=3000.0)
    ap.add_argument("--max-compiles", type=int, default=MAX_COMPILES)
    a = ap.parse_args()
    if a.problem and a.file:
        r = polish(a.problem, Path(a.file).read_text(), max_compiles=a.max_compiles)
        print(json.dumps({k: v for k, v in r.items() if k != "proof"}, indent=1))
        if a.out and r.get("status") == "improved":
            Path(a.out).write_text(r["proof"].rstrip() + "\n")
        return 0
    if not (a.work_root and a.run_id):
        ap.error("--problem with --file, or --work-root with --run-id")
    c = polish_work_root(ROOT / a.work_root, a.run_id, set(a.problems) if a.problems else None, a.deadline_s, a.max_compiles)
    print(f"hb_polish: {c['problems']} stored best(s) polished, {c['improved']} strictly better, {c['banked']} banked as new bests "
          f"(summed gain {c['gain']:+.2f}), {c['compiles']} compiles, {c['skipped_deadline']} left for the deadline; run {a.run_id}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
