#!/usr/bin/env python3
"""End-stage family "hp" (open-track re-derivation, docs/open_tools_rederive.md 2.4): harness/hb_polish.py's two rewrites as a candidate













"""
from __future__ import annotations

import hashlib, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness import hb_polish as HP              
from scorer.tokenize import split_declaration              

OPS = ("hp:cert", "hp:prune")
ALL_OPS = OPS
MAX_PER_OP = 40
PROBE_K = 12                                                                          
PROBE_MAX_FILES = 2
_ONLY_SITE = re.compile(r"\b(simp_all|simp|dsimp)(\s+only\s*\[)")
_TRY_THIS = re.compile(r"^Try (?:this|these):\s*(?:\[apply\]\s*)?", re.S)


def proof_key(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def probe_hb_cap(heartbeats) -> int:
    """`maxHeartbeats` (thousands) of a probe copy: the `?` forms re-run the same calls, so twice the incumbent's + 1000."""
    try:
        h = max(0, int(heartbeats or 0))
    except (TypeError, ValueError):
        h = 0
    return 2 * h + 1000


def _ops(ctx: dict | None) -> tuple:
    c = ctx or {}
    if c.get("ops") is None:
        return OPS
    want = {str(o) if str(o).startswith("hp:") else "hp:" + str(o) for o in c["ops"]}
    return tuple(o for o in OPS if o in want)


def _bracket_items(t: str, i: int):
    from harness.hb_polish import _items
    return _items(t, i)


def _at_line(messages) -> list[dict]:
    """The copy's messages with pos.line replaced by the line within the copy ("decl_line", t3_suggest.batch_compiler)."""
    out = []
    for m in messages or []:
        if m.get("decl_line") is None:
            continue
        out.append(dict(m, pos=dict(m.get("pos") or {}, line=m["decl_line"])))
    return out


def _prune_probe(decl: str) -> tuple[str, list]:
    sites = list(_ONLY_SITE.finditer(decl))
    return _ONLY_SITE.sub(lambda m: m.group(1) + "?" + m.group(2), decl), sites


def _prune_sugg(decl: str, probe_text: str, messages) -> dict:
    """{site index: Lean's list} at each `simp? only [..]` of the prune probe (leantools.simp_prune's parse, by copy line)."""
    pos = {}
    for k, m in enumerate(re.finditer(r"\b(simp_all|simp|dsimp)\?(\s+only\s*\[)", probe_text)):
        pos[(probe_text.count("\n", 0, m.start()) + 1, m.start() - (probe_text.rfind("\n", 0, m.start()) + 1))] = k
    sugg: dict = {}
    for msg in messages or []:
        d = str(msg.get("data", ""))
        p = msg.get("pos") or {}
        k = pos.get((p.get("line"), p.get("column")))
        if k is None or not _TRY_THIS.match(d):
            continue
        t = _TRY_THIS.sub("", d, count=1)
        b = t.find("[")
        got = _bracket_items(t, b) if b >= 0 else (0, [])
        if got is not None:
            L = sugg.setdefault(k, [])
            L += [x for x in got[1] if x not in L]
    return sugg


def probe(proof: str, statement: str, compile_batch, *, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict:
    st = stats if stats is not None else {}
    for c in ("probes", "judged", "sites", "answered"):
        st.setdefault(c, 0)
    proof = proof.rstrip()
    body = split_declaration(proof, statement)
    if body is None:
        return {}
    start = len(proof) - len(body)
    ops = _ops(ctx)
    texts, kinds = [], []
    sites = HP.cert_sites(proof, start) if "hp:cert" in ops else []
    by_head: dict = {}
    for k, s_ in enumerate(sites):                                                                                             
        by_head.setdefault(s_["head"], []).append(k)                                                    
    for h, ks in by_head.items():
        ph, pos = HP.probe_of(proof, [sites[k] for k in ks])
        texts.append(ph); kinds.append(("cert", ks, pos))
    psites = []
    if "hp:prune" in ops:
        pp, psites = _prune_probe(proof)
        psites = [m for m in psites if m.start() >= start]
        if psites:
            texts.append(pp); kinds.append(("prune", None, None))
    if not texts:
        return {}
    got = list(compile_batch(texts) or []) + [None] * len(texts)
    st["probes"] += len(texts)
    st["judged"] += sum(1 for g in got[:len(texts)] if g is not None)
    st["sites"] += len(sites) + len(psites)
    cert: dict = {}
    prune: dict = {}
    for (kind, idx, pos), text, msgs in zip(kinds, texts, got):
        if msgs is None:
            continue
        ms = _at_line(msgs)
        if kind == "cert":
            if any(m.get("severity") == "error" for m in ms):
                continue
            for j, v in HP.suggestions(text, pos, ms, 0).items():
                k = idx[j]
                if k not in cert and v is not None:
                    cert[k] = v
        else:
            if any(m.get("severity") == "error" for m in ms):
                continue
            prune = _prune_sugg(proof, text, ms)
    st["answered"] += len(cert) + len(prune)
    if log:
        log(f"hp probe: {len(sites)} cert site(s) answered {len(cert)}; {len(psites)} only-list(s) answered {len(prune)}")
    if not cert and not prune:
        return {}
    return {"hp_probe": {"cert": {str(k): v for k, v in cert.items()}, "prune": {str(k): v for k, v in prune.items()}},
            "hp_probe_for": proof_key(proof)}


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = MAX_PER_OP, ctx: dict | None = None) -> list[dict]:
    c = ctx or {}
    proof = proof.rstrip()
    body = split_declaration(proof, statement)
    res = c.get("hp_probe") if c.get("hp_probe_for") == proof_key(proof) else None
    if body is None or not isinstance(res, dict):
        return []
    start = len(proof) - len(body)
    ops = _ops(c)
    out, seen = [], {proof}
    if "hp:cert" in ops:
        sites = HP.cert_sites(proof, start)
        sugg = {int(k): v for k, v in (res.get("cert") or {}).items() if int(k) < len(sites)}
        ks = sorted(sugg)
        sets = [[k] for k in ks] + ([ks] if len(ks) > 1 else [])
        n = 0
        for ch in sets:
            if n >= int(max_per_op):
                break
            d = HP.rewrite(proof, sites, sugg, ch)
            if d in seen or split_declaration(d, statement) is None:
                continue
            seen.add(d); n += 1
            note = "; ".join(f"{sites[k]['head']} only [{len(sugg[k])}]" for k in ch)
            out.append({"op": "hp:cert", "decl": d, "note": note[:200], "site": str(sites[ch[0]]["start"]) if len(ch) == 1 else "all"})
    if "hp:prune" in ops:
        psites = list(_ONLY_SITE.finditer(proof))
        sugg = {int(k): v for k, v in (res.get("prune") or {}).items() if int(k) < len(psites)}
        edits = {}
        for k, items in sugg.items():
            m = psites[k]
            if m.start() < start:
                continue
            lb = m.end() - 1
            got = _bracket_items(proof, lb)
            if got is None or len(items) >= len(got[1]):
                continue
            only_end = m.start(2) + m.group(2).index("only") + 4
            edits[k] = (only_end, got[0], (" [" + ", ".join(items) + "]") if items else "", len(got[1]) - len(items))
        ks = sorted(edits)
        sets = [[k] for k in ks] + ([ks] if len(ks) > 1 else [])
        n = 0
        for ch in sets:
            if n >= int(max_per_op):
                break
            d = proof
            for k in sorted(ch, key=lambda k: -edits[k][0]):
                a, b, new, _ = edits[k]
                d = d[:a] + new + d[b:]
            if d in seen or split_declaration(d, statement) is None:
                continue
            seen.add(d); n += 1
            out.append({"op": "hp:prune", "decl": d, "note": f"{sum(edits[k][3] for k in ch)} lemma(s) dropped at {len(ch)} list(s)",
                        "site": str(psites[ch[0]].start()) if len(ch) == 1 else "all"})
    return out
