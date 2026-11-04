#!/usr/bin/env python3
"""End-stage family "hr" (open-track re-derivation, docs/open_tools_rederive.md 2.4): harness/hb_rewrite.py's lemmavariant operator as a




"""
from __future__ import annotations

import sys, threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness import hb_rewrite as HR              
from harness.normalize import apply              
from scorer.tokenize import split_declaration              

OPS = ("hr:lemmavariant",)
ALL_OPS = OPS
MAX_PER_OP = 40
_LOCK = threading.Lock()                                    


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = MAX_PER_OP, ctx: dict | None = None) -> list[dict]:
    c = ctx or {}
    row = c.get("row")
    if not isinstance(row, dict) or (c.get("ops") is not None and "hr:lemmavariant" not in [str(o) for o in c["ops"]]):
        return []
    body = split_declaration(proof, statement)
    if body is None:
        return []
    head = proof[:len(proof) - len(body)]
    with _LOCK:
        old = dict(HR._CTX)
        HR._CTX.clear()
        HR._CTX.update(name=row.get("name"), row=row)
        try:
            sites = HR.sites(body, ("lemmavariant",))
        finally:
            HR._CTX.clear()
            HR._CTX.update(old)
    out, seen = [], {proof.rstrip()}
    for s in sites:
        if len(out) >= int(max_per_op):
            break
        nb = apply(body, [s])
        decl = head + nb
        if decl.rstrip() in seen or split_declaration(decl, statement) != nb:
            continue
        seen.add(decl.rstrip())
        out.append({"op": "hr:lemmavariant", "decl": decl, "note": s.note, "site": str(s.span[0])})
    return out
