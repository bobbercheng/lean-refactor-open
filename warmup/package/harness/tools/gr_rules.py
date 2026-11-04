#!/usr/bin/env python3
"""End-stage family "gr" (open-track re-derivation, docs/open_tools_rederive.md 2.4): harness/gap_rules.py's 17 rule kinds as a candidate







"""
from __future__ import annotations

import sys, threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness import gap_rules as GR              
from harness.normalize import apply              
from scorer.tokenize import split_declaration              

OPS = tuple("gr:" + k for k in GR.KINDS)
ALL_OPS = OPS
CLOSERS_BY_SCOPE: dict | None = None
_LOCK = threading.Lock()


def scope_of(proof: str, ctx: dict | None) -> str:
    from harness.tools.t3_reclose import _scope
    return _scope(proof, ctx)


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int | None = None, ctx: dict | None = None) -> list[dict]:
    c = ctx or {}
    body = split_declaration(proof, statement)
    if body is None:
        return []
    head = proof[:len(proof) - len(body)]
    kinds = None
    if c.get("ops") is not None:
        want = {str(o) if str(o).startswith("gr:") else "gr:" + str(o) for o in c["ops"]}
        kinds = tuple(k for k in GR.KINDS if "gr:" + k in want)
        if not kinds:
            return []
    caps = dict(GR.DEFAULT_CAPS)
    if max_per_op is not None:
        caps = {k: min(v, int(max_per_op)) for k, v in caps.items()}
    with _LOCK:
        old = GR.CLOSERS
        if CLOSERS_BY_SCOPE is not None:
            GR.CLOSERS = tuple(CLOSERS_BY_SCOPE.get(scope_of(proof, c)) or old)
        try:
            rules = GR.candidates(body, caps, kinds)
        finally:
            GR.CLOSERS = old
    out, seen = [], {proof.rstrip()}
    for r in rules:
        nb = apply(body, [r])
        decl = head + nb
        if decl.rstrip() in seen or split_declaration(decl, statement) != nb:
            continue
        seen.add(decl.rstrip())
        out.append({"op": "gr:" + r.kind, "decl": decl, "note": r.note, "site": str(r.edits[0][0]) if r.edits else "0"})
    return out
