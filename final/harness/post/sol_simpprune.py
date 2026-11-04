"""Prune supplied hints while keeping Lean's ambient simplifier facts.

A stronger version of sol_simphints: non-only certificates can include default
library lemmas that make the printed certificate longer than the original list.
Intersect the certificate with the supplied hints instead. The existing gate
validates the result; ordinary certificate candidates remain available.
"""
from __future__ import annotations

# provenance: research lane gaplane2-sol (worktree lra-gl2-sol), commit 6cee22b, ported unchanged into open-post-v3 (2026-11-04)

import re

from harness.post import sol_simphints as S
from harness.post.d4_kit import Emitter, head_body, proof_key
from scorer.tokenize import count_tokens

FAMILY = "sol_simpprune"
has_sites = S.has_sites
query = S.query


def candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None):
    try:
        hb = head_body(proof, statement)
        if not hb or not ctx or ctx.get("key") != proof_key(proof):
            return []
        head, body = hb
        ss = S.sites(body)
        edits = []
        key = lambda s: re.sub(r"\s+", " ", s).strip()
        for i, cert in (ctx.get("hints") or {}).items():
            if not isinstance(i, int) or not 0 <= i < len(ss) or not isinstance(cert, str):
                continue
            s = ss[i]
            if s.only:
                continue
            used = S.suggestion(f"Try this: {s.family} only {cert}", s.family)
            given = S.split_hints(body[s.left + 1:s.right - 1])
            if used is None or given is None or any(S.code(h) != h for h in given):
                continue
            wanted = {key(h) for h in used}
            # Exclusion hints and the star affect the ambient set. They need
            # not appear by name in TryThis, so retain them conservatively.
            keep = [h for h in given if key(h) in wanted or h == "*" or h.startswith("-")]
            new = "[" + ", ".join(keep) + "]" if keep else ""
            if count_tokens(new) < count_tokens(body[s.left:s.right]):
                edits.append((s.left, s.right, new))
        em = Emitter(proof, statement, head, body, int(max_per_op or 8))
        if edits:
            em.add(FAMILY + ":intersection", S.apply_edits(body, edits),
                   f"{len(edits)} supplied lists intersected with used-hint certificates")
        old = S.candidates(proof, statement, max_per_op=8, ctx=ctx)
        for c in old[:4]:
            chb = head_body(c["decl"], statement)
            if chb:
                em.add(FAMILY + ":certificate", chb[1], c.get("note", "ordinary simplifier certificate"))
        for e in sorted(edits, key=lambda e: -(count_tokens(body[e[0]:e[1]]) - count_tokens(e[2])))[:3]:
            em.add(FAMILY + ":single", S.apply_edits(body, [e]), "one supplied-list intersection")
        return em.out
    except (TypeError, ValueError, KeyError, IndexError):
        return []
