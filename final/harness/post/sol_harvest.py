"""Combined hint harvesting with one shared simplifier query.

The shared declaration runs original simp? steps and sandboxed bare-head trials.
Typed local facts use their separate type-directed query. Primitive certificates
and disjoint whole-candidate edits are offered to the ordinary unchanged gate.
"""
from __future__ import annotations

# provenance: research lane gaplane2-sol (worktree lra-gl2-sol), commit 6cee22b, ported unchanged into open-post-v3 (2026-11-04)

from harness.post import sol_factterms as F, sol_hintheads as H, sol_probe as P
from harness.post import sol_simphints as S, sol_simpprune as R
from harness.post.d4_kit import Emitter, head_body, proof_key
from scorer.tokenize import count_tokens

FAMILY = "sol_harvest"


def has_sites(proof, statement):
    return S.has_sites(proof, statement) or F.has_sites(proof, statement)


def query_text(proof, statement):
    hb = head_body(proof, statement)
    if not hb:
        return None
    head, body = hb
    ss = S.sites(body)
    if not ss:
        return None
    trials = H.hint_lists(body)[:H.MAX_PROBES]
    calls = {}
    for i, (s, hints, _) in enumerate(trials):
        loc = H.location(body, s.right)
        tac = s.family + "?" + (" only" if s.only else "") + " " + hints + loc
        original = body[s.start:s.right] + loc
        calls.setdefault(s.start, []).append(P.equivalent_call(i, tac, original))
    prefix = ('theorem solHarvestDummy : True := by\n'
              f'  trace "{S.MARKER}"\n  trivial\n\n'
              'set_option maxHeartbeats 2000000 in\n')
    parts, cursor, positions = [], 0, {}
    # Every site is non-overlapping, so positions can be computed while copying
    # source left to right. Tagged sandbox output is distinct from these exact
    # positions of the original question-mark tactic calls.
    size = len(prefix) + len(head)
    for i, s in enumerate(ss):
        before = body[cursor:s.start]
        parts.append(before)
        size += len(before)
        wrapped = calls.get(s.start)
        if wrapped:
            opening = "(" + "; ".join(wrapped) + "; "
            parts.append(opening)
            size += len(opening)
        p = size
        old = body[s.start:s.word_end] + "?" + body[s.word_end:s.right]
        end = s.right
        if wrapped:
            loc = H.location(body, s.right)
            old += loc + ")"
            end += len(loc)
        parts.append(old)
        size += len(old)
        positions[p] = i
        cursor = end
    parts.append(body[cursor:])
    text = prefix + head + "".join(parts)
    mapped = {}
    for p, i in positions.items():
        line = text.count("\n", 0, p) + 1
        left = text.rfind("\n", 0, p) + 1
        mapped[(line, p - left)] = i
        mapped[(line, len(text[left:p].encode()))] = i
    return text, mapped, ss, trials


def query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None):
    out = {"key": proof_key(proof), "simp": None, "heads": None, "facts": None}
    qt = query_text(proof, statement)
    if qt:
        text, positions, ss, trials = qt
        result = run(text, (versions or [None])[0])
        if getattr(result, "ok", False):
            messages = getattr(result, "messages", [])
            hints = S.parse_query(messages, positions, ss)
            edits = H.parse_query(messages, trials)
            out["simp"] = {"key": out["key"], "hints": hints}
            out["heads"] = {"key": out["key"], "edits": edits}
            if log:
                log(f"{FAMILY}: shared query returned {len(hints)} simp certificates and {len(edits)} head edits")
        elif log:
            log(f"{FAMILY}: shared query failed: {str(getattr(result, 'errors', []))[:180]}")
    if F.has_sites(proof, statement):
        out["facts"] = F.query(proof, statement, run, versions=versions, ctx=ctx, stats=stats, log=log)
    return out


def edit_between(body, new):
    if body == new:
        return None
    a = 0
    while a < min(len(body), len(new)) and body[a] == new[a]:
        a += 1
    z = 0
    while z < min(len(body) - a, len(new) - a) and body[-1 - z] == new[-1 - z]:
        z += 1
    b = len(body) - z
    return a, b, new[a:len(new) - z if z else len(new)]


def disjoint_edits(body, edits):
    out = []
    for e in sorted(set(edits), key=lambda e: (-(count_tokens(body[e[0]:e[1]]) - count_tokens(e[2])), e)):
        a, b, _ = e
        if any(a < d and c < b or a == c for c, d, _ in out):
            continue
        out.append(e)
    return out


def candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None):
    try:
        hb = head_body(proof, statement)
        if not hb or not ctx or ctx.get("key") != proof_key(proof):
            return []
        head, body = hb
        groups = [R.candidates(proof, statement, ctx=ctx.get("simp")),
                  H.candidates(proof, statement, ctx=ctx.get("heads")),
                  F.candidates(proof, statement, ctx=ctx.get("facts"))]
        em = Emitter(proof, statement, head, body, int(max_per_op or 8))
        fact_typed = next((c for c in groups[2] if c["op"].endswith(":typed")), None)
        fact_inferred = next((c for c in groups[2] if c["op"].endswith(":inferred")), None)
        for tag, fact in (("typed", fact_typed), ("inferred", fact_inferred)):
            chosen = [g[0] for g in groups[:2] if g] + ([fact] if fact else [])
            edits = []
            for c in chosen:
                chb = head_body(c["decl"], statement)
                e = edit_between(body, chb[1]) if chb else None
                if e:
                    edits.append(e)
            edits = disjoint_edits(body, edits)
            if edits:
                em.add(FAMILY + ":joint_" + tag, S.apply_edits(body, edits),
                       f"{len(edits)} disjoint environment-harvested edits")
        # Keep each primitive's strongest certificate as a fallback if a union
        # fails or loses heartbeat score. Reserve space before alternatives.
        sources = [g[0] for g in groups if g]
        if fact_typed:
            sources.append(fact_typed)
        sources += [c for g in groups for c in g[1:3]]
        for c in sources:
            chb = head_body(c["decl"], statement)
            if chb:
                em.add(FAMILY + ":" + c["op"], chb[1], c.get("note", "environment certificate"))
        return em.out
    except (TypeError, ValueError, KeyError, IndexError):
        return []
