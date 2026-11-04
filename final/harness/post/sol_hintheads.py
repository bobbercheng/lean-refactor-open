"""Let the simplifier infer arguments of its existing applied hints.

Hint names are read from the input proof. Each shorter hint list is tried with
simp? in the row's actual local context, in a sandbox that then restores state.
Only Lean's used-hint certificates become candidate edits. This reaches applied
lemma arguments that ordinary used-hint pruning preserves.
"""
from __future__ import annotations

# provenance: research lane gaplane2-sol (worktree lra-gl2-sol), commit 6cee22b, ported unchanged into open-post-v3 (2026-11-04)

import re

from harness.post import sol_probe as P, sol_simphints as S
from harness.post.d4_kit import Emitter, IDENT, head_body, proof_key
from scorer.tokenize import count_tokens

FAMILY = "sol_hintheads"
MAX_PROBES = 16
HEAD = re.compile(r"^((?:[↓↑]\s*)*(?:←\s*)?)@?(" + IDENT + r")(?=\s|\$)([\s\S]+)$")
KEYWORDS = {"show", "by", "fun", "let", "match", "if", "then", "else", "have", "forall", "exists", "do", "Type", "Prop"}


def shorter_hint(item: str) -> str:
    m = HEAD.match(item)
    if not m or m[2] in KEYWORDS:
        return item
    new = m[1] + m[2]
    return new if count_tokens(new) < count_tokens(item) else item


def hint_lists(body: str):
    out = []
    for site in S.sites(body):
        # A simpa probe must also elaborate its using term; left for another op.
        if site.family == "simpa":
            continue
        items = S.split_hints(body[site.left + 1:site.right - 1])
        if items is None:
            continue
        changes = [(i, shorter_hint(h)) for i, h in enumerate(items) if shorter_hint(h) != h]
        if not changes:
            continue
        # All heads first, then individual changes. The latter preserve difficult
        # specialized local induction hypotheses when another head can be bare.
        subsets = [changes]
        if len(changes) > 1:
            subsets += [[c] for c in sorted(changes, key=lambda c: -(count_tokens(items[c[0]]) - count_tokens(c[1])))[:3]]
        seen = set()
        for subset in subsets:
            new = list(items)
            for i, h in subset:
                new[i] = h
            new = list(dict.fromkeys(new))
            text = "[" + ", ".join(new) + "]"
            if text not in seen:
                seen.add(text)
                gain = count_tokens(body[site.left:site.right]) - count_tokens(text)
                if gain > 0:
                    out.append((site, text, gain))
        # Generic local-context query: let simp find the hypotheses needed to
        # discharge premises of a bare conditional lemma.
        all_heads = list(dict.fromkeys(shorter_hint(h) for h in items))
        if "*" not in all_heads:
            text = "[" + ", ".join(all_heads + ["*"]) + "]"
            gain = count_tokens(body[site.left:site.right]) - count_tokens(text)
            if gain > 0 and text not in seen:
                out.append((site, text, gain))
    # First give every site its best trial, then spend the rest of the bounded
    # budget on alternatives. Large failed sites cannot hide all smaller ones.
    out.sort(key=lambda x: (-x[2], x[0].start, x[1]))
    first, rest, used = [], [], set()
    for trial in out:
        if trial[0].start in used:
            rest.append(trial)
        else:
            used.add(trial[0].start)
            first.append(trial)
    return first + rest


def has_sites(proof: str, statement: str) -> bool:
    hb = head_body(proof, statement)
    return bool(hb and hint_lists(hb[1]))


def location(body: str, right: int) -> str:
    """Conservative, single-line simp location suffix, if present."""
    tail = S.code(body[right:]).split("\n", 1)[0]
    m = re.match(r"[ \t]+at\b([ \t]+(?:\*|⊢|" + IDENT + r"))*", tail)
    return m.group(0) if m else ""


def query_text(proof: str, statement: str):
    hb = head_body(proof, statement)
    if not hb:
        return None
    head, body = hb
    trials = hint_lists(body)[:MAX_PROBES]
    if not trials:
        return None
    inserts = {}
    for i, (site, hints, gain) in enumerate(trials):
        tactic = site.family + "?" + (" only" if site.only else "") + " " + hints + location(body, site.right)
        original = body[site.start:site.right] + location(body, site.right)
        inserts.setdefault(site.start, []).append(P.call(i, tactic, original))
    qb = body
    # Insert sandbox queries as separate tactics, keeping the original call. A
    # parenthesized tactic sequence protects semicolon/<;> and inline contexts.
    for start, calls in sorted(inserts.items(), reverse=True):
        site = next(s for s, _, _ in trials if s.start == start)
        # End after the hint list and its location; outside parentheses the rest
        # of the original proof has exactly its old tactic state.
        end = site.right + len(location(body, site.right))
        old = body[start:end]
        qb = qb[:start] + "(" + "; ".join(calls) + "; " + old + ")" + qb[end:]
    return P.PREFIX + f"set_option maxHeartbeats 1000000 in\n" + head + qb, trials


def parse_query(messages, trials):
    out = []
    for i, texts in P.parse(messages).items():
        if not 0 <= i < len(trials):
            continue
        site, raw, gain = trials[i]
        used = []
        bad = False
        for text in texts:
            if "Try this:" not in text:
                continue
            hints = S.suggestion(text, site.family)
            if hints is None:
                bad = True
                break
            for h in hints:
                if h not in used:
                    used.append(h)
        if bad or not any("Try this:" in s for s in texts):
            continue
        text = "[" + ", ".join(used) + "]" if used else ""
        out.append((site.left, site.right, text))
        # For non-only calls retain only used *supplied* hints, so built-in simp
        # lemmas in the certificate do not erase the benefit of argument inference.
        if not site.only:
            given = S.split_hints(raw[1:-1]) or []
            key = lambda s: re.sub(r"\s+", " ", s).strip()
            wanted = {key(h) for h in used}
            # A star is printed as individual local names when they are
            # accessible. Keep it in the supplied-hint variant as their source.
            keep = [h for h in given if key(h) in wanted or h == "*"]
            out.append((site.left, site.right, "[" + ", ".join(keep) + "]" if keep else ""))
    return out


def query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None):
    qt = query_text(proof, statement)
    if qt is None:
        return None
    text, trials = qt
    result = run(text, (versions or [None])[0])
    if not getattr(result, "ok", False):
        if log:
            log(f"{FAMILY}: query failed: {str(getattr(result, 'errors', []))[:180]}")
        return None
    edits = parse_query(getattr(result, "messages", []), trials)
    if log:
        log(f"{FAMILY}: {len(trials)} trials returned {len(edits)} hint lists")
    return {"key": proof_key(proof), "edits": edits}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    try:
        hb = head_body(proof, statement)
        if not hb or not ctx or ctx.get("key") != proof_key(proof):
            return []
        head, body = hb
        allowed = {(s.left, s.right) for s, _, _ in hint_lists(body)}
        best, singles = {}, []
        for a, b, text in (ctx.get("edits") or []):
            if (a, b) not in allowed or not isinstance(text, str):
                continue
            if text and (not text.startswith("[") or not text.endswith("]") or S.split_hints(text[1:-1]) is None):
                continue
            gain = count_tokens(body[a:b]) - count_tokens(text)
            if gain <= 0:
                continue
            edit = (a, b, text)
            singles.append(edit)
            if (a, b) not in best or count_tokens(text) < count_tokens(best[(a, b)][2]):
                best[(a, b)] = edit
        em = Emitter(proof, statement, head, body, int(max_per_op or 8))
        if best:
            em.add(FAMILY + ":joint", S.apply_edits(body, best.values()), f"{len(best)} simp lists with inferred hint arguments")
        for e in sorted(singles, key=lambda e: -(count_tokens(body[e[0]:e[1]]) - count_tokens(e[2])))[:6]:
            em.add(FAMILY + ":single", S.apply_edits(body, [e]), "sandboxed simp certificate infers existing hint arguments")
        return em.out[:int(max_per_op or 8)]
    except (TypeError, ValueError, KeyError, IndexError):
        return []
