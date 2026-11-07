"""Minimize existing simp lemma lists using the row's own simp? certificates.

Distinct from region/closer search: keeps every tactic and its context, and queries
only existing simplifier calls. No library facts or benchmark data are stored.
The ordinary post-step gate validates each resulting declaration on every pin.
"""
from __future__ import annotations

# provenance: research lane gaplane2-sol (worktree lra-gl2-sol), commit 6cee22b, ported unchanged into open-post-v3 (2026-11-04)

import re
from dataclasses import dataclass

from harness.normalize import _mask, _pairs
from harness.post.d4_kit import Emitter, head_body, msg_text, proof_key
from scorer.tokenize import count_tokens

FAMILY = "sol_simphints"
MAX_SITES = 40
QUERY_HB = 200000
MARKER = "SOL_SIMPHINT_BASE"
WORD = re.compile(r"(?<![\w'.])(?:simp_all|simpa|simp)(?![\w'?!])")


def code(text: str) -> str:
    mask = _mask(text)
    return "".join(" " if mask[i] and c != "\n" else c for i, c in enumerate(text))


@dataclass(frozen=True)
class Site:
    start: int
    word_end: int
    left: int
    right: int
    only: bool
    family: str


def sites(body: str) -> list[Site]:
    clean = code(body)
    pairs = _pairs(body, _mask(body))
    out = []
    for m in WORD.finditer(clean):
        p = m.end()
        if clean[p:p + 1] == "!":
            p += 1
        word_end = p
        while p < len(clean) and clean[p].isspace():
            p += 1
        only = bool(re.match(r"only\b", clean[p:]))
        if only:
            p += 4
            while p < len(clean) and clean[p].isspace():
                p += 1
        if clean[p:p + 1] != "[" or p not in pairs:
            continue
        q = pairs[p] + 1
        if count_tokens(body[p:q]) < 4:
            continue
        out.append(Site(m.start(), word_end, p, q, only, m.group()))
    # Nested simp calls inside another call's lemma list are left alone.
    out = [s for s in out if not any(t.left <= s.start < t.right for t in out)]
    return out[:MAX_SITES]


def has_sites(proof: str, statement: str) -> bool:
    hb = head_body(proof, statement)
    return bool(hb and sites(hb[1]))


def split_hints(text: str) -> list[str] | None:
    """Top-level comma split with Lean comments, strings and brackets respected."""
    mask = _mask(text)
    pairs = _pairs(text, mask)
    out, start, i = [], 0, 0
    while i < len(text):
        if i in pairs:
            i = pairs[i] + 1
            continue
        if not mask[i] and text[i] == ",":
            out.append(text[start:i].strip())
            start = i + 1
        i += 1
    out.append(text[start:].strip())
    hints = [s for s in out if s]
    # Reject unbalanced input rather than synthesizing broken certificates.
    clean = code(text)
    if any(c in "([{⟨" and i not in pairs for i, c in enumerate(clean)):
        return None
    return hints


def suggestion(text: str, family: str) -> list[str] | None:
    """Read Lean's TryThis text; accept only one simplifier certificate."""
    if "Try this:" not in text:
        return None
    s = text.split("Try this:", 1)[1].strip()
    s = re.sub(r"^\[apply\]\s*", "", s)
    m = re.match(re.escape(family) + r"!?\s+only\b", s)
    if not m:
        return None
    p = m.end()
    while p < len(s) and s[p].isspace():
        p += 1
    if s[p:p + 1] != "[":
        return [] if not s[p:] or re.match(r"(?:at|using)\b", s[p:]) else None
    pairs = _pairs(s, _mask(s))
    if p not in pairs:
        return None
    tail = s[pairs[p] + 1:].strip()
    if tail and not re.match(r"(?:at|using)\b", tail):
        return None
    return split_hints(s[p + 1:pairs[p]])


def query_text(proof: str, statement: str):
    hb = head_body(proof, statement)
    if not hb:
        return None
    head, body = hb
    ss = sites(body)
    if not ss:
        return None
    # The dummy consumes declaration modifiers from the file prefix and emits a
    # position anchor. Prefix line counts are not an allowed input to the op.
    prefix = (f'theorem solSimpHintDummy : True := by\n'
              f'  trace "{MARKER}"\n  trivial\n\n'
              f'set_option maxHeartbeats {QUERY_HB} in\n')
    inserts = [s.word_end for s in ss]
    qb = body
    for p in reversed(inserts):
        qb = qb[:p] + "?" + qb[p:]
    text = prefix + head + qb
    positions = {}
    for i, s in enumerate(ss):
        p = len(prefix) + len(head) + s.start + sum(j <= s.start for j in inserts)
        line = text.count("\n", 0, p) + 1
        line_start = text.rfind("\n", 0, p) + 1
        col = len(text[line_start:p])
        byte_col = len(text[line_start:p].encode())
        positions[(line, col)] = i
        positions[(line, byte_col)] = i
    return text, positions, ss


def parse_query(messages, positions, ss) -> dict[int, str]:
    shifts = set()
    for m in messages or []:
        if msg_text(m).strip() == MARKER and isinstance(m, dict):
            p = m.get("pos") or {}
            if isinstance(p.get("line"), int):
                shifts.add(p["line"] - 2)
    if len(shifts) != 1:
        return {}
    shift = next(iter(shifts))
    used, bad = {}, set()
    for m in messages or []:
        if not isinstance(m, dict):
            continue
        p = m.get("pos") or {}
        if not isinstance(p.get("line"), int):
            continue
        i = positions.get((p["line"] - shift, p.get("column")))
        if i is None or "Try this:" not in msg_text(m):
            continue
        hints = suggestion(msg_text(m), ss[i].family)
        if hints is None:
            bad.add(i)
            continue
        acc = used.setdefault(i, [])
        for h in hints:
            if h not in acc:
                acc.append(h)
    return {i: "[" + ", ".join(hs) + "]" for i, hs in used.items() if i not in bad}


def query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None):
    qt = query_text(proof, statement)
    if qt is None:
        return None
    text, positions, ss = qt
    # Exceptions (including the harness's budget signal) propagate to its caller;
    # unsuccessful or timed-out compiles provide no candidates.
    r = run(text, (versions or [None])[0])
    if not getattr(r, "ok", False):
        if log:
            log(f"{FAMILY}: query failed: {str(getattr(r, 'errors', []))[:160]}")
        return None
    hints = parse_query(getattr(r, "messages", []), positions, ss)
    if log:
        log(f"{FAMILY}: {len(hints)}/{len(ss)} sites returned certificates")
    return {"key": proof_key(proof), "hints": hints}


def apply_edits(body: str, edits) -> str:
    for a, b, text in sorted(edits, reverse=True):
        body = body[:a] + text + body[b:]
    return body


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    try:
        hb = head_body(proof, statement)
        if not hb or not ctx or ctx.get("key") != proof_key(proof):
            return []
        head, body = hb
        ss = sites(body)
        raw, only = [], []
        for i, hints in (ctx.get("hints") or {}).items():
            if not isinstance(i, int) or not 0 <= i < len(ss) or not isinstance(hints, str):
                continue
            s = ss[i]
            if suggestion(f"Try this: {s.family} only {hints}", s.family) is None:
                continue
            replacement = "" if hints == "[]" else hints
            if count_tokens(replacement) < count_tokens(body[s.left:s.right]):
                raw.append((s.left, s.right, replacement))
            cert = " only" + (" " + hints if hints != "[]" else "")
            before = body[s.word_end:s.right]
            if count_tokens(cert) < count_tokens(before):
                only.append((s.word_end, s.right, cert))
        em = Emitter(proof, statement, head, body, int(max_per_op or 8))
        for kind, edits in (("trim", raw), ("only", only)):
            if not edits:
                continue
            em.add(f"{FAMILY}:{kind}", apply_edits(body, edits), f"{len(edits)} environment-certified simp hint lists")
            if len(edits) > 1:
                for e in sorted(edits, key=lambda e: -(count_tokens(body[e[0]:e[1]]) - count_tokens(e[2])))[:4]:
                    em.add(f"{FAMILY}:{kind}", apply_edits(body, [e]), "one environment-certified simp hint list")
        return sorted(em.out, key=lambda c: count_tokens(c["decl"]))[:int(max_per_op or 8)]
    except (TypeError, ValueError, KeyError, IndexError):
        return []
