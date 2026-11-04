"""Find shorter library terms for explicit, typed local facts.

Queries exact? at a small intermediate fact's own type, not at a main proof
closer. Facts already in term mode retain their bindings and all downstream
proof structure. Only strictly shorter terms from Lean suggestions are used.
"""
from __future__ import annotations

# provenance: research lane gaplane2-sol (worktree lra-gl2-sol), commit 6cee22b, ported unchanged into open-post-v3 (2026-11-04)

import re
from dataclasses import dataclass

from harness.normalize import _mask, _pairs
from harness.post import sol_probe as P, sol_simphints as S
from harness.post.d4_kit import Emitter, IDENT, head_body, proof_key
from scorer.tokenize import count_tokens

FAMILY = "sol_factterms"
MAX_PROBES = 8
HAVE = re.compile(r"^([ \t]*)have[ \t]+(" + IDENT + r")[ \t]*:[ \t]*(.+)$")


@dataclass(frozen=True)
class Site:
    start: int
    end: int
    indent: str
    name: str
    typ: str
    term: str


def top_assignment(text):
    mask = _mask(text)
    pairs = _pairs(text, mask)
    i = 0
    while i < len(text):
        if i in pairs:
            i = pairs[i] + 1
            continue
        if not mask[i] and text.startswith(":=", i):
            return i
        i += 1
    return None


def sites(body):
    out, offset = [], 0
    lines = body.splitlines(keepends=True)
    for j, line in enumerate(lines):
        raw = line.rstrip("\r\n")
        clean = S.code(raw)
        m = HAVE.match(clean)
        start = offset
        offset += len(line)
        if not m:
            continue
        a = top_assignment(raw[m.start(3):])
        if a is None:
            continue
        a += m.start(3)
        end = start + len(raw)
        tail = []
        for ln in lines[j + 1:]:
            code = S.code(ln).rstrip("\r\n")
            if code.strip() and len(code) - len(code.lstrip()) <= len(m[1]):
                break
            tail.append(ln.rstrip("\r\n"))
            end += len(ln)
        # Include the newline after the head, but leave the final newline in
        # place so an edit never joins the following tactic onto this fact.
        if tail:
            end = start + len(line) + sum(len(ln) for ln in lines[j + 1:j + 1 + len(tail)])
            if body[end - 1:end] == "\n":
                end -= 1
        typ = raw[m.start(3):a].strip()
        term = (raw[a + 2:] + ("\n" + "\n".join(tail) if tail else "")).strip()
        if not typ or not term or count_tokens(term) < 5:
            continue
        # A tactic wrapper elaborates the expected type before the original
        # RHS can resolve its holes. Skip underspecified ascriptions rather
        # than making the whole row's query fail.
        if re.search(r"(?<![\w'])_(?![\w'])", S.code(typ)):
            continue
        # Root tactic-mode facts belong to structural/closer search. Term-mode
        # lambdas may contain tactic subproofs, but the query asks for one whole
        # term at the fact's stated type and preserves its binding.
        if clean != raw or S.code(term) != term or re.match(r"(?:by|do)\b", term):
            continue
        pairs = _pairs(term, _mask(term))
        if any(c in "([{⟨" and i not in pairs for i, c in enumerate(S.code(term))):
            continue
        if re.search(r"(?:=>|\$|:=|,|\|)\s*$", term):
            continue
        out.append(Site(start, end, m[1], m[2], typ, term))
    out = [s for s in out if not any(t.start < s.start < t.end for t in out)]
    return sorted(out, key=lambda s: (-count_tokens(s.term), s.start))


def has_sites(proof, statement):
    hb = head_body(proof, statement)
    return bool(hb and sites(hb[1]))


def query_text(proof, statement):
    hb = head_body(proof, statement)
    if not hb:
        return None
    head, body = hb
    trials = sites(body)[:MAX_PROBES]
    if not trials:
        return None
    edits = []
    for i, s in enumerate(trials):
        original = "exact (" + s.term + ")"
        probe = P.call(i, "exact?", original)
        term_lines = s.term.splitlines()
        replay = "exact (" + term_lines[0]
        replay += "".join("\n  " + ln for ln in term_lines[1:]) + ")"
        text = s.indent + f"have {s.name} : {s.typ} := by\n" + s.indent + "  " + probe + "\n" + s.indent + "  " + replay
        edits.append((s.start, s.end, text))
    return P.PREFIX + "set_option maxHeartbeats 1000000 in\n" + head + S.apply_edits(body, edits), trials


def exact_term(text):
    if "Try this:" not in text:
        return None
    text = text.split("Try this:", 1)[1].strip()
    text = re.sub(r"^\[apply\]\s*", "", text)
    m = re.match(r"exact\s+([\s\S]+)$", text)
    if not m:
        return None
    term = m[1].strip()
    clean = S.code(term)
    if not term or clean != term or re.search(r"\b(?:sorry|admit|run_tac)\b|[;]", clean):
        return None
    pairs = _pairs(term, _mask(term))
    if any(c in "([{⟨" and i not in pairs for i, c in enumerate(clean)):
        return None
    return term


def parse_query(messages, trials):
    edits = []
    for i, texts in P.parse(messages).items():
        if not 0 <= i < len(trials):
            continue
        terms = [exact_term(t) for t in texts if "Try this:" in t]
        # A fact has exactly one goal. Several differing suggestions at the
        # same index would signal duplicated execution or ambiguous syntax.
        if not terms or any(t is None for t in terms) or len(set(terms)) != 1:
            continue
        s, term = trials[i], terms[0]
        if count_tokens(term) < count_tokens(s.term):
            edits.append((s.start, s.end, term))
    return edits


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
        log(f"{FAMILY}: {len(trials)} fact queries returned {len(edits)} shorter terms")
    return {"key": proof_key(proof), "edits": edits}


def candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None):
    try:
        hb = head_body(proof, statement)
        if not hb or not ctx or ctx.get("key") != proof_key(proof):
            return []
        head, body = hb
        allowed = {(s.start, s.end): s for s in sites(body)}
        typed, inferred = [], []
        for a, b, term in ctx.get("edits") or []:
            s = allowed.get((a, b))
            if not s or not isinstance(term, str) or exact_term("Try this: exact " + term) != term:
                continue
            if count_tokens(term) >= count_tokens(s.term):
                continue
            rendered = term.replace("\n", "\n" + s.indent)
            typed.append((a, b, s.indent + f"have {s.name} : {s.typ} := {rendered}"))
            inferred.append((a, b, s.indent + f"have {s.name} := {rendered}"))
        em = Emitter(proof, statement, head, body, int(max_per_op or 8))
        for tag, edits in (("inferred", inferred), ("typed", typed)):
            if edits:
                em.add(FAMILY + ":" + tag, S.apply_edits(body, edits), f"{len(edits)} shorter local fact terms found by type")
        for e in inferred[:3] + typed[:3]:
            em.add(FAMILY + ":single", S.apply_edits(body, [e]), "type-directed local fact suggestion")
        return em.out
    except (TypeError, ValueError, KeyError, IndexError):
        return []
