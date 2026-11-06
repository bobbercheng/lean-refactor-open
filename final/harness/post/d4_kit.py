#!/usr/bin/env python3
# Vendored, unchanged except for this comment and the `harness.post` imports, from the closed line's bet D4 code (branch closed-bets-d4 402c44d2, harness/tools/d4_kit.py) for the open post-step harness/open_post.py (2026-11-03).
"""Bet D4 helpers (not an end-stage family; harness/tools/__init__.py lists only families): the op-set rule, the proof key, the
declaration's head / body split, the term-line guard and the candidate emitter that the D4 families (d4_implied, d4_inlineeq, d4_search,
d4_lex, d4_micro) share. Pure: no compile, no I/O, no table, no row knowledge."""
from __future__ import annotations

import hashlib, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402

IDENT = r"[^\W\d][\w'!?₀-₉]*(?:\.(?:\d+|[^\W\d][\w'!?₀-₉]*))*"
IDENT_RE = re.compile(r"^%s$" % IDENT)
NEWLINE_BODY_RE = re.compile(r"[ \t]*\n")
AXIOM_ALLOW = ("propext", "Classical.choice", "Quot.sound")   # = scorer.compile.AXIOM_ALLOW (test_d4): the env queries' axiom gate


def op_names(family: str, ops) -> list[str]:
    """Op names with the "<family>:" prefix (a comma-separated string or a list; names given with or without the prefix)."""
    out = []
    for o in (ops.split(",") if isinstance(ops, str) else list(ops or [])):
        o = str(o).strip()
        if o:
            out.append(o if o.startswith(family + ":") else f"{family}:{o}")
    return out


def ops_for(family: str, ops: tuple, default_ops: tuple, opt_in_ops: tuple, ctx: dict | None) -> tuple[str, ...]:
    """The op set of a call, in OPS order: ctx["ops"] when given (the end stage's allow-list), else the default ops plus the opt-in ops
    named in ctx["opt_in"] (golf_ops' rule)."""
    ctx = ctx or {}
    if ctx.get("ops") is not None:
        want = set(op_names(family, ctx["ops"]))
        return tuple(o for o in ops if o in want)
    extra = set(op_names(family, ctx.get("opt_in"))) & set(opt_in_ops)
    return tuple(o for o in ops if o in default_ops or o in extra)


def proof_key(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def axiom_ok(var: str) -> str:
    """The Lean test "`var` is one of AXIOM_ALLOW" (the env queries keep a library constant only when every axiom Lean.collectAxioms
    finds for it passes: a real `axiom` or a sorried theorem never becomes a bridge; under Lean's module system an imported theorem is
    an axiom to the importer: from v4.30 collectAxioms reads the exporting module's own table for it, so its real axioms are tested;
    before v4.30 it reads as its own axiom and is dropped, coverage only)."""
    return " || ".join(f"{var} == ``{a}" for a in AXIOM_ALLOW)


def lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'


def head_body(proof: str, statement: str) -> tuple[str, str] | None:
    """(head = the statement and its `:=`, body = the text after it), or None when the proof does not start with the statement."""
    body = split_declaration(proof, statement)
    if body is None:
        return None
    return proof[:len(proof) - len(body)], body


def term_line_ok(body: str) -> bool:
    """False for a body that starts on the line after `:=` (the official worker counts that line break as one more token)."""
    return not NEWLINE_BODY_RE.match(body)


class Emitter:
    """Collects candidates of one call: distinct texts, never the incumbent, statement intact, body on the `:=` line when the incumbent's
    is, optionally only token savers; a per-op cap."""

    def __init__(self, proof: str, statement: str, head: str, body: str, cap: int):
        self.proof, self.statement, self.head, self.body = proof, statement, head, body
        self.t0 = count_tokens(body)
        self.newline0 = not term_line_ok(body)
        self.cap = int(cap)
        self.out: list[dict] = []
        self.seen = {proof.rstrip()}
        self.per_op: dict = {}

    def full(self, op: str) -> bool:
        return self.per_op.get(op, 0) >= self.cap

    def add(self, op: str, new_body: str, note: str, *, save: bool = True, extra: dict | None = None) -> bool:
        if self.full(op):
            return False
        decl = self.head + new_body
        if decl.rstrip() in self.seen or split_declaration(decl, self.statement) != new_body:
            return False
        if not self.newline0 and not term_line_ok(new_body):
            return False
        if save and count_tokens(new_body) >= self.t0:
            return False
        self.seen.add(decl.rstrip())
        self.per_op[op] = self.per_op.get(op, 0) + 1
        self.out.append({"op": op, "decl": decl, "note": note, **(extra or {})})
        return True


def msg_text(m) -> str:
    return str((m or {}).get("data", "")) if isinstance(m, dict) else str(m)


def line_of(text: str, i: int) -> int:
    return text.count("\n", 0, i) + 1
