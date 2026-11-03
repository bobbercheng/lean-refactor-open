"""Forbidden-pattern filter, mirroring the Arena's app.py `_FORBIDDEN_PATTERNS`



"""
from __future__ import annotations

import re

MAX_PROOF_BYTES = 256 * 1024

FORBIDDEN_PATTERNS: list[tuple[str, re.Pattern]] = [
    ("#eval", re.compile(r"#\s*eval\b")),
    ("#reduce", re.compile(r"#\s*reduce\b")),
    ("IO", re.compile(r"\bIO\b")),
    ("unsafe def/fun/theorem", re.compile(r"\bunsafe\s+(def|fun|theorem|lemma)\b")),
    ("extern", re.compile(r"\bextern\b")),
    ("initialize", re.compile(r"\binitialize\b")),
    ("@[implemented_by]", re.compile(r"@\[\s*implemented[_]?[Bb]y\b")),
    ("@[extern]", re.compile(r"@\[\s*extern\b")),
    ("sorry", re.compile(r"\bsorry\b")),
    ("sorryAx", re.compile(r"\bsorryAx\b")),
    ("admit", re.compile(r"\badmit\b")),
    ("axiom", re.compile(r"\baxiom\b")),
    ("native_decide", re.compile(r"\bnative_decide\b")),
    ("ofReduceBool", re.compile(r"\bofReduceBool\b")),
    ("ofReduceNat", re.compile(r"\bofReduceNat\b")),
    ("run_cmd", re.compile(r"\brun_cmd\b")),
    ("run_elab", re.compile(r"\brun_elab\b")),
    ("run_tac", re.compile(r"\brun_tacq?\b")),
    ("by_elab", re.compile(r"\bby_elabq?\b")),
    ("run_meta", re.compile(r"\brun_meta\b")),
    ("simproc", re.compile(r"\bd?simproc(?:_decl|_pattern)?\b")),
    ("eval%", re.compile(r"\beval%")),
    ("unsafe IO", re.compile(r"\bunsafe(?:Base|E)?IO\b")),
    ("decide +native", re.compile(r"\+\s*native\b|\bnative\s*:=\s*true\b")),
    ("#exit", re.compile(r"#\s*exit\b")),
    ("#count_heartbeats", re.compile(r"#\s*count_heartbeats\b")),
    ("attribute command", re.compile(r"(?m)^\s*attribute\b")),
    ("macro/elab/notation", re.compile(r"\b(macro|macro_rules|elab|elab_rules|notation|syntax)\b")),
    ("deriving instance", re.compile(r"\bderiving\s+instance\b")),
    ("auxiliary declaration", re.compile(r"(?m)^\s*(def|abbrev|instance|structure|inductive|class|opaque)\b")),
]
                                                                                                                                          
HEARTBEAT_IDENT = re.compile(r"[\w.'!?«»]*heartbeat[\w'!?«»]*", re.IGNORECASE)


def strip_lean_comments(text: str) -> str:
    out: list[str] = []
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == '"':
            out.append(c)
            i += 1
            while i < n:
                out.append(text[i])
                if text[i] == "\\" and i + 1 < n:
                    out.append(text[i + 1])
                    i += 2
                    continue
                if text[i] == '"':
                    i += 1
                    break
                i += 1
            continue
        if text.startswith("/-", i):
            depth, i = 1, i + 2
            while i < n and depth:
                if text.startswith("/-", i):
                    depth += 1
                    i += 2
                elif text.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            out.append(" ")
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(c)
        i += 1
    return "".join(out)


def check_forbidden(code: str) -> str | None:
    """Return the label of the first forbidden pattern hit, or None."""
    if len(code.encode("utf-8")) > MAX_PROOF_BYTES:
        return f"too large (> {MAX_PROOF_BYTES // 1024} KB)"
    stripped = strip_lean_comments(code)
    for label, pat in FORBIDDEN_PATTERNS:
        if pat.search(stripped):
            return label
    for m in HEARTBEAT_IDENT.finditer(stripped):
        if m.group().replace("«", "").replace("»", "").split(".")[-1] != "maxHeartbeats":
            return f"{m.group()} (heartbeat measurement)"
    return None
