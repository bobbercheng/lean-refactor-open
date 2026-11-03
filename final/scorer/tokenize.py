"""Proof-body token count, replicating the Arena's `proof_length`.













"""
from __future__ import annotations

import re

MERGE_OPS = [":=", "!=", "&&", "-.", "->", "<-", "...", "..", "::", ":>",
             "<;>", ";;", "==", "||", "=>", "<=", ">=", "⁻¹", "?_"]
_OPS_BY_LEN = sorted(MERGE_OPS, key=len, reverse=True)


def remove_comments(s: str) -> str:
    s = re.sub(r" */-.*?-/", "", s, flags=re.DOTALL)
    s = re.sub(r" *--.*", "", s)
    return s


def _lex_line(line: str) -> list[str]:
    toks: list[str] = []
    cur = ""
    for ch in line:
        if ch == " ":
            if cur:
                toks.append(cur)
                cur = ""
            continue
        if ch.isalnum() or ch in "_.'":
            cur += ch
        else:
            if cur:
                toks.append(cur)
                cur = ""
            toks.append(ch)
    if cur:
        toks.append(cur)
    merged: list[str] = []
    i = 0
    while i < len(toks):
        hit = None
        for op in _OPS_BY_LEN:
            j, cat = i, ""
            while j < len(toks) and len(cat) < len(op):
                cat += toks[j]
                j += 1
            if cat == op:
                hit = (op, j)
                break
        if hit:
            merged.append(hit[0])
            i = hit[1]
        else:
            merged.append(toks[i])
            i += 1
    return merged


def tokens(body: str) -> list[str]:
    out: list[str] = []
    for line in remove_comments(body).split("\n"):
        if not line.strip():
            continue
        out.extend(_lex_line(line))
    return out


def count_tokens(body: str) -> int:
    return len(tokens(body))


def split_declaration(decl: str, statement: str) -> str | None:
    """Return the proof body of a full declaration, or None if it does not
"""
    if not decl.startswith(statement):
        return None
    rest = decl[len(statement):]
    m = re.match(r"\s*:=", rest)
    if not m:
        return None
    return rest[m.end():]
