"""Junk detection for model output (2026-10-14, operator: "We need programtic way to reject the junk"; docs/warmup_clean_recheck.md).








"""
from __future__ import annotations

import re

MAX_ARG_CHARS = 60_000                                                                                     
STEP = 1_000                                                               


def degenerate_tail(raw: str, window: int = 2000) -> bool:
    """True when `raw` ENDS in degenerate repetition (2026-10-11 warm-up Sol run: all 26 tool calls cut at the output cap were this:

"""
    tail = raw[-window:]
    if len(tail) < 200:
        return False
    if len(re.sub(r"(\\[tnr]|\s)+", "", tail)) < 0.1 * len(tail):
        return True
    return any(len(tail) >= 20 * k and sum(a != b for a, b in zip(tail, tail[k:])) <= 0.05 * (len(tail) - k) for k in range(1, 41))


def junk_reason(text: str, start: int = 0, max_chars: int = MAX_ARG_CHARS) -> str | None:
    """Why `text` (a tool call's raw arguments, or reply text) is junk, or None: over `max_chars`, or degenerate repetition at any check
"""
    if len(text) > max_chars:
        return f"{len(text)} chars of arguments (over {max_chars})"
    for i in range(max(STEP * (start // STEP + 1), 2 * STEP), len(text) + 1, STEP):
        if degenerate_tail(text[:i]):
            return f"degenerate repetition at char {i - 2 * STEP}-{i}: {text[max(0, i - 60):i]!r}"
    return None


class StreamGuard:
    """Incremental junk check over growing texts keyed by a slot (tool-call index, or 'content'): call `feed(slot, text)` with the full text
"""

    def __init__(self, max_chars: int = MAX_ARG_CHARS):
        self.max_chars, self.done = max_chars, {}

    def feed(self, slot, text: str) -> str | None:
        last = self.done.get(slot, 0)
        if len(text) - last < STEP and len(text) <= self.max_chars:
            return None
        self.done[slot] = len(text) - len(text) % STEP
        return junk_reason(text, start=last, max_chars=self.max_chars)
