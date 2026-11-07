#!/usr/bin/env python3
"""Tactic-block spans of a proof body (post-step v2 shared module; owner: hintgrind, also read by other span ops). Pure text: no compile,
no table, no row knowledge. Every span is a range of the body that ends where a goal is closed (the end of a tactic block), so a closer
put in its place is a well-formed candidate.

  parse     the body (the text after the statement's `:=`, as scorer.tokenize.split_declaration gives it) is split into tactic blocks and
            steps by layout, the way Lean's tactic parser reads a `by` block: a block's column is the column of its first tactic; a step
            starts on a line whose first code character sits at that column (outside open brackets) and runs until the next such line,
            or until a line at a smaller column ends the block. Comments and string literals are masked (harness/normalize._mask) before
            anything is read. WRAPPER-TRANSPARENT: `by unhygienic`, `by classical`, `by unhygienic classical` (wrapper words alone on
            the `by` line) and `:=` + line break + `by` open the block on the next code line; the wrapper text stays byte for byte
            outside every span.
  nested    blocks inside a step: the body of `case tag xs =>` / `case' ... =>` / `next xs =>` (on the same line or the lines below), of
            a `·` bullet, of each `| tag xs =>` alternative of an `induction` / `cases` / `match` / `fun_induction` / `fun_cases` step
            with arms (arms may sit at the step's own column), and the `by` block of a `have` / `haveI` / `replace` / `suffices` step
            (a `by` that ends a line, or `by` followed by the block's first tactic).
  spans     (each one >= MIN_STEPS steps or >= MIN_TOKENS lexer tokens)
    suffix    the last k = 1..MAX_SUFFIX steps of any block, and the whole block when it is longer
    arm       a whole block that is the body of a case / next / bullet / alternative
    havebody  a whole block that is the `by` block of a have-like step
    region    a split step (SPLIT heads: induction, cases, rcases / obtain with a `|` pattern, match, by_cases, split, fun_induction,
              fun_cases, constructor, refine with a `?_` hole) through the end of its block, arms included; "head" is the split step
              without its `with` arms (None for `match`, whose arms cannot be dropped)
  A span is {"kind", "lo", "hi" (body offsets: the first step's first code character .. the last step's last code character), "indent"
  (the block's column), "steps", "text", "tokens", "head" (region), "head_text", "block" (the block's index)}. Replacing body[lo:hi] by a
  one-line closer keeps every byte outside the span (the indentation before lo included).
    python3 harness/post/spans.py --file body.lean     the spans as JSON lines"""
from __future__ import annotations

import argparse, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask  # noqa: E402
from scorer.tokenize import count_tokens  # noqa: E402

WRAPPERS = ("unhygienic", "classical")
MIN_STEPS = 2
MIN_TOKENS = 8
MAX_SUFFIX = 8
SPLIT = ("induction", "induction'", "cases", "cases'", "rcases", "obtain", "match", "by_cases", "split", "fun_induction", "fun_cases",
         "constructor", "refine", "refine'")
ARM_HEADS = ("induction", "induction'", "cases", "cases'", "match", "fun_induction", "fun_cases", "rcases")
HAVE_HEADS = ("have", "haveI", "replace", "suffices", "obtain")
OPEN, CLOSE = "([{⟨⦃‹", ")]}⟩⦄›"
_WORD = re.compile(r"[^\W\d][\w'!?]*")
_BY_END = re.compile(r"(?<![\w'.])by[ \t]*$")


def _code(body: str) -> str:
    """The body with comment / string characters blanked (newlines kept)."""
    m = _mask(body)
    return "".join((" " if (m[i] and ch != "\n") else ch) for i, ch in enumerate(body))


def _lines(code: str) -> list[tuple[int, int]]:
    """[(start, end)] offsets of each line (end excludes the newline)."""
    out, pos = [], 0
    for ln in code.split("\n"):
        out.append((pos, pos + len(ln)))
        pos += len(ln) + 1
    return out


def _col(code: str, i: int) -> int:
    return i - (code.rfind("\n", 0, i) + 1)


def _skip_ws(code: str, i: int, end: int) -> int:
    while i < end and code[i] in " \t\n\r":
        i += 1
    return i


def _skip_wrappers(code: str, i: int, end: int) -> int:
    """From just after a `by`: skip blanks and the wrapper words (module docstring, "parse"); the offset of the block's first tactic. A
    wrapper is transparent only when the rest of its line holds nothing but wrapper words (its tactic sequence starts below)."""
    j = _skip_ws(code, i, end)
    while True:
        m = _WORD.match(code, j)
        if not (m and m.group(0) in WRAPPERS and m.end() <= end):
            return j
        le = code.find("\n", m.end())
        le = len(code) if le < 0 else le
        if all(w in WRAPPERS for w in code[m.end():le].split()):
            j = _skip_ws(code, m.end(), end)
            continue
        return j


def _depths(code: str) -> list[int]:
    """Bracket depth before each character (masked text: comments and strings are blank)."""
    d, out = 0, []
    for ch in code:
        out.append(d)
        if ch in OPEN:
            d += 1
        elif ch in CLOSE:
            d = max(0, d - 1)
    out.append(d)
    return out


class Parser:
    def __init__(self, body: str):
        self.body = body
        self.code = _code(body)
        self.depth = _depths(self.code)
        self.blocks: list[dict] = []

    # ------------------------------------------------------------------------------------------------------------------------- steps
    def _line_end(self, i: int) -> int:
        j = self.code.find("\n", i)
        return len(self.code) if j < 0 else j

    def _next_line_start(self, i: int) -> int:
        j = self.code.find("\n", i)
        return len(self.code) if j < 0 else j + 1

    def _first_code(self, ls: int, end: int) -> int | None:
        """The first non-blank character of the line starting at ls (before end), else None."""
        le = min(self._line_end(ls), end)
        j = ls
        while j < le and self.code[j] in " \t\r":
            j += 1
        return j if j < le else None

    def _trim(self, lo: int, hi: int) -> int:
        """hi moved back over trailing blanks / blank lines (the step's last code character + 1)."""
        while hi > lo and self.code[hi - 1] in " \t\r\n":
            hi -= 1
        return hi

    def block(self, start: int, end: int, kind: str, parent: int | None = None) -> int | None:
        """Parse the block whose first tactic is at `start`, inside [start, end). Returns the block index (None: no step)."""
        code = self.code
        start = _skip_ws(code, start, end)
        if start >= end:
            return None
        col = _col(code, start)
        base_depth = self.depth[start]
        steps = []
        cur = start
        ls = self._next_line_start(start)
        stop = end
        while ls < end:
            fc = self._first_code(ls, end)
            if fc is None:
                ls = self._next_line_start(ls)
                continue
            c = _col(code, fc)
            if self.depth[fc] > base_depth:   # inside an open bracket: a continuation
                ls = self._next_line_start(ls)
                continue
            if c < col:
                stop = ls
                break
            if c == col and not code.startswith("|", fc):
                steps.append((cur, self._trim(cur, ls)))
                cur = fc
            ls = self._next_line_start(ls)
        steps.append((cur, self._trim(cur, stop)))
        steps = [(a, b) for a, b in steps if b > a]
        if not steps:
            return None
        idx = len(self.blocks)
        blk = {"index": idx, "kind": kind, "col": col, "lo": steps[0][0], "hi": steps[-1][1], "parent": parent, "steps": []}
        self.blocks.append(blk)
        for a, b in steps:
            blk["steps"].append(self.step(a, b, col, idx))
        return idx

    def step(self, a: int, b: int, col: int, bidx: int) -> dict:
        code = self.code
        m = _WORD.match(code, a)
        head = m.group(0) if m else code[a:a + 1]
        st = {"lo": a, "hi": b, "head": head, "children": [], "arms": False}
        # case / next / bullets: the body after `=>` / `·`
        if head in ("case", "case'", "next"):
            k = self._arrow(a, b)
            if k is not None:
                ch = self.block(k, b, "arm", bidx)
                if ch is not None:
                    st["children"].append(ch)
            return st
        if code.startswith("·", a) or (code.startswith(".", a) and code[a + 1:a + 2] in " \t"):
            ch = self.block(a + 1, b, "arm", bidx)
            if ch is not None:
                st["children"].append(ch)
            return st
        # alternatives `| tag xs => tacs` at line starts
        if head in ARM_HEADS:
            alts = self._alternatives(a, b)
            if alts:
                st["arms"] = True
                st["head_hi"] = self._trim(a, alts[0][0])
                for (p, q) in alts:
                    k = self._arrow(p, q)
                    if k is not None:
                        ch = self.block(k, q, "arm", bidx)
                        if ch is not None:
                            st["children"].append(ch)
                return st
        if head in HAVE_HEADS:   # (an `obtain` with a `|` pattern is a split; its `:= by` block is a have-like body all the same)
            k = self._have_by(a, b)
            if k is not None:
                ch = self.block(k, b, "havebody", bidx)
                if ch is not None:
                    st["children"].append(ch)
        return st

    def _arrow(self, a: int, b: int) -> int | None:
        """The offset after the first depth-0 `=>` of [a, b) (the start of an arm's body), else None."""
        d0 = self.depth[a]
        i = self.code.find("=>", a, b)
        while i >= 0:
            if self.depth[i] == d0:
                return i + 2
            i = self.code.find("=>", i + 2, b)
        return None

    def _alternatives(self, a: int, b: int) -> list[tuple[int, int]]:
        """[(start, end)] of the `|` alternatives that start lines inside the step [a, b), when the step's first line (or a later line before
        the first alternative) ends with `with`."""
        code = self.code
        d0 = self.depth[a]
        starts = []
        ls = self._next_line_start(a)
        while ls < b:
            fc = self._first_code(ls, b)
            if fc is not None and code.startswith("|", fc) and self.depth[fc] == d0:
                starts.append(fc)
            ls = self._next_line_start(ls)
        if not starts:
            return []
        pre = code[a:starts[0]].rstrip()
        if not re.search(r"(?<![\w'.])with$", pre):
            return []
        col0 = _col(code, starts[0])
        starts = [s for s in starts if _col(code, s) == col0]
        out = []
        for i, s in enumerate(starts):
            e = starts[i + 1] if i + 1 < len(starts) else b
            out.append((s, self._trim(s, e)))
        if any(self._arrow(p, q) is None for p, q in out):
            return []   # `|` lines of a multi-line pattern, not tactic alternatives
        return out

    def _have_by(self, a: int, b: int) -> int | None:
        """A have-like step's `by` block start: `:= by` that ends a line, or `:= by tac` (the tactic's offset), at the step's depth."""
        code = self.code
        d0 = self.depth[a]
        for m in re.finditer(r":=[ \t]*\n?[ \t]*by(?![\w'])", code[a:b]):
            i = a + m.start()
            if self.depth[i] != d0:
                continue
            k = a + m.end()
            j = _skip_wrappers(code, k, b)
            if j >= b:
                return None
            return j
        return None


def parse(body: str) -> dict | None:
    """{"blocks": [...], "code": masked body} or None when the body is not a `by` block (a term proof)."""
    p = Parser(body)
    code = p.code
    m = re.match(r"\s*by(?![\w'])", code)
    if not m:
        return None
    j = _skip_wrappers(code, m.end(), len(code))
    if j >= len(code):
        return None
    top = p.block(j, len(code), "top")
    if top is None:
        return None
    return {"blocks": p.blocks, "code": code, "top": top}


def _is_split(code: str, st: dict) -> bool:
    h = st["head"]
    if h not in SPLIT:
        return False
    text = code[st["lo"]:st["hi"]]
    if h in ("rcases", "obtain"):
        return "|" in text.split(":=")[0] if h == "obtain" else "|" in text
    if h in ("refine", "refine'"):
        return "?_" in text
    return True


def spans(body: str, *, min_steps: int = MIN_STEPS, min_tokens: int = MIN_TOKENS, max_suffix: int = MAX_SUFFIX) -> list[dict]:
    """The spans of the body (module docstring), deduplicated by (kind, lo, hi), in block order."""
    pr = parse(body)
    if pr is None:
        return []
    code = pr["code"]
    out, seen = [], set()

    def add(kind, blk, i, j, **extra):
        lo, hi = blk["steps"][i]["lo"], blk["steps"][j]["hi"]
        text = body[lo:hi]
        n = j - i + 1
        key = (kind, lo, hi)
        if key in seen:
            return
        tok = count_tokens(text)
        if n < min_steps and tok < min_tokens:
            return
        seen.add(key)
        out.append(dict({"kind": kind, "lo": lo, "hi": hi, "indent": blk["col"], "steps": n, "text": text, "tokens": tok,
                         "block": blk["index"]}, **extra))

    for blk in pr["blocks"]:
        st = blk["steps"]
        n = len(st)
        whole = {"arm": "arm", "havebody": "havebody"}.get(blk["kind"], "suffix")
        add(whole, blk, 0, n - 1)
        for k in range(1, min(max_suffix, n) + 1):
            if k == n:
                continue
            add("suffix", blk, n - k, n - 1)
        for i, s in enumerate(st):
            if not _is_split(code, s):
                continue
            if s["head"] == "match":
                head = None
            elif s.get("arms"):
                head = body[s["lo"]:s["head_hi"]]
                head = re.sub(r"[ \t]*\bwith[ \t]*$", "", head.rstrip())
            else:
                head = body[s["lo"]:s["hi"]]
            if head is not None and "\n" in head.strip():
                head = None   # a multi-line head: only the whole-region replacement
            add("region", blk, i, n - 1, head=head, head_lo=s["lo"])
    return out


def replace(body: str, sp: dict, text: str) -> str:
    """The body with the span replaced by `text` (a one-line closer, or several lines already indented after the first)."""
    return body[:sp["lo"]] + text + body[sp["hi"]:]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--file", required=True)
    a = ap.parse_args(argv)
    body = Path(a.file).read_text()
    for sp in spans(body):
        print(json.dumps({k: v for k, v in sp.items()}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
