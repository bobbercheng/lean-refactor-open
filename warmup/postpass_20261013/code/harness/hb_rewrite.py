#!/usr/bin/env python3
"""Heartbeat micro-normalizer (measured heartbeat techniques and the $0 plan; 2026-10-13): a deterministic, model-free
$0 CPU post-pass next to the lexer normalizer (harness/normalize.py) and the certificate polish (harness/hb_polish.py). Each operator is a
site class; every site is tried separately on a COMPILING proof and kept only where the WHOLE proof scores higher by more than the noise
margin (score = (L + H + Z) / 3, so a heartbeat win that costs arena tokens (scorer/tokenize.py) must still raise the score):
  repeatrw        `repeat rw [h] (at l)` / `repeat (rw [h])` / `repeat` + one indented `rw [h]` line -> `simp only [h] (at l)`
  rw2rewrite      `rw [..]` -> `rewrite [..]`: rw = rewrite + try (with_reducible rfl); the rfl attempt costs heartbeats, and where it was
                  closing a goal the compile fails and the site is rejected (`rw .. at h` included: its rfl also targets the main goal).
                  rwa / erw / nth_rw / rw_mod_cast / rw? / simp_rw are not sites; neither is a `rw` inside a conv block (conv's rw has no
                  rfl) nor the last tactic of a block that must close its goals (`by`, `·`, `=>`): its rfl closed the goal. The last
                  tactic of a combinator block (all_goals, <;>, try, ...) is a late site: never in an all-at-once group, tried last.
  simponly2dsimp  `simp only [..]` -> `dsimp only [..]` (definitional steps 86-100% cheaper; non-definitional ones fail to compile)
  simprw2only     `simp_rw [a, b]` -> `simp only [a, b]` (sequential vs simultaneous: the compile decides; +1 token)
  withreducible   `first | apply X | exact Y | ..` -> `first | with_reducible apply X | ..` (measured 686 -> 622); only an alternative
                  that is a single apply / exact (no depth-0 `<;>` / `;`, no continuation line), since with_reducible takes a sequence
  exists2refine   `exists a, b` -> `refine ⟨a, b, ?_⟩` (exists = refine + try trivial) or `exact ⟨a, b, rfl⟩`
  use2refine      Mathlib `use a, b` -> `refine ⟨a, b, ?_⟩` (use runs its discharger on the leftover goal), `exists a, b` (token-neutral,
                  the lighter `try trivial` discharger), `exact ⟨a, b⟩` (a complete argument list: the goal closed) or `exact ⟨a, b, rfl⟩`
Variants of one call share its span: the first variant that pays is kept, the others are skipped; the layout (last tactic of its block or
not) only orders them. Sites are found in tactic position only (line start, after `by`, `<;>`, `;`, `=>`, `|`, `·`, `(`, `{`, all_goals /
any_goals / try / iterate ...), never inside comments or strings, and only after the body's first `by`; `use` / `exists` additionally not
after `(` / `{` / a `fun` arrow / a `|` outside `first` (term notation `exists x, p`), and not when an argument continues on the next line.
Algorithm (per proof): the sites of every selected operator in priority order (the order above) then position; a stored best is first
re-measured on the primary toolchain (one compile: the stored H can be stale or lucky) and the gain is judged against max(stored, fresh).
Per operator one all-at-once compile when it has >= 2 free sites and the budget allows (hb_polish's cert pattern); on success a
leave-one-out pass drops every site whose removal does not lower the score (skipped for rw2rewrite, whose sites can only remove work);
else greedy site by site, each candidate compiled on the primary toolchain (normalize.evaluate, injectable); a site is kept only when the
provisional score rises by more than --min-gain (default 0.05: an unchanged proof re-measures up to +-0.03, docs/lr_skill_eval.md).
--max-compiles bounds the evaluations (one is reserved for the final check) and --deadline-s stops starting new candidates and the pin
fallback. The final proof must compile on every listed toolchain with Z unchanged and score more than --min-gain above max(stored, fresh)
(one fallback round drops one operator's sites at a time when a pin broke); else the report says 'no gain' and the input proof is kept.
    python3 harness/hb_rewrite.py --problem NAME --file proof.lean [--out O] [--ops op1,op2] [--min-gain G]     one proof; JSON report
    python3 harness/hb_rewrite.py --work-root R --run-id ID [--problems ...] [--deadline-s S] [--max-compiles N] [--ops ...] [--kind K]
        every stored best of a line, strictly better results banked through harness/inrun.locked_check (provenance hb-rewrite@cpu, kind
        closed-dev-only by default, api-dev-only for an open / API line) exactly as hb_polish does; stdout carries counts only, rows as
        row#k (no problem names; errors by exception class only)."""
from __future__ import annotations

import argparse, json, re, sys, time
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs, apply, OPEN, CLOSE  # noqa: E402
from harness.hb_polish import prov, _pick  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

OPS = ("repeatrw", "rw2rewrite", "simponly2dsimp", "simprw2only", "withreducible", "exists2refine", "use2refine")   # priority order
MONOTONE = ("rw2rewrite",)   # a site can only remove work (the try-rfl): no leave-one-out after an all-at-once success
MAX_COMPILES = 24
MIN_GAIN = 0.05   # noise margin: an unchanged proof re-measures up to +-0.03 in score (docs/lr_skill_eval.md)
EPS = 1e-9
KINDS = ("closed-dev-only", "api-dev-only")
RUN_ID_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*")

# the token before a tactic that puts it in tactic position
TAC_PREV_SYMS = {"\n", "<;>", "<|>", "=>", "·", ";", "|", "(", "{", "focus."}
TAC_PREV_WORDS = {"by", "all_goals", "any_goals", "try", "repeat", "repeat'", "iterate", "focus", "with_reducible",
                  "with_reducible_and_instances", "with_unfolding_all", "then", "else", "classical"}
LOC_RE = re.compile(r"[ \t]+at(?:[ \t]+(?:⊢|\*|[^\s;()<|\[\]⟨⟩{},]+))+")
CFG_RE = re.compile(r"\(\s*[A-Za-z_]+\s*:=")


def _word_re(w: str) -> re.Pattern:
    return re.compile(r"(?<![\w.'?!])" + w + r"(?![\w'?!])")


RW_RE, SIMPRW_RE, REPEAT_RE, FIRST_RE = _word_re("rw"), _word_re("simp_rw"), _word_re("repeat"), _word_re("first")
CONV_RE = re.compile(r"(?<![\w.'?!])conv(?:_lhs|_rhs)?(?![\w'?!])")
SIMPONLY_RE = re.compile(r"(?<![\w.'?!])simp[ \t]+only(?![\w'?!])")
USE_RE = re.compile(r"(?<![\w.'?!])(use|exists)(?![\w'?!])")
BY_RE = _word_re("by")
BY_END_RE = re.compile(r"(?<![\w.'?!])by$")
FUN_RE = re.compile(r"(?<![\w.'?!])(?:fun|λ)(?![\w'?!])|λ")
ARROW_HDR_RE = re.compile(r"(?:^|[\s·.;(])(?:case'?|next|on_goal)(?![\w'?!])|(?:^|\s)\|(?=\s)")
OPEN_TAIL_RE = re.compile(r"(?:(?<![\w.'?!])(?:by|fun)|=>|λ)\s*$")


@dataclass
class Site:
    op: str
    edits: tuple    # ((pos, delete_len, insert_text), ...) on the ORIGINAL body (normalize.apply)
    span: tuple     # (start, end) of the tactic call it rewrites: sites with overlapping spans conflict (variants of one call share it)
    note: str
    variant: int = 0
    dtok: int = 0   # arena-token delta of this site alone
    late: bool = False   # tried after every other site, never in an all-at-once group


# ---- layout helpers ---------------------------------------------------------------------------------------------------------------------
def _ls(body: str, i: int) -> int:
    return body.rfind("\n", 0, i) + 1


def _col(body: str, i: int) -> int:
    return i - _ls(body, i)


def _indent_at(body: str, ls: int) -> int:
    k = ls
    while k < len(body) and body[k] in " \t":
        k += 1
    return k - ls


def _skip_ws(body: str, k: int, newlines: bool = True) -> int:
    while k < len(body) and (body[k] in " \t" or (newlines and body[k] == "\n")):
        k += 1
    return k


def _line_end(body: str, k: int) -> int:
    j = body.find("\n", k)
    return len(body) if j < 0 else j


def _code(body: str, mask: list, a: int, b: int) -> str:
    """The unmasked text of body[a:b] (comments and strings dropped)."""
    return "".join(ch for p, ch in enumerate(body[a:b], a) if not mask[p])


def _rest(body: str, mask: list, k: int) -> str:
    """The code (comments and their text dropped) on the rest of the line from k."""
    return "".join(ch for p, ch in enumerate(body[k:_line_end(body, k)], k) if not mask[p] or ch == '"').strip()


def _next_code_line(body: str, mask: list, k: int):
    """(line start, indent) of the first line after position k's line holding unmasked code; None at the end of the body."""
    ls = _line_end(body, k) + 1
    while ls < len(body):
        le = _line_end(body, ls)
        if any(not body[p].isspace() and not mask[p] for p in range(ls, le)):
            return ls, _indent_at(body, ls)
        ls = le + 1
    return None


def _parent_line(body: str, mask: list, ls: int):
    """Start of the nearest earlier line holding code that is less indented than the line at ls; None when there is none."""
    ind = _indent_at(body, ls); e = ls - 1
    while e >= 0:
        q = body.rfind("\n", 0, e) + 1
        if _code(body, mask, q, e).strip() and _indent_at(body, q) < ind:
            return q
        e = q - 1
    return None


def _prev_token(body: str, mask: list, i: int) -> str:
    j = i - 1
    while j >= 0 and (body[j] in " \t" or (mask[j] and body[j] != "\n")):
        j -= 1
    if j < 0 or body[j] == "\n":
        return "\n"
    ch = body[j]
    if ch.isalnum() or ch in "_'!?":
        k = j
        while k >= 0 and (body[k].isalnum() or body[k] in "_.'!?"):
            k -= 1
        w = body[k + 1:j + 1]
        if w.isdigit():   # `iterate 3 rw [h]`
            return "iterate" if _prev_token(body, mask, k + 1) == "iterate" else w
        return w
    for sym in ("<;>", "<|>", "=>"):
        if body.startswith(sym, j + 1 - len(sym)):
            return sym
    if ch == "|":
        if j > 0 and body[j - 1] == "<":
            return "<|"   # the pipe operator, a term position
        return "||" if j > 0 and body[j - 1] == "|" else "|"
    if ch == ".":
        return "focus." if j == 0 or body[j - 1] in " \t\n" else "."
    return ch


def _tac_pos(body: str, mask: list, i: int, first_by: int) -> bool:
    if mask[i] or first_by < 0 or i <= first_by:
        return False
    p = _prev_token(body, mask, i)
    return p in TAC_PREV_SYMS or p in TAC_PREV_WORDS


def _first_by(body: str, mask: list) -> int:
    for m in BY_RE.finditer(body):
        if not mask[m.start()]:
            return m.start()
    return -1


def _call_rules(body: str, pairs: dict, k: int, allow_cfg: bool = True):
    """From k (after a head): (config span or None, '[' index, index after its ']') or None."""
    k = _skip_ws(body, k); cfg = None
    if allow_cfg and k < len(body) and body[k] == "(" and k in pairs and CFG_RE.match(body, k):
        cfg = (k, pairs[k] + 1); k = _skip_ws(body, pairs[k] + 1)
    if k >= len(body) or body[k] != "[" or k not in pairs:
        return None
    return cfg, k, pairs[k] + 1


def _loc_end(body: str, mask: list, k: int) -> int:
    """End of an `at l ..` clause starting at k (k itself when there is none); never runs into a comment."""
    e = k
    while e < len(body) and not mask[e] and body[e] != "\n":
        e += 1
    m = LOC_RE.match(body, k, e)
    return m.end() if m else k


def _note(body: str, a: int, b: int) -> str:
    return re.sub(r"\s+", " ", body[a:b])[:48]


def _split_args(body: str, mask: list, pairs: dict, a: int, b: int) -> list[str]:
    """The depth-0 comma-separated pieces of body[a:b], each verbatim (stripped): commas in strings, comments and brackets do not split."""
    out, s, p = [], a, a
    while p < b:
        if mask[p]:
            p += 1; continue
        ch = body[p]
        if ch in OPEN and p in pairs:
            p = pairs[p] + 1; continue
        if ch == ",":
            out.append(body[s:p].strip()); s = p + 1
        p += 1
    out.append(body[s:b].strip())
    return out


def _top_seq(body: str, mask: list, pairs: dict, a: int, b: int) -> bool:
    """Does body[a:b] hold a depth-0 `;` (also `<;>`), i.e. more than one tactic?"""
    p = a
    while p < b:
        if mask[p]:
            p += 1; continue
        if body[p] in OPEN and p in pairs:
            p = pairs[p] + 1; continue
        if body[p] == ";":
            return True
        p += 1
    return False


def _args_end(body: str, mask: list, pairs: dict, k: int):
    """End of a comma-separated term list starting at k (the arguments of use / exists): the line end unless the line ends with `,`;
    stops at `<;>`, `<|>`, `;`, `|`, an unmatched closer or a comment. None when a bracket is unbalanced."""
    n, start = len(body), k
    while k < n:
        if mask[k]:
            if body[k] == '"':
                while k < n and mask[k]:
                    k += 1
                continue
            break
        ch = body[k]
        if ch in OPEN:
            if k not in pairs:
                return None
            k = pairs[k] + 1; continue
        if ch in CLOSE or ch == ";" or body.startswith("<;>", k) or body.startswith("<|>", k):
            break
        if ch == "|" and not (k > 0 and body[k - 1] in "<|") and not body.startswith("|>", k) and not body.startswith("||", k):
            break   # an alternative bar ends the tactic; `<|`, `|>.`, `||` are term operators
        if ch == "\n":
            if body[start:k].rstrip().endswith(","):
                k += 1; continue
            break
        k += 1
    while k > start and body[k - 1] in " \t\n":
        k -= 1
    return k


def _block_col(body: str, mask: list, i: int) -> int:
    """The column of the tactic block holding the tactic at i: the line's indent when only comments precede it on its line."""
    ls = _ls(body, i)
    return _indent_at(body, ls) if not _code(body, mask, ls, i).strip() else i - ls


def _is_final(body: str, mask: list, i: int, end: int) -> bool:
    """Is the tactic at [i, end) the last one of its block (nothing after it on the line but closers; next code line less indented)?"""
    r = _rest(body, mask, end)
    if r:
        return all(c in ")]}⟩ " for c in r)
    nx = _next_code_line(body, mask, end)
    return nx is None or nx[1] < _block_col(body, mask, i)


def _block_must_close(body: str, mask: list, i: int) -> bool:
    """Must the tactic block holding the tactic at i close its goals? True for a `by` block, a `·` bullet and a `=>` alternative / case;
    False for combinator blocks (all_goals, any_goals, try, repeat, iterate, focus, `<;>`, `;`, first alternatives) and when unsure."""
    ls = _ls(body, i)
    if _code(body, mask, ls, i).strip():
        return _prev_token(body, mask, i) in ("by", "·", "focus.", "=>")
    q = _parent_line(body, mask, ls)
    if q is None:
        return False
    pc = _code(body, mask, q, _line_end(body, q)).rstrip()
    if BY_END_RE.search(pc) or pc.endswith("=>"):
        return True
    st = q + _indent_at(body, q)
    if body[st] == "·" or (body[st] == "." and body[st + 1:st + 2] in (" ", "\t")):
        return _skip_ws(body, st + 1, newlines=False) - q == _indent_at(body, ls)   # the bullet's own block
    return False


def _conv_arrow(body: str, mask: list, a: int, b: int):
    """Column (from a) of the `=>` of a conv header in body[a:b], or None."""
    for m in CONV_RE.finditer(body, a, b):
        if mask[m.start()]:
            continue
        j = body.find("=>", m.end(), b)
        while j >= 0 and mask[j]:
            j = body.find("=>", j + 2, b)
        if j >= 0:
            return j - a
    return None


def _in_conv(body: str, mask: list, i: int) -> bool:
    """Is the tactic at i inside a conv block (`conv ... => tac` on its line, or under a conv header line)?"""
    ls = _ls(body, i)
    if _conv_arrow(body, mask, ls, i) is not None:
        return True
    ind, q = _indent_at(body, ls), _parent_line(body, mask, ls)
    while q is not None:
        le = _line_end(body, q); pc = _code(body, mask, q, le).rstrip(); col = _conv_arrow(body, mask, q, le)
        if col is not None and (pc.endswith("=>") or ind > col):
            return True
        if BY_END_RE.search(pc):
            return False
        ind, q = _indent_at(body, q), _parent_line(body, mask, q)
    return False


def _tactic_arrow(body: str, mask: list, i: int) -> bool:
    """Is the `=>` just before i the arrow of a tactic alternative (case / next / on_goal / `| pat =>`), not of a `fun`?"""
    pre = _code(body, mask, _ls(body, i), i)
    head = pre[:pre.rfind("=>")]
    return not FUN_RE.search(head) and bool(ARROW_HDR_RE.search(head))


def _in_first(body: str, mask: list, i: int) -> bool:
    """Is the `|` just before i an alternative bar of `first` (on this line, or a bar line under a `first` line)?"""
    ls = _ls(body, i); pre = _code(body, mask, ls, i)
    if FIRST_RE.search(pre):
        return True
    if pre.strip() != "|":
        return False
    e = ls - 1
    while e >= 0:   # the bar lines above, then the line that opened them
        q = body.rfind("\n", 0, e) + 1; c = _code(body, mask, q, e).strip()
        if c and not c.startswith("|"):
            return bool(FIRST_RE.search(c))
        e = q - 1
    return False


# ---- sites ------------------------------------------------------------------------------------------------------------------------------
def _repeatrw(body, mask, pairs, fb):
    out = []
    for m in REPEAT_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):
            continue
        k = _skip_ws(body, m.end(), newlines=False); close = None; block = False
        if k < len(body) and body[k] == "(" and k in pairs:
            close = pairs[k]; r = _skip_ws(body, k + 1)
        elif k >= len(body) or body[k] == "\n" or mask[k]:
            nx = _next_code_line(body, mask, i)
            if nx is None or nx[1] <= _col(body, i):
                continue
            r = nx[0] + nx[1]; block = True
        else:
            r = k
        mr = RW_RE.match(body, r)
        if not mr:
            continue
        got = _call_rules(body, pairs, mr.end(), allow_cfg=False)
        if not got:
            continue
        _cfg, lb, rb = got; end = _loc_end(body, mask, rb)
        if close is not None:
            if body[end:close].strip():
                continue
            span_end = close + 1
            if _rest(body, mask, span_end):
                continue
        else:
            if _rest(body, mask, end):
                continue
            span_end = end
            nx2 = _next_code_line(body, mask, end)
            if block and nx2 is not None and nx2[1] > _col(body, i):   # a second line in the repeat block
                continue
            if not block and nx2 is not None and nx2[1] >= _col(body, r):   # a further line of the repeat body, aligned with the rw
                continue
        repl = "simp only " + body[lb:rb] + body[rb:end]
        out.append(Site("repeatrw", ((i, span_end - i, repl),), (i, span_end), _note(body, i, span_end)))
    return out


def _rw2rewrite(body, mask, pairs, fb):
    out = []
    for m in RW_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):   # conv's rw is rewrite already (no rfl)
            continue
        got = _call_rules(body, pairs, m.end())
        if not got:
            continue
        end = _loc_end(body, mask, got[2]); late = False
        if _is_final(body, mask, i, end):
            if _block_must_close(body, mask, i):   # the last tactic of a closing block: its rfl closed the goal, rewrite cannot
                continue
            late = True
        out.append(Site("rw2rewrite", ((i, 2, "rewrite"),), (i, end), _note(body, i, end), late=late))
    return out


def _simponly2dsimp(body, mask, pairs, fb):
    out = []
    for m in SIMPONLY_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        k = _skip_ws(body, m.end(), newlines=False)
        end = pairs[k] + 1 if k < len(body) and body[k] == "[" and k in pairs else m.end()
        end = _loc_end(body, mask, end)
        out.append(Site("simponly2dsimp", ((i, 4, "dsimp"),), (i, end), _note(body, i, end)))
    return out


def _simprw2only(body, mask, pairs, fb):
    out = []
    for m in SIMPRW_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        got = _call_rules(body, pairs, m.end())
        if not got:
            continue
        cfg, _lb, rb = got; end = _loc_end(body, mask, rb)
        edits = ((i, 7, "simp"), (cfg[1], 0, " only")) if cfg else ((i, 7, "simp only"),)
        out.append(Site("simprw2only", edits, (i, end), _note(body, i, end)))
    return out


def _alt_end(body: str, mask: list, pairs: dict, a: int) -> int:
    """End of the `first` alternative starting at a: the next depth-0 `|` on the line, a closer, or the line end."""
    j, n = a, len(body)
    while j < n and body[j] != "\n":
        if mask[j] and body[j] != '"':
            j = _line_end(body, j) if body.startswith("--", j) else j + 1; continue
        if body[j] in OPEN and j in pairs:
            j = pairs[j] + 1; continue
        if body[j] in CLOSE or (body[j] == "|" and not body.startswith("||", j) and not body.startswith("|>", j)
                                and not body.startswith("<|", j - 1)):
            break
        j += 1
    return j


def _withreducible(body, mask, pairs, fb):
    out = []
    n = len(body)
    for m in FIRST_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        base_col = _indent_at(body, _ls(body, i)); k = m.end(); bar_col = None
        while True:
            k = _skip_ws(body, k, newlines=False)
            if k < n and (body[k] == "\n" or (mask[k] and body[k] != '"')):
                # bars on the following lines: the first at least at the `first` line's indent, later ones at the first bar's column or
                # right of it (first saves its position at the first `|` and checks later bars with colGe)
                nx = _next_code_line(body, mask, k)
                if nx is None or body[nx[0] + nx[1]] != "|" or nx[1] < (base_col if bar_col is None else bar_col):
                    break
                k = nx[0] + nx[1]
            if k >= n or body[k] != "|" or body.startswith("||", k) or body.startswith("|>", k):
                break
            if bar_col is None:
                bar_col = _col(body, k)
            a = _skip_ws(body, k + 1, newlines=False)
            j = _alt_end(body, mask, pairs, a)
            mw = re.match(r"(apply|exact)(?![\w'?!])", body[a:a + 8])
            if mw and not mask[a] and not _top_seq(body, mask, pairs, a, j):
                cont = False
                if j >= n or body[j] == "\n":   # the alternative runs to its line end: a deeper non-bar line continues it
                    nx = _next_code_line(body, mask, a)
                    cont = nx is not None and nx[1] > bar_col and body[nx[0] + nx[1]] != "|"
                if not cont:
                    out.append(Site("withreducible", ((a, 0, "with_reducible "),), (a, a + len(mw.group(1))), _note(body, a, _line_end(body, a))))
            if j < n and body[j] in CLOSE:
                break
            k = j
    return out


def _use_exists(body, mask, pairs, fb, want):
    out = []
    for m in USE_RE.finditer(body):
        head, i = m.group(1), m.start()
        if head not in want or not _tac_pos(body, mask, i, fb):
            continue
        if m.end() >= len(body) or body[m.end()] not in " \t":
            continue
        p = _prev_token(body, mask, i)
        if p in ("(", "{") or (p == "=>" and not _tactic_arrow(body, mask, i)) or (p == "|" and not _in_first(body, mask, i)):
            continue   # the term notation `exists x, p` (in a type, a fun body, a set-builder)
        k = _skip_ws(body, m.end(), newlines=False)
        if head == "use" and re.match(r"\(\s*disch", body[k:k + 12]):
            continue
        end = _args_end(body, mask, pairs, k)
        if end is None or end <= k:
            continue
        if OPEN_TAIL_RE.search(body[k:end]):
            continue   # the last argument goes on below (`by`, `fun`, `=>`)
        nxt = _skip_ws(body, end, newlines=False)
        if nxt < len(body) and body[nxt] in ")}" and p != "by":
            continue   # closed by a bracket: a term
        if not _rest(body, mask, end):
            nx = _next_code_line(body, mask, end)
            if nx is not None and nx[1] > _block_col(body, mask, i):
                continue   # an argument continued on the next line
        args = _split_args(body, mask, pairs, k, end)
        if not all(args):
            continue
        a = ", ".join(args); final = _is_final(body, mask, i, end); op = "use2refine" if head == "use" else "exists2refine"
        ref, ex_rfl = f"refine ⟨{a}, ?_⟩", f"exact ⟨{a}, rfl⟩"
        if head == "use":
            variants = [f"exact ⟨{a}⟩", ex_rfl, f"exists {a}", ref] if final else [ref, f"exists {a}", f"exact ⟨{a}⟩", ex_rfl]
        else:
            variants = [ex_rfl, ref] if final else [ref, ex_rfl]
        for v, rep in enumerate(variants):
            out.append(Site(op, ((i, end - i, rep),), (i, end), _note(body, i, end), variant=v))
    return out


def sites(body: str, ops=OPS) -> list[Site]:
    """Every site of the selected operators in the proof body, ordered by operator priority, position, variant; dtok filled in."""
    mask = _mask(body); pairs = _pairs(body, mask); fb = _first_by(body, mask); out: list[Site] = []
    for op in OPS:
        if op not in ops:
            continue
        if op == "repeatrw": got = _repeatrw(body, mask, pairs, fb)
        elif op == "rw2rewrite": got = _rw2rewrite(body, mask, pairs, fb)
        elif op == "simponly2dsimp": got = _simponly2dsimp(body, mask, pairs, fb)
        elif op == "simprw2only": got = _simprw2only(body, mask, pairs, fb)
        elif op == "withreducible": got = _withreducible(body, mask, pairs, fb)
        elif op == "exists2refine": got = _use_exists(body, mask, pairs, fb, ("exists",))
        else: got = _use_exists(body, mask, pairs, fb, ("use",))
        out += sorted(got, key=lambda s: (s.span[0], s.variant))
    t0 = count_tokens(body); seen = set(); uniq = []
    for s in out:
        if s.edits in seen:
            continue
        seen.add(s.edits); s.dtok = count_tokens(apply(body, [s])) - t0; uniq.append(s)
    return uniq


def conflicts(s: Site, kept: list[Site]) -> bool:
    a, b = s.span
    return any((a < k.span[1] and k.span[0] < b) or a == k.span[0] for k in kept)


# ---- the per-proof pass -----------------------------------------------------------------------------------------------------------------
def rewrite_proof(name: str, decl: str, *, base: dict | None = None, evaluate_fn=None, statement: str | None = None,
                  max_compiles: int = MAX_COMPILES, ops=OPS, deadline: float | None = None, clock=time.monotonic,
                  all_at_once: bool = True, min_gain: float = MIN_GAIN) -> dict:
    """The report of one proof: status (improved / no sites / no gain / input does not compile / input not fully scored / statement
    differs), before (the fresh measurement) / stored (a given base) / after, sites (calls) and candidates, applied counts per operator,
    kept sites, gain (against the fresh measurement), compiles, stopped (max-compiles / deadline), proof. evaluate_fn(decl, full) ->
    {ok, score, Z, prov | L+H, tokens, heartbeats}; full=True checks every listed toolchain. Every evaluate call counts as one compile.
    base: the stored best's numbers; then the input is re-measured on the primary toolchain (one compile, full=False) and its Z kept."""
    if evaluate_fn is None or statement is None:
        from harness.leantools import ROWS
        from harness.normalize import evaluate
        from probe.verify_candidates import newest_first
        row = ROWS[name]; versions = newest_first(row["version_info"])
        evaluate_fn = evaluate_fn or (lambda d, full: evaluate(name, d, versions, full))
        statement = statement or row["statement"]
    decl = decl.rstrip(); body = split_declaration(decl, statement)
    if body is None:
        return {"problem": name, "status": "statement differs", "compiles": 0}
    head = decl[:len(decl) - len(body)]; n = [0]

    def ev(d: str, full: bool) -> dict:
        n[0] += 1
        return evaluate_fn(d, full) or {}
    stored = base if (base and base.get("ok") and base.get("score") is not None and base.get("Z") is not None) else None
    ss = sites(body, ops)
    calls: dict = {}
    for s in ss:
        calls.setdefault(s.op, set()).add(s.span)
    res = {"problem": name, "sites": {op: len(v) for op, v in calls.items()}, "candidates": len(ss), "applied": {}, "compiles": 0,
           "stopped": None}
    if stored is not None:
        res["stored"] = _pick(stored)
    if not ss:
        res.update(status="no sites", before=_pick(stored) if stored else None, proof=decl); res["after"] = res["before"]; return res
    if stored is not None:   # re-measure: the stored H may be stale or a lucky draw of the heartbeat noise
        fresh = ev(decl, False); b0 = dict(fresh)
        if fresh.get("ok"):
            Z0 = float(stored["Z"]); b0.update(Z=Z0, score=round(prov(fresh) - (100.0 - Z0) / 3, 2))
            floor = max(float(stored["score"]), b0["score"])
    else:
        b0 = ev(decl, True)
    res["before"] = _pick(b0); res["compiles"] = n[0]
    if not b0.get("ok"):
        res.update(status="input does not compile", after=res["before"], proof=decl); return res
    if b0.get("score") is None or b0.get("Z") is None:
        res.update(status="input not fully scored", after=res["before"], proof=decl); return res
    if stored is None:
        Z0 = float(b0["Z"]); floor = float(b0["score"])
    kept: list[Site] = []; cur_p = prov(b0); cache: dict = {}

    def trial(chosen: list[Site]) -> dict:
        cand = head + apply(body, chosen)
        if cand not in cache:
            cache[cand] = ev(cand, False)
        return cache[cand]

    def stop_reason():
        if n[0] >= max_compiles - 1:
            return "max-compiles"
        if deadline is not None and clock() >= deadline:
            return "deadline"
        return None
    groups = [(op, [s for s in ss if s.op == op and not s.late], True) for op in OPS] + [("late", [s for s in ss if s.late], False)]
    for op, group, aao in groups:
        if not group or res["stopped"]:
            continue
        done: set = set()
        free: list[Site] = []
        for s in group:
            if not conflicts(s, kept) and not conflicts(s, free):
                free.append(s)
        if aao and all_at_once and len(free) >= 2 and n[0] + len(free) + 1 < max_compiles - 1 and stop_reason() is None:
            e = trial(kept + free)
            if e.get("ok") and prov(e) > cur_p + min_gain:
                kept += free; cur_p = prov(e); done |= {id(s) for s in free}
                if op not in MONOTONE:   # leave-one-out: a site that does not pay on its own is dropped
                    for s in free:
                        why = stop_reason()
                        if why:
                            res["stopped"] = why; break
                        e2 = trial([x for x in kept if x is not s])
                        if e2.get("ok") and prov(e2) >= cur_p - EPS:
                            kept = [x for x in kept if x is not s]; cur_p = prov(e2)
        for s in group:
            if res["stopped"]:
                break
            if id(s) in done or conflicts(s, kept):
                continue
            why = stop_reason()
            if why:
                res["stopped"] = why; break
            e = trial(kept + [s])
            if e.get("ok") and prov(e) > cur_p + min_gain:
                kept.append(s); cur_p = prov(e)
    res["compiles"] = n[0]
    if not kept:
        res.update(status="no gain", reason="no site raised the score", after=res["before"], proof=decl); return res

    def z_of(e: dict):
        return None if e.get("Z") is None else float(e["Z"])

    def full_ok(e: dict) -> bool:
        return (bool(e.get("ok")) and z_of(e) is not None and z_of(e) >= Z0 - EPS and e.get("score") is not None
                and float(e["score"]) > floor + min_gain)
    fin = ev(head + apply(body, kept), True)
    if fin.get("ok") and z_of(fin) is not None and z_of(fin) < Z0 - EPS:   # a pin broke: drop one operator's sites at a time
        for op in [o for o in OPS if any(s.op == o for s in kept)]:
            if n[0] >= max_compiles or (deadline is not None and clock() >= deadline):
                res["stopped"] = res["stopped"] or ("max-compiles" if n[0] >= max_compiles else "deadline"); break
            trial_k = [s for s in kept if s.op != op]
            if not trial_k:
                continue
            e = ev(head + apply(body, trial_k), True)
            if full_ok(e):
                kept, fin = trial_k, e; break
    res["compiles"] = n[0]
    if not full_ok(fin):
        why = ("final check does not compile" if not fin.get("ok") else "final check reported no Z" if z_of(fin) is None else
               "pins broke" if z_of(fin) < Z0 - EPS else "not strictly better on the full check")
        res.update(status="no gain", reason=why, after=res["before"], tried=_pick(fin), proof=decl); return res
    for s in kept:
        res["applied"][s.op] = res["applied"].get(s.op, 0) + 1
    res.update(status="improved", after=_pick(fin), gain=round(float(fin["score"]) - float(b0["score"]), 2), proof=head + apply(body, kept),
               kept=[{"op": s.op, "note": s.note, "dtok": s.dtok} for s in kept])
    if stored is not None:
        res["gain_vs_stored"] = round(float(fin["score"]) - float(stored["score"]), 2)
    return res


# ---- the line post-pass -----------------------------------------------------------------------------------------------------------------
def valid_run_id(run_id) -> bool:
    return isinstance(run_id, str) and bool(RUN_ID_RE.fullmatch(run_id)) and ".." not in run_id


def _bank(w: Path, name: str, proof: str, run_id: str, kind: str = "closed-dev-only", lock_wait: float = 1700.0) -> dict:
    from harness.inrun import locked_check
    return locked_check(w, name, proof, {"kind": kind, "model": "hb-rewrite@cpu", "run_id": run_id, "mode": "hb-rewrite"},
                        ROOT / "probe/runs" / run_id / "verified.jsonl", lock_wait=lock_wait)


def _stored_score(st: Path, fallback) -> float:
    try:
        return float(json.loads(st.read_text())["best"]["score"])
    except Exception:  # noqa: BLE001
        return float(fallback or 0)


def rewrite_work_root(work_root: Path, run_id: str, problems=None, deadline_s: float = 3000.0, max_compiles: int = MAX_COMPILES, ops=OPS,
                      rewrite_fn=None, check_fn=None, clock=time.monotonic, kind: str = "closed-dev-only", min_gain: float = MIN_GAIN) -> dict:
    """Every stored best of a line rewritten; a strictly better proof is banked through the normal check path as run `run_id`. Stops
    starting new problems (and new candidates inside one) after deadline_s; the bank's lock wait is bounded by the time left (>= 60 s).
    Counts only: rows are numbered, never named; a failing row is recorded by its exception class and the pass goes on."""
    if not valid_run_id(run_id):
        raise ValueError("run id: letters, digits, '.', '_', '-' only, no '..'")
    if kind not in KINDS:
        raise ValueError(f"kind must be one of {KINDS}")
    from harness.leantools import ROWS
    t0 = clock(); dl = t0 + deadline_s
    rewrite_fn = rewrite_fn or rewrite_proof
    check_fn = check_fn or (lambda w, name, proof: _bank(w, name, proof, run_id, kind=kind, lock_wait=max(60.0, dl - clock())))
    c = {"problems": 0, "improved": 0, "banked": 0, "gain": 0.0, "compiles": 0, "skipped_deadline": 0, "errors": 0, "bank_errors": 0,
         "rows": []}
    k = 0
    for st in sorted(Path(work_root).glob("*/state.json")):
        try:
            s = json.loads(st.read_text())
        except (OSError, ValueError):
            continue
        name = s.get("problem"); b = s.get("best") or {}
        if (problems and name not in problems) or not b.get("proof") or name not in ROWS:
            continue
        k += 1
        if clock() >= dl:
            c["skipped_deadline"] += 1; c["rows"].append({"row": k, "status": "skipped (deadline)"}); continue
        base = ({"ok": True, "score": b["score"], "Z": b["Z"], "L": b.get("L"), "H": b.get("H"), "tokens": b.get("tokens"), "heartbeats": b.get("heartbeats")}
                if b.get("Z") is not None and b.get("score") is not None else None)
        try:
            r = rewrite_fn(name, b["proof"], base=base, max_compiles=max_compiles, ops=ops, deadline=dl, min_gain=min_gain)
        except Exception as ex:  # noqa: BLE001  (one problem's failure never stops the pass; the class name only, never the message)
            c["errors"] += 1; c["rows"].append({"row": k, "status": f"error {type(ex).__name__}"}); continue
        c["problems"] += 1; c["compiles"] += r.get("compiles") or 0
        row = {"row": k, "status": r.get("status"), "compiles": r.get("compiles"), "applied": r.get("applied") or {}, "banked": False}
        if r.get("status") == "improved":
            c["improved"] += 1
            prev = _stored_score(st, b.get("score"))   # re-read now: a live line may have moved its best during the pass
            try:
                chk = check_fn(st.parent, name, r["proof"]) or {}
            except Exception as ex:  # noqa: BLE001  (a lock timeout or a write error: recorded by class, the pass goes on)
                c["bank_errors"] += 1; row["status"] = f"bank error {type(ex).__name__}"; c["rows"].append(row); continue
            if chk.get("new_best"):
                g = float(chk.get("score") or 0) - prev
                c["banked"] += 1; c["gain"] += g; row.update(banked=True, gain=round(g, 2))
        c["rows"].append(row)
    c["gain"] = round(c["gain"], 2)
    return c


def _ops_arg(s: str | None) -> tuple:
    if not s:
        return OPS
    got = tuple(o.strip() for o in s.split(",") if o.strip())
    bad = [o for o in got if o not in OPS]
    if bad:
        raise SystemExit(f"unknown operator(s) {bad}; known: {','.join(OPS)}")
    return got


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem"); ap.add_argument("--file"); ap.add_argument("--out")
    ap.add_argument("--work-root", help="a line's work root (relative to the checkout, or absolute): rewrite every stored best")
    ap.add_argument("--run-id", help="with --work-root: the run id its banked records go under")
    ap.add_argument("--problems", nargs="*", default=None); ap.add_argument("--deadline-s", type=float, default=3000.0)
    ap.add_argument("--max-compiles", type=int, default=MAX_COMPILES)
    ap.add_argument("--min-gain", type=float, default=MIN_GAIN, help="the score rise a site and the final proof must exceed (noise margin)")
    ap.add_argument("--kind", choices=KINDS, default="closed-dev-only",
                    help="provenance kind of banked records: closed-dev-only (never imported into the bank) or api-dev-only (an open / API line)")
    ap.add_argument("--ops", default=None, help=f"comma-separated subset of {','.join(OPS)}")
    a = ap.parse_args(argv)
    ops = _ops_arg(a.ops)
    if a.problem and a.file:
        r = rewrite_proof(a.problem, Path(a.file).read_text(), max_compiles=a.max_compiles, ops=ops, deadline=time.monotonic() + a.deadline_s,
                          min_gain=a.min_gain)
        print(json.dumps({k: v for k, v in r.items() if k != "proof"}, indent=1, ensure_ascii=False))
        if a.out and r.get("status") == "improved":
            Path(a.out).write_text(r["proof"].rstrip() + "\n")
        return 0
    if not (a.work_root and a.run_id):
        ap.error("--problem with --file, or --work-root with --run-id")
    if not valid_run_id(a.run_id):
        ap.error("--run-id: letters, digits, '.', '_', '-' only, no '..'")
    c = rewrite_work_root(ROOT / a.work_root, a.run_id, set(a.problems) if a.problems else None, a.deadline_s, a.max_compiles, ops,
                          kind=a.kind, min_gain=a.min_gain)
    for r in c["rows"]:
        ap_s = ",".join(f"{k}:{v}" for k, v in sorted((r.get("applied") or {}).items()))
        print(f"row#{r['row']} {r['status']}" + (f" compiles {r['compiles']}" if r.get("compiles") is not None else "")
              + (f" applied {ap_s}" if ap_s else "") + (f" banked {r['gain']:+.2f}" if r.get("banked") else ""))
    print(f"hb_rewrite: {c['problems']} stored best(s) rewritten, {c['improved']} strictly better, {c['banked']} banked as new bests "
          f"(summed gain {c['gain']:+.2f}), {c['compiles']} compiles, {c['skipped_deadline']} left for the deadline, {c['errors']} errors, "
          f"{c['bank_errors']} bank errors; run {a.run_id}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
