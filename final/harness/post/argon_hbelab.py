#!/usr/bin/env python3
"""Gap-lane op `argon_hbelab`: heartbeat & elaboration optimizer for the open post-step.

Addresses the open-to-closed H (heartbeat) gap (115.25 row-points across the 60-row
benchmark; 75.59 row-points on the 30 GB10-measurable rows) and secondary L savings
from elaboration-simplifying rewrites that were disabled or unreached in the open track:

  1. rw2rewrite / nthrw   `rw [...]` -> `rewrite [...]` and `nth_rw` -> `nth_rewrite`
                          in non-closing tactic positions outside `conv` (skips the
                          implicit `with_reducible rfl` attempt after every rewrite).
  2. simponly2dsimp       `simp only [...]` (without reverse arrows `←`) -> `dsimp only [...]`
                          (definitional reduction in the kernel/elaborator without full simp
                          congruence, lemma matching, or discharger traversal).
  3. dsimp_unfold         `unfold f ... (at loc)` -> `dsimp only [f, ...] (at loc)`.
  4. simp_target          `simp/dsimp ... at *` -> drop `at *` (-2 tokens and avoids
                          re-simplifying every local hypothesis when only the goal matters).
  5. simp_once            `simp_all only [...]` -> `simp only [*, ...]`, `simp_all [...]` ->
                          `simp [*, ...]`, and `simp_all` -> `simp at *` (avoids fixed-point
                          cross-hypothesis simp loops).
  6. set_let / set_have   `set x ... := v` (without `with h`) -> `let x ... := v` or
                          `have x ... := v` (0 tokens; skips `set`'s `kabstract` replacement
                          pass over the goal and all local hypotheses).
  7. let_have             `let x ... := v` (non-recursive) -> `have x ... := v` (0 tokens;
                          prevents expensive `zeta`/`zetaDelta` unfolding of local terms).
  8. ext_funext           `ext x ...` (simple identifier binders) -> `funext x ...` (0 tokens;
                          skips `@[ext]` theorem search).
  9. congr_arg / nofun    `congrArg (fun x => ...) h` -> `congr_arg _ h` and
                          `fun x => False.elim ...` -> `nofun` (saves tokens and elaboration).
 10. simp_config          Core Lean `Simp.Config` flags (`+singlePass`, `-dsimp`, `-proj`,
                          `+zetaDelta`, `+contextual`, `-iota`, `-zeta`) on `simp`, `simpa`,
                          `simp_all`, `dsimp` calls.
 11. grind_config         Core Lean `Grind.Config` flags (`-linarith`, "-ring", "-ac",
                          "-order", "-abstractProof", "-funext", "-etaStruct", "-splitIte",
                          "-splitMatch") on `grind` calls.
 12. preorder             Pre-order `↓` modifier on quantifier/sum/eval/map lemmas in `simp`
                          lists (top-down rewrite before binder descent).

All candidates are pre-screened via `query()` in 1-2 single-file compiles on the primary pin:
  - Mode 1 (CommandElabM `#eval` heartbeat measurement): measures exact heartbeats of up to
    15 variants per file under `withoutModifyingEnv`, keeping only variants predicted to
    raise the row's score (`predicted > 0` at the row's token/heartbeat exchange rate), and
    synthesizes a greedy non-overlapping combination (`argon_hbelab:combo`) of the winners.
  - Mode 2 (Multi-theorem plain compile fallback for `module` files where `CommandElabM` is
    not imported, e.g. Strata): compiles up to 24 variants in one plain file with `#check`
    line markers, filtering out all non-compiling variants and combining verified zero/negative
    token edits into `argon_hbelab:combo_0tok`.

Model-free, deterministic, $0, self-contained (no external tables, no row names or proof text).
"""
from __future__ import annotations

# provenance: research lane gaplane-argon (worktree lra-gl-argon), commit d7dee71, ported unchanged into open-post-v3 (2026-11-04)

from dataclasses import dataclass
import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scorer.tokenize import count_tokens, split_declaration  # noqa: E402


def _full_decl(statement: str, body: str) -> str:
    sep = "" if body.startswith(("\n", " ", "\t")) else "\n  "
    return f"{statement.rstrip()} :={sep}{body.rstrip()}\n"


def _proof_key(proof: str) -> str:
    return hashlib.sha256((proof or "").rstrip().encode()).hexdigest()[:16]


def _lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t") + '"'


def _msg_text(m: dict) -> str:
    return str(m.get("data") or "")

FAMILY = "argon_hbelab"
MAX_SCREEN_FILES = 2
MAX_VARIANTS_PER_FILE = 16
MAX_PLAIN_VARIANTS = 24
MEASURE_S = 210.0
DEFAULT_VARIANT_S = 12.0

IDENT = r"[^\W\d][\w'!?₀-₉]*"
OPEN_TO_CLOSE = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}
CLOSE_CHARS = frozenset(")]}⟩")

TAC_PREV_WORDS = frozenset({
    "by", "try", "repeat", "all_goals", "any_goals", "focus", "first", "on_goal",
})
TAC_PREV_SYMS = frozenset({"\n", ";", "<;>", "<|>", "=>", "·", "|"})

# Core Lean 4 Simp.Config and Grind.Config boolean option toggles (syntax-only, core Lean 4)
SIMP_FLAGS: dict[str, tuple[tuple[str, str], ...]] = {
    "simp": (
        ("+singlePass", "single-pass simp"),
        ("-dsimp", "disable dsimp pass in simp"),
        ("-proj", "disable projection reduction in simp"),
        ("+zetaDelta", "unfold local let-bindings in simp"),
        ("+contextual", "enable contextual simplification"),
        ("-iota", "disable iota reduction in simp"),
        ("-zeta", "disable zeta reduction in simp"),
    ),
    "simpa": (
        ("+singlePass", "single-pass simpa"),
        ("-dsimp", "disable dsimp pass in simpa"),
        ("-proj", "disable projection reduction in simpa"),
        ("+zetaDelta", "unfold local let-bindings in simpa"),
        ("+contextual", "enable contextual simpa"),
    ),
    "simp_all": (
        ("+singlePass", "single-pass simp_all"),
        ("-dsimp", "disable dsimp pass in simp_all"),
        ("-proj", "disable projection reduction in simp_all"),
        ("+zetaDelta", "unfold local let-bindings in simp_all"),
        ("-contextual", "disable contextual pass in simp_all"),
    ),
    "dsimp": (
        ("-proj", "disable projection reduction in dsimp"),
        ("+zetaDelta", "unfold local let-bindings in dsimp"),
        ("-zeta", "disable zeta reduction in dsimp"),
        ("-iota", "disable iota reduction in dsimp"),
        ("-beta", "disable beta reduction in dsimp"),
    ),
}

GRIND_FLAGS: tuple[tuple[str, str], ...] = (
    ("-linarith", "disable linarith solver in grind"),
    ("-ring", "disable ring solver in grind"),
    ("-ac", "disable AC solver in grind"),
    ("-order", "disable order solver in grind"),
    ("-abstractProof", "disable proof abstraction in grind"),
    ("-funext", "disable funext in grind"),
    ("-etaStruct", "disable etaStruct in grind"),
    ("-splitIte", "disable if-then-else splitting in grind"),
    ("-splitMatch", "disable match splitting in grind"),
)


@dataclass(frozen=True)
class EditCand:
    op: str
    edits: tuple[tuple[int, int, str], ...]
    body: str
    decl: str
    note: str
    dtok: int
    prio: int


# ---------------------------------------------------------------------------
# Lexical masking & bracket pairing (pure, self-contained)
# ---------------------------------------------------------------------------
def _mask(s: str) -> list[bool]:
    n = len(s)
    m = [False] * n
    i = 0
    depth = 0
    in_line = False
    in_str = False
    while i < n:
        c = s[i]
        nxt = s[i + 1] if i + 1 < n else ""
        if in_line:
            if c == "\n":
                in_line = False
            else:
                m[i] = True
            i += 1
        elif depth > 0:
            m[i] = True
            if c == "/" and nxt == "-":
                m[i + 1] = True
                depth += 1
                i += 2
            elif c == "-" and nxt == "/":
                m[i + 1] = True
                depth -= 1
                i += 2
            else:
                i += 1
        elif in_str:
            m[i] = True
            if c == "\\" and i + 1 < n:
                m[i + 1] = True
                i += 2
            elif c == '"':
                in_str = False
                i += 1
            else:
                i += 1
        else:
            if c == "-" and nxt == "-":
                in_line = True
                m[i] = True
                m[i + 1] = True
                i += 2
            elif c == "/" and nxt == "-":
                depth = 1
                m[i] = True
                m[i + 1] = True
                i += 2
            elif c == '"':
                in_str = True
                m[i] = True
                i += 1
            else:
                i += 1
    return m


def _pairs(s: str, mask: list[bool]) -> dict[int, int]:
    stack: list[tuple[str, int]] = []
    out: dict[int, int] = {}
    for i, c in enumerate(s):
        if mask[i]:
            continue
        if c in OPEN_TO_CLOSE:
            stack.append((OPEN_TO_CLOSE[c], i))
        elif c in CLOSE_CHARS:
            if stack and stack[-1][0] == c:
                _, o = stack.pop()
                out[o] = i
            else:
                stack.clear()
    return out


def _line_start(s: str, i: int) -> int:
    return s.rfind("\n", 0, i) + 1


def _line_end(s: str, i: int) -> int:
    j = s.find("\n", i)
    return len(s) if j < 0 else j


def _indent_at(s: str, ls: int) -> int:
    j = ls
    while j < len(s) and s[j] in (" ", "\t"):
        j += 1
    return j - ls


def _code(s: str, mask: list[bool], a: int, b: int) -> str:
    return "".join(" " if mask[k] and s[k] != "\n" else s[k] for k in range(a, b))


def _skip_ws(s: str, i: int, *, newlines: bool = True) -> int:
    ws = (" ", "\t", "\n") if newlines else (" ", "\t")
    while i < len(s) and s[i] in ws:
        i += 1
    return i


def _first_by(body: str, mask: list[bool]) -> int:
    for m in re.finditer(r"(?<![\w.'?!])by(?![\w'?!])", body):
        if not mask[m.start()]:
            return m.start()
    return -1


def _prev_token(body: str, mask: list[bool], i: int) -> str:
    j = i - 1
    while j >= 0 and (body[j] in (" ", "\t") or (mask[j] and body[j] != "\n")):
        j -= 1
    if j < 0 or body[j] == "\n":
        return "\n"
    for sym in ("<;>", "<|>", "=>"):
        if body.startswith(sym, j + 1 - len(sym)):
            return sym
    ch = body[j]
    if ch.isalnum() or ch in "_'!?₀₁₂₃₄₅₆₇₈₉":
        k = j
        while k >= 0 and (body[k].isalnum() or body[k] in "_.'!?₀₁₂₃₄₅₆₇₈₉"):
            k -= 1
        return body[k + 1:j + 1]
    if ch == "|":
        if j > 0 and body[j - 1] == "<":
            return "<|"
        if body[j + 1:j + 2] == ">":
            return "|>"
        return "|"
    return ch


def _tac_pos(body: str, mask: list[bool], i: int, fb: int) -> bool:
    if fb < 0 or i <= fb or mask[i]:
        return False
    pt = _prev_token(body, mask, i)
    if pt in TAC_PREV_WORDS or pt in TAC_PREV_SYMS:
        if pt == "=>":
            ls = _line_start(body, i)
            pre = _code(body, mask, ls, i)
            head = pre[:pre.rfind("=>")]
            if re.search(r"(?<![\w.'?!])(?:fun|λ)(?![\w'?!])", head):
                return False
        return True
    return False


def _parent_line(body: str, mask: list[bool], ls: int) -> int | None:
    ind = _indent_at(body, ls)
    e = ls - 1
    while e >= 0:
        q = body.rfind("\n", 0, e) + 1
        if _code(body, mask, q, e).strip() and _indent_at(body, q) < ind:
            return q
        e = q - 1
    return None


_CONV_HDR_RE = re.compile(r"(?<![\w.'?!])conv(?:_lhs|_rhs)?(?![\w'?!])")
_BY_END_RE = re.compile(r"(?<![\w.'?!])by\s*$")


def _in_conv(body: str, mask: list[bool], i: int) -> bool:
    ls = _line_start(body, i)
    pre = _code(body, mask, ls, i)
    if _CONV_HDR_RE.search(pre) and "=>" in pre:
        return True
    ind = _indent_at(body, ls)
    q = _parent_line(body, mask, ls)
    while q is not None:
        le = _line_end(body, q)
        pc = _code(body, mask, q, le).rstrip()
        if _CONV_HDR_RE.search(pc) and "=>" in pc:
            return True
        if _BY_END_RE.search(pc):
            return False
        ind = _indent_at(body, q)
        q = _parent_line(body, mask, q)
    return False


def _next_code_line(body: str, mask: list[bool], pos: int) -> tuple[int, int] | None:
    le = _line_end(body, pos)
    ls = le + 1
    while ls < len(body):
        nle = _line_end(body, ls)
        c = _code(body, mask, ls, nle).strip()
        if c:
            return ls, _indent_at(body, ls)
        ls = nle + 1
    return None


def _is_closing_tail(body: str, mask: list[bool], i: int, end: int) -> bool:
    """Conservative check: is the tactic [i, end) the final tactic of its indentation block?"""
    le = _line_end(body, end)
    rest_line = _code(body, mask, end, le).strip()
    if rest_line and not rest_line.startswith((")", "]", "}")):
        return False
    if rest_line.startswith((")", "]", "}")):
        return True
    nx = _next_code_line(body, mask, end)
    if nx is None:
        return True
    ls = _line_start(body, i)
    my_ind = _indent_at(body, ls)
    nx_ls, nx_ind = nx
    nx_code = _code(body, mask, nx_ls, _line_end(body, nx_ls)).lstrip()
    if nx_ind < my_ind:
        return True
    if nx_ind == my_ind and nx_code.startswith(("·", "|", "case ", "next ")):
        return True
    return False


def _loc_end(body: str, mask: list[bool], pos: int) -> int:
    """If `at ...` follows `pos` on the same tactic line, return the end of the `at` clause."""
    k = _skip_ws(body, pos, newlines=False)
    m = re.match(r"at(?![\w'?!])[ \t]*(\*|(?:[^\W\d][\w'!?₀-₉]*[ \t]*)+)?", body[k:])
    if not m or mask[k]:
        return pos
    end = k + m.end()
    while end > k and body[end - 1] in (" ", "\t"):
        end -= 1
    # Make sure we didn't consume `by` or `with` or `using` as a hypothesis name
    clause = body[k:end]
    toks = clause.split()
    while len(toks) > 1 and toks[-1] in ("by", "with", "using", "only", "in", "from", "do"):
        toks.pop()
    if len(toks) == 1 and "*" not in clause:
        return pos
    if len(toks) >= 2:
        last = toks[-1]
        idx = body.find(last, k)
        if idx >= 0:
            return idx + len(last)
    return end


def apply_edits(body: str, edits: tuple[tuple[int, int, str], ...]) -> str:
    out = body
    for start, length, repl in sorted(edits, key=lambda x: x[0], reverse=True):
        out = out[:start] + repl + out[start + length:]
    return out


def edits_conflict(
    body: str,
    e1: tuple[tuple[int, int, str], ...],
    e2: tuple[tuple[int, int, str], ...],
) -> bool:
    for s1, l1, _ in e1:
        end1 = s1 + l1
        ls1 = _line_start(body, s1)
        for s2, l2, _ in e2:
            end2 = s2 + l2
            ls2 = _line_start(body, s2)
            if ls1 == ls2:
                return True
            if not (end1 < s2 or end2 < s1):
                return True
    return False


def _merge_flag_edits(
    cands: list[EditCand],
) -> list[tuple[tuple[tuple[int, int, str], ...], list[str]]]:
    """Group winning config/only insertions on the same tactic line into combined edits."""
    by_pos: dict[int, list[tuple[int, int, str, str]]] = {}
    for c in cands:
        if len(c.edits) != 1:
            continue
        op_kind = c.op.split(":")[-1]
        if op_kind not in ("simp_config", "grind_config", "grind_only", "add_only"):
            continue
        s, l, r = c.edits[0]
        if l != 0:
            continue
        by_pos.setdefault(s, []).append((s, l, r, c.note))

    out: list[tuple[tuple[tuple[int, int, str], ...], list[str]]] = []
    for s, items in by_pos.items():
        if len(items) < 2:
            continue
        # Ensure +/-config flags always precede `only` when at the same offset
        flags = [it for it in items if it[2].strip() != "only"]
        onlys = [it for it in items if it[2].strip() == "only"]
        ordered = flags + onlys[:1]
        if len(ordered) < 2:
            continue
        seen_r: list[str] = []
        notes: list[str] = []
        for _, _, r, n in ordered:
            if r not in seen_r:
                seen_r.append(r)
                notes.append(n)
        merged_repl = "".join(seen_r)
        out.append((((s, 0, merged_repl),), notes))
    return out


# ---------------------------------------------------------------------------
# Candidate site extractors
# ---------------------------------------------------------------------------
_RW_RE = re.compile(r"(?<![\w.'?!])rw(?![\w'?!])")
_NTHRW_RE = re.compile(r"(?<![\w.'?!])nth_rw(?![\w'?!])")
_SIMPONLY_RE = re.compile(r"(?<![\w.'?!])simp([ \t]+only)(?![\w'?!])")
_UNFOLD_RE = re.compile(r"(?<![\w.'?!])(unfold)((?:[ \t]+" + IDENT + r"(?:\." + IDENT + r")*)+)")
_SIMP_HEAD_RE = re.compile(r"(?<![\w.'?!])(simp_all|simpa|simp|dsimp)(?![\w'?!])")
_GRIND_HEAD_RE = re.compile(r"(?<![\w.'?!])(grind)(?![\w'?!])")
_CFG_RE = re.compile(r"\([ \t]*config[ \t]*:=")
_PREORDER_HINT = re.compile(r"eval_|_eval\b|sum_|_sum\b|map_|_map\b|forall|exists|funext|_apply\b|_comp\b|_cons\b")


def _parse_simp_prefix(body: str, mask: list[bool], pairs: dict[int, int], m_end: int) -> dict | None:
    """Parse optional `(config := ...)`, `+opt`/`-opt`, `only`, `[...]` on the same line."""
    p = _skip_ws(body, m_end, newlines=False)
    cfgs = []
    options: set[str] = set()
    while p < len(body) and not mask[p]:
        if body[p] == "(" and p in pairs and _CFG_RE.match(body, p):
            cfgs.append((p, pairs[p] + 1))
            p = _skip_ws(body, pairs[p] + 1, newlines=False)
            continue
        opt = re.match(r"([+-])([A-Za-z]\w*)\b", body[p:])
        if opt:
            options.add(opt.group(2))
            p = _skip_ws(body, p + opt.end(), newlines=False)
            continue
        break
    only_span = None
    m_only = re.match(r"only(?![\w'?!])", body[p:])
    if m_only and not mask[p]:
        only_span = (p, p + m_only.end())
        p = _skip_ws(body, p + m_only.end(), newlines=False)
    args_span = None
    if p < len(body) and not mask[p] and body[p] == "[" and p in pairs:
        args_span = (p, pairs[p] + 1)
        p = _skip_ws(body, pairs[p] + 1, newlines=False)
    at_star = None
    m_at = re.match(r"at[ \t]+\*(?![\w'?!])", body[p:])
    if m_at and not mask[p]:
        at_star = (p, p + m_at.end())
    return {
        "cfgs": cfgs,
        "options": options,
        "only": only_span,
        "args": args_span,
        "at_star": at_star,
        "after": p,
    }


def _arg_spans(body: str, mask: list[bool], pairs: dict[int, int], a: int, b: int) -> list[tuple[int, int]]:
    out: list[tuple[int, int]] = []
    s = a
    p = a
    while p < b:
        if mask[p]:
            p += 1
            continue
        if body[p] in OPEN_TO_CLOSE and p in pairs:
            p = pairs[p] + 1
            continue
        if body[p] == ",":
            x, y = s, p
            while x < y and body[x].isspace():
                x += 1
            while y > x and body[y - 1].isspace():
                y -= 1
            if y > x:
                out.append((x, y))
            s = p + 1
        p += 1
    x, y = s, b
    while x < y and body[x].isspace():
        x += 1
    while y > x and body[y - 1].isspace():
        y -= 1
    if y > x:
        out.append((x, y))
    return out


def _collect_candidates(body: str, statement: str) -> list[EditCand]:
    mask = _mask(body)
    pairs = _pairs(body, mask)
    fb = _first_by(body, mask)
    if fb < 0:
        return []
    tok0 = count_tokens(body)
    raw: list[tuple[str, tuple[tuple[int, int, str], ...], str, int]] = []

    # 1. rw2rewrite and nthrw
    rw_edits_nonclosing: list[tuple[int, int, str]] = []
    for m in _RW_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):
            continue
        k = _skip_ws(body, m.end(), newlines=False)
        if k < len(body) and body[k] == "(" and k in pairs and _CFG_RE.match(body, k):
            k = _skip_ws(body, pairs[k] + 1, newlines=False)
        if k >= len(body) or body[k] != "[" or k not in pairs:
            continue
        rb = pairs[k] + 1
        end = _loc_end(body, mask, rb)
        closing = _is_closing_tail(body, mask, i, end)
        ed = (i, 2, "rewrite")
        snippet = " ".join(body[i:min(end, i + 48)].split())
        if not closing:
            rw_edits_nonclosing.append(ed)
            raw.append((f"{FAMILY}:rw2rewrite", (ed,), f"rw -> rewrite: {snippet}", 15))

    for m in _NTHRW_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):
            continue
        end = _line_end(body, i)
        if _is_closing_tail(body, mask, i, end):
            continue
        ed = (i, len("nth_rw"), "nth_rewrite")
        rw_edits_nonclosing.append(ed)
        raw.append((f"{FAMILY}:nthrw", (ed,), "nth_rw -> nth_rewrite", 16))

    if len(rw_edits_nonclosing) >= 2:
        raw.append((
            f"{FAMILY}:rw2rewrite_all",
            tuple(sorted(rw_edits_nonclosing, key=lambda x: x[0])),
            f"rw -> rewrite at all {len(rw_edits_nonclosing)} non-closing sites",
            10,
        ))

    # 2. simponly2dsimp (`simp only [...]` without reverse rewrites `←` / `<-` -> `dsimp only [...]`)
    dsimp_edits: list[tuple[int, int, str]] = []
    for m in _SIMPONLY_RE.finditer(body):
        i = m.start()
        if not _tac_pos(body, mask, i, fb):
            continue
        k = _skip_ws(body, m.end(), newlines=False)
        if k < len(body) and body[k] == "[" and k in pairs:
            list_text = _code(body, mask, k + 1, pairs[k])
            if "←" in list_text or "<-" in list_text:
                continue
            end = _loc_end(body, mask, pairs[k] + 1)
            prio = 12 if "↓" not in list_text else 22
        else:
            end = _loc_end(body, mask, m.end())
            prio = 11
        ed = (i, 4, "dsimp")
        dsimp_edits.append(ed)
        snippet = " ".join(body[i:min(end, i + 48)].split())
        raw.append((f"{FAMILY}:simponly2dsimp", (ed,), f"simp only -> dsimp only: {snippet}", prio))

    if len(dsimp_edits) >= 2:
        raw.append((
            f"{FAMILY}:simponly2dsimp_all",
            tuple(sorted(dsimp_edits, key=lambda x: x[0])),
            f"simp only -> dsimp only at all {len(dsimp_edits)} sites",
            11,
        ))

    # 3. dsimp_unfold (`unfold f g` -> `dsimp only [f, g]`)
    for m in _UNFOLD_RE.finditer(body):
        i = m.start(1)
        if not _tac_pos(body, mask, i, fb):
            continue
        names = m.group(2).split()
        if not names:
            continue
        ed = (i, m.end(2) - i, f"dsimp only [{', '.join(names)}]")
        raw.append((f"{FAMILY}:dsimp_unfold", (ed,), f"unfold -> dsimp only [{', '.join(names)}]", 14))

    # 4. simp_target, simp_once, simp_config, preorder
    simp_config_sites: list[tuple[int, int, str, int, set[str]]] = []
    for m in _SIMP_HEAD_RE.finditer(body):
        i = m.start(1)
        head = m.group(1)
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):
            continue
        if i + len(head) < len(body) and body[i + len(head)] == "?":
            continue
        info = _parse_simp_prefix(body, mask, pairs, m.end(1))
        if info is None:
            continue

        # 4a. simp_target: drop `at *` (-2 tokens + saves hypothesis simplification)
        if head in ("simp", "dsimp") and info["at_star"] is not None:
            a0, a1 = info["at_star"]
            while a0 > m.end(1) and body[a0 - 1] in (" ", "\t"):
                a0 -= 1
            raw.append((f"{FAMILY}:simp_target", ((a0, a1 - a0, ""),), f"{head}: drop `at *`", 5))

        # 4a2. add_only: `simp/dsimp/simpa/simp_all [a, b]` -> `... only [a, b]`
        if info["only"] is None and info["args"] is not None:
            lb, rb = info["args"]
            raw.append((
                f"{FAMILY}:add_only",
                ((lb, 0, "only "),),
                f"{head} [...] -> {head} only [...]",
                12,
            ))
            if head == "simp":
                list_text = _code(body, mask, lb + 1, rb - 1)
                if "←" not in list_text and "<-" not in list_text:
                    raw.append((
                        f"{FAMILY}:simponly2dsimp",
                        ((i, 4, "dsimp"), (lb, 0, "only ")),
                        "simp [...] -> dsimp only [...]",
                        13,
                    ))

        # 4b. simp_once: `simp_all` -> `simp` with `*` or `at *`
        if head == "simp_all":
            if info["args"] is not None:
                lb, rb = info["args"]
                inside = body[lb + 1:rb - 1].strip()
                if not re.search(r"(?:^|,)\s*\*\s*(?:,|$)", inside):
                    ins = "* " if not inside else "*, "
                    ed = ((i, len("simp_all"), "simp"), (lb + 1, 0, ins))
                    raw.append((f"{FAMILY}:simp_once", ed, "simp_all [...] -> simp [*, ...]", 18))
            elif info["only"] is None:
                le = _line_end(body, info["after"])
                rest = _code(body, mask, info["after"], le).strip()
                if not rest:
                    ed = ((i, len("simp_all"), "simp"), (info["after"], 0, " at *"))
                    raw.append((f"{FAMILY}:simp_once", ed, "simp_all -> simp at *", 19))

        # 4c. Record site weight for simp_config ordering (heavier simp lists & bare simp first)
        if not info["cfgs"]:
            weight = 50
            if info["args"] is not None:
                lb, rb = info["args"]
                spans = _arg_spans(body, mask, pairs, lb + 1, rb - 1)
                weight = len(spans) * 10 + (20 if info["only"] is None else 0)
            elif info["only"] is None:
                weight = 60
            simp_config_sites.append((weight, i, head, m.end(1), info["options"]))

        # 4d. preorder (`↓` on quantifier/eval/sum/map rules in simp lists)
        if head in ("simp", "simpa", "simp_all") and info["args"] is not None:
            lb, rb = info["args"]
            spans = _arg_spans(body, mask, pairs, lb + 1, rb - 1)
            taken = 0
            for x, y in spans:
                arg = body[x:y].strip()
                if not arg or arg[0] in "↓↑-*" or arg.startswith("<-"):
                    continue
                clean_arg = arg.lstrip("← ")
                if _PREORDER_HINT.search(clean_arg):
                    raw.append((f"{FAMILY}:preorder", ((x, 0, "↓"),), f"preorder ↓{clean_arg[:28]}", 28))
                    taken += 1
                    if taken >= 3:
                        break

    # Emit simp_config candidates on the heaviest sites first
    simp_config_sites.sort(key=lambda x: (-x[0], x[1]))
    for rank, (_w, i, head, head_end, opts) in enumerate(simp_config_sites[:6]):
        for flag_idx, (setting, desc) in enumerate(SIMP_FLAGS.get(head, ())):
            fname = setting[1:]
            if fname in opts:
                continue
            prio = 20 + rank * 2 + flag_idx
            raw.append((
                f"{FAMILY}:simp_config",
                ((head_end, 0, " " + setting),),
                f"{head} {setting} ({desc})",
                prio,
            ))

    # 5. grind_only & grind_config
    for m in _GRIND_HEAD_RE.finditer(body):
        i = m.start(1)
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):
            continue
        after = _skip_ws(body, m.end(1), newlines=False)
        if after < len(body) and (body[after:after + 2] == "=>" or body[after] == "?"):
            continue
        info = _parse_simp_prefix(body, mask, pairs, m.end(1))
        if info is None or info["cfgs"]:
            continue
        if info["only"] is None:
            if info["args"] is not None:
                lb, _rb = info["args"]
                raw.append((
                    f"{FAMILY}:grind_only",
                    ((lb, 0, "only "),),
                    "grind [...] -> grind only [...]",
                    14,
                ))
            else:
                raw.append((
                    f"{FAMILY}:grind_only",
                    ((info["after"], 0, " only"),),
                    "grind -> grind only",
                    14,
                ))
        for flag_idx, (setting, desc) in enumerate(GRIND_FLAGS):
            fname = setting[1:]
            if fname in info["options"]:
                continue
            raw.append((
                f"{FAMILY}:grind_config",
                ((m.end(1), 0, " " + setting),),
                f"grind {setting} ({desc})",
                21 + flag_idx,
            ))

    # 6. set_let / set_have (`set x ... := v` without `with h` -> `let x ... := v` / `have x ... := v`)
    set_let_edits: list[tuple[int, int, str]] = []
    for m in re.finditer(r"(?m)^[ \t]*(set)[ \t]+(" + IDENT + r")\b", body):
        i = m.start(1)
        if not _tac_pos(body, mask, i, fb):
            continue
        le = _line_end(body, i)
        line_code = _code(body, mask, i, le)
        if ":=" not in line_code or re.search(r"(?<![\w.'?!])with(?![\w'?!])", line_code):
            continue
        name = m.group(2)
        ed_let = (i, 3, "let")
        ed_have = (i, 3, "have")
        set_let_edits.append(ed_let)
        raw.append((f"{FAMILY}:set_let", (ed_let,), f"set {name} -> let {name}", 13))
        raw.append((f"{FAMILY}:set_have", (ed_have,), f"set {name} -> have {name}", 17))

    if len(set_let_edits) >= 2:
        raw.append((
            f"{FAMILY}:set_let_all",
            tuple(sorted(set_let_edits, key=lambda x: x[0])),
            f"set -> let at all {len(set_let_edits)} sites without `with`",
            12,
        ))

    # 7. let_have (`let x ... := v` -> `have x ... := v`)
    for m in re.finditer(r"(?m)^[ \t]*(let)[ \t]+(" + IDENT + r")\b", body):
        i = m.start(1)
        name = m.group(2)
        if name == "rec" or not _tac_pos(body, mask, i, fb):
            continue
        le = _line_end(body, i)
        if ":=" not in _code(body, mask, i, le):
            continue
        raw.append((f"{FAMILY}:let_have", ((i, 3, "have"),), f"let {name} -> have {name}", 16))

    # 8. ext_funext (`ext x ...` -> `funext x ...`)
    for m in re.finditer(r"(?<![\w.'?!])(ext)((?:[ \t]+" + IDENT + r")+)(?=[ \t]*(?:\n|;|$|<;>))", body):
        i = m.start(1)
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):
            continue
        raw.append((f"{FAMILY}:ext_funext", ((i, 3, "funext"),), f"ext -> funext{m.group(2)}", 15))

    # 9. congr_arg (`congrArg (fun x => ...) h` -> `congr_arg _ h`) and vacuous_function (`nofun`)
    for m in re.finditer(r"(?<![\w.'?!])congr_?[aA]rg[ \t]*\((?:fun|λ)\b", body):
        i = m.start()
        if mask[i] or i <= fb:
            continue
        open_p = body.find("(", i)
        if open_p not in pairs:
            continue
        close_p = pairs[open_p]
        raw.append((
            f"{FAMILY}:congr_arg",
            ((i, close_p + 1 - i, "congr_arg _"),),
            "congrArg (fun ...) -> congr_arg _",
            6,
        ))

    for m in re.finditer(r"\((?:fun|λ)\b[^()\n]*=>[ \t]*False\.elim\b", body):
        i = m.start()
        if mask[i] or i <= fb or i not in pairs:
            continue
        close_p = pairs[i]
        raw.append((
            f"{FAMILY}:vacuous_function",
            ((i, close_p + 1 - i, "nofun"),),
            "(fun ... => False.elim ...) -> nofun",
            6,
        ))

    # Deduplicate by resulting body and build EditCand list
    seen_bodies: set[str] = {body.rstrip()}
    out: list[EditCand] = []
    for op, edits, note, prio in raw:
        new_body = apply_edits(body, edits)
        if new_body.rstrip() in seen_bodies:
            continue
        seen_bodies.add(new_body.rstrip())
        dtok = count_tokens(new_body) - tok0
        out.append(EditCand(
            op=op,
            edits=edits,
            body=new_body,
            decl=_full_decl(statement, new_body),
            note=note,
            dtok=dtok,
            prio=prio,
        ))
    out.sort(key=lambda c: (c.prio, c.dtok))
    return out


# ---------------------------------------------------------------------------
# Environment query: Mode 1 (`#eval` heartbeat screen) & Mode 2 (plain check)
# ---------------------------------------------------------------------------
_DECL_HEAD_RE = re.compile(
    r"\A((?:\s+|/--(?:(?!-/).)*-/|@\[[^\]]*\])*)"
    r"((?:(?:private|protected|noncomputable|nonrec|unsafe|partial|scoped|local)\s+)*)"
    r"(theorem|lemma)\s+([^\s(:{\[⦃]+)",
    re.S,
)

_EVAL_TEMPLATE = """
set_option Elab.async false in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let lraArgonSrc : String := __LRA_SRC__
  let lraArgonIdx : Nat := __LRA_IDX__
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command lraArgonSrc with
  | .error _ =>
    Lean.logInfo (Lean.toMessageData ("LRAD4M\\t" ++ toString lraArgonIdx ++ "\\t0\\t0\\tparse"))
  | .ok lraArgonStx =>
    let lraArgonRel : Lean.Name := __LRA_NAME_EXPR__
    let lraArgonN1 := (← Lean.getCurrNamespace) ++ lraArgonRel
    let (lraArgonOk, lraArgonDh) ← Lean.withoutModifyingEnv do
      let lraArgonT0 ← IO.getNumHeartbeats
      Lean.Elab.Command.elabCommand lraArgonStx
      let lraArgonT1 ← IO.getNumHeartbeats
      let lraArgonEnv ← Lean.getEnv
      let lraArgonN2 := Lean.mkPrivateName lraArgonEnv lraArgonN1
      let lraArgonN := if lraArgonEnv.contains lraArgonN2 then lraArgonN2 else lraArgonN1
      let mut lraArgonGood := false
      if lraArgonEnv.contains lraArgonN then
        lraArgonGood := !((← Lean.collectAxioms lraArgonN).contains ``sorryAx)
      pure (lraArgonGood, lraArgonT1 - lraArgonT0)
    Lean.logInfo (Lean.toMessageData ("LRAD4M\\t" ++ toString lraArgonIdx ++ "\\t" ++ (if lraArgonOk then "1" else "0") ++ "\\t" ++ toString (lraArgonDh / 1000)))
"""


def _lean_name_expr(rel_name: str) -> str:
    parts = [p for p in rel_name.split(".") if p]
    expr = "Lean.Name.anonymous"
    for p in parts:
        expr = f"Lean.Name.str ({expr}) {_lean_str(p)}"
    return expr


def _renamed_decl(statement: str, body: str, i: int) -> tuple[str, str] | None:
    """Return `(full_renamed_decl, rel_name)` preserving `private` and dotted namespace prefix."""
    m = _DECL_HEAD_RE.match(statement)
    if not m or ".{" in m.group(4):
        return None
    mods = m.group(2) or ""
    orig_name = m.group(4)
    keep_priv = "private " if "private" in mods.split() else ""
    if "." in orig_name:
        ns_prefix, short_orig = orig_name.rsplit(".", 1)
        rel_name = f"{ns_prefix}.lraArgon{i}"
    else:
        short_orig = orig_name
        rel_name = f"lraArgon{i}"
    rest_stmt = statement[m.end():]
    renamed_stmt = f"{keep_priv}theorem {rel_name}{rest_stmt}"
    # Rename any recursive/self-reference in body
    new_body = re.sub(r"(?<![\w.'?!])" + re.escape(orig_name) + r"(?![\w'?!])", rel_name, body)
    if short_orig != orig_name:
        new_body = re.sub(r"(?<![\w.'?!])" + re.escape(short_orig) + r"(?![\w'?!])", f"lraArgon{i}", new_body)
    sep = "" if new_body.startswith(("\n", " ", "\t")) else "\n  "
    return f"{renamed_stmt.rstrip()} :={sep}{new_body.rstrip()}\n", rel_name


def _screen_text(statement: str, bodies: list[str]) -> str | None:
    chunks = ["theorem lraArgonDummy : True := trivial\n"]
    for i, b in enumerate(bodies):
        got = _renamed_decl(statement, b, i)
        if got is None:
            return None
        decl_src, rel_name = got
        blk = (
            _EVAL_TEMPLATE
            .replace("__LRA_SRC__", _lean_str(decl_src))
            .replace("__LRA_IDX__", str(i))
            .replace("__LRA_NAME_EXPR__", _lean_name_expr(rel_name))
        )
        chunks.append(blk)
    return "".join(chunks)


def _parse_screen(messages: list | None, n: int) -> dict[int, dict]:
    out: dict[int, dict] = {}
    for m in messages or ():
        for ln in _msg_text(m).split("\n"):
            p = ln.strip().split("\t")
            if len(p) >= 4 and p[0] == "LRAD4M" and p[1].isdigit() and int(p[1]) < n and p[3].isdigit():
                out[int(p[1])] = {"ok": p[2] == "1", "hb": int(p[3])}
    return out


_NO_CMD_ELAB: set[str] = set()


def _plain_check_text(statement: str, bodies: list[str]) -> tuple[str, list[tuple[int, int]]] | None:
    """Fallback batch compiler for `module` files where `CommandElabM` is not in scope.
    Uses `IO.getNumHeartbeats` (in `Init`, always in scope) around each theorem after an initial
    warm-up declaration so both compile validity (`ok`) and exact heartbeat cost (`hb`) are
    measured in a single compile.
    Returns `(text, spans)` where `spans[i] = (start_line, check_line)` are 1-based line numbers
    within `text`, and line 2 is `#check @lraArgonDummy`."""
    if not bodies:
        return None
    warm = _renamed_decl(statement, bodies[0], 999)
    if warm is None:
        return None
    warm_src, _ = warm
    lines: list[str] = [
        "theorem lraArgonDummy : True := trivial",
        "#check @lraArgonDummy",
        "set_option Elab.async false",
        "set_option maxHeartbeats 400000 in",
    ]
    for dl in warm_src.rstrip("\n").split("\n"):
        lines.append(dl)
    spans: list[tuple[int, int]] = []
    for i, b in enumerate(bodies):
        got = _renamed_decl(statement, b, i)
        if got is None:
            return None
        decl_src, rel_name = got
        lines.append(f'#eval show IO Unit from do let h ← IO.getNumHeartbeats; IO.println s!"LRAHB_S\\t{i}\\t{{h}}"')
        start_ln = len(lines) + 1
        lines.append("set_option maxHeartbeats 400000 in")
        for dl in decl_src.rstrip("\n").split("\n"):
            lines.append(dl)
        lines.append(f'#eval show IO Unit from do let h ← IO.getNumHeartbeats; IO.println s!"LRAHB_E\\t{i}\\t{{h}}"')
        lines.append(f"#check @{rel_name}")
        end_ln = len(lines)
        spans.append((start_ln, end_ln))
    return "\n".join(lines) + "\n", spans


def _parse_plain_check(messages: list | None, spans: list[tuple[int, int]]) -> dict[int, dict]:
    """Map messages from `_plain_check_text` to `{i: {"ok": bool, "hb": int | None}}`."""
    msgs = list(messages or ())
    base_line = None
    s_hb: dict[int, int] = {}
    e_hb: dict[int, int] = {}
    for m in msgs:
        txt = _msg_text(m)
        if base_line is None and m.get("severity") == "information" and "lraArgonDummy" in txt:
            ln = (m.get("pos") or {}).get("line")
            if isinstance(ln, int) and ln >= 2:
                base_line = ln
        for line in txt.split("\n"):
            p = line.strip().split("\t")
            if len(p) == 3 and p[1].isdigit() and p[2].isdigit():
                if p[0] == "LRAHB_S":
                    s_hb[int(p[1])] = int(p[2])
                elif p[0] == "LRAHB_E":
                    e_hb[int(p[1])] = int(p[2])
    if base_line is None:
        return {}
    offset = base_line - 2
    out: dict[int, dict] = {}
    for i, (s_ln, e_ln) in enumerate(spans):
        abs_s = offset + s_ln
        abs_e = offset + e_ln
        has_check_info = False
        has_err = False
        for m in msgs:
            ln = (m.get("pos") or {}).get("line")
            if not isinstance(ln, int) or ln < abs_s or ln > abs_e:
                continue
            sev = m.get("severity")
            txt = _msg_text(m)
            if sev == "error" or m.get("kind") == "hasSorry" or ("declaration uses" in txt and "sorry" in txt):
                has_err = True
            elif sev == "information" and ln == abs_e and f"lraArgon{i}" in txt:
                has_check_info = True
        hb_val = None
        if i in s_hb and i in e_hb and e_hb[i] >= s_hb[i]:
            hb_val = (e_hb[i] - s_hb[i]) // 1000
        out[i] = {"ok": has_check_info and not has_err, "hb": hb_val}
    return out


def _screen_budget(ctx: dict | None) -> int:
    cs = (ctx or {}).get("compile_s")
    per = max(1.0, float(cs) / 2.0) if isinstance(cs, (int, float)) and cs > 0 else DEFAULT_VARIANT_S
    return max(2, min(MAX_VARIANTS_PER_FILE, int(MEASURE_S / per)))


def _predicted(ctl_hb: int, dtok: int, hb: int, exchange: float | None) -> float:
    if not exchange:
        return float(-dtok)
    return float(ctl_hb - hb) - float(dtok) * float(exchange)


def _build_winner_dicts(
    proof: str,
    statement: str,
    body0: str,
    winners: list[EditCand],
) -> list[dict]:
    out_dicts: list[dict] = []
    seen_decls: set[str] = {proof.rstrip()}

    # 1. Combine multiple winning config/only flags at the same tactic site
    for merged_ed, notes in _merge_flag_edits(winners):
        m_body = apply_edits(body0, merged_ed)
        m_decl = _full_decl(statement, m_body)
        if m_decl.rstrip() not in seen_decls:
            seen_decls.add(m_decl.rstrip())
            out_dicts.append({
                "op": f"{FAMILY}:flag_combo",
                "decl": m_decl,
                "note": "flag combo: " + " + ".join(notes[:4]),
            })

    # 2. Build greedy non-overlapping combination of winners on distinct lines
    combo_edits: tuple[tuple[int, int, str], ...] = ()
    combo_ops: list[str] = []
    for c in winners:
        if len(c.edits) > 1 and c.op.endswith("_all"):
            continue
        if not edits_conflict(body0, combo_edits, c.edits):
            combo_edits = tuple(sorted(combo_edits + c.edits, key=lambda x: x[0]))
            combo_ops.append(c.op.split(":")[-1])
    if len(combo_ops) >= 2:
        c_body = apply_edits(body0, combo_edits)
        c_decl = _full_decl(statement, c_body)
        if c_decl.rstrip() not in seen_decls:
            seen_decls.add(c_decl.rstrip())
            out_dicts.append({
                "op": f"{FAMILY}:combo",
                "decl": c_decl,
                "note": f"combo ({'+'.join(combo_ops[:4])})",
            })

    for c in winners:
        if c.decl.rstrip() not in seen_decls:
            seen_decls.add(c.decl.rstrip())
            out_dicts.append({"op": c.op, "decl": c.decl, "note": c.note})
    return out_dicts


def has_sites(proof: str, statement: str) -> bool:
    body = split_declaration(proof, statement)
    if body is None:
        return False
    return bool(_collect_candidates(body, statement))


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    ctx = dict(ctx or {})
    body0 = split_declaration(proof, statement)
    if body0 is None or _renamed_decl(statement, body0, 0) is None:
        return ctx
    all_cands = _collect_candidates(body0, statement)
    if not all_cands:
        return ctx

    vs = versions or (None,)
    exchange = ctx.get("exchange")
    per_file = _screen_budget(ctx)
    max_files = 1 if isinstance(ctx.get("compile_s"), (int, float)) and float(ctx["compile_s"]) > 35.0 else MAX_SCREEN_FILES
    cap = (per_file - 1) * max_files
    pool = all_cands[:cap]

    scored: list[tuple[float, int, EditCand]] = []
    ctl_ok_any = False
    files_run = 0
    stmt_key = _proof_key(statement)

    if stmt_key not in _NO_CMD_ELAB:
        for f_idx in range(0, len(pool), per_file - 1):
            if files_run >= max_files:
                break
            chunk = pool[f_idx:f_idx + per_file - 1]
            txt = _screen_text(statement, [body0] + [c.body for c in chunk])
            if txt is None:
                break
            r = run(txt, vs[0])
            files_run += 1
            rd = _parse_screen(getattr(r, "messages", None), len(chunk) + 1)
            ctl = rd.get(0) or {"ok": False}
            if not ctl.get("ok"):
                if f_idx == 0 and not rd:
                    _NO_CMD_ELAB.add(stmt_key)
                break
            ctl_ok_any = True
            ctl_hb = int(ctl["hb"])
            for k, c in enumerate(chunk, 1):
                rk = rd.get(k) or {"ok": False}
                if not rk.get("ok"):
                    continue
                pr = _predicted(ctl_hb, c.dtok, int(rk["hb"]), exchange)
                if pr > 0:
                    scored.append((pr, f_idx + k, c))

    if ctl_ok_any:
        scored.sort(key=lambda x: (-x[0], x[1]))
        winners = [c for _, _, c in scored]
        out_dicts = _build_winner_dicts(proof, statement, body0, winners)
        if stats is not None:
            stats["argon_hbelab_mode"] = "eval_hb"
            stats["argon_hbelab_files"] = files_run
            stats["argon_hbelab_winners"] = len(out_dicts)
        ctx["argon_hbelab_for"] = _proof_key(proof)
        ctx["argon_hbelab_cands"] = out_dicts
        return ctx

    # Mode 2 fallback: multi-theorem compile with IO.getNumHeartbeats for `module` files (e.g. Strata)
    plain_pool = all_cands[:MAX_PLAIN_VARIANTS - 1]
    built = _plain_check_text(statement, [body0] + [c.body for c in plain_pool])
    if built is not None:
        ptxt, spans = built
        r2 = run(ptxt, vs[0])
        files_run += 1
        rd2 = _parse_plain_check(getattr(r2, "messages", None), spans)
        ctl2 = rd2.get(0) or {"ok": False}
        if ctl2.get("ok"):
            ctl_hb2 = ctl2.get("hb")
            if isinstance(ctl_hb2, int):
                scored2: list[tuple[float, int, EditCand]] = []
                for k, c in enumerate(plain_pool, 1):
                    rk = rd2.get(k) or {"ok": False}
                    if not rk.get("ok") or not isinstance(rk.get("hb"), int):
                        continue
                    pr = _predicted(ctl_hb2, c.dtok, int(rk["hb"]), exchange)
                    if pr > 0:
                        scored2.append((pr, k, c))
                scored2.sort(key=lambda x: (-x[0], x[1]))
                winners2 = [c for _, _, c in scored2]
            else:
                winners2 = [c for k, c in enumerate(plain_pool, 1) if (rd2.get(k) or {}).get("ok")]
            out_dicts = _build_winner_dicts(proof, statement, body0, winners2)
            if stats is not None:
                stats["argon_hbelab_mode"] = "plain_hb"
                stats["argon_hbelab_files"] = files_run
                stats["argon_hbelab_winners"] = len(out_dicts)
            ctx["argon_hbelab_for"] = _proof_key(proof)
            ctx["argon_hbelab_cands"] = out_dicts
            return ctx

    return ctx


def candidates(proof: str, statement: str, *, exchange=None, max_per_op: int | None = None, ctx=None) -> list[dict]:
    ctx = ctx or {}
    if ctx.get("argon_hbelab_for") == _proof_key(proof) and "argon_hbelab_cands" in ctx:
        out = list(ctx["argon_hbelab_cands"])
        return out if max_per_op is None else out[:max_per_op]

    body = split_declaration(proof, statement)
    if body is None:
        return []
    cands = _collect_candidates(body, statement)
    out = [{"op": c.op, "decl": c.decl, "note": c.note} for c in cands]
    return out if max_per_op is None else out[:max_per_op]
