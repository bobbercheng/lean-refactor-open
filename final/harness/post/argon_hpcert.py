#!/usr/bin/env python3
"""Gap-lane op `argon_hpcert`: `?`-certificate extraction, `only`-list pruning, and
single-file measured bracket-item elimination for the open post-step.

Addresses the second uncovered open-to-closed gap mechanism identified in `gaplane/NOTES.md`:
  1. `cert` (`simp?` / `dsimp?` / `simpa?` / `simp_all?` / `grind?`):
     Replaces bare or non-`only` `simp`, `dsimp`, `simpa`, `simp_all`, `grind` calls with
     Lean's exact `"Try this: <head> only [...]"` certificate from a single probe compile
     (avoiding global `@[simp]` / `@[grind]` theorem search at elaboration time).
  2. `prune` (`simp? only [...]` / `dsimp? only [...]` / `simpa? only [...]` / `simp_all? only [...]`):
     Replaces existing `only [...]` lists with Lean's shorter `"Try this:"` list when unused
     lemmas are present (saving both L tokens and H heartbeats).
  3. `drop_item` / `drop_list` (measured bracket-item ddmin across `simp`, `dsimp`, `simpa`,
     `simp_all`, `grind`, `rw`, `rewrite`, `nth_rw`, `nth_rewrite`):
     Even when Lean's `simp` or `rw` applies a lemma in `[L_1, ..., L_m]`, a downstream tactic
     (`grind`, `omega`, `linarith`, `ring`, `simp`, `aesop`, etc.) often closes the goal without
     it. Unlike `d4_closerprep` (which only inspects `simp` immediately before `decide`),
     `argon_hpcert` screens single-item drops across all tactic bracket lists in the proof
     using a single-file heartbeat-measured batch compile (`CommandElabM` `#eval` with
     `IO.getNumHeartbeats` fallback for `module` files) and synthesizes a multi-drop `combo`
     from all compatible winning drops.

Self-contained under `harness/post/argon_hpcert.py`; imports only `scorer.tokenize` plus
the Python standard library. Reads zero external files or tables.
"""
from __future__ import annotations

# provenance: research lane gaplane-argon (worktree lra-gl-argon), commit d7dee71, ported unchanged into open-post-v3 (2026-11-04)

import hashlib
import re
from dataclasses import dataclass

from scorer.tokenize import count_tokens, split_declaration

FAMILY = "argon_hpcert"

MAX_VARIANTS_PER_FILE = 16
MAX_SCREEN_FILES = 2
MAX_PLAIN_VARIANTS = 24
MEASURE_S = 100.0
DEFAULT_VARIANT_S = 6.0

IDENT_START = r"[A-Za-z_\u03b1-\u03c9\u0391-\u03a9]"
IDENT_CONT = r"[A-Za-z0-9_'\u03b1-\u03c9\u0391-\u03a9\u2080-\u2089!?]"
IDENT = f"{IDENT_START}{IDENT_CONT}*(?:\\.{IDENT_START}{IDENT_CONT}*)*"

OPEN_TO_CLOSE = {"(": ")", "[": "]", "{": "}", "⟨": "⟩", "‹": "›", "⦃": "⦄"}
CLOSE_TO_OPEN = {v: k for k, v in OPEN_TO_CLOSE.items()}

_CERT_HEAD_RE = re.compile(r"(?<![\w.'?!])(simp_all|simpa|simp|dsimp|grind)(?![\w'?!])")
_BRACKET_TAC_RE = re.compile(
    r"(?<![\w.'?!])(simp_all|simpa|simp|dsimp|grind|nth_rewrite|nth_rw|rewrite|rw)(?![\w'?!])"
)
_RULE_CLAUSE_RE = re.compile(r"\s*(?:add|erase|rule_sets|simp_config|config)\b")
_TRY_THIS_RE = re.compile(r"Try (?:this|these):\s*(?:\[apply\]\s*)?", re.S)


@dataclass(frozen=True)
class EditCand:
    op: str
    edits: tuple[tuple[int, int, str], ...]
    body: str
    decl: str
    note: str
    dtok: int
    prio: int
    drop_info: tuple[int, int, int, tuple[str, ...]] | None = None  # (lb, rb, drop_idx, items_tuple)


def _proof_key(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode("utf-8")).hexdigest()[:16]


def _full_decl(statement: str, body: str) -> str:
    s = statement.rstrip()
    if body.startswith(("\n", " ", "\t")):
        return f"{s} :={body}"
    return f"{s} := {body}"


def _lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t") + '"'


def _msg_text(m: dict) -> str:
    return str(m.get("data") or m.get("message") or m.get("text") or "")


def _mask(s: str) -> list[bool]:
    n = len(s)
    out = [False] * n
    i = 0
    depth = 0
    in_str = False
    while i < n:
        c = s[i]
        nxt = s[i + 1] if i + 1 < n else ""
        if in_str:
            out[i] = True
            if c == "\\" and i + 1 < n:
                out[i + 1] = True
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if depth > 0:
            out[i] = True
            if c == "/" and nxt == "-":
                depth += 1
                if i + 1 < n:
                    out[i + 1] = True
                i += 2
                continue
            if c == "-" and nxt == "/":
                depth -= 1
                if i + 1 < n:
                    out[i + 1] = True
                i += 2
                continue
            i += 1
            continue
        if c == "-" and nxt == "-":
            while i < n and s[i] != "\n":
                out[i] = True
                i += 1
            continue
        if c == "/" and nxt == "-":
            depth = 1
            out[i] = True
            if i + 1 < n:
                out[i + 1] = True
            i += 2
            continue
        if c == '"':
            in_str = True
            out[i] = True
            i += 1
            continue
        i += 1
    return out


def _pairs(s: str, mask: list[bool]) -> dict[int, int]:
    stack: list[tuple[str, int]] = []
    out: dict[int, int] = {}
    for i, c in enumerate(s):
        if mask[i]:
            continue
        if c in OPEN_TO_CLOSE:
            stack.append((c, i))
        elif c in CLOSE_TO_OPEN:
            want = CLOSE_TO_OPEN[c]
            for j in range(len(stack) - 1, -1, -1):
                if stack[j][0] == want:
                    _, start = stack[j]
                    del stack[j:]
                    out[start] = i
                    break
    return out


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


def _line_start(s: str, idx: int) -> int:
    j = s.rfind("\n", 0, idx)
    return 0 if j < 0 else j + 1


def _line_indent(s: str, idx: int) -> int:
    ls = _line_start(s, idx)
    k = ls
    while k < len(s) and s[k] in (" ", "\t"):
        k += 1
    return k - ls


def _in_conv(body: str, mask: list[bool], pos: int) -> bool:
    ls = _line_start(body, pos)
    line_before = "".join(" " if mask[k] else body[k] for k in range(ls, pos))
    if re.search(r"(?<![\w.'?!])conv(?:_lhs|_rhs)?(?![\w'?!])", line_before):
        return True
    my_ind = _line_indent(body, pos)
    cur = ls - 1
    while cur > 0:
        prev_ls = _line_start(body, cur)
        code = "".join(" " if mask[k] else body[k] for k in range(prev_ls, cur + 1)).strip()
        if code:
            ind = _line_indent(body, prev_ls)
            if ind < my_ind:
                if re.match(r"conv(?:_lhs|_rhs)?(?![\w'?!])", code):
                    return True
                my_ind = ind
                if my_ind == 0:
                    break
        cur = prev_ls - 1
    return False


def _in_rule_clause(body: str, mask: list[bool], pos: int) -> bool:
    depth = 0
    for i in range(pos - 1, -1, -1):
        if mask[i]:
            continue
        if body[i] == ")":
            depth += 1
        elif body[i] == "(":
            if depth == 0:
                return bool(_RULE_CLAUSE_RE.match(body, i + 1))
            depth -= 1
    return False


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
        return "|"
    return ch


def _tac_pos(body: str, mask: list[bool], i: int, fb: int) -> bool:
    if fb < 0 or i <= fb or mask[i] or _in_rule_clause(body, mask, i):
        return False
    pt = _prev_token(body, mask, i)
    return pt in ("\n", ";", "<;>", "<|>", "=>", "by", "·", "|", "(", "{", "all_goals", "any_goals", "try", "repeat", "focus")


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


def _parse_bracket_items(text: str, lb: int) -> tuple[int, list[str]] | None:
    if lb < 0 or lb >= len(text) or text[lb] != "[":
        return None
    mask = _mask(text)
    pairs = _pairs(text, mask)
    if lb not in pairs:
        return None
    rb = pairs[lb]
    spans = _arg_spans(text, mask, pairs, lb + 1, rb)
    items = [re.sub(r"\s+", " ", text[x:y].strip()) for x, y in spans if text[x:y].strip()]
    return rb + 1, items


def apply_edits(body: str, edits: tuple[tuple[int, int, str], ...]) -> str:
    s = body
    for start, length, repl in sorted(edits, key=lambda x: x[0], reverse=True):
        s = s[:start] + repl + s[start + length:]
    return s


def _parse_tac_clause(body: str, mask: list[bool], pairs: dict[int, int], head_end: int) -> dict | None:
    """Parse `<head> (±opt | (config := ...))* [only] [[...]]`."""
    p = head_end
    n = len(body)
    has_cfg = False
    has_opt = False
    while p < n:
        p = _skip_ws(body, p, newlines=False)
        if p >= n or mask[p]:
            break
        if body[p] == "(" and p in pairs and re.match(r"\(\s*(?:config|discharger)\s*:=", body[p:]):
            has_cfg = True
            p = pairs[p] + 1
            continue
        if body[p] in "+-" and p + 1 < n and body[p + 1].isalpha():
            m = re.match(r"[+-]" + IDENT, body[p:])
            if m:
                has_opt = True
                p += m.end()
                continue
        break
    opts_end = p
    p = _skip_ws(body, p, newlines=False)
    if p < n and body[p] == "!":
        return None
    only_span = None
    m_only = re.match(r"only(?![\w'?!])", body[p:])
    if m_only and not mask[p]:
        only_span = (p, p + 4)
        p = _skip_ws(body, p + 4, newlines=False)
    args_span = None
    if p < n and not mask[p] and body[p] == "[" and p in pairs:
        args_span = (p, pairs[p] + 1)
    return {
        "has_cfg": has_cfg,
        "has_opt": has_opt,
        "opts_end": opts_end,
        "only": only_span,
        "args": args_span,
    }


def _find_probe_sites(body: str) -> list[dict]:
    """Find all `cert` (non-`only`) and `prune` (`only [...]`) sites in `body`."""
    mask = _mask(body)
    pairs = _pairs(body, mask)
    fb = _first_by(body, mask)
    if fb < 0:
        return []
    sites: list[dict] = []
    for m in _CERT_HEAD_RE.finditer(body):
        i = m.start(1)
        head = m.group(1)
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):
            continue
        if m.end(1) < len(body) and body[m.end(1)] in ("?", "!"):
            continue
        after = _skip_ws(body, m.end(1), newlines=False)
        if after < len(body) and body[after:after + 2] == "=>":
            continue
        info = _parse_tac_clause(body, mask, pairs, m.end(1))
        if info is None or info["has_cfg"]:
            continue
        if info["only"] is not None:
            if info["args"] is None:
                continue
            lb, rb = info["args"]
            spans = _arg_spans(body, mask, pairs, lb + 1, rb - 1)
            items = [re.sub(r"\s+", " ", body[x:y].strip()) for x, y in spans if body[x:y].strip()]
            if not items:
                continue
            sites.append({
                "kind": "prune",
                "head": head,
                "start": i,
                "head_end": m.end(1),
                "opts_end": info["opts_end"],
                "only_end": info["only"][1],
                "args_span": (lb, rb),
                "orig_items": items,
            })
        else:
            head_opts = body[i:info["opts_end"]].rstrip()
            args_end = info["args"][1] if info["args"] is not None else i + len(head_opts)
            sites.append({
                "kind": "cert",
                "head": head,
                "head_opts": head_opts,
                "start": i,
                "head_end": m.end(1),
                "opts_end": info["opts_end"],
                "only_end": None,
                "args_span": info["args"],
                "args_end": args_end,
                "orig_items": [],
            })
    return sites


def _collect_pure_candidates(body: str, statement: str) -> list[EditCand]:
    """Pure single-item and single-list drops across tactic bracket lists."""
    mask = _mask(body)
    pairs = _pairs(body, mask)
    fb = _first_by(body, mask)
    if fb < 0:
        return []
    tok0 = count_tokens(body)
    raw: list[tuple[str, tuple[tuple[int, int, str], ...], str, int, tuple[int, int, int, tuple[str, ...]] | None]] = []

    for m in _BRACKET_TAC_RE.finditer(body):
        i = m.start(1)
        head = m.group(1)
        if not _tac_pos(body, mask, i, fb) or _in_conv(body, mask, i):
            continue
        p = _skip_ws(body, m.end(1), newlines=False)
        if p < len(body) and body[p] in ("?", "!"):
            continue
        if head in ("nth_rw", "nth_rewrite"):
            m_num = re.match(r"\d+[ \t]*", body[p:])
            if m_num:
                p += m_num.end()
        info = _parse_tac_clause(body, mask, pairs, p) if head not in ("rw", "rewrite", "nth_rw", "nth_rewrite") else None
        if info is not None:
            if info["args"] is None:
                continue
            lb, rb = info["args"]
            has_only = info["only"] is not None
        else:
            if p < len(body) and body[p] == "(" and p in pairs:
                p = _skip_ws(body, pairs[p] + 1, newlines=False)
            if p >= len(body) or body[p] != "[" or p not in pairs:
                continue
            lb, rb = p, pairs[p] + 1
            has_only = False

        spans = _arg_spans(body, mask, pairs, lb + 1, rb - 1)
        items = [body[x:y].strip() for x, y in spans if body[x:y].strip()]
        if not items:
            continue
        items_tuple = tuple(items)
        if head == "grind":
            mod_edits: list[tuple[int, int, str]] = []
            for (x, y), it in zip(spans, items):
                m_mod = re.match(r"^(?:=_|=|\!|←|→|usr\b)\s*", body[x:y])
                if m_mod:
                    ed_m = (x, m_mod.end(), "")
                    mod_edits.append(ed_m)
                    raw.append((
                        f"{FAMILY}:grind_mod_strip",
                        (ed_m,),
                        f"grind: strip modifier on `{it[:28]}`",
                        3,
                        None,
                    ))
            if len(mod_edits) >= 2:
                raw.append((
                    f"{FAMILY}:grind_mod_strip",
                    tuple(mod_edits),
                    "grind: strip all `=`/`!` modifiers",
                    3,
                    None,
                ))
        if head in ("simp", "simpa", "simp_all", "grind") and not has_only:
            # Drop `[...]` on non-`only` simp/simpa/simp_all/grind -> bare `<head>`
            a0 = lb
            while a0 > m.end(1) and body[a0 - 1] in (" ", "\t"):
                a0 -= 1
            raw.append((
                f"{FAMILY}:drop_list",
                ((a0, rb - a0, ""),),
                f"{head}: drop [{items[0][:24]}...]",
                10 if len(items) == 1 else 14,
                None,
            ))
        elif has_only and info is not None:
            only_s, only_e = info["only"]
            a_only = only_s
            while a_only > m.end(1) and body[a_only - 1] in (" ", "\t"):
                a_only -= 1
            if head == "grind":
                raw.append((
                    f"{FAMILY}:drop_list",
                    ((only_e, rb - only_e, ""),),
                    f"grind only [...] -> grind only",
                    11,
                    None,
                ))
                raw.append((
                    f"{FAMILY}:drop_list",
                    ((a_only, rb - a_only, ""),),
                    f"grind only [...] -> grind",
                    13,
                    None,
                ))
            elif head in ("simp", "dsimp") and not info["has_opt"] and not info["has_cfg"] and len(items) <= 2:
                raw.append((
                    f"{FAMILY}:drop_list",
                    ((i, rb - i, "dsimp"),),
                    f"{head} only [...] -> dsimp",
                    12,
                    None,
                ))
            if head in ("simp", "simpa", "simp_all") and len(items) <= 3:
                raw.append((
                    f"{FAMILY}:drop_list",
                    ((a_only, rb - a_only, ""),),
                    f"{head} only [...] -> {head}",
                    15,
                    None,
                ))
        if len(items) == 1:
            continue

        # Multi-item bracket list: try dropping each item (heaviest token items first)
        for idx, item in enumerate(items):
            if item == "*":
                continue
            kept = [it for j, it in enumerate(items) if j != idx]
            repl = ", ".join(kept)
            ed = ((lb + 1, (rb - 1) - (lb + 1), repl),)
            item_toks = max(1, count_tokens(item))
            prio = max(4, 24 - min(18, item_toks * 2))
            raw.append((
                f"{FAMILY}:drop_item",
                ed,
                f"{head}: drop `{item[:32]}`",
                prio,
                (lb, rb, idx, items_tuple),
            ))

    seen_bodies: set[str] = {body.rstrip()}
    out: list[EditCand] = []
    for op, edits, note, prio, drop_info in raw:
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
            drop_info=drop_info,
        ))
    out.sort(key=lambda c: (c.prio, c.dtok))
    return out


# ---------------------------------------------------------------------------
# Environment query: Step A (`?` probe) + Step B (`eval_hb` / `plain_hb`)
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
  let lraHpSrc : String := __LRA_SRC__
  let lraHpIdx : Nat := __LRA_IDX__
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command lraHpSrc with
  | .error _ =>
    Lean.logInfo (Lean.toMessageData ("LRAD4M\\t" ++ toString lraHpIdx ++ "\\t0\\t0\\tparse"))
  | .ok lraHpStx =>
    let lraHpRel : Lean.Name := __LRA_NAME_EXPR__
    let lraHpN1 := (← Lean.getCurrNamespace) ++ lraHpRel
    let (lraHpOk, lraHpDh) ← Lean.withoutModifyingEnv do
      let lraHpT0 ← IO.getNumHeartbeats
      Lean.Elab.Command.elabCommand lraHpStx
      let lraHpT1 ← IO.getNumHeartbeats
      let lraHpEnv ← Lean.getEnv
      let lraHpN2 := Lean.mkPrivateName lraHpEnv lraHpN1
      let lraHpN := if lraHpEnv.contains lraHpN2 then lraHpN2 else lraHpN1
      let mut lraHpGood := false
      if lraHpEnv.contains lraHpN then
        lraHpGood := !((← Lean.collectAxioms lraHpN).contains ``sorryAx)
      pure (lraHpGood, lraHpT1 - lraHpT0)
    Lean.logInfo (Lean.toMessageData ("LRAD4M\\t" ++ toString lraHpIdx ++ "\\t" ++ (if lraHpOk then "1" else "0") ++ "\\t" ++ toString (lraHpDh / 1000)))
"""

_NO_CMD_ELAB: set[str] = set()


def _lean_name_expr(rel_name: str) -> str:
    parts = [p for p in rel_name.split(".") if p]
    expr = "Lean.Name.anonymous"
    for p in parts:
        expr = f"Lean.Name.str ({expr}) {_lean_str(p)}"
    return expr


def _renamed_decl(statement: str, body: str, i: int) -> tuple[str, str] | None:
    m = _DECL_HEAD_RE.match(statement)
    if not m or ".{" in m.group(4):
        return None
    mods = m.group(2) or ""
    orig_name = m.group(4)
    keep_priv = "private " if "private" in mods.split() else ""
    if "." in orig_name:
        ns_prefix, short_orig = orig_name.rsplit(".", 1)
        rel_name = f"{ns_prefix}.lraHp{i}"
    else:
        short_orig = orig_name
        rel_name = f"lraHp{i}"
    rest_stmt = statement[m.end():]
    renamed_stmt = f"{keep_priv}theorem {rel_name}{rest_stmt}"
    new_body = re.sub(r"(?<![\w.'?!])" + re.escape(orig_name) + r"(?![\w'?!])", rel_name, body)
    if short_orig != orig_name:
        new_body = re.sub(r"(?<![\w.'?!])" + re.escape(short_orig) + r"(?![\w'?!])", f"lraHp{i}", new_body)
    sep = "" if new_body.startswith(("\n", " ", "\t")) else "\n  "
    return f"{renamed_stmt.rstrip()} :={sep}{new_body.rstrip()}\n", rel_name


def _build_probe_text(statement: str, body: str, sites: list[dict]) -> tuple[str, dict[tuple[int, int], int], dict[int, int]] | None:
    """Build a single-compile `?` probe text for `sites` and map `(rel_line, col) -> site_idx`."""
    simp_idxs = [k for k, s in enumerate(sites) if s["head"] != "grind"]
    grind_idxs = [k for k, s in enumerate(sites) if s["head"] == "grind"]
    groups = [g for g in (simp_idxs, grind_idxs) if g]
    if not groups:
        return None

    lines: list[str] = [
        "theorem lraHpDummy : True := trivial",
        "#check @lraHpDummy",
    ]
    pos_map: dict[tuple[int, int], int] = {}
    line_only_map: dict[int, list[int]] = {}

    for g_idx, idxs in enumerate(groups):
        base_got = _renamed_decl(statement, body, 800 + g_idx)
        if base_got is None:
            return None
        base_decl_src, _ = base_got
        r_body_len = len(body.rstrip())
        # Re-detect sites on the renamed body so recursive theorem name replacements cannot shift offsets
        sep_idx = base_decl_src.find(":=")
        if sep_idx >= 0:
            after_eq = sep_idx + 2
            if base_decl_src[after_eq:after_eq + 3] == "\n  " and not body.startswith(("\n", " ", "\t")):
                after_eq += 3
            renamed_body = base_decl_src[after_eq:-1]
            local_sites = _find_probe_sites(renamed_body)
            use_sites = local_sites if len(local_sites) == len(sites) else sites
            p_body = renamed_body
            prefix = base_decl_src[:after_eq]
        else:
            use_sites = sites
            p_body = body
            prefix = base_decl_src[:-r_body_len - 1]

        for k in sorted(idxs, key=lambda idx: -use_sites[idx]["head_end"]):
            he = use_sites[k]["head_end"]
            p_body = p_body[:he] + "?" + p_body[he:]
        decl_src = f"{prefix}{p_body.rstrip()}\n"
        prefix_len = len(prefix)
        lines.append("set_option maxHeartbeats 400000 in")
        decl_first_line = len(lines) + 1
        for dl in decl_src.rstrip("\n").split("\n"):
            lines.append(dl)
        for rank, k in enumerate(sorted(idxs, key=lambda idx: use_sites[idx]["start"])):
            pos_in_pbody = use_sites[k]["start"] + rank
            pos_in_decl = prefix_len + pos_in_pbody
            rel_ln = decl_first_line + decl_src.count("\n", 0, pos_in_decl)
            col = pos_in_decl - (decl_src.rfind("\n", 0, pos_in_decl) + 1)
            pos_map[(rel_ln, col)] = k
            line_only_map.setdefault(rel_ln, []).append(k)

    lines.append("#check @Lean.Elab.Command.elabCommand")
    unambiguous_line_map = {ln: ks[0] for ln, ks in line_only_map.items() if len(ks) == 1}
    return "\n".join(lines) + "\n", pos_map, unambiguous_line_map


def _parse_probe_messages(
    messages: list | None,
    pos_map: dict[tuple[int, int], int],
    line_map: dict[int, int],
) -> dict[int, list[str]]:
    msgs = list(messages or ())
    base_line = None
    for m in msgs:
        if m.get("severity") == "information" and "lraHpDummy" in _msg_text(m):
            ln = (m.get("pos") or {}).get("line")
            if isinstance(ln, int) and ln >= 2:
                base_line = ln
                break
    offset = (base_line - 2) if base_line is not None else 0
    out: dict[int, list[str]] = {}
    for m in msgs:
        txt = _msg_text(m)
        if not _TRY_THIS_RE.search(txt):
            continue
        p = m.get("pos") or {}
        ln = p.get("line")
        col = p.get("column")
        if not isinstance(ln, int):
            continue
        rel_ln = ln - offset
        k = pos_map.get((rel_ln, col)) if isinstance(col, int) else None
        if k is None:
            k = line_map.get(rel_ln)
        if k is None:
            continue
        after_try = re.split(r"\n\s*\[apply\]|\n\n", _TRY_THIS_RE.sub("", txt, count=1))[0].strip()
        b = after_try.find("[")
        if b >= 0:
            got = _parse_bracket_items(after_try, b)
            if got is None:
                continue
            items = got[1]
        elif re.search(r"\bonly\b", after_try):
            items = []
        else:
            continue
        cur = out.setdefault(k, [])
        for it in items:
            if it and not it.startswith("#") and it not in cur:
                cur.append(it)
    return out


def _candidates_from_probe(
    body: str,
    statement: str,
    sites: list[dict],
    sugg: dict[int, list[str]],
) -> list[EditCand]:
    tok0 = count_tokens(body)
    cert_edits: list[tuple[int, int, str]] = []
    prune_edits: list[tuple[int, int, str]] = []
    raw: list[tuple[str, tuple[tuple[int, int, str], ...], str, int]] = []

    for k, items in sorted(sugg.items()):
        if k < 0 or k >= len(sites):
            continue
        s = sites[k]
        if s["kind"] == "cert":
            head_opts = s.get("head_opts") or s["head"]
            repl = f"{head_opts} only" + (f" [{', '.join(items)}]" if items else "")
            ed = (s["start"], s["args_end"] - s["start"], repl)
            cert_edits.append(ed)
            raw.append((
                f"{FAMILY}:cert",
                (ed,),
                f"{s['head']} -> {s['head']} only [{len(items)}]",
                2,
            ))
            if s["head"] == "grind" and items:
                stripped = [re.sub(r"^(?:=_|=|\!|←|→|usr\b)\s*", "", it) for it in items]
                if stripped != items:
                    repl_s = f"{head_opts} only [{', '.join(stripped)}]"
                    ed_s = (s["start"], s["args_end"] - s["start"], repl_s)
                    raw.append((
                        f"{FAMILY}:cert",
                        (ed_s,),
                        f"grind -> grind only [{len(stripped)}] (no mod)",
                        2,
                    ))
        elif s["kind"] == "prune":
            orig_items = s["orig_items"]
            if len(items) >= len(orig_items):
                continue
            only_end = s["only_end"]
            _lb, rb = s["args_span"]
            clean_items = list(items)
            if s["head"] == "grind" and clean_items:
                orig_set = set(orig_items)
                clean_items = [
                    re.sub(r"^(?:=_|=|\!|←|→|usr\b)\s*", "", it)
                    if re.sub(r"^(?:=_|=|\!|←|→|usr\b)\s*", "", it) in orig_set else it
                    for it in clean_items
                ]
            repl = f" [{', '.join(clean_items)}]" if clean_items else ""
            ed = (only_end, rb - only_end, repl)
            prune_edits.append(ed)
            dropped = len(orig_items) - len(clean_items)
            raw.append((
                f"{FAMILY}:prune",
                (ed,),
                f"{s['head']} only: drop {dropped} unused lemma(s)",
                1,
            ))

    if len(prune_edits) >= 2:
        raw.insert(0, (
            f"{FAMILY}:prune_all",
            tuple(sorted(prune_edits, key=lambda x: x[0])),
            f"prune all {len(prune_edits)} `only` lists",
            0,
        ))
    if len(cert_edits) >= 2:
        raw.insert(0, (
            f"{FAMILY}:cert_all",
            tuple(sorted(cert_edits, key=lambda x: x[0])),
            f"certify all {len(cert_edits)} sites",
            1,
        ))

    seen: set[str] = {body.rstrip()}
    out: list[EditCand] = []
    for op, edits, note, prio in raw:
        nb = apply_edits(body, edits)
        if nb.rstrip() in seen:
            continue
        seen.add(nb.rstrip())
        out.append(EditCand(
            op=op,
            edits=edits,
            body=nb,
            decl=_full_decl(statement, nb),
            note=note,
            dtok=count_tokens(nb) - tok0,
            prio=prio,
        ))
    return out


def _screen_text(statement: str, bodies: list[str]) -> str | None:
    chunks = ["theorem lraHpDummy : True := trivial\n"]
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


def _plain_check_text(statement: str, bodies: list[str]) -> tuple[str, list[tuple[int, int]]] | None:
    if not bodies:
        return None
    warm = _renamed_decl(statement, bodies[0], 999)
    if warm is None:
        return None
    warm_src, _ = warm
    lines: list[str] = [
        "theorem lraHpDummy : True := trivial",
        "#check @lraHpDummy",
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
    msgs = list(messages or ())
    base_line = None
    s_hb: dict[int, int] = {}
    e_hb: dict[int, int] = {}
    for m in msgs:
        txt = _msg_text(m)
        if base_line is None and m.get("severity") == "information" and "lraHpDummy" in txt:
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
            elif sev == "information" and ln == abs_e and f"lraHp{i}" in txt:
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


def _edits_overlap(e1: tuple[tuple[int, int, str], ...], e2: tuple[tuple[int, int, str], ...]) -> bool:
    for s1, l1, _ in e1:
        end1 = s1 + l1
        for s2, l2, _ in e2:
            end2 = s2 + l2
            if not (end1 < s2 or end2 < s1):
                return True
    return False


def _build_winner_dicts(
    proof: str,
    statement: str,
    body0: str,
    winners: list[EditCand],
) -> list[dict]:
    out_dicts: list[dict] = []
    seen_decls: set[str] = {proof.rstrip()}

    # 1. Combine multiple winning `drop_item` edits within the SAME bracket list `[lb:rb]`
    by_bracket: dict[tuple[int, int], tuple[tuple[str, ...], list[int]]] = {}
    for c in winners:
        if c.drop_info is None:
            continue
        lb, rb, idx, items_tuple = c.drop_info
        _, idxs = by_bracket.setdefault((lb, rb), (items_tuple, []))
        if idx not in idxs and len(idxs) + 1 < len(items_tuple):
            idxs.append(idx)

    bracket_merged_edits: list[tuple[int, int, str]] = []
    for (lb, rb), (items_tuple, drop_idxs) in sorted(by_bracket.items()):
        drop_set = set(drop_idxs)
        kept = [it for j, it in enumerate(items_tuple) if j not in drop_set]
        ed = (lb + 1, (rb - 1) - (lb + 1), ", ".join(kept))
        bracket_merged_edits.append(ed)
        if len(drop_idxs) >= 2:
            m_body = apply_edits(body0, (ed,))
            m_decl = _full_decl(statement, m_body)
            if m_decl.rstrip() not in seen_decls:
                seen_decls.add(m_decl.rstrip())
                out_dicts.append({
                    "op": f"{FAMILY}:multi_drop",
                    "decl": m_decl,
                    "note": f"drop {len(drop_idxs)} items from list",
                })

    # 2. Combine non-overlapping winners across the entire proof body
    combo_edits: tuple[tuple[int, int, str], ...] = tuple(bracket_merged_edits)
    combo_count = sum(len(v[1]) for v in by_bracket.values())
    for c in winners:
        if c.drop_info is not None or c.op.endswith("_all"):
            continue
        if not _edits_overlap(combo_edits, c.edits):
            combo_edits = tuple(sorted(combo_edits + c.edits, key=lambda x: x[0]))
            combo_count += 1
    if combo_count >= 2 and combo_edits:
        c_body = apply_edits(body0, combo_edits)
        c_decl = _full_decl(statement, c_body)
        if c_decl.rstrip() not in seen_decls:
            seen_decls.add(c_decl.rstrip())
            out_dicts.append({
                "op": f"{FAMILY}:combo",
                "decl": c_decl,
                "note": f"combo ({combo_count} verified edits)",
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
    return bool(_find_probe_sites(body) or _collect_pure_candidates(body, statement))


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    ctx = dict(ctx or {})
    body0 = split_declaration(proof, statement)
    if body0 is None or _renamed_decl(statement, body0, 0) is None:
        return ctx

    vs = versions or (None,)
    exchange = ctx.get("exchange")
    files_run = 0

    # Step A: 1-compile `?` certificate & prune probe
    stmt_key = _proof_key(statement)
    probe_sites = _find_probe_sites(body0)
    probe_cands: list[EditCand] = []
    if probe_sites:
        built_p = _build_probe_text(statement, body0, probe_sites)
        if built_p is not None:
            ptxt, pos_map, line_map = built_p
            rp = run(ptxt, vs[0])
            files_run += 1
            rp_msgs = list(getattr(rp, "messages", None) or ())
            if any("elabCommand" in _msg_text(m) and m.get("severity") == "error" for m in rp_msgs):
                _NO_CMD_ELAB.add(stmt_key)
            sugg = _parse_probe_messages(rp_msgs, pos_map, line_map)
            if sugg:
                probe_cands = _candidates_from_probe(body0, statement, probe_sites, sugg)

    pure_cands = _collect_pure_candidates(body0, statement)
    seen_b: set[str] = {body0.rstrip()}
    all_cands: list[EditCand] = []
    for c in probe_cands + pure_cands:
        if c.body.rstrip() not in seen_b:
            seen_b.add(c.body.rstrip())
            all_cands.append(c)

    if not all_cands:
        return ctx

    per_file = _screen_budget(ctx)
    max_files = 1 if isinstance(ctx.get("compile_s"), (int, float)) and float(ctx["compile_s"]) > 35.0 else MAX_SCREEN_FILES
    cap = (per_file - 1) * max_files
    pool = all_cands[:cap]

    scored: list[tuple[float, int, EditCand]] = []
    ctl_ok_any = False
    stmt_key = _proof_key(statement)

    if stmt_key not in _NO_CMD_ELAB:
        for f_idx in range(0, len(pool), per_file - 1):
            if files_run >= max_files + (1 if probe_sites else 0):
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
            stats["argon_hpcert_mode"] = "eval_hb"
            stats["argon_hpcert_files"] = files_run
            stats["argon_hpcert_winners"] = len(out_dicts)
        ctx["argon_hpcert_for"] = _proof_key(proof)
        ctx["argon_hpcert_cands"] = out_dicts
        return ctx

    # Mode 2 fallback: multi-theorem compile with IO.getNumHeartbeats for `module` files (e.g. Strata)
    plain_pool = all_cands[:MAX_PLAIN_VARIANTS - 1]
    built = _plain_check_text(statement, [body0] + [c.body for c in plain_pool])
    if built is not None:
        ptxt2, spans = built
        r2 = run(ptxt2, vs[0])
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
                stats["argon_hpcert_mode"] = "plain_hb"
                stats["argon_hpcert_files"] = files_run
                stats["argon_hpcert_winners"] = len(out_dicts)
            ctx["argon_hpcert_for"] = _proof_key(proof)
            ctx["argon_hpcert_cands"] = out_dicts
            return ctx

    return ctx


def candidates(proof: str, statement: str, *, exchange=None, max_per_op: int | None = None, ctx=None) -> list[dict]:
    ctx = ctx or {}
    if ctx.get("argon_hpcert_for") == _proof_key(proof) and "argon_hpcert_cands" in ctx:
        out = list(ctx["argon_hpcert_cands"])
        return out if max_per_op is None else out[:max_per_op]

    body = split_declaration(proof, statement)
    if body is None:
        return []
    cands = _collect_pure_candidates(body, statement)
    out = [{"op": c.op, "decl": c.decl, "note": c.note} for c in cands]
    return out if max_per_op is None else out[:max_per_op]
