#!/usr/bin/env python3
"""Structural op "opus_hoist" of the open post-step (gap lane opus, 2026-11-03): a step repeated across the goals of a flat goal list
-> ONE `any_goals` / `all_goals` step.

  site      a tactic block (the body's tactic structure parsed by indentation: `by` blocks, `=>` arms, `·` bullets) holding m >= 2
            own-line, single-line occurrences of the same tactic T (exact text; not a block opener, not on a bullet line). Open proofs
            close the goals of an `induction` / `cases` / `fun_induction` one after another (unhygienic flat lists) and repeat the
            same steps per goal (`subst_vars`, `unfold f`, `dsimp only`, `cases h`, `rfl`); the closed proofs hoist them.
  generate  hoist:any   the first occurrence -> `any_goals T`, the later occurrences in that block deleted
            hoist:all   the same with `all_goals T`
            (one candidate per (block, T) and combinator; largest saving first)
  screen    query(): all candidates in ONE d4_measure file (the incumbent the control); only those predicted to read higher are
            proposed. Lean decides whether the goals the later steps meet are still the ones they close.
Pure text plus the row's own environment (the screen compile). No row name, table or proof text."""
from __future__ import annotations

# provenance: research lane gaplane-opus (worktree lra-gl-opus), commit ef7dde5, ported unchanged into open-post-v3 (2026-11-04)

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from harness.post import opus_screen as SC  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "opus_hoist"
MAX_PER_OP = 16
BULLET = "·"
OPENER_END = re.compile(r"(?:\bby|=>|\bwith|:=|\bfrom|<;>|\bthen|\belse|\bdo|[(\[{⟨,])\s*$")
SKIP_T = re.compile(r"^(?:case|next|\||·|have|obtain|let|set|show|calc|suffices|rename_i|exacts?|refine|use|exists)\b")


def _indent(ln: str) -> int:
    return len(ln) - len(ln.lstrip(" "))


def parse(body: str) -> list[dict]:
    """One record per non-blank line: {"i", "col" (tactic column), "start" (a tactic start), "block" (block id), "bullet"}."""
    mask = _mask(body)
    L = body.split("\n")
    offs, o = [], 0
    for ln in L:
        offs.append(o)
        o += len(ln) + 1
    recs = []
    stack: list[tuple[int, int]] = []   # (column, block id)
    nid = 0
    prev_open = True                    # the body starts after `:=`; ` by` on the first line opens the block
    for i, ln in enumerate(L):
        if not ln.strip():
            continue
        code = "".join(ch for k, ch in enumerate(ln) if not mask[offs[i] + k]).rstrip() if any(mask[offs[i]:offs[i] + len(ln)]) else ln.rstrip()
        if not code.strip():
            continue
        d = _indent(ln)
        s = ln.lstrip(" ")
        if i == 0:
            prev_open = bool(re.search(r"\bby\s*$", code)) or code.strip() == ""
            recs.append({"i": i, "col": d, "start": False, "block": -1, "bullet": False, "code": code})
            continue
        while stack and d < stack[-1][0]:
            stack.pop()
        bullet = s.startswith(BULLET)
        if stack and d == stack[-1][0]:
            start, blk = True, stack[-1][1]
        elif prev_open or not stack:
            nid += 1
            stack.append((d, nid))
            start, blk = True, nid
        else:
            start, blk = False, stack[-1][1] if stack else -1   # a continuation line
        col = d
        if bullet and start:
            rest = s[len(BULLET):]
            col = d + len(BULLET) + (len(rest) - len(rest.lstrip(" ")))
            nid += 1
            stack.append((col, nid))
        recs.append({"i": i, "col": col, "start": start, "block": blk, "bullet": bullet, "code": code})
        prev_open = bool(OPENER_END.search(code))
    return recs


MAX_W = 3   # a repeated run of up to this many consecutive one-line steps -> `T1 <;> T2 <;> ...`


def sites(body: str) -> list[dict]:
    L = body.split("\n")
    recs = parse(body)
    seqs: dict = {}
    for k, r in enumerate(recs):
        if not r["start"] or r["block"] < 0:
            continue
        ok = not r["bullet"]
        nxt = recs[k + 1] if k + 1 < len(recs) else None
        if nxt is not None and not nxt["start"] and nxt["col"] > r["col"]:
            ok = False   # a multi-line tactic
        t = r["code"].strip()
        if len(t) < 3 or OPENER_END.search(t) or SKIP_T.match(t) or t != L[r["i"]].strip():
            ok = False
        seqs.setdefault(r["block"], []).append((r["i"], t if ok else None))
    out = []
    for blk, seq in seqs.items():
        for w in range(1, MAX_W + 1):
            occ: dict = {}
            last_end: dict = {}
            for j in range(len(seq) - w + 1):
                win = seq[j:j + w]
                if any(t is None for _, t in win) or any(win[x + 1][0] != win[x][0] + 1 for x in range(w - 1)):
                    continue
                key = tuple(t for _, t in win)
                if j < last_end.get(key, 0):
                    continue   # overlaps the previous occurrence
                occ.setdefault(key, []).append(win[0][0])
                last_end[key] = j + w
            for key, ls in occ.items():
                if len(ls) >= 2:
                    out.append({"block": blk, "tactic": " <;> ".join(key), "lines": ls, "w": w})
    return out


def _span(s: dict) -> set:
    return {i + x for i in s["lines"] for x in range(s.get("w", 1))}


def _apply(L: list[str], sel: list[dict], comb: str) -> str | None:
    firsts, drop = {}, set()
    for s in sel:
        w = s.get("w", 1)
        firsts[s["lines"][0]] = s["tactic"]
        drop |= {s["lines"][0] + x for x in range(1, w)}
        drop |= {i + x for i in s["lines"][1:] for x in range(w)}
    if set(firsts) & drop:
        return None
    NL = []
    for i, ln in enumerate(L):
        if i in firsts:
            NL.append(ln[:_indent(ln)] + f"{comb} " + firsts[i])
        elif i not in drop:
            NL.append(ln)
    return "\n".join(NL)


def raw_candidates(body: str) -> list[tuple[str, str, str]]:
    if SC.unchecked(body):
        return []
    L = body.split("\n")
    t0 = count_tokens(body)
    out = []
    ss = sites(body)
    for s in ss:
        for comb in ("any_goals", "all_goals"):
            nb = _apply(L, [s], comb)
            if nb is not None and count_tokens(nb) < t0:
                out.append((t0 - count_tokens(nb), comb.split("_")[0], nb,
                            f"`{s['tactic'][:40]}` x{len(s['lines'])} at line {s['lines'][0] + 1} -> {comb}"))
    if len(ss) >= 2:
        sel = []
        for s in sorted(ss, key=lambda s: -len(s["lines"]) * len(s["tactic"])):
            if not any(_span(x) & _span(s) for x in sel):
                sel.append(s)
        nb = _apply(L, sel, "any_goals") if len(sel) >= 2 else None
        if nb is not None and count_tokens(nb) < t0:
            out.append((t0 - count_tokens(nb) + 0.5, "joint", nb, f"{len(ss)} repeated steps -> any_goals"))
    out.sort(key=lambda x: (-x[0], x[1] != "any"))
    return [(v, nb, note) for _, v, nb, note in out]


def has_sites(proof: str, statement: str) -> bool:
    try:
        body = split_declaration(proof, statement)
        return bool(body) and bool(raw_candidates(body))
    except Exception:
        return False


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return []
        head, body = hb
        em = K.Emitter(proof, statement, head, body, int(max_per_op or MAX_PER_OP))
        raws = raw_candidates(body)
        scr = (ctx or {}).get("hoist_screen") if (ctx or {}).get("hoist_key") == K.proof_key(proof) else None
        if scr is not None:
            up = dict(scr.get("up", []))
            uns = set(scr.get("unscreened", []))
            raws = sorted([r for r in raws if r[1] in up], key=lambda r: -up[r[1]]) + [r for r in raws if r[1] in uns]
        for var, nb, note in raws:
            em.add(f"{FAMILY}:{var}", nb, note)
        return em.out
    except Exception:
        return []


def query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None) -> dict | None:
    """One screen file (harness/post/opus_screen.py: measured, else plain) over the candidates; {} when nothing to screen."""
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return {}
        _, body = hb
        raws = raw_candidates(body)
        if len(raws) <= 1:
            return {}
        got = SC.screen(statement, body, [r[1] for r in raws], run, ctx, log=log, tag=FAMILY, max_files=1)
        if got is None:
            return {}
        return {"hoist_key": K.proof_key(proof), "hoist_screen": got}
    except Exception as e:  # never raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:200]}")
        return {}
