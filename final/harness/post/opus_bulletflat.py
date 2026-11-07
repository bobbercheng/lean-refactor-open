#!/usr/bin/env python3
"""Structural op "opus_bulletflat" of the open post-step (gap lane opus, extension 2026-11-04): a case split's bullet arms -> a FLAT
goal list (the shape the closed proofs use: each arm's steps in Lean's goal order, without the `·` focusing dots). Most tactics act on
the main goal only, so the flat list runs the same steps on the same goals; Lean decides the exceptions (all_goals, `<;>` into the
next arm, goal-order sensitive tactics).

  sites     a sibling group: consecutive own-line bullets `· T` at the same column in one block (a bullet line's arm = it and the
            following lines indented deeper than the dot). An arm is flattened by removing the dot (and the spaces after it) and
            dedenting the arm's other lines by the same width; a line that is not indented that deep makes the arm unflattenable.
  generate  bulletflat:all    every flattenable bullet of the proof at once
            bulletflat:group  one sibling group flattened (largest group first)
            bulletflat:last   the LAST arm of a group only (it focuses the only remaining goal of the group)
  screen    query(): through harness/post/opus_screen.py (measured, else plain) when there are >= 2 candidates; only the predicted-up
            ones are proposed, best first.
  unchecked a proof with a kernel-unchecked closer (kskip's `debug.skipKernelTC`) has no site.
Pure text plus the row's own environment. No row name, table or proof text."""

# provenance: research lane gaplane-opus (worktree lra-gl-opus), commit 2822f68, ported into open-post-v5-lanes (2026-11-04) unchanged
from __future__ import annotations

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.post import d4_kit as K  # noqa: E402
from harness.post import opus_screen as SC  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "opus_bulletflat"
MAX_PER_OP = 12
MAX_SCREEN = 24
BULLET = re.compile(r"^( *)·([ \t]+)(\S.*)$")
NEXT = re.compile(r"^( *)next((?:[ \t]+[^\s=]+)*)[ \t]*=>[ \t]*(.*)$")
# `case tag xs =>` (one tag, no `|` alternatives): flattened like `next xs =>` (Lean decides whether the goal order matches the tag)
CASE = re.compile(r"^( *)case[ \t]+[^\s|=]+((?:[ \t]+[^\s|=]+)*)[ \t]*=>[ \t]*(.*)$")


def _ind(ln: str) -> int:
    return len(ln) - len(ln.lstrip(" "))


def arms(L: list[str]) -> list[dict]:
    """[{"i": bullet line, "end": exclusive end line, "col": dot column, "w": width of `· ` }] in order."""
    out = []
    for i, ln in enumerate(L):
        if "--" in ln:
            continue
        m = BULLET.match(ln)
        kind = "dot"
        if m:
            col = len(m.group(1))
            w = 1 + len(m.group(2))
        else:
            m = NEXT.match(ln) or CASE.match(ln)
            if not m:
                continue
            kind = "next"
            col = len(m.group(1))
            nxt = next((x for x in L[i + 1:] if x.strip()), None)
            if m.group(3).strip():
                w = None   # arm content on the header line: its other lines must be deeper than the header
            elif nxt is None or _ind(nxt) <= col:
                continue
            else:
                w = _ind(nxt) - col
        e = i + 1
        while e < len(L) and (not L[e].strip() or _ind(L[e]) > col):
            e += 1
        while e > i + 1 and not L[e - 1].strip():
            e -= 1
        if kind == "next" and w is None:
            deep = [_ind(L[k]) for k in range(i + 1, e) if L[k].strip()]
            if deep and min(deep) <= col:
                continue
            w = (min(deep) - col) if deep else 0
        out.append({"i": i, "end": e, "col": col, "w": w, "kind": kind})
    return out


def groups(L: list[str], A: list[dict]) -> list[list[dict]]:
    """Sibling groups: arms at the same column where each next arm starts right where the previous one ends."""
    out, cur = [], []
    for a in A:
        if cur and cur[-1]["col"] == a["col"] and cur[-1]["end"] == a["i"]:
            cur.append(a)
            continue
        # an arm nested inside the current group's last arm does not break the group: groups are found per column
        if cur:
            out.append(cur)
        cur = [a]
    if cur:
        out.append(cur)
    # merge: groups split only by nested arms (an arm whose start lies inside a previous arm at a smaller column)
    merged: list[list[dict]] = []
    for g in out:
        for h in merged:
            if h[-1]["col"] == g[0]["col"] and h[-1]["end"] == g[0]["i"]:
                h.extend(g)
                break
        else:
            merged.append(g)
    return merged


def flatten(L: list[str], sel: list[dict]) -> list[str] | None:
    L = list(L)
    for a in sorted(sel, key=lambda a: -a["i"]):
        need = a["col"] + a["w"]
        if a.get("kind") == "next":
            m = NEXT.match(L[a["i"]]) or CASE.match(L[a["i"]])
            if not m:
                return None
            names = " ".join(m.group(2).split())
            head = [m.group(1) + "rename_i " + names] if names else []
            if m.group(3).strip():
                head.append(m.group(1) + m.group(3).strip())
            for k in range(a["i"] + 1, a["end"]):
                if L[k].strip() and _ind(L[k]) < need:
                    return None
            rest = [x[a["w"]:] if x.strip() else x for x in L[a["i"] + 1:a["end"]]]
            L[a["i"]:a["end"]] = head + rest
            continue
        m = BULLET.match(L[a["i"]])
        if not m:
            return None
        L[a["i"]] = m.group(1) + m.group(3)
        for k in range(a["i"] + 1, a["end"]):
            if not L[k].strip():
                continue
            if _ind(L[k]) < need:
                return None
            L[k] = L[k][a["w"]:]
    return L


def raw_candidates(body: str) -> list[tuple[str, str, str]]:
    if SC.unchecked(body):
        return []
    L = body.split("\n")
    A = arms(L)
    if not A:
        return []
    G = groups(L, A)
    t0 = count_tokens(body)
    out, seen = [], set()

    def add(var, sel, note):
        F = flatten(L, sel)
        if F is None:
            return
        nb = "\n".join(F)
        if nb in seen or count_tokens(nb) >= t0:
            return
        seen.add(nb)
        out.append((var, nb, note))

    ok_all = [a for a in A if flatten(L, [a]) is not None]
    add("all", ok_all, f"{len(ok_all)} bullets flattened")
    for g in sorted(G, key=lambda g: (-len(g), g[0]["i"])):
        add("group", g, f"group of {len(g)} bullets at line {g[0]['i'] + 1} flattened")
    for g in G:
        add("last", [g[-1]], f"last bullet at line {g[-1]['i'] + 1} flattened")
    return out


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
        scr = (ctx or {}).get("bulletflat_screen") if (ctx or {}).get("bulletflat_key") == K.proof_key(proof) else None
        if scr is not None:
            up = dict(scr.get("up", []))
            raws = sorted([r for r in raws if r[1] in up], key=lambda r: -up[r[1]])
        for var, nb, note in raws:
            em.add(f"{FAMILY}:{var}", nb, note)
        return em.out
    except Exception:
        return []


def query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None) -> dict | None:
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return {}
        _, body = hb
        raws = raw_candidates(body)[:MAX_SCREEN]
        if len(raws) <= 1:
            return {}
        got = SC.screen(statement, body, [r[1] for r in raws], run, ctx, log=log, tag=FAMILY, max_files=1)
        if got is None:
            return {}
        return {"bulletflat_key": K.proof_key(proof), "bulletflat_screen": got}
    except Exception as e:  # never raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:200]}")
        return {}
