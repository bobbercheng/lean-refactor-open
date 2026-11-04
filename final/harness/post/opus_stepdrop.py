#!/usr/bin/env python3
"""Structural op "opus_stepdrop" of the open post-step (gap lane opus, 2026-11-03): drop preparation steps that the rest of the block
no longer needs (a generalisation of opus_scaffold from `have` / `obtain` to every non-binding preparation step).

  site      an own-line tactic step (single- or multi-line, its continuation lines included) in a tactic block (indentation parse of
            opus_hoist.parse) that
              - starts with a PREPARATION head: simp / simp only / simp_all / dsimp / norm_num / unfold / delta / rw / rewrite / erw /
                push_cast / norm_cast / ring_nf / field_simp / clear / subst / subst_vars / show / change / beta_reduce / push_neg /
                specialize / replace / split_ifs at / zeta / intro? no (binding steps never),
              - is not on a bullet line, holds no nested block (no `by` / `=>` / `·` inside), no comment,
              - is not the last step of its block (the last one closes the goal).
  generate  stepdrop:joint  every site the screen read OK (when the query ran) removed at once
            stepdrop:del    one site removed (largest saving first)
  screen    query(): the single deletions (largest first) in at most 2 d4_measure files (the incumbent the control); only the ones
            predicted to read higher are proposed, and their joint first.
  unchecked  a proof that contains `debug.skipKernelTC` (the kskip op's closer) has NO site by default: its `decide +kernel` is
            not checked by the kernel, so dropping the steps before it "succeeds" without the goal being decided (MEASURED on
            open_r2post PauliMatrix row: +12.37 row points from such a drop). Opt in: ALLOW_UNCHECKED = True.
Pure text plus the row's own environment. No row name, table or proof text."""
from __future__ import annotations

# provenance: research lane gaplane-opus (worktree lra-gl-opus), commit ef7dde5, ported unchanged into open-post-v3 (2026-11-04)

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from harness.post import opus_screen as SC  # noqa: E402
from harness.post.opus_hoist import parse  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "opus_stepdrop"
MAX_PER_OP = 16
MAX_FILES = 2
PREP = re.compile(r"^(?:simp_all|simp|dsimp|norm_num|unfold|delta|rw|rewrite|erw|rwa|push_cast|norm_cast|ring_nf|field_simp|clear|"
                  r"subst_vars|subst|show|change|beta_reduce|push_neg|specialize|replace|zeta_reduce|simp_rw|conv_lhs|conv_rhs|"
                  r"generalize|set_option)\b(?![\w'])")
NESTED = re.compile(r"(?<![\w'])by(?![\w'])|=>|^\s*·")


UNCHECKED = "skipKernelTC"
ALLOW_UNCHECKED = False


def sites(body: str) -> list[tuple]:
    """[(first line, end line exclusive, bullet prefix or None)] of the droppable steps. A step on a bullet line `· T` hands its
    bullet to the next step of the bullet's block (prefix = the bullet line's text up to the tactic column)."""
    if UNCHECKED in body and not ALLOW_UNCHECKED:
        return []
    L = body.split("\n")
    recs = parse(body)
    out = []
    starts = [k for k, r in enumerate(recs) if r["start"]]
    for idx, k in enumerate(starts):
        r = recs[k]
        if r["block"] < 0:
            continue
        line0 = L[r["i"]]
        t = line0[r["col"]:].strip() if r["bullet"] else r["code"].strip()
        if not PREP.match(t) or (not r["bullet"] and t != line0.strip()):
            continue
        # its lines: up to the next record that starts a step at a column <= its own
        e = k + 1
        while e < len(recs) and not (recs[e]["start"] and recs[e]["col"] <= r["col"]):
            e += 1
        if e >= len(recs):
            continue
        same = (recs[e]["block"] != r["block"]) if r["bullet"] else (recs[e]["block"] == r["block"])   # a bullet's step opens its block
        if e >= len(recs) or recs[e]["col"] != r["col"] or not same or recs[e]["bullet"]:
            continue   # the last step of its block
        lines = range(r["i"], recs[e]["i"])
        text = "\n".join([line0[r["col"]:]] + [L[i] for i in lines][1:])
        if NESTED.search(line0[r["col"]:]) or any(NESTED.search(L[i]) for i in list(lines)[1:]) or "--" in text or "/-" in text:
            continue
        if r["bullet"]:
            out.append((r["i"], recs[e]["i"], line0[:r["col"]]))
            continue
        last = max(i for i in lines if L[i].strip())   # trailing blank lines stay
        out.append((r["i"], last + 1, None))
    return out


def _drop(L: list[str], sel: list[tuple]) -> str | None:
    gone = {i for a, b, _ in sel for i in range(a, b)}
    heir = {b: p for a, b, p in sel if p is not None}
    if set(heir) & gone:
        return None
    out = []
    for i, ln in enumerate(L):
        if i in gone:
            continue
        out.append(heir[i] + ln[len(heir[i]):] if i in heir else ln)
    return "\n".join(out)


def raw_candidates(body: str, ok: list | None = None) -> list[tuple[str, str, str]]:
    L = body.split("\n")
    t0 = count_tokens(body)
    singles = []
    for s in sites(body):
        nb = _drop(L, [s])
        if nb is not None and count_tokens(nb) < t0:
            singles.append((t0 - count_tokens(nb), s, nb))
    singles.sort(key=lambda x: (x[1][2] is not None, -x[0], x[1][:2]))   # bullet hand-overs after the plain drops (screen capacity)
    out = []
    if ok is not None:
        keep = []
        for d, s, nb in singles:
            if nb in ok and _drop(L, keep + [s]) is not None:
                keep.append(s)
        if len(keep) >= 2:
            out.append(("joint", _drop(L, keep), f"{len(keep)} preparation steps dropped"))
        out += [("del", nb, f"step at line {s[0] + 1} dropped, -{d} tokens") for d, s, nb in singles if nb in ok]
        return out
    return [("del", nb, f"step at line {s[0] + 1} dropped, -{d} tokens") for d, s, nb in singles]


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
        scr = (ctx or {}).get("stepdrop_screen") if (ctx or {}).get("stepdrop_key") == K.proof_key(proof) else None
        if scr is not None:
            up = dict(scr.get("up", []))
            raws = raw_candidates(body, ok=list(up))
            joint = [r for r in raws if r[0] == "joint"]
            raws = joint + sorted([r for r in raws if r[0] != "joint"], key=lambda r: -up.get(r[1], 0))
        else:
            raws = raw_candidates(body)
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
        got = SC.screen(statement, body, [r[1] for r in raws], run, ctx, log=log, tag=FAMILY, max_files=2)
        if got is None:
            return {}
        return {"stepdrop_key": K.proof_key(proof), "stepdrop_screen": got}
    except Exception as e:  # never raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:200]}")
        return {}
