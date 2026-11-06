#!/usr/bin/env python3
"""Post-step op `hb_smartunfold` (branch open-post-v5-smartunfold, 2026-11-04): sound elaborator unfolding toggles inside the proof.

`set_option smartUnfolding false in` (default true) makes the elaborator's whnf / defeq unfold a structurally recursive definition through
its compiled recursor form instead of the smart-unfolding auxiliary; on some goals (concrete `decide`, `rfl`, defeq-heavy `exact` / `simp`)
that is cheaper. It is a plain elaboration option: the kernel still checks the final term (no `debug.*`, no heartbeat option, no kernel
option; scorer/forbidden.py does not list it). Four tokens, so it only pays where it saves enough heartbeats.

  candidates (each a single insertion into the proof body; the statement and `:=` untouched)
    whole     `by set_option smartUnfolding false in` + the original tactic block (term mode: `set_option smartUnfolding false in` + the
              term), and the same for the other sound defeq / instance / dsimp / cleanup toggles in TOGGLES (true -> false)
    step      a `set_option smartUnfolding false in` line at the block column in front of one top-level tactic step, the step's lines
              indented two more (the option's block then ends at the next step), for the K_STEP steps with the highest
              unfolding-heavy keyword weight (no per-step profile: the screen measures every copy's heartbeats)
    nested    ` set_option smartUnfolding false in` right after a nested `by` (that block only), K_BY of them by the same weight
    suffix    a `set_option smartUnfolding false in` line before a top-level step (that step and every later one), K_SUFFIX of them
  screen    one or two batch files on the primary pin (harness/post/argon_hbelab's `#eval` heartbeat screen, read-only reuse; its plain
            multi-theorem fallback for files without CommandElabM): the input as copy 0, then the candidates; a candidate is kept when it
            compiles sorry-free and its predicted score change (heartbeats saved minus added tokens at the row's exchange) is positive;
            winners are ranked by that prediction, and the stack of all winning whole-proof toggles and the union of the winning
            step / nested insertions are proposed after them. The post-step's accept gate decides (real meter, every pin, paired re-read).
Model-free, deterministic, $0; reads only the proof and the statement."""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scorer.tokenize import count_tokens, split_declaration  # noqa: E402
from harness.post import argon_hbelab as AH  # noqa: E402  (read-only reuse: masking, renamed copies, batch heartbeat screens)

FAMILY = "hb_smartunfold"
SU = "smartUnfolding"
# sound elaboration toggles whose default is true (defeq laziness, instance canonicity); never debug.*, heartbeat or kernel options
TOGGLES = (SU, "backward.isDefEq.lazyWhnfCore", "backward.isDefEq.lazyProjDelta", "backward.synthInstance.canonInstances",
           # v5b (screen 2026-11-04 07:20): more true-by-default elaboration options (Lean's option table, v4.30.0): the dsimp / cleanup
           # pair exists on every pin (v4.25.0 .. v4.35.0-rc3); the last three from v4.29 on (an older pin fails the accept gate's pins)
           "backward.dsimp.useDefEqAttr", "cleanup.letToHave",
           "backward.isDefEq.implicitBump", "backward.isDefEq.respectTransparency", "backward.whnf.reducibleClassField")
K_STEP = 5
K_BY = 4
K_SUFFIX = 3
MAX_SCREEN_FILES = 2
SLOW_COMPILE_S = 35.0   # an input slower than this gets one screen file

_BY_RE = re.compile(r"(?<![\w.'?!])by(?![\w'?!])")
_KW_WEIGHT = (("decide", 5), ("rfl", 4), ("norm_num", 3), ("simp_all", 3), ("simpa", 3), ("dsimp", 3), ("simp", 3), ("unfold", 3),
              ("show", 3), ("change", 3), ("exact", 1), ("apply", 1), ("refine", 1), ("omega", 1), ("grind", 2), ("trivial", 2),
              ("cases", 1), ("induction", 1), ("rcases", 1), ("obtain", 1), ("aesop", 2), ("rw", 1), ("calc", 1))
_KW_RE = {k: re.compile(r"(?<![\w.'?!])" + re.escape(k) + r"(?![\w'?!])") for k, _ in _KW_WEIGHT}
_NOT_STEP = ("<;>", "<|>", "|", ")", "]", "}", "⟩", ",", "=>", ".", "termination_by", "decreasing_by", "where")


def _key(proof: str) -> str:
    return hashlib.sha256((proof or "").rstrip().encode()).hexdigest()[:16]


def _opt(name: str) -> str:
    return f"set_option {name} false in"


def _weight(code: str) -> int:
    return sum(w * len(_KW_RE[k].findall(code)) for k, w in _KW_WEIGHT)


def _decl(head: str, body: str) -> str:
    """head = the input's text up to and including `:=` (statement and its own separator kept byte for byte)."""
    return f"{head}{body.rstrip()}\n"


def _insert(body: str, ins: list[tuple]) -> str:
    """Apply edits: (pos, text) inserts, (a, b, text) replaces body[a:b]; non-overlapping, any order."""
    eds = sorted((e[0], e[0], e[1]) if len(e) == 2 else tuple(e) for e in ins)
    out, last = [], 0
    for a, b, txt in eds:
        out.append(body[last:a]); out.append(txt); last = b
    out.append(body[last:])
    return "".join(out)


def _span(e: tuple) -> tuple[int, int]:
    return (e[0], e[0]) if len(e) == 2 else (e[0], e[1])


def _overlap(x: tuple, y: tuple) -> bool:
    (a1, b1), (a2, b2) = _span(x), _span(y)
    if a1 == b1 and a2 == b2:
        return a1 == a2
    return not (b1 <= a2 or b2 <= a1) or (a1 == b1 and a2 < a1 < b2) or (a2 == b2 and a1 < a2 < b1)


def _first_code(body: str, mask: list[bool]) -> int:
    i = 0
    while i < len(body) and (mask[i] or body[i] in " \t\n\r"):
        i += 1
    return i


def _top_steps(body: str, mask: list[bool], by_end: int) -> list[tuple[int, int, int]]:
    """Top-level steps of the block opened by the `by` ending at by_end: [(start, end, column)]; start = the step's first character,
    end = the next step's start (or the block end). Lines at the block column that continue a step (`<;>`, `|`, closers) are no step."""
    i = by_end
    while i < len(body) and (mask[i] or body[i] in " \t\n\r"):
        i += 1
    if i >= len(body):
        return []
    col = i - AH._line_start(body, i)
    starts = [i]
    block_end = len(body)
    pos = AH._line_end(body, i)
    while pos < len(body):
        ls = pos + 1
        if ls >= len(body):
            break
        j = ls
        while j < len(body) and body[j] in " \t":
            j += 1
        le = AH._line_end(body, ls)
        if j >= le or mask[j]:          # blank or comment line
            pos = le
            continue
        c = j - ls
        if c < col:
            block_end = ls
            break
        if c == col and not body.startswith(_NOT_STEP, j):
            starts.append(j)
        elif c == col and body.startswith(("termination_by", "decreasing_by", "where"), j):
            block_end = ls
            break
        pos = le
    out = []
    for k, s in enumerate(starts):
        e = starts[k + 1] if k + 1 < len(starts) else block_end
        out.append((s, e, col))
    return out


TIER1 = TOGGLES[:3]   # the whole-proof toggles that won in the first screens (smartUnfolding, lazyWhnfCore, lazyProjDelta)


def _sites(body: str) -> list[dict]:
    """Pure candidate insertions in screen priority order: the TIER1 whole forms, then the local forms round-robin (suffix, nested,
    step; each kind heaviest first), then the other whole forms. A slow row's single screen file holds about 9 copies; with every
    whole form first the local winners were crowded out (screen 3, 2026-11-04: a suffix winner of +0.43 lost)."""
    raw = _sites_raw(body)
    w1 = [x for x in raw if x["kind"] == "whole" and x["toggle"] in TIER1]
    w2 = [x for x in raw if x["kind"] == "whole" and x["toggle"] not in TIER1]
    groups = [[x for x in raw if x["kind"] == k] for k in ("suffix", "nested", "step")]
    rr = [g[i] for i in range(max((len(g) for g in groups), default=0)) for g in groups if i < len(g)]
    return w1 + rr + w2


def _sites_raw(body: str) -> list[dict]:
    """Pure candidate insertions by kind: [{"kind", "ins": [(pos, text)], "toggle", "note", "w"}]."""
    mask = AH._mask(body)
    code = AH._code(body, mask, 0, len(body))
    out: list[dict] = []
    f = _first_code(body, mask)
    if f >= len(body):
        return out
    top_by = body.startswith("by", f) and _BY_RE.match(body, f) is not None
    # whole
    for t in TOGGLES:
        if re.search(r"set_option\s+" + re.escape(t) + r"\b", code):
            continue
        ins = [(f + 2, " " + _opt(t))] if top_by else [(f, _opt(t) + " ")]
        out.append({"kind": "whole", "ins": ins, "toggle": t, "note": f"whole proof: {_opt(t)}", "w": 10 ** 6})
    if re.search(r"set_option\s+" + SU + r"\b", code):
        return out
    steps = _top_steps(body, mask, f + 2) if top_by else []
    # step (one top-level step): its own `set_option ... in` line at the block column, the step's lines indented two more (the inner
    # tactic block then ends at the next step, whose column is smaller), heaviest steps first
    st = [(_weight(code[s:e]), -k, s, e, c) for k, (s, e, c) in enumerate(steps)]
    st = [x for x in st if x[0] > 0 and len(steps) > 1]
    st.sort(reverse=True)
    for w, nk, s, e, col in st[:K_STEP]:
        ls = AH._line_start(body, s)
        if s - ls != col or body[ls:s].strip():
            continue                      # the step does not start its own line (the first step on the `by` line)
        seg = body[ls:e]
        core = seg.rstrip(" \t\n")
        reind = "\n".join(("  " + ln) if ln.strip() else ln for ln in core.split("\n"))
        first_line = body[s:AH._line_end(body, s)].strip()
        out.append({"kind": "step", "ins": [(ls, ls + len(core), " " * col + _opt(SU) + "\n" + reind)], "toggle": SU, "w": w,
                    "note": f"step {-nk + 1}/{len(steps)}: {first_line[:60]}"})
    # nested `by` (that block only)
    nb = []
    for m in _BY_RE.finditer(body):
        p = m.start()
        if mask[p] or (top_by and p == f):
            continue
        # the block: to the end of the line, plus following lines indented deeper than the line holding the `by`
        ls = AH._line_start(body, p)
        ind = AH._indent_at(body, ls)
        e = AH._line_end(body, p)
        while e < len(body):
            nls = e + 1
            nle = AH._line_end(body, nls)
            if nls < len(body) and AH._indent_at(body, nls) > ind and nle > nls + AH._indent_at(body, nls):
                e = nle
            elif nls < len(body) and nle == nls + AH._indent_at(body, nls):
                e = nle
            else:
                break
        w = _weight(code[m.end():e])
        if w > 0:
            nb.append((w, -p, m.end()))
    nb.sort(reverse=True)
    for w, np_, end in nb[:K_BY]:
        out.append({"kind": "nested", "ins": [(end, " " + _opt(SU))], "toggle": SU, "w": w,
                    "note": f"nested by at {-np_}: {body[-np_:AH._line_end(body, -np_)].strip()[:60]}"})
    # suffix (a line before step k: steps k.. end), the heaviest tails first, never the first step (that is the whole form)
    sf = []
    for k in range(1, len(steps)):
        s = steps[k][0]
        sf.append((_weight(code[s:steps[-1][1]]) * 10 // (len(steps) - k + 1), -k, s, steps[k][2]))
    sf.sort(reverse=True)
    for w, nk, s, col in sf[:K_SUFFIX]:
        if w <= 0 or -nk == len(steps) - 1:   # the last step's suffix is its step form
            continue
        ls = AH._line_start(body, s)
        if s - ls != col or body[ls:s].strip():
            continue                      # the step does not start its own line
        out.append({"kind": "suffix", "ins": [(ls, " " * col + _opt(SU) + "\n")], "toggle": SU, "w": w,
                    "note": f"steps {-nk + 1}..{len(steps)}"})
    return out


def _cand(head: str, body: str, site_list: list[dict], op: str, note: str) -> dict:
    ins = [x for s in site_list for x in s["ins"]]
    nb = _insert(body, ins)
    return {"op": op, "decl": _decl(head, nb), "body": nb, "note": note[:160],
            "dtok": count_tokens(nb) - count_tokens(body)}


def pure_candidates(proof: str, statement: str) -> list[dict]:
    body = split_declaration(proof, statement)
    if body is None:
        return []
    out, seen = [], {proof.rstrip()}
    head = proof[:len(proof) - len(body)]
    for s in _sites(body):
        c = _cand(head, body, [s], f"{FAMILY}:{s['kind']}" + ("" if s["toggle"] == SU else ":" + s["toggle"].split(".")[-1]),
                  s["note"])
        c["site"] = s
        if c["decl"].rstrip() not in seen:
            seen.add(c["decl"].rstrip()); out.append(c)
    return out


def has_sites(proof: str, statement: str) -> bool:
    body = split_declaration(proof, statement)
    if body is None or AH._renamed_decl(statement, body, 0) is None:
        return False
    return bool(pure_candidates(proof, statement))


def _screen_per_file(ctx: dict) -> int:
    return AH._screen_budget(ctx)


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    """Batch heartbeat screen of the pure candidates (copy 0 = the input). Returns ctx + {"hb_smartunfold_for", "hb_smartunfold_cands",
    "hb_smartunfold_screen"}; on no usable screen the ctx comes back without them (candidates() then proposes the whole form only)."""
    ctx = dict(ctx or {})
    body0 = split_declaration(proof, statement)
    if body0 is None or AH._renamed_decl(statement, body0, 0) is None:
        return ctx
    pool = pure_candidates(proof, statement)
    if not pool:
        return ctx
    head = proof[:len(proof) - len(body0)]
    say = log or (lambda *a: None)
    vs = versions or (None,)
    exchange = ctx.get("exchange")
    per_file = _screen_per_file(ctx)
    cs = ctx.get("compile_s")
    max_files = 1 if isinstance(cs, (int, float)) and float(cs) > SLOW_COMPILE_S else MAX_SCREEN_FILES
    pool = pool[:(per_file - 1) * max_files]
    rows: list[tuple[dict, dict]] = []   # (candidate, {"ok", "hb"})
    ctl_hb = None
    mode = None
    for f_idx in range(0, len(pool), per_file - 1):
        chunk = pool[f_idx:f_idx + per_file - 1]
        txt = AH._screen_text(statement, [body0] + [c["body"] for c in chunk])
        if txt is None:
            break
        r = run(txt, vs[0])
        rd = AH._parse_screen(getattr(r, "messages", None), len(chunk) + 1)
        ctl = rd.get(0) or {"ok": False}
        if not ctl.get("ok"):
            break
        mode = "eval_hb"
        ctl_hb = int(ctl["hb"]) if ctl_hb is None else min(ctl_hb, int(ctl["hb"]))
        rows += [(c, rd.get(k) or {"ok": False}) for k, c in enumerate(chunk, 1)]
    if mode is None:
        built = AH._plain_check_text(statement, [body0] + [c["body"] for c in pool[:AH.MAX_PLAIN_VARIANTS - 1]])
        if built is not None:
            ptxt, spans = built
            r2 = run(ptxt, vs[0])
            rd2 = AH._parse_plain_check(getattr(r2, "messages", None), spans)
            ctl2 = rd2.get(0) or {"ok": False}
            if ctl2.get("ok") and isinstance(ctl2.get("hb"), int):
                mode, ctl_hb = "plain_hb", int(ctl2["hb"])
                rows = [(c, rd2.get(k) or {"ok": False}) for k, c in enumerate(pool[:AH.MAX_PLAIN_VARIANTS - 1], 1)]
    if mode is None:
        say(f"{FAMILY}: no usable screen ({len(pool)} candidates); whole form only")
        return ctx
    scored = []
    screen = []
    for c, rk in rows:
        ok = bool(rk.get("ok")) and isinstance(rk.get("hb"), int)
        pr = AH._predicted(ctl_hb, c["dtok"], int(rk["hb"]), exchange) if ok else None
        screen.append({"op": c["op"], "note": c["note"][:80], "ok": ok, "hb": rk.get("hb"), "dtok": c["dtok"],
                       "pred": None if pr is None else round(pr, 1)})
        if ok and pr > 0:
            scored.append((pr, len(scored), c))
    scored.sort(key=lambda x: (-x[0], x[1]))
    winners = [c for _, _, c in scored]
    out, seen = [], {proof.rstrip()}
    for c in winners:
        if c["decl"].rstrip() not in seen:
            seen.add(c["decl"].rstrip()); out.append({"op": c["op"], "decl": c["decl"], "note": c["note"]})
    whole = [c["site"] for c in winners if c["site"]["kind"] == "whole"]
    if len(whole) >= 2:   # stack every winning whole-proof toggle (each insertion at the same point; order = screen rank)
        ins_pos = whole[0]["ins"][0][0]
        txt = "".join(s["ins"][0][1] for s in whole) if all(s["ins"][0][0] == ins_pos for s in whole) else None
        if txt is not None:
            stk = _cand(head, body0, [{"ins": [(ins_pos, txt)]}], f"{FAMILY}:whole_stack", "whole stack: " + " + ".join(
                s["toggle"].split(".")[-1] for s in whole))
            if stk["decl"].rstrip() not in seen:
                seen.add(stk["decl"].rstrip()); out.insert(1, {"op": stk["op"], "decl": stk["decl"], "note": stk["note"]})
    local = [c["site"] for c in winners if c["site"]["kind"] in ("step", "nested")]
    uniq: list[dict] = []
    for s_ in local:   # greedy by screen rank: an edit overlapping a kept one (a nested `by` inside a re-indented step) is skipped
        if not any(_overlap(s_["ins"][0], u["ins"][0]) for u in uniq):
            uniq.append(s_)
    if len(uniq) >= 2:
        un = _cand(head, body0, uniq, f"{FAMILY}:union", f"union of {len(uniq)} step/nested insertions")
        if un["decl"].rstrip() not in seen:
            seen.add(un["decl"].rstrip()); out.append({"op": un["op"], "decl": un["decl"], "note": un["note"]})
    best = min((x["hb"] for x in screen if x["ok"]), default=None)
    say(f"{FAMILY}: screen {mode} ctl {ctl_hb} hb, {len(screen)} copies ({sum(x['ok'] for x in screen)} ok), best {best} hb, "
        f"{len(winners)} predicted winners")
    if stats is not None:
        stats[f"{FAMILY}_mode"] = mode
        stats[f"{FAMILY}_winners"] = len(out)
    ctx[f"{FAMILY}_for"] = _key(proof)
    ctx[f"{FAMILY}_cands"] = out
    ctx[f"{FAMILY}_screen"] = {"ctl_hb": ctl_hb, "mode": mode, "copies": screen}
    return ctx


def candidates(proof: str, statement: str, *, exchange=None, max_per_op: int | None = None, ctx=None) -> list[dict]:
    ctx = ctx or {}
    if ctx.get(f"{FAMILY}_for") == _key(proof) and f"{FAMILY}_cands" in ctx:
        out = list(ctx[f"{FAMILY}_cands"])
    else:   # no screen: the whole-proof smartUnfolding form only (one reading)
        out = [{"op": c["op"], "decl": c["decl"], "note": c["note"]} for c in pure_candidates(proof, statement)
               if c["site"]["kind"] == "whole" and c["site"]["toggle"] == SU][:1]
    return out if max_per_op is None else out[:max_per_op]
