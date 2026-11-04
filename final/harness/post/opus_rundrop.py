#!/usr/bin/env python3
"""Structural op "opus_rundrop" of the open post-step (gap lane opus, pass 2, 2026-11-03): drop a RUN of consecutive steps of a tactic
block (any kind of step: have / obtain / intro / cases / simp / rw / ...), the block's last step (its closer) kept. Lean decides.

Gap mechanism: the open proofs carry about 2.4x the `have` count and 2x the tactic lines of the closed ones (MEASURED on the bundle
sets, see gaplane/reports/opus_rundrop.md). Much of it is scaffolding that the block's own closer does not need: a chain such as
`have h := f x` / `simp at h` / `obtain ⟨a, b⟩ := h` before a `simp_all` / `omega` / `grind` / `aesop` closer. The single-step drops
(opus_stepdrop, opus_scaffold, lint_delete's delsearch) cannot remove such a chain: each step alone is needed by the next one, only the
whole chain is unneeded. rundrop tries the chains.

  block     the indentation parse of opus_hoist.parse: steps of one block = its own-line tactic starts (a step's continuation and
            nested lines included); a bullet line `· ...` is one step of the outer block (never inside a run); `case` / `next` /
            `| tag =>` / `<;>`-continued steps are never inside a run either.
  runs      [i..j] with j < the block's last step:
              suffix   j = last - 1: "the closer alone, from step i on" (all i),
              window   j - i + 1 in {2, 3} anywhere before the closer,
              single   i = j for the non-preparation steps (binding steps: have / obtain / intro / rcases / cases / ...; the
                       preparation ones are opus_stepdrop's).
            only runs that save tokens and (v4, DEADNAMES) whose bound names (have / obtain / intro / rcases ... patterns, `this`)
            are not written again in the rest of the block: such a run cannot compile (pass 2: ~1300 screened runs, 11 OK, every OK
            one passes this filter); it removes ~65% of the runs on the measurable rows, so most rows fit in one screen.
            At most MAX_SCREEN, the largest saving first within each kind, kinds interleaved
            (v2: single, suffix, single, window; v1 was suffix, window, single: its only wins were singles).
  generate  rundrop:joint  the screen's OK runs, greedily the largest first, non-overlapping and not in one block's adjacent
                           (a joint of overlapping or touching runs is a different run: not proposed unless screened)
            rundrop:run    one run dropped (screen order: predicted gain first)
  screen    query(): the runs in up to MAX_FILES one-file screens (harness/post/opus_screen.py: measured, else plain); only the
            screen's OK runs are proposed.
  unchecked a proof with `debug.skipKernelTC` has no site (see opus_stepdrop: kernel-unchecked closers judge nothing).
Pure text plus the row's own environment. No row name, table or proof text."""
from __future__ import annotations

# provenance: research lane gaplane-opus (worktree lra-gl-opus), commit ef7dde5, ported unchanged into open-post-v3 (2026-11-04)

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.post import d4_kit as K  # noqa: E402
from harness.post import opus_screen as SC  # noqa: E402
from harness.post.opus_hoist import parse  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "opus_rundrop"
MAX_PER_OP = 16
MAX_FILES = 4      # v3: up to 4 screen files (v1/v2: 2); rows with few runs still use 1-2
MAX_SCREEN = 56    # v3: 56 runs (v1/v2: 28)
WINDOWS = (2, 3)
DEADNAMES = True   # v4: never screen a run whose bound names are written again later in the block
PREP = re.compile(r"^(?:simp_all|simp|dsimp|norm_num|unfold|delta|rw|rewrite|erw|rwa|push_cast|norm_cast|ring_nf|field_simp|clear|"
                  r"subst_vars|subst|show|change|beta_reduce|push_neg|specialize|replace|zeta_reduce|simp_rw|conv_lhs|conv_rhs|"
                  r"generalize|set_option)\b(?![\w'])")
NOSTEP = re.compile(r"^(?:·|case\b|case'|next\b|\||<;>|on_goal\b|pick_goal\b|swap\b|rotate_left\b|rotate_right\b|all_goals\b|"
                    r"any_goals\b|focus\b|\})")
COMMENT = re.compile(r"--|/-")


def blocks(body: str) -> list[list[tuple[int, int, str]]]:
    """Per block (in order): its steps [(first line, end line exclusive, first-line text)]; the block's last step closes it."""
    L = body.split("\n")
    recs = parse(body)
    by_blk: dict = {}
    for k, r in enumerate(recs):
        if not r["start"] or r["block"] < 0:
            continue
        e = k + 1
        d = _indent(L[r["i"]])
        while e < len(recs) and not (recs[e]["start"] and _indent(L[recs[e]["i"]]) <= d):
            e += 1
        end = recs[e]["i"] if e < len(recs) else len(L)
        last = end - 1
        while last > r["i"] and not L[last].strip():
            last -= 1
        txt = "·" if r["bullet"] else L[r["i"]].strip()
        by_blk.setdefault(r["block"], []).append((r["i"], last + 1, txt))
    return [by_blk[b] for b in sorted(by_blk, key=lambda b: by_blk[b][0][0])]


def _indent(ln: str) -> int:
    return len(ln) - len(ln.lstrip(" "))


def _movable(step: tuple[int, int, str], L: list[str]) -> bool:
    t = step[2]
    if NOSTEP.match(t):
        return False
    if any(COMMENT.search(L[i]) for i in range(step[0], step[1])):
        return False
    return True


_ID = r"[^\W\d][\w'!?₀-₉ₐ-ₜ]*"
_KW = {"rfl", "_", "this", "fun", "with", "at", "using", "only", "by", "from", "if", "then", "else", "do", "in", "match", "show"}
_BINDERS = re.compile(r"^(?:have|haveI|have'|let|set|obtain|rcases|rintro|intro|intros|generalize|by_cases|choose|rename_i|"
                      r"cases'|induction'|lift|by_contra|by_contra!|contrapose!|push_neg|replace|specialize)\b")


def _names(text: str) -> set[str]:
    return {m.group(0) for m in re.finditer(r"(?<![\w.'])" + _ID, text)} - _KW


def bound(t: str) -> set[str]:
    """Names (incl. `this`) that the step whose first line is `t` (stripped) brings into scope for the LATER steps of its block.
    `replace` / `specialize` re-bind an existing name (dropping them leaves the old one): nothing. Unknown steps: nothing."""
    m = _BINDERS.match(t)
    if not m:
        return set()
    kw = m.group(0)
    rest = t[len(kw):].strip()
    if kw in ("replace", "specialize", "push_neg"):
        return set()
    if kw in ("have", "haveI", "have'", "let", "set"):
        n = re.match(_ID, rest)
        if not n or rest.startswith(":") or n.group(0) in _KW:
            return {"this"} if kw.startswith("have") else set()
        out = {n.group(0)}
        w = re.search(r"\bwith\s+(" + _ID + ")", rest) if kw == "set" else None
        return out | ({w.group(1)} if w else set())
    if kw == "obtain":
        pat = rest.split(":=")[0]
        pat = re.split(r"\s:\s", pat)[0] if not pat.lstrip().startswith("(") else pat
        return _names(pat) or ({"this"} if pat.strip() == "" else set())
    if kw in ("rcases",):
        w = rest.split(" with ", 1)
        return _names(w[1]) if len(w) == 2 else set()
    if kw in ("cases'", "induction'"):
        w = rest.split(" with ", 1)
        return _names(w[1]) if len(w) == 2 else set()
    if kw in ("rintro", "intro", "intros", "rename_i", "by_contra", "by_contra!", "contrapose!"):
        return _names(rest.split(":")[0]) if kw != "rintro" else _names(rest)
    if kw == "by_cases":
        n = re.match(r"(" + _ID + r")\s*:", rest)
        return {n.group(1)} if n else {"h"}
    if kw == "generalize":
        a = rest.split(":", 1)
        out = _names(a[0]) if len(a) == 2 else set()
        e = rest.rsplit("=", 1)
        return out | (_names(e[1].split(" at ")[0]) if len(e) == 2 else set())
    if kw == "choose":
        return _names(rest.split(" using ")[0])
    if kw == "lift":
        w = rest.split(" with ", 1)
        return _names(w[1]) if len(w) == 2 else set()
    return set()


def live_after(L: list[str], steps, i: int, j: int) -> bool:
    """True when a name bound by steps i..j is written again in the rest of the block (steps j+1.. to the block's end: the kept
    closer included). Such a run cannot compile in practice (the name is gone): v4 does not screen it."""
    names: set = set()
    for k in range(i, j + 1):
        names |= bound(steps[k][2])
    if not names:
        return False
    rest = "\n".join(L[steps[j + 1][0]:steps[-1][1]])
    return any(re.search(r"(?<![\w.'])" + re.escape(n) + r"(?![\w'!?₀-₉])", rest) for n in names)


def runs(body: str) -> list[tuple[str, int, int, int]]:
    """[(kind, first line, end line exclusive, tokens saved)] ordered for the screen."""
    if SC.unchecked(body):
        return []
    L = body.split("\n")
    t0 = count_tokens(body)
    seen = set()
    kinds: dict = {"suffix": [], "window": [], "single": []}
    for steps in blocks(body):
        m = len(steps)
        if m < 2:
            continue
        mov = [_movable(s, L) for s in steps]
        for i in range(m - 1):
            for j in range(i, m - 1):
                if not all(mov[i:j + 1]):
                    break
                n = j - i + 1
                if j == m - 2:
                    kind = "suffix" if n >= 2 else ("single" if not PREP.match(steps[i][2]) else "suffix")
                elif n in WINDOWS:
                    kind = "window"
                elif n == 1 and not PREP.match(steps[i][2]):
                    kind = "single"
                else:
                    continue
                a, b = steps[i][0], steps[j][1]
                if (a, b) in seen or (DEADNAMES and live_after(L, steps, i, j)):
                    continue
                nb = _drop(L, [(a, b)])
                d = t0 - count_tokens(nb)
                if d <= 0:
                    continue
                seen.add((a, b))
                kinds[kind].append((kind, a, b, d))
    for k in kinds:
        kinds[k].sort(key=lambda x: (-x[3], x[1]))
    out = []
    order = [kinds["single"], kinds["suffix"], kinds["single"], kinds["window"]]   # v2: singles get half the screen
    while any(order) and len(out) < MAX_SCREEN:
        for q in order:
            if q and len(out) < MAX_SCREEN:
                out.append(q.pop(0))
    return out


def _drop(L: list[str], spans: list[tuple[int, int]]) -> str:
    gone = {i for a, b in spans for i in range(a, b)}
    return "\n".join(ln for i, ln in enumerate(L) if i not in gone)


def raw_candidates(body: str, ok: list | None = None) -> list[tuple[str, str, str]]:
    L = body.split("\n")
    rs = runs(body)
    bodies = [(r, _drop(L, [(r[1], r[2])])) for r in rs]
    if ok is None:
        return [("run", nb, f"{r[0]} run lines {r[1] + 1}-{r[2]} dropped, -{r[3]} tokens") for r, nb in bodies]
    okset = set(ok)
    good = [(r, nb) for r, nb in bodies if nb in okset]
    out = []
    keep: list = []
    for r, _ in sorted(good, key=lambda x: -x[0][3]):
        if all(r[2] < a or b < r[1] for _, a, b, _ in keep):   # neither overlapping nor touching
            keep.append(r)
    if len(keep) >= 2:
        out.append(("joint", _drop(L, [(a, b) for _, a, b, _ in keep]), f"{len(keep)} runs dropped"))
    out += [("run", nb, f"{r[0]} run lines {r[1] + 1}-{r[2]} dropped, -{r[3]} tokens") for r, nb in good]
    return out


def has_sites(proof: str, statement: str) -> bool:
    try:
        body = split_declaration(proof, statement)
        return bool(body) and bool(runs(body))
    except Exception:
        return False


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return []
        head, body = hb
        em = K.Emitter(proof, statement, head, body, int(max_per_op or MAX_PER_OP))
        scr = (ctx or {}).get("rundrop_screen") if (ctx or {}).get("rundrop_key") == K.proof_key(proof) else None
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
    """Up to MAX_FILES screen files over the runs; {} when nothing to screen."""
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return {}
        _, body = hb
        raws = raw_candidates(body)
        if not raws:
            return {}
        got = SC.screen(statement, body, [r[1] for r in raws], run, ctx, log=log, tag=FAMILY, max_files=MAX_FILES)
        if got is None:
            return {}
        return {"rundrop_key": K.proof_key(proof), "rundrop_screen": got}
    except Exception as e:  # never raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:200]}")
        return {}
