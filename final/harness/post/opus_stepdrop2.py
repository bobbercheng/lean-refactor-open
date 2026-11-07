#!/usr/bin/env python3
"""Op "opus_stepdrop2" (gl2-opus stepdrop v0.7) of the open post-step (gap lane opus, 2026-11-04): delete SCAFFOLDING STEPS (whole multi-line steps, chiefly
`have h : T := by ..` blocks and the cleanup steps around them) that the proof's own later closers do not need, keyed on Lean's feedback.

Mechanism (the gap): the open proofs carry about 2.7x as many multi-line non-final steps as the closed ones (open_r2post 169 on the 30
measurable rows, closed_r1post 62; 13.6k vs 2.9k tokens): intermediate facts proved in a `have` block and handed to a closer that can
often find (or does not need) them, `simp at h` / `norm_num at h` preparations before `simp_all` / `omega` / `linarith`, and so on.
The open package's sweep deletes single-line standalone tactics one at a time; nothing deletes a multi-line step, and nothing deletes a
named `have` together with its mentions in later hint lists.

  parse     every tactic block of the body (the top block and each nested `by` / `=>` / `·` block: opus_goalmerge.find_blocks).
  sites     each NON-FINAL step of a block (the final one closes the block's goals) whose head is not a goal-shaping or binding
            tactic (intro / cases / induction / constructor / refine / apply / exact / use / bullets / case arms / ...).
            - a step that binds names (`have h`, `obtain ⟨a, b⟩`, `set x`, `let x`): deleted only when every later mention of each name
              is a whole item of a bracket hint list (`simp [h, ..]`, `linarith [h]`, `grind [h]`); those items are deleted with it (an
              emptied list goes with its brackets).
            - an anonymous `have :` / `have := ..`: deleted when `this` is not mentioned later.
            - other steps (`simp at h`, `norm_num`, `rw [..] at h`, `show`, `change`, ...): deleted as they are.
  query     (<= 2 compiles, primary pin) the d4_measure one-file screen (plain renamed copies when the file has no meta library) of the
            single deletions (most tokens saved first), then pairs of adjacent steps and tail runs (steps k..n-2 of a block, the
            final step left to close from step k's state), and "final step alone" (an automation closer that is the last step of
            its block given the block's opening goal) (<= 2 x 15, 3 x 15 for a fast row); then (1 compile) the union of the non-overlapping screened-ok
            deletions, when there are >= 2.
            Union variants (one compile, all in one file): by predicted gain, singles only, predicted gainers only.
  candidates the screened-ok unions first (by predicted gain), then the screened singles / pairs / runs by predicted gain.
Pure text + Lean's feedback; no table, no row name, no lemma list: a candidate is the proof with steps (and hint items) removed. The
post-step's gate decides (every pin, paired re-reading, audit)."""

# provenance: research lane gaplane2-opus (worktree lra-gl2-opus), commit 76c3883, ported into open-post-v5-lanes (2026-11-04) as opus_stepdrop2 (renamed: open-post-v3 already has a module opus_stepdrop; only its op/family names changed)
from __future__ import annotations

import re, sys, zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from harness.post.opus_goalmerge import find_blocks, join_bullets, plain_text, parse_plain  # noqa: E402

FAMILY = "opus_stepdrop2"
SCREEN_N = 15
SCREEN_CHUNKS = 2
EXTRA_CHUNKS = 2    # v0.7: more chunks while the screen finds deletions
FAST_S = 20.0       # an input that compiles within this many seconds gets one more screen chunk
# heads whose deletion changes the goal structure or binds what later steps need: never deleted
KEEP_HEADS = {
    "rintro", "cases", "cases'", "rcases", "induction", "induction'", "constructor", "refine", "refine'", "apply",
    "exact", "use", "exists", "existsi", "by_cases", "split", "split_ifs", "by_contra", "by_contra!", "contrapose", "contrapose!", "ext",
    "funext", "congr", "calc", "match", "fun", "·", "case", "case'", "next", "|", "left", "right", "exfalso", "trans", "symm",
    "obtain'", "next", "on_goal", "pick_goal", "swap", "rotate_left", "rotate_right", "all_goals", "any_goals", "focus",
    "unhygienic", "classical", "suffices", "wlog", "induction_on", "fin_cases", "interval_cases", "match_target", "generalize", "revert",
    "specialize", "exacts", "constructorm", "rcases'", "nofun", "nomatch", "omega", "linarith", "nlinarith", "decide", "rfl",
    "simp_all", "grind", "aesop", "tauto", "trivial", "assumption", "contradiction", "positivity", "ring", "field_simp", "norm_num!",
    "absurd", "exact_mod_cast", "simpa", "first", "try", "repeat", "iterate", "conv",
}
STRONG = {"omega", "simp_all", "grind", "aesop", "decide", "tauto", "linarith", "nlinarith", "norm_num", "simp", "positivity", "fun_prop",
          "continuity", "measurability", "trivial", "simpa", "exact?", "bv_decide", "polyrith", "itauto", "cutsat", "lia"}
BINDERS = ("have", "haveI", "obtain", "set", "let", "letI")
SHAPERS = ("intro", "intros", "rename_i", "clear", "subst")   # v0.5: deleted when the names they introduce are not mentioned later
IDENT = r"[A-Za-z_À-ɏͰ-Ͽἀ-῿][\w'!?À-ɏͰ-Ͽἀ-῿₀-₉ₐ-ₜ]*"


def _head(step: str) -> str:
    s = step.strip()
    m = re.match(r"\S+", s)
    return m.group(0) if m else ""


def bound_names(step: str) -> list[str] | None:
    """Names bound by a binder step ([] for an anonymous `have`), None when the binder form is not understood."""
    s = step.strip()
    h = _head(s)
    if h in ("have", "haveI", "set", "let", "letI"):
        rest = s[len(h):].lstrip()
        if rest.startswith((":", ":=")):
            return []
        m = re.match(rf"({IDENT})\s*(?::|:=|\s)", rest)
        if not m:
            return None
        names = [m.group(1)]
        if h == "set":
            w = re.search(rf"\bwith\s+({IDENT})\s*$", s.split("\n")[0])
            if w:
                names.append(w.group(1))
        return names
    if h == "obtain":
        m = re.match(r"obtain\s+(⟨.*?⟩|" + IDENT + r")\s*(?::|:=)", s, re.S)
        if not m:
            return None
        return [x for x in re.findall(IDENT, m.group(1)) if x not in ("rfl", "_")]
    return None


def _list_items(lines: list[str], names: list[str], start: int, end: int | None = None, skip=()):
    """Edits {line index: new text} removing every mention of `names` in lines[start:end] (the binder's scope; lines in `skip` are
    deleted anyway) when each is a whole item of a bracket list (optionally `←`-prefixed); None when some mention is not such an item."""
    edits = {}
    pat = re.compile(rf"(?<![\w.']){'|'.join(re.escape(n) for n in names)}(?![\w'])")
    for j in range(start, len(lines) if end is None else end):
        if j in skip:
            continue
        l = lines[j]
        if not pat.search(l):
            continue
        new = l
        # remove `name` items from bracket lists: `[a, h, b]` -> `[a, b]`, `[h]` -> dropped with its leading space
        for n in names:
            item = rf"(?:←\s*)?{re.escape(n)}"
            new = re.sub(rf"\s*\[\s*{item}\s*\]", "", new)
            new = re.sub(rf"\[\s*{item}\s*,\s*", "[", new)
            new = re.sub(rf",\s*{item}\s*(?=[,\]])", "", new)
        if pat.search(new):
            return None
        edits[j] = new
    return edits


def step_edits(lines: list[str], a: int, b: int, hi: int, skip=()):
    """(edits, head) deleting the step lines[a:b] of a block ending at hi (plus its names' hint items), or None when not deletable."""
    step = "\n".join(lines[a:b])
    h = _head(step)
    if h in KEEP_HEADS or not h or h.startswith(("·", "|", "<;>")):
        return None
    edits = {j: None for j in range(a, b)}
    if h in SHAPERS:
        if "\n" in step.strip():
            return None
        if h in ("intro", "intros", "rename_i"):
            names = [x for x in re.findall(IDENT, step.strip()[len(h):]) if x != "_"]
            rest = "\n".join(lines[j] for j in range(b, hi) if j not in skip)
            if any(re.search(rf"(?<![\w.']){re.escape(x)}(?![\w'])", rest) for x in names):
                return None
    elif h in BINDERS:
        names = bound_names(step)
        if names is None:
            return None
        if not names:
            if re.search(r"(?<![\w.'])this(?![\w'])", "\n".join(lines[j] for j in range(b, hi) if j not in skip)):
                return None
        else:
            more = _list_items(lines, names, b, hi, skip)
            if more is None:
                return None
            edits.update(more)
    return edits, h


def sites(body: str, pairs: bool = True):
    """(lines, [(edits, note)]) where edits = {line index: new text or None (deleted)} over lines = find_blocks(body)[0]: each
    deletable non-final step alone, then (pairs) each two adjacent deletable non-final steps together (a binder's names may be
    mentioned in the other deleted step)."""
    fb = find_blocks(body) if body is not None else None
    if not fb:
        return None, []
    lines, blocks = fb
    out, seen = [], set()
    for bi, (depth, lo, hi, col, st) in enumerate(blocks):
        if len(st) < 2:
            continue
        for k, (a, b) in enumerate(st[:-1]):
            if (a, b) in seen:
                continue
            r = step_edits(lines, a, b, hi)
            if r is None:
                continue
            edits, h = r
            seen.add((a, b))
            more = sum(1 for v in edits.values() if v is not None)
            out.append((edits, f"block {bi} step {k} ({h}, {b - a} lines)" + (f" + {more} hint line(s)" if more else "")))
        if pairs:
            for k in range(len(st) - 2):
                (a1, b1), (a2, b2) = st[k], st[k + 1]
                r1 = step_edits(lines, a1, b1, hi, skip=set(range(a2, b2)))
                r2 = step_edits(lines, a2, b2, hi) if r1 else None
                if not (r1 and r2):
                    continue
                e = dict(r2[0])
                e.update({j: v for j, v in r1[0].items() if j not in range(a2, b2)})
                if any(j in r2[0] and r2[0][j] is not None and v is not None for j, v in r1[0].items()):
                    continue   # both rewrite one hint line: skip (rare)
                out.append((e, f"[pair] block {bi} steps {k},{k + 1} ({r1[1]}, {r2[1]})"))
        if pairs:   # tail runs: steps k..n-2 (>= 3 of them) deleted, the block's final step left to close from step k's state
            n = len(st)
            for k in range(n - 4, -1, -1):
                run_lines = set(range(st[k][0], st[n - 2][1]))
                e, ok = {}, True
                for (a, b) in st[k:n - 1]:
                    r = step_edits(lines, a, b, hi, skip=run_lines)
                    if r is None:
                        ok = False
                        break
                    for j, v in r[0].items():
                        if j in e and e[j] is not None and v is not None and e[j] != v:
                            ok = False
                        if j not in e or v is None:
                            e[j] = v
                if not ok:
                    break   # a longer run contains the same blocker
                out.append((e, f"[pair] block {bi} tail run steps {k}..{n - 2}"))
            # final step alone: every earlier step of the block deleted, goal shapers too, when the final step is an automation
            # closer that works on the block's opening goal (it introduces / splits itself) and mentions no name bound in the block
            fa, fb_ = st[-1]
            fin = "\n".join(lines[fa:fb_]).strip()
            if n >= 2 and _head(fin) in STRONG and not any(lines[j].lstrip().startswith(("·", "|", "case ", "next ")) for j in range(st[0][0], fa)):
                pre = "\n".join(lines[st[0][0]:fa])
                bound = set(re.findall(IDENT, " ".join(re.findall(r"(?:intro|intros|rintro|obtain|rcases|cases|have|set|let|with)\s+([^:=\n]*)", pre))))
                if not any(re.search(rf"(?<![\w.']){re.escape(x)}(?![\w'])", fin) for x in bound if x not in ("_", "rfl", "with", "at")):
                    e = {j: None for j in range(st[0][0], fa)}
                    out.append((e, f"[pair] block {bi} final step alone ({_head(fin)})"))
    return lines, out


def apply_edits(lines: list[str], edits: dict) -> str:
    new = []
    for j, l in enumerate(lines):
        if j in edits:
            if edits[j] is None:
                continue
            new.append(edits[j])
        else:
            new.append(l)
    return join_bullets("\n".join(new)) + "\n"


def site_bodies(body: str, pairs: bool = True):
    """(lines, [(edits, new body, saved, note)]): singles most tokens saved first, then pairs (only proper savings)."""
    lines, ss = sites(body, pairs)
    if not ss:
        return lines, []
    t0 = count_tokens(body)
    out = []
    for edits, note in ss:
        nb = apply_edits(lines, edits)
        sv = t0 - count_tokens(nb)
        if sv > 0:
            out.append((edits, nb, sv, note))
    out.sort(key=lambda x: (0 if "[pair]" not in x[3] else 1 if "final step alone" in x[3] else 2, -x[2]))
    return lines, out


def union(lines: list[str], picks: list[dict]):
    """The edits of picks (best first) that touch disjoint lines, merged."""
    used, merged, n = set(), {}, 0
    for e in picks:
        if used & set(e):
            continue
        used |= set(e)
        merged.update(e)
        n += 1
    return merged, n


# ------------------------------------------------------------------------------------------------------------------------------ op API
def has_sites(proof: str, statement: str) -> bool:
    try:
        body = split_declaration(proof, statement)
        return bool(site_bodies(body)[1]) if body is not None else False
    except Exception:  # noqa: BLE001
        return False


def _screen(statement: str, body: str, bodies: list[str], run, version, hb_ok):
    """[{ok, hb}] per body (None for a body without a reading), ctl, hb_ok."""
    rd, ctl = None, None
    if hb_ok is not False:
        txt = MS.text(statement, [body] + bodies)
        if txt is not None:
            rr = run(txt, version)
            rd = MS.parse(getattr(rr, "messages", None), len(bodies) + 1)
            hb_ok = bool((rd.get(0) or {}).get("ok"))
            if hb_ok:
                ctl = rd.pop(0)
                rd = {k - 1: v for k, v in rd.items()}
            else:
                rd = None
    if rd is None:
        txt = plain_text(statement, bodies)
        if txt is None:
            return [None] * len(bodies), None, hb_ok
        rr = run(txt, version)
        rd = parse_plain(getattr(rr, "messages", None), len(bodies))
    return [rd.get(j) for j in range(len(bodies))], ctl, hb_ok


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict | None:
    try:
        return _query(proof, statement, run, versions=versions, ctx=ctx, log=log)
    except Exception as e:  # noqa: BLE001  (a failure proposes nothing)
        if log:
            log(f"stepdrop: query failed ({type(e).__name__}: {str(e)[:120]})")
        return None


def _query(proof: str, statement: str, run, *, versions=None, ctx=None, log=None) -> dict | None:
    body = split_declaration(proof, statement)
    if body is None:
        return None
    lines, sb = site_bodies(body)
    if not sb:
        return None
    vs = list(versions or [None])
    exchange = (ctx or {}).get("exchange")
    t0 = count_tokens(body)
    screened, hb_ok, ctl0 = [], None, None
    cs = (ctx or {}).get("compile_s")
    nchunks = SCREEN_CHUNKS + (1 if isinstance(cs, (int, float)) and cs <= FAST_S else 0)
    if len(sb) > nchunks * SCREEN_N:   # v0.6: the size-ordered chunks, then ONE extra chunk: the remaining sites rotated by the
        rest = sb[nchunks * SCREEN_N:]     # proof's hash (a later pass, on a new proof, screens other sites, not the same failing ones)
        off = zlib.crc32(body.encode()) % len(rest)
        sb = sb[:nchunks * SCREEN_N] + rest[off:] + rest[:off]
        nchunks += 1
    f = 0
    while True:   # v0.7: a row whose screen keeps finding deletions gets up to EXTRA_CHUNKS more chunks (rows with many sites)
        if f >= nchunks + (EXTRA_CHUNKS if screened else 0):
            break
        chunk = sb[f * SCREEN_N:(f + 1) * SCREEN_N]
        f += 1
        if not chunk:
            break
        rds, ctl, hb_ok = _screen(statement, body, [x[1] for x in chunk], run, vs[0], hb_ok)
        ctl0 = ctl0 or ctl
        for (edits, nb, sv, note), x in zip(chunk, rds):
            if x and x.get("ok"):
                pred = MS.predicted(ctl, body, nb, x, exchange) if ctl else float(sv)
                screened.append({"variant": f"{FAMILY}:{'run' if '[pair]' in note else 'single'}", "body": nb, "edits": edits, "note": note, "pred": pred, "hb": x.get("hb")})
    unions = []
    if len(screened) >= 2:
        def pv(x):
            return x["pred"] if x["pred"] is not None else -1e18
        picks = sorted(screened, key=lambda x: -pv(x))
        variants = []   # union variants (all in one screen file): by predicted gain; singles only; predicted gainers only
        for tag, sel in (("all", picks), ("singles", [p for p in picks if p["variant"].endswith(":single")]),
                         ("gainers", [p for p in picks if pv(p) > 0])):
            merged, n = union(lines, [p["edits"] for p in sel])
            if n >= 2:
                nb = apply_edits(lines, merged)
                if nb not in [v[1] for v in variants]:
                    variants.append((tag, nb, n))
        if variants:
            rds, ctl, hb_ok = _screen(statement, body, [v[1] for v in variants], run, vs[0], hb_ok)
            for (tag, nb, n), x in zip(variants, rds):
                if x and x.get("ok"):
                    pred = MS.predicted(ctl, body, nb, x, exchange) if ctl else float(t0 - count_tokens(nb))
                    unions.append({"variant": f"{FAMILY}:union", "body": nb, "note": f"union ({tag}) of {n} screened deletions",
                                   "pred": pred, "hb": x.get("hb")})
    if log:
        log(f"stepdrop: sites={len(sb)} screened_ok={len(screened)} unions_ok={len(unions)}")
    for s in screened:
        s.pop("edits", None)
    return {"stepdrop": {"screened": screened, "unions": unions, "key": K.proof_key(proof)}}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    try:
        q = (ctx or {}).get("stepdrop")
        if not q or q.get("key") != K.proof_key(proof):
            return []
        sc = sorted(q.get("screened") or [], key=lambda x: -(x["pred"] if x["pred"] is not None else -1e18))
        un = sorted(q.get("unions") or [], key=lambda x: -(x["pred"] if x["pred"] is not None else -1e18))
        sc = un + sc
        out = []
        for x in sc:
            out.append({"op": x["variant"], "decl": statement.rstrip() + " :=" + x["body"].rstrip(), "note": f"{x['note']}; pred {x['pred']}"})
        return out[: (max_per_op or 8)]
    except Exception:  # noqa: BLE001
        return []
