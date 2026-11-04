#!/usr/bin/env python3
"""v5_cse (post-step v5, branch open-post-v5-v5cse, 2026-11-04): generic common-subexpression sharing. A bracket-balanced parenthesised
subterm that occurs two or more times in a tactic proof is bound once by a new `have` step and each occurrence becomes the new name.

    has_sites(proof, statement) -> bool                                           (pure)
    query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None) -> dict
    candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None) -> [{"op", "decl", "note"}]   (pure; screened only)

  site      a `( ... )` group of the body (comments and strings masked, harness/post/spans._code) of at least MIN_TOKENS (5) scorer tokens
            whose whitespace-normalised text occurs m >= 2 times. Skipped: a group holding `by`, a `?` hole, a top-level `|` (an
            alternative pattern), a named argument `(x := v)`, a binder group `(x y : T)`, a monadic `(← e)`; an occurrence that
            overlaps a comment or a string. The body must be a `by` block (spans.parse).
  place     the tactic blocks of spans.parse (by blocks, case / next / bullet / alternative arms, have-by bodies): the innermost block
            whose one step, or several steps, hold all the occurrences; the binding goes in as a new step before the first of those
            steps (variant `have`). Variant `split` (occurrences in sibling blocks or later goals): before the nearest earlier split
            step of that block (spans.SPLIT: induction / cases / constructor / refine ?_ / ...). A placement is dropped when one of
            the term's free names (its identifiers' first components, the term's own λ binders excluded) is bound between the
            placement and the last occurrence (intro / rintro / obtain / rcases / cases .. with / `| .. =>` / next / case / fun / λ /
            ∀ / ∃ / ∑ / ∏ / have / let / set / generalize ...): the binding would then mean another thing, or nothing.
  edit      `have H := t'` (t' = the group without its outer parens; a group with a top-level cdot `·` keeps them: the cdot function)
            inserted at the block's column; each occurrence -> `H` (a blank added when it would glue to a neighbouring token). H is
            the first of H, H1, H2, ... that is not a word of the proof. Variant `anyg` (occurrences in two or more steps of the
            block: sibling goals of `next` / `case` / bullets / a flat goal list): `any_goals have H := t'` at the same place, so that
            each goal where t elaborates gets its own H (a hypothesis the split re-introduces per goal means another thing in each).
            Variant `set` (`set H := t'`, Mathlib): also replaces t in the goal and the hypotheses, so that a later rewrite / simp
            whose pattern now holds H still finds it (MEASURED: `rewrite` failed to find its pattern under `have` / `let`).
            Variant `let` (`let H := t'`): a value (or a function) bound
            by `have` is opaque to the defeq checks of exact / refine / apply / rfl (MEASURED on VM1, v3x2: `rfl` and `Finset.mem_filter`
            applications failed under `have`), so every site also gets a `let` copy, screened after the `have` copies. Maximal
            groups first: a group whose occurrences all sit inside the occurrences of a kept larger group is dropped unless it occurs
            more often. Only edits that save tokens (scorer.tokenize.count_tokens) are kept.
  screen    query(): ONE d4_measure file (harness/post/opus_screen.screen: measured, else plain): the incumbent the control, the
            greedy joint of disjoint sites (when there are two or more), one copy per site (largest saving first, MAX_SITES at most),
            then the `anyg`, `let` and `set` copies and the earlier placements, as many as the file's budget takes; a second file (only when two or more
            sites read up and the first joint did not, or did not hold them all) with the joint of the passing sites. When the stock
            screen does not read and harness/post/v4_rescreen is importable (post-step v4), the same copies go through its
            context-keeping copies (its trigger, then the screen under its fixed context); without it, nothing. At most 2 screen
            compiles per row and round (v4_rescreen's memoised trigger aside). Only the copies that read OK and predicted > 0 are
            proposed (best predicted first, MAX_PER_OP); the gate is unchanged.
  measured  VM1 2026-11-04, --ops v5_cse alone (3 compile slots, 4 rows at once, harness/post/v4_rescreen importable; commit with the
            `set` variant): on run 3's v3 pass-1 output 8 rows adopted, paired +2.80 row-points, stored mean 80.9703 -> 81.0165
            (+0.046); on the v3 two-pass snapshot output 10 rows, +3.35, 81.183 -> 81.2385 (+0.056). Without `set`: run 2 + v2 twice
            11 rows, +3.16, 80.8552 -> 80.9082. The `anyg` joint alone gave +1.45 to +1.53 on one row; `let` copies were the first
            adoption on 11 of 26 adopted rows and sit in most joints (`have` hides a value: rfl / defeq / omega fail); `set` added two
            rows (+0.13); one row's adoption needs v4_rescreen's context-keeping copies (+0.26). A second invocation on its own output
            adds nothing.
Model-free and deterministic; reads only the proof, the statement and the row's own environment (the screen compiles). No row name,
table or proof text."""
from __future__ import annotations

import importlib, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from harness.post import opus_screen as SC  # noqa: E402
from harness.post import spans as SP  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "v5_cse"
MIN_TOKENS = 5       # a shared group has at least this many scorer tokens (its parentheses included; spec 7: 5 adds groups used 3+ times)
MAX_SITES = 12       # single-site copies per screen file at most (largest saving first)
MAX_PER_OP = 4       # proposals per round (= open_post READS)
MAX_GROUPS = 64      # repeated groups examined per proof at most (largest static saving first)
NAMES = ("H", "H1", "H2", "H3", "H4", "H5", "H6", "H7", "H8", "H9", "Hc", "Hd")
VALUE_HEADS = ("exact", "refine", "refine'", "apply", "use", "exists")
KW_TEXT = {"anyhave": "any_goals have"}
_ID = r"(?:(?![λΠΣ])[^\W\d])(?:(?![λΠΣ])[\w'!?])*"   # Lean: λ / Π / Σ are never identifier letters
IDENT = re.compile(r"(?<![\w'!?.])" + _ID)
WORD = re.compile(_ID)
BY = re.compile(r"(?<![\w'.])by(?![\w'!?])")
HOLE = re.compile(r"(?<![\w'!?])\?")
NAMED_ARG = re.compile(r"\A\(\s*" + _ID + r"\s*:=")
BINDER_GROUP = re.compile(r"\A\(\s*" + _ID + r"(?:\s+" + _ID + r")*\s*:(?!=)")
# binder constructs whose names are read (an over-approximation: any word in the binder text counts)
_B_TERM = re.compile(r"(?:(?<![\w'.])fun(?![\w'])|λ|[∀∃∑∏⋃⋂⨆⨅∫Σ∮](?:ᶠ|!|'|⁻|₀)*)(.*?)(?:=>|↦|,)", re.S)
_B_ARROW = re.compile(r"(?:(?:^|\n)[ \t]*(?:·[ \t]*)?(?:next(?![\w'])|case'?(?![\w'])[ \t]+\S+)|\|(?!\|))([^|\n]*?)=>", re.S)
# keyword binders read to the end of their LOGICAL line (the line and the more indented lines below it: a long `intro` list wraps)
_B_LINE = re.compile(r"(?<![\w'.])(?:intro|intros|rintro|intro'|rintros|introv|rename_i|induction'|cases'|ext|ext1|funext|choose|peel|"
                     r"lift|filter_upwards|refine_lift|with)(?![\w'])")
# have-like steps: every word from the keyword to the first `:` (the name and its binders: `have h x (hx : p x) : ...`); none = `this`
_B_NAMED = re.compile(r"(?<![\w'.])(?:have|haveI|let|letI|set|replace|suffices|obtain|by_cases|by_contra!?|contrapose!?|generalize|wlog)"
                      r"(?![\w'])")
_B_GEN = re.compile(r"(?<![\w'.])generalize(?![\w'])[^\n]*?=[ \t]*(" + _ID + r")")
_B_SETB = re.compile(r"\{\s*(" + _ID + r")\s*(?::[^|}]*|∈[^|}]*)?\|(?!\|)")


# ------------------------------------------------------------------------------------------------------------------------------ pure
def _parens(code: str) -> list[tuple[int, int]]:
    """[(a, b)] of the balanced `( ... )` groups of the masked body (other bracket kinds kept balanced; a stray closer is ignored)."""
    st, out = [], []
    for i, ch in enumerate(code):
        if ch in SP.OPEN:
            st.append((ch, i))
        elif ch in SP.CLOSE:
            k = SP.CLOSE.index(ch)
            if st and SP.OPEN.index(st[-1][0]) == k:
                o, j = st.pop()
                if o == "(":
                    out.append((j, i + 1))
    return out


def _depth1(t: str):
    """Yield (i, ch) of the characters of group t (its outer parens included) at bracket depth 1 (inside the outer pair only)."""
    d = 0
    for i, ch in enumerate(t):
        if ch in SP.OPEN:
            d += 1
            continue
        if ch in SP.CLOSE:
            d -= 1
            continue
        if d == 1:
            yield i, ch


def has_cdot(t: str) -> bool:
    return any(ch == "·" for _, ch in _depth1(t))


def _top_bar(t: str) -> bool:
    s = "".join(ch for _, ch in _depth1(t))
    return bool(re.search(r"(?<![|])\|(?![|])", s))


def group_ok(t: str) -> bool:
    """The group's own text rules (module docstring, "site")."""
    if BY.search(t) or HOLE.search(t) or NAMED_ARG.match(t) or BINDER_GROUP.match(t) or _top_bar(t):
        return False
    if t[1:].lstrip().startswith("←"):
        return False
    return True


def own_binders(t: str) -> set:
    out = set()
    for m in _B_TERM.finditer(t):
        out |= set(WORD.findall(m.group(1)))
    return out


def free_names(t: str) -> set:
    """The first components of t's identifiers (not after a `.`), its own λ / fun / ∀ binders excluded."""
    return set(IDENT.findall(t)) - own_binders(t)


def _logical_end(text: str, i: int) -> int:
    """The end of the logical line holding offset i: its line and the following lines indented deeper than it (blank lines skipped)."""
    ls = text.rfind("\n", 0, i) + 1
    ind = len(text[ls:]) - len(text[ls:].lstrip(" \t"))
    end = text.find("\n", i)
    while end >= 0:
        nxt = text.find("\n", end + 1)
        ln = text[end + 1:nxt if nxt >= 0 else len(text)]
        if ln.strip() and len(ln) - len(ln.lstrip(" \t")) <= ind:
            return end
        if nxt < 0:
            return len(text)
        end = nxt
    return len(text)


def binder_names(region: str) -> set:
    """Every word a binder construct of `region` (masked text, the occurrences blanked) may bind (module docstring, "place")."""
    out = set()
    for rx in (_B_TERM, _B_ARROW):
        for m in rx.finditer(region):
            out |= set(WORD.findall(m.group(1) or ""))
    for m in _B_LINE.finditer(region):
        out |= set(WORD.findall(region[m.end():_logical_end(region, m.start())]))
    for m in _B_NAMED.finditer(region):
        seg = region[m.end():_logical_end(region, m.start())].split(":", 1)[0]
        ws = WORD.findall(seg)
        out |= set(ws) if ws else {"this"}
    for rx in (_B_GEN, _B_SETB):
        for m in rx.finditer(region):
            out.add(m.group(1))
    return out


def _chain(blocks: list, top: int, o: int) -> list[tuple[int, int]]:
    """[(block, step)] from the top block down to the innermost step that holds offset o."""
    out, b = [], top
    while b is not None:
        blk = blocks[b]
        hit = next((si for si, st in enumerate(blk["steps"]) if st["lo"] <= o < st["hi"]), None)
        if hit is None:
            break
        out.append((b, hit))
        st = blk["steps"][hit]
        b = next((ch for ch in st["children"] if blocks[ch]["lo"] <= o < blocks[ch]["hi"]), None)
    return out


def _common(chains: list) -> tuple[int, int] | None:
    """(block, first step) of the innermost block that holds every occurrence."""
    if not chains or any(not c for c in chains):
        return None
    d = 0
    while True:
        if len({c[d][0] for c in chains}) != 1:
            return None if d == 0 else (chains[0][d - 1][0], min(c[d - 1][1] for c in chains))
        same_step = len({c[d][1] for c in chains}) == 1
        if same_step and all(len(c) > d + 1 for c in chains) and len({c[d + 1][0] for c in chains}) == 1:
            d += 1
            continue
        return chains[0][d][0], min(c[d][1] for c in chains)


def _fresh(proof: str, k: int = 1) -> list[str]:
    used = set(WORD.findall(proof))
    return [n for n in NAMES if n not in used][:k]


def _sub_text(t: str) -> str:
    """t' (module docstring, "edit"): one line; the outer parens dropped unless the group is a cdot function."""
    flat = " ".join(t.split())
    return flat if has_cdot(t) else " ".join(flat[1:-1].split())


_BINDER_START = re.compile(r"\A(?:fun(?![\w'])|λ|[∀∃∑∏⋃⋂⨆⨅∫Σ∮])")


def _ascription(t: str) -> int | None:
    """The offset in t of a top-level type-ascription colon `(e : T)` (not `:=` / `::`, not a binder's colon), else None."""
    if _BINDER_START.match(t[1:].lstrip()):
        return None
    for i, ch in _depth1(t):
        if ch == ":" and t[i + 1:i + 2] not in ("=", ":") and t[i - 1:i] != ":":
            return i
    return None


def def_text(t: str) -> str:
    """What follows `have H` / `let H`: ` := t'`, or ` : T := e` for an ascription group `(e : T)` (cheaper than keeping the parens)."""
    if not has_cdot(t):
        k = _ascription(t)
        if k is not None:
            e, ty = " ".join(t[1:k].split()), " ".join(t[k + 1:-1].split())
            if e and ty:
                return f" : {ty} := {e}"
    return f" := {_sub_text(t)}"


def _ident_char(ch: str) -> bool:
    return bool(ch) and (ch.isalnum() or ch in "_'!?")


def _repl(body: str, a: int, b: int, name: str) -> str:
    pre = body[a - 1] if a > 0 else ""
    post = body[b] if b < len(body) else ""
    s = name
    if pre and pre not in " \t\n([{⟨,":
        s = " " + s
    if _ident_char(post):
        s = s + " "
    return s


def sites(body: str, proof: str | None = None) -> list[dict]:
    """The sites of the body, largest static saving first: {"key", "text", "occ" [(a, b)], "places" [(variant, P, col)], "let"
    (bool), "save" (tokens one copy saves)}."""
    pr = SP.parse(body)
    if pr is None:
        return []
    code, blocks, top = pr["code"], pr["blocks"], pr["top"]
    groups: dict = {}
    for a, b in _parens(code):
        t = body[a:b]
        if code[a:b] != t or not group_ok(t):
            continue
        if count_tokens(t) < MIN_TOKENS:
            continue
        groups.setdefault(" ".join(t.split()), []).append((a, b))
    reps = []
    for key, occ in groups.items():
        occ = sorted(set(occ))
        # occurrences of one text cannot overlap unless nested in themselves (impossible for equal lengths); keep disjoint ones
        dis = []
        for a, b in occ:
            if not dis or a >= dis[-1][1]:
                dis.append((a, b))
        if len(dis) >= 2:
            n = count_tokens(body[dis[0][0]:dis[0][1]])
            reps.append((len(dis) * (n - 1) - 2 - count_tokens(def_text(body[dis[0][0]:dis[0][1]])), key, dis))
    reps.sort(key=lambda x: (-x[0], x[1]))
    names = _fresh(proof if proof is not None else body)
    if not names:
        return []
    out, kept = [], []
    for save, key, occ in reps[:MAX_GROUPS]:
        if save <= 0:
            continue
        # maximal groups first: a group inside a kept larger group is dropped unless it occurs more often
        if any(all(any(ka <= a and b <= kb for ka, kb in k["occ"]) for a, b in occ) and len(k["occ"]) >= len(occ) for k in kept):
            continue
        t = body[occ[0][0]:occ[0][1]]
        chains = [_chain(blocks, top, a) for a, _ in occ]
        com = _common(chains)
        if com is None:
            continue
        B, k = com
        blk = blocks[B]
        free = free_names(t)
        places = []
        cands = [("have", k)]
        j = next((j for j in range(k - 1, -1, -1) if SP._is_split(code, blk["steps"][j])), None)
        if j is not None:
            cands.append(("split", j))
        for var, si in cands:
            P = blk["steps"][si]["lo"]
            region = list(code[P:occ[-1][0]])
            for a, b in occ:
                for i in range(max(a, P), min(b, occ[-1][0])):
                    region[i - P] = " "
            if free & binder_names("".join(region)):
                continue
            places.append((var, P, blk["col"]))
        if not places:
            continue
        heads = [blocks[c[-1][0]]["steps"][c[-1][1]]["head"] for c in chains]
        steps_b = {si for c in chains for bi, si in c if bi == B}
        site = {"key": key, "text": t, "occ": occ, "places": places, "save": save,
                "let": True, "value_heads": all(h in VALUE_HEADS for h in heads),
                # occurrences in two or more steps of the block (sibling goals: `next` / `case` / bullets / a flat goal list): the
                # binding also as `any_goals have`, so that every goal where the term elaborates gets its own copy of it
                "multi": len(steps_b) > 1 and places[0][0] == "have"}
        kept.append(site)
        out.append(site)
    return out


def apply(body: str, edits: list[tuple]) -> str | None:
    """edits: [(site, place (variant, P, col), keyword, name)] with disjoint occurrences -> the new body (None: overlap)."""
    ops = []   # (pos, order, end, text): order 0 insertion before order 1 replacement at the same position
    spans, ins = [], {}
    for site, (var, P, col), kw, name in edits:
        ins[P] = ins.get(P, "") + f"{KW_TEXT.get(kw, kw)} {name}{def_text(site['text'])}\n" + " " * col   # same place: edit order
        for a, b in site["occ"]:
            spans.append((a, b))
            ops.append((a, 1, b, _repl(body, a, b, name)))
    ops += [(P, 0, P, text) for P, text in ins.items()]
    spans.sort()
    if any(spans[i][1] > spans[i + 1][0] for i in range(len(spans) - 1)):
        return None
    for P, *_ in [o for o in ops if o[1] == 0]:
        if any(a < P < b for a, b in spans):
            return None
    out = body
    for pos, order, end, text in sorted(ops, key=lambda o: (o[0], o[1]), reverse=True):
        out = out[:pos] + text + out[end:]
    return out


def _disjoint(s1: dict, s2: dict) -> bool:
    return not any(a < d and c < b for a, b in s1["occ"] for c, d in s2["occ"])


def raw_copies(body: str, proof: str | None = None) -> list[dict]:
    """The screen copies, in screen order: the greedy joint (2+ sites), one primary copy per site (MAX_SITES), then the alternatives
    (`anyg` copies, `let` copies, `set` copies, the earlier placements).
    Each {"var", "body", "note", "sites" [site keys], "pick" [(site index, place index, kw)]}; only token savers."""
    ss = sites(body, proof)
    if not ss:
        return []
    t0 = count_tokens(body)
    name0 = _fresh(proof if proof is not None else body, len(NAMES))
    if not name0:
        return []
    prim, anygs, lets, sets, splits = [], [], [], [], []
    for i, s in enumerate(ss[:MAX_SITES]):
        # the primary copy (`have`, innermost placement), then `let` there (a value: `have` hides it from defeq / rfl), then the
        # earlier placements (before the block's split step)
        opts = ([(0, "have")] + ([(0, "let")] if s["let"] else []) + ([(0, "anyhave")] if s.get("multi") else [])
                + [(0, "set")] + [(pi, "have") for pi in range(1, len(s["places"]))])
        for n, (pi, kw) in enumerate(opts):
            nb = apply(body, [(s, s["places"][pi], kw, name0[0])])
            if nb is None or count_tokens(nb) >= t0:
                continue
            var = s["places"][pi][0] if kw == "have" else {"let": "let", "anyhave": "anyg", "set": "set"}[kw]
            c = {"var": var, "body": nb, "pick": [(i, pi, kw)], "save": t0 - count_tokens(nb),
                 "note": f"`{s['key'][:48]}` x{len(s['occ'])} -> {kw} {name0[0]} ({var})"}
            (prim if n == 0 else anygs if kw == "anyhave" else lets if kw == "let" else sets if kw == "set" else splits).append(c)
    out = []
    joint = joint_copy(body, ss, [c["pick"][0] for c in prim], name0)
    if joint is not None and count_tokens(joint["body"]) < t0:
        out.append(joint)
    return out + prim + anygs + lets + sets + splits


def joint_copy(body: str, ss: list[dict], picks: list[tuple], names: list[str]) -> dict | None:
    """The greedy joint (in `picks` order) of disjoint sites, distinct names; None when fewer than two fit."""
    sel, edits = [], []
    for i, pi, kw in picks:
        s = ss[i]
        if any(not _disjoint(s, ss[j]) for j, _, _ in sel) or len(sel) >= len(names):
            continue
        sel.append((i, pi, kw))
        edits.append((s, s["places"][pi], kw, names[len(sel) - 1]))
    if len(sel) < 2:
        return None
    nb = apply(body, edits)
    if nb is None:
        return None
    return {"var": "joint", "body": nb, "pick": sel, "save": count_tokens(body) - count_tokens(nb),
            "note": f"{len(sel)} shared terms -> {', '.join(f'{kw} {n}' for (_, _, kw), n in zip(sel, names))}"}


def has_sites(proof: str, statement: str) -> bool:
    try:
        body = split_declaration(proof, statement)
        return bool(body) and bool(raw_copies(body, proof))
    except Exception:  # noqa: BLE001
        return False


# ------------------------------------------------------------------------------------------------------------------------------ query
def _rescreen(statement: str, body: str, bodies: list[str], run, ctx, versions, log):
    """v4_rescreen's context-keeping copies (post-step v4), when that module is present: its trigger, then the screen under its fixed
    context. None when it is absent, the row has no such context, or neither control reads."""
    try:
        VR = importlib.import_module("harness.post.v4_rescreen")
    except Exception:  # noqa: BLE001  (v3 base: no context-keeping copies)
        return None
    meter = getattr(run, "meter", None)
    vs = list(versions or getattr(meter, "versions", None) or [None])
    cx = VR.row_ctx(getattr(meter, "row", None), vs[0])
    if not VR.has_context(statement, cx):
        return None
    v = VR.trigger(statement, body, cx, run, vs[0], log=log)
    if v not in ("measured", "plain"):
        return None
    with VR._fixed(VR.Ctx(cx.attached, cx.private, mode=v)):
        if v == "plain":
            SC._PLAIN_ONLY.add(statement)
        return SC.screen(statement, body, bodies, run, ctx, log=log, tag=FAMILY, max_files=1)


def _screen(statement, body, bodies, run, ctx, versions, log):
    got = SC.screen(statement, body, bodies, run, ctx, log=log, tag=FAMILY, max_files=1)
    if got is None:
        got = _rescreen(statement, body, bodies, run, ctx, versions, log)
    return got


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    """One screen file over the copies (a second for the joint of the passing sites); {"cse_key", "cse_up": [(body, predicted, var,
    note)]}; {} when nothing to screen."""
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return {}
        _, body = hb
        copies = raw_copies(body, proof)
        if not copies:
            return {}
        per = max(1, MS.budget(ctx or {}) - 1)
        copies = copies[:per]
        got = _screen(statement, body, [c["body"] for c in copies], run, ctx, versions, log)
        if got is None:
            return {}
        pr = {b: p for b, p in got.get("up", [])}
        up = [(c["body"], pr[c["body"]], c["var"], c["note"]) for c in copies if c["body"] in pr]
        # the second file: the joint of the passing sites (one copy per site: its best passing copy)
        ss = sites(body, proof)
        best: dict = {}
        for c in copies:
            if c["var"] != "joint" and c["body"] in pr and len(c["pick"]) == 1:
                i = c["pick"][0][0]
                if i not in best or pr[c["body"]] > best[i][0]:
                    best[i] = (pr[c["body"]], c["pick"][0])
        j0 = next((c for c in copies if c["var"] == "joint"), None)
        held = {i for i, _, _ in (j0 or {}).get("pick", [])}
        if len(best) >= 2 and not (j0 is not None and j0["body"] in pr and set(best) <= held):
            picks = [p for _, p in sorted(best.values(), key=lambda x: -x[0])]
            j2 = joint_copy(body, ss, picks, _fresh(proof, len(NAMES)))
            if j2 is not None and j2["body"] not in pr:
                got2 = _screen(statement, body, [j2["body"]], run, ctx, versions, log)
                for b, p in (got2 or {}).get("up", []):
                    if b == j2["body"]:
                        up.append((b, p, "joint2", j2["note"]))
        up.sort(key=lambda x: -x[1])
        if stats is not None:
            stats[FAMILY] = {"copies": len(copies), "up": len(up), "mode": got.get("mode")}
        if log:
            log(f"{FAMILY}: {len(copies)} cop(ies) screened ({got.get('mode')}), {len(up)} predicted up")
        return {"cse_key": K.proof_key(proof), "cse_up": up}
    except Exception as e:  # noqa: BLE001  (never raise; a budget stop propagates)
        if e.__class__.__name__ == "_Stop":
            raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:200]}")
        return {}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    """The query's screened copies (only for the proof it read), best predicted first; [] without a query."""
    try:
        c = ctx or {}
        if c.get("cse_key") != K.proof_key(proof):
            return []
        hb = K.head_body(proof, statement)
        if hb is None:
            return []
        head, body = hb
        em = K.Emitter(proof, statement, head, body, int(max_per_op or MAX_PER_OP))
        for nb, p, var, note in c.get("cse_up") or []:
            em.add(f"{FAMILY}:{var}", nb, f"{note}; predicted {p:.0f}")
        return em.out
    except Exception:  # noqa: BLE001
        return []


def main(argv=None) -> int:
    """Static census: python3 harness/post/v5_cse.py PROOFS.jsonl ROWS.jsonl  (sites and copy savings per row; no compile)."""
    import json
    a = list(sys.argv[1:] if argv is None else argv)
    rows = {json.loads(x)["name"]: json.loads(x) for x in open(a[1])}
    tot = 0.0
    for ln in open(a[0]):
        r = json.loads(ln)
        st = rows[r["name"]]["statement"]
        body = split_declaration(r["proof"], st)
        if body is None:
            continue
        cs = raw_copies(body, r["proof"])
        if cs:
            L = float(rows[r["name"]].get("proof_length") or 1)
            best = max(c["save"] for c in cs)
            tot += best * 100.0 / (3 * L)
            print(f"{r['name'][-40:]:40s} copies {len(cs):2d} best save {best:3d} upper {best * 100.0 / (3 * L):.2f}")
            for c in cs:
                print(f"      {c['var']:6s} {c['save']:3d} {c['note']}")
    print(f"upper row-pts {tot:.2f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
