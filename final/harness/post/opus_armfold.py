#!/usr/bin/env python3
"""Structural op "opus_armfold" of the open post-step (gap lane opus, 2026-11-03): merge the parallel branches of a case split into one
combinator.

  site      a SPLIT GROUP: a tactic HEAD (any single tactic, possibly with continuation lines) directly followed, at the same tactic
            column, by k >= 2 sibling arms that close the goals it produced:
              bullets   `· body` blocks (the head on its own line, or the inner tactic of a parent bullet line `· HEAD`);
              alts      `HEAD with` + `| tag xs => body` arms (cases / induction / rcases-free `with` forms; never `match`).
            Comments and strings are masked; a group whose text holds a comment is skipped.
  generate  (every candidate is shorter than the incumbent; Lean decides whether it compiles)
    armfold:arm<i>   the whole group -> `HEAD <;> X`, X = arm i's own body (one tactic as it is; several tactics as `(`seq`)` on the
                     following lines, and as a `<;>` chain); for alts, X must not mention the arm's own binder names
    armfold:union    every arm is one closer of the same family with the same tail (`simp [..]`, `simp_all [..]`, `grind [..]`,
                     `norm_num [..]`, `linarith [..]`, ...): `HEAD <;> fam [union of the lists]`
  screen    query(): when there are more candidates than one reading per pass can cover, all of them (fewest tokens first) go through
            ONE d4_measure file (the incumbent is the control); only the ones predicted to read higher are proposed.
Pure text plus the row's own environment (the screen compile). No row name, no table, no proof text: every token of a candidate is the
proof's own or Lean syntax (`<;>`, parentheses)."""
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

FAMILY = "opus_armfold"
MAX_PER_OP = 24
MAX_X = 60          # tokens of the folded tactic at most
BULLET = "·"
FAMS = ("simp_all", "simp", "norm_num", "field_simp", "grind", "linarith", "nlinarith", "positivity", "aesop", "simpa", "dsimp",
        "omega", "ring_nf", "push_cast")
FAM_RE = re.compile(r"^(?P<fam>" + "|".join(FAMS) + r")(?P<only>\s+only)?(?:\s*\[(?P<args>[^\[\]]*(?:\[[^\[\]]*\][^\[\]]*)*)\])?(?P<tail>.*)$",
                    re.S)
BAD_HEAD_END = re.compile(r"(?:\bby|=>|\bwith|:=|\bfun\s.*|[(\[{⟨,]|\bthen|\belse|\bdo|<;>|<\|>)\s*$")
BAD_HEAD_START = re.compile(r"^(?:match|calc|conv|case|next|show|·|\||have|let|suffices|obtain\b.*:=\s*$)")
IDENT = re.compile(r"[A-Za-z_Ͱ-Ͽἀ-῿℀-⅏][\w'!?₀-ₜͰ-Ͽ]*")


def _indent(ln: str) -> int:
    return len(ln) - len(ln.lstrip(" "))


def _lines(body: str):
    """[(start offset, line text)] of the body."""
    out, i = [], 0
    for ln in body.split("\n"):
        out.append((i, ln))
        i += len(ln) + 1
    return out


def _col(ln: str) -> int:
    """The tactic column of a code line (a bullet line's tactic sits after `· `)."""
    s = ln.lstrip(" ")
    d = _indent(ln)
    if s.startswith(BULLET):
        rest = s[len(BULLET):]
        return d + len(BULLET) + (len(rest) - len(rest.lstrip(" ")))
    return d


def _blank(ln: str) -> bool:
    return not ln.strip()


def _block_end(L: list, i: int, d: int) -> int:
    """Index after the last line of the item starting at line i whose lines are indented deeper than column d."""
    j = i + 1
    while j < len(L) and (_blank(L[j][1]) or _indent(L[j][1]) > d):
        j += 1
    while j > i + 1 and _blank(L[j - 1][1]):
        j -= 1
    return j


def _arm_tactics(lines: list[str], col: int) -> list[list[str]]:
    """Split an arm body (lines, the first already stripped of its bullet / `=>`, all at tactic column `col` or deeper) into tactics."""
    tacs: list[list[str]] = []
    for k, ln in enumerate(lines):
        if k == 0 or _indent(ln) <= col:
            tacs.append([ln])
        else:
            tacs[-1].append(ln)
    return tacs


def _render_x(tacs: list[list[str]], col: int) -> list[str]:
    """The arm body as ONE tactic text to follow `<;> ` (list: the spellings)."""
    if not tacs:
        return []
    flat = [t for t in tacs]
    if len(flat) == 1:
        t = flat[0]
        return ["\n".join([t[0].strip()] + t[1:])]
    out = []
    # `(` seq `)` on the following lines, the arm's own indentation kept (one column deeper than the group)
    seq = []
    for t in flat:
        seq.append(" " * (col + 2) + t[0].strip())
        seq.extend(t[1:])
    out.append("(\n" + "\n".join(seq) + ")")
    # a `<;>` chain (one goal per step: the same proof when every step leaves at most one goal)
    if all(len(t) == 1 for t in flat):
        out.append(" <;> ".join(t[0].strip() for t in flat))
    return out


def _binders(header: str) -> set[str]:
    """Names bound by an alt header `| tag xs` / `| @tag _ x` / `| tag1 | tag2` (the tag itself excluded)."""
    names = set()
    for alt in header.split("|"):
        toks = IDENT.findall(alt.replace("@", " "))
        names.update(t for t in toks[1:] if t != "_")
    return names


def groups(body: str) -> list[dict]:
    """The split groups of the body (module docstring, "site")."""
    mask = _mask(body)
    L = _lines(body)
    out = []
    n = len(L)

    def masked_any(a: int, b: int) -> bool:
        return any(mask[a:b])

    # ---- bullet groups
    i = 0
    seen_first = set()
    for i in range(n):
        off, ln = L[i]
        s = ln.lstrip(" ")
        if not s.startswith(BULLET) or i in seen_first:
            continue
        d = _indent(ln)
        # collect sibling bullets at indent d
        arms, j = [], i
        while j < n and not _blank(L[j][1]) and _indent(L[j][1]) == d and L[j][1].lstrip(" ").startswith(BULLET):
            e = _block_end(L, j, d)
            arms.append((j, e))
            seen_first.add(j)
            j = e
            while j < n and _blank(L[j][1]):
                j += 1
        if len(arms) < 2:
            continue
        # the head: the nearest previous tactic start at column d
        h = i - 1
        while h >= 0 and (_blank(L[h][1]) or _indent(L[h][1]) > d and _col(L[h][1]) != d):
            h -= 1
        if h < 0:
            continue
        hl = L[h][1]
        if _col(hl) != d:
            continue
        # the head's lines h..i-1 (continuations deeper than d)
        if any(not _blank(L[k][1]) and _indent(L[k][1]) <= d for k in range(h + 1, i)):
            continue
        head_lines = [L[k][1] for k in range(h, i) if not _blank(L[k][1])]
        head_text = "\n".join(head_lines)
        hs = head_lines[0].lstrip(" ")
        if hs.startswith(BULLET):
            hs = hs[len(BULLET):].lstrip(" ")
        if BAD_HEAD_START.match(hs) or BAD_HEAD_END.search(head_lines[-1]):
            continue
        a0, b0 = L[h][0], (L[arms[-1][1] - 1][0] + len(L[arms[-1][1] - 1][1]))
        if masked_any(a0, b0):
            continue
        # arms
        arm_x = []
        for (s0, e0) in arms:
            first = L[s0][1]
            fs = first.lstrip(" ")[len(BULLET):]
            col = d + len(BULLET) + (len(fs) - len(fs.lstrip(" ")))
            lines = [" " * col + fs.lstrip(" ")] + [L[k][1] for k in range(s0 + 1, e0)]
            arm_x.append(_arm_tactics(lines, col))
        out.append({"kind": "bullets", "start": a0, "end": b0, "head": head_text, "head_end": L[i - 1][0] + len(L[i - 1][1])
                    if i - 1 >= h else None, "col": d, "arms": arm_x, "binders": [set() for _ in arm_x],
                    "head_start": L[h][0]})

    # ---- `with` alt groups
    for h in range(n):
        off, ln = L[h]
        code = ln.rstrip()
        if not re.search(r"\swith$", code):
            continue
        hs = ln.lstrip(" ")
        if hs.startswith(BULLET):
            hs = hs[len(BULLET):].lstrip(" ")
        if not re.match(r"^(?:unhygienic\s+)?(?:cases|induction|fun_induction|fun_cases|cases'|induction')\b", hs):
            continue
        d = _col(ln)
        arms, j = [], h + 1
        while j < n and not _blank(L[j][1]) and _indent(L[j][1]) >= d and L[j][1].lstrip(" ").startswith("|"):
            ad = _indent(L[j][1])
            e = _block_end(L, j, ad)
            arms.append((j, e, ad))
            j = e
        if len(arms) < 2:
            continue
        a0, b0 = L[h][0], L[arms[-1][1] - 1][0] + len(L[arms[-1][1] - 1][1])
        if masked_any(a0, b0):
            continue
        arm_x, binders, ok = [], [], True
        for (s0, e0, ad) in arms:
            first = L[s0][1].lstrip(" ")
            m = re.match(r"^(\|.*?)=>(.*)$", first)
            if not m:
                ok = False
                break
            hdr, rest = m.group(1), m.group(2).strip()
            col = ad + 2
            lines = ([" " * col + rest] if rest else []) + [L[k][1] for k in range(s0 + 1, e0)]
            if not lines:
                ok = False
                break
            col = _indent(lines[0])
            arm_x.append(_arm_tactics(lines, col))
            binders.append(_binders(hdr))
        if not ok:
            continue
        head_text = re.sub(r"\s+with$", "", ln.rstrip())
        out.append({"kind": "alts", "start": a0, "end": b0, "head": head_text, "col": d, "arms": arm_x, "binders": binders,
                    "head_start": L[h][0]})
    return out


def _union(arms: list[list[list[str]]]) -> str | None:
    """`fam [a ∪ b ...]tail` when every arm is one single-line closer of the same family / `only` / tail."""
    fam = only = tail = None
    items: list[str] = []
    for tacs in arms:
        if len(tacs) != 1 or len(tacs[0]) != 1:
            return None
        m = FAM_RE.match(tacs[0][0].strip())
        if not m:
            return None
        f, o, t = m.group("fam"), bool(m.group("only")), m.group("tail").strip()
        if fam is None:
            fam, only, tail = f, o, t
        elif (f, o, t) != (fam, only, tail):
            return None
        for a in _split_args(m.group("args") or ""):
            if a and a not in items:
                items.append(a)
    if fam is None:
        return None
    s = fam + (" only" if only else "") + (f" [{', '.join(items)}]" if items else "") + (" " + tail if tail else "")
    return s


def _split_args(s: str) -> list[str]:
    out, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def _mentions(tacs: list[list[str]], names: set[str]) -> bool:
    if not names:
        return False
    txt = "\n".join("\n".join(t) for t in tacs)
    return any(tok in names for tok in IDENT.findall(txt))


def raw_candidates(body: str) -> list[tuple[str, str, str]]:
    """[(variant, new body, note)] for every group, the likeliest first: the folded tactic X shortest first (a short arm body is a
    generic closer; a long one is specific to its own goal), arms over MAX_X tokens skipped."""
    if SC.unchecked(body):
        return []
    out = []
    t0 = count_tokens(body)
    for g in groups(body):
        pre, post = body[:g["head_start"]], body[g["end"]:]
        hl = g["head"].split("\n")
        xs = []
        for i, tacs in enumerate(g["arms"]):
            if g["kind"] == "alts" and _mentions(tacs, g["binders"][i]):
                continue
            for k, x in enumerate(_render_x(tacs, g["col"])):
                xs.append((f"arm{i}" + ("" if k == 0 else "c"), x))
        u = _union(g["arms"])
        if u is not None and not any(_mentions(t, g["binders"][i]) for i, t in enumerate(g["arms"]) if g["kind"] == "alts"):
            xs.append(("union", u))
        if g["kind"] == "alts" and not any(_mentions(t, g["binders"][i]) for i, t in enumerate(g["arms"])):
            alts = [_render_x(t, g["col"]) for t in g["arms"]]
            if all(alts) and all("\n" not in a[-1] for a in alts):
                xs.append(("first", "first | " + " | ".join(a[-1] for a in alts)))
        out.extend(_elim(g, body, pre, post, t0))
        for var, x in xs:
            if count_tokens(x) > MAX_X:
                continue
            new = pre + "\n".join(hl[:-1] + [hl[-1].rstrip() + " <;> " + x]) + post
            if count_tokens(new) >= t0:
                continue
            out.append((count_tokens(x), var, new,
                        f"{g['kind']} group of {len(g['arms'])} arms at line {K.line_of(body, g['start'])} -> one `<;>` ({var})"))
    try:
        out.extend(flat_elim(body))
    except Exception:
        pass
    out.sort(key=lambda t: (t[0], count_tokens(t[2])))
    return [(v, n, note) for _, v, n, note in out]


SPLIT_RE = re.compile(r"^(?:by_cases|split_ifs|split|rcases|obtain|cases|cases')\b")


def _elim(g: dict, body: str, pre: str, post: str, t0: int) -> list:
    """armfold:elim  a bullet group under a pure case split -> the split dropped and ONE arm's body kept (the arm does not mention
    a name the split binds): the split was not needed for that proof."""
    if g["kind"] != "bullets":
        return []
    hl = g["head"].split("\n")
    first = hl[0]
    fs = first.lstrip(" ")
    bullet = fs.startswith(BULLET)
    hs = fs[len(BULLET):].lstrip(" ") if bullet else fs
    if not SPLIT_RE.match(hs):
        return []
    if hs.startswith(("rcases", "obtain")) and "|" not in g["head"]:
        return []
    bound = {t for t in IDENT.findall(g["head"].split(":", 1)[0] if hs.startswith("by_cases") else
                                       (g["head"].split(" with ", 1)[1] if " with " in g["head"] else
                                        g["head"].split(":=", 1)[0][len("obtain"):] if hs.startswith("obtain") else ""))}
    bound -= {"by_cases", "with", "rfl", "_"}
    out = []
    d = g["col"]
    for i, tacs in enumerate(g["arms"]):
        if _mentions(tacs, bound):
            continue
        lines = [ln for t in tacs for ln in t]
        acol = _indent(lines[0])
        delta = acol - d
        if delta < 0 or any(ln.strip() and _indent(ln) < delta for ln in lines):
            continue
        new_lines = [ln[delta:] for ln in lines]
        if bullet:
            ind = first[:len(first) - len(fs)]
            new_lines[0] = ind + BULLET + " " + new_lines[0].lstrip(" ")
        new = pre + "\n".join(new_lines) + post
        if count_tokens(new) < t0:
            out.append((0, f"elim{i}", new, f"split at line {K.line_of(body, g['start'])} dropped, arm {i} kept (elim)"))
    return out


CLOSER_RE = re.compile(r"^(?:exact|exacts|simpa|omega|linarith|nlinarith|rfl|decide|grind|aesop|assumption|contradiction|tauto|"
                       r"positivity|ring|trivial|exfalso|absurd|nomatch|solve_by_elim|apply_rules|norm_num(?!.*\bat\b)|"
                       r"simp(?:_all)?(?!.*\bat\b)|linear_combination|field_simp(?!.*\bat\b))\b")


def flat_elim(body: str) -> list:
    """armfold:flatelim  a two-goal split step written flat (`by_cases h : P` / `rcases e with p | q`, its two goals closed one
    after the other by the following steps of the same block) -> the split dropped and ONE goal's steps kept: the first goal's
    steps up to its first (or second) closing step, or the steps after that boundary (the second goal and the rest of the block).
    The kept steps must not mention a name the split binds."""
    from harness.post.opus_hoist import parse
    L = body.split("\n")
    recs = [r for r in parse(body)]
    starts = [r for r in recs if r["start"]]
    t0 = count_tokens(body)
    out = []
    for k, r in enumerate(starts):
        t = r["code"].strip()
        if r["bullet"]:
            continue
        m = re.match(r"^by_cases\s+(\S+)\s*:", t)
        if m:
            bound = {m.group(1)}
        elif re.match(r"^rcases\b.*\swith\s", t) and t.split(" with ", 1)[-1].count("|") == 1 and "⟨" not in t.split(" with ", 1)[-1]:
            bound = set(IDENT.findall(t.split(" with ", 1)[-1]))
        else:
            continue
        bound -= {"rfl", "_"}
        blk = [x for x in starts[k + 1:] if x["block"] == r["block"] and x["col"] == r["col"]]
        # stop at the end of the block (a start at a smaller column)
        seq = []
        for x in starts[k + 1:]:
            if x["col"] < r["col"]:
                break
            if x["block"] == r["block"] and x["col"] == r["col"]:
                if x["bullet"]:
                    seq = []
                    break
                seq.append(x)
        if len(seq) < 2:
            continue
        def span(a: int, b: int) -> tuple[int, int]:
            # line range of starts seq[a..b) with their continuation lines
            lo = seq[a]["i"]
            hi = seq[b]["i"] if b < len(seq) else _block_end_line(L, recs, seq[-1], r["col"])
            return lo, hi
        closers = [j for j, x in enumerate(seq) if CLOSER_RE.match(x["code"].strip())][:2]
        for j in closers:
            if j + 1 >= len(seq):
                continue
            cut = j + 1
            s_lo = r["i"]
            first_lo, first_hi = span(0, cut)
            second_lo, second_hi = span(cut, len(seq))
            keep_first = L[:s_lo] + L[first_lo:first_hi] + L[second_hi:]
            keep_second = L[:s_lo] + L[second_lo:]
            for var, NL, kept in (("flatelim1", keep_first, L[first_lo:first_hi]), ("flatelim2", keep_second, L[second_lo:second_hi])):
                if bound and any(tok in bound for tok in IDENT.findall("\n".join(kept))):
                    continue
                nb = "\n".join(NL)
                if count_tokens(nb) < t0:
                    out.append((0, var, nb, f"flat split at line {r['i'] + 1} dropped, {var[-1]}st/nd goal's steps kept (cut after step {cut})"))
    return out


def _block_end_line(L: list[str], recs: list, last: dict, col: int) -> int:
    """The line index after the last line of the step `last` (its continuation lines included) within a block at column col."""
    i = last["i"] + 1
    while i < len(L) and (not L[i].strip() or _indent(L[i]) > col):
        i += 1
    while i > last["i"] + 1 and not L[i - 1].strip():
        i -= 1
    return i


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
        cap = int(max_per_op or MAX_PER_OP)
        em = K.Emitter(proof, statement, head, body, cap)
        screened = (ctx or {}).get("armfold_screen") if (ctx or {}).get("armfold_key") == K.proof_key(proof) else None
        raws = raw_candidates(body)
        if screened is not None:
            keep = {b: pr for b, pr in screened.get("up", [])}
            raws = sorted([r for r in raws if r[1] in keep], key=lambda r: -keep[r[1]]) + \
                [r for r in raws if r[1] in set(screened.get("unscreened", []))]
        for var, new, note in raws:
            em.add(f"{FAMILY}:{'arm' if var.startswith('arm') else 'elim' if var.startswith('elim') else 'flatelim' if var.startswith('flatelim') else var}", new, note)
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
        raws = [r for r in raw_candidates(body) if count_tokens(r[1]) < count_tokens(body)]
        if len(raws) <= 1:
            return {}
        got = SC.screen(statement, body, [r[1] for r in raws], run, ctx, log=log, tag=FAMILY, max_files=1)
        if got is None:
            return {}
        return {"armfold_key": K.proof_key(proof), "armfold_screen": got}
    except Exception as e:  # never raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:200]}")
        return {}
