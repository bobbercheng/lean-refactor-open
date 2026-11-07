#!/usr/bin/env python3
"""Op "opus_goalmerge" of the open post-step (gap lane opus, 2026-11-04): merge PARALLEL GOAL BLOCKS into one combinator, keyed on
Lean's own goal count.

Mechanism (the gap): the open proofs close the goals of a case split one block at a time (flat `unhygienic` sequences, `·` bullets),
often with the same or interchangeable blocks; the closed proofs factor them into `S <;> T`, `all_goals T`, `all_goals first | ..`.

  parse     the body's top tactic block (`by` / `by unhygienic` + newline, steps at the block's column; a line deeper than the column,
            or after a line ending in a continuation token, belongs to the step above). No site when the body has comments.
  query 1   (one compile, primary pin) the declaration itself with `trace "LRAGMk"; trace_state` before every step and after the last
            one: Lean's goal display gives g[k] = the number of open goals before step k (count of `⊢` lines). Nothing else is read.
  blocks    from step p with g[p] >= 2 goals the following steps are cut into goal blocks: a block ends at the first step after which
            fewer goals remain than before the block started (Lean works on the main goal; a step that closes more than one goal, e.g.
            `all_goals X`, ends a multi-goal block). A split step i (g[i+1] > g[i]) owns the blocks of its new goals.
  generate  (only block texts of the proof itself; every alternative is one step of the proof, one-lined when it has no layout-
            sensitive part; a `·` bullet contributes its content, a leading `all_goals` / `any_goals` is dropped)
    goalmerge:tail   steps p..end (the whole rest of the top block, which closes all g[p] goals) -> `all_goals T` for one block text T,
                     or `all_goals first | T1 | .. | Tn` over the distinct block texts (most frequent first)
    goalmerge:split  a split step S and the blocks of its goals -> `S <;> T` / `S <;> first | T1 | .. | Tn`
            only candidates with fewer tokens than the proof given.
  query 2   (<= 2 compiles) the d4_measure one-file screen of the candidates (cheapest first, at most the file budget): ok + heartbeats
            of each; candidates() proposes the screened ones that read higher (d4_measure.predicted > 0) first, then the rest of the
            screened ok ones. Without a query answer no candidate is proposed (the blind space is too wide).
Pure text + Lean's feedback; no table, no row name, no lemma list: every token of a candidate is the proof's own or Lean syntax
(`all_goals`, `first`, `|`, `<;>`, parentheses, `;`). The post-step's gate decides (every pin, paired re-reading, audit)."""
from __future__ import annotations

# provenance: research lane gaplane2-opus (worktree lra-gl2-opus), commit ed5d5bc, ported unchanged into open-post-v3 (2026-11-04)

import re, sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402

FAMILY = "goalmerge"
HEAD_RE = re.compile(r"\A[ \t]*by(?P<u>[ \t]+unhygienic)?[ \t]*\n")
CONT_END = ("<;>", "by", "=>", ":=", ",", "(", "[", "⟨", "{", "$", "<|", "|>", "∘", "fun", "λ", "→", "↔", "∧", "∨", "·", "with", "at",
            "using", "=", "+", "*", "-", "/", "≤", "<", ">", "≥", "▸", "|")
CONT_START = ("<;>", "|", ")", "]", "}", "⟩", "with", "at ", "using", "<|>", "▸", ".")
NOLINE = re.compile(r"(?:\bby|=>|\bwith|·|\bfun|λ|\bcalc|\bmatch|\bcase|\bnext|\bconv)\s*$", re.M)
MARK = "LRAGM"
MAX_CANDS = 30      # candidates screened per row (cheapest first)
MAX_ALTS = 6        # alternatives in one `first`


def _ind(l: str) -> int:
    return len(l) - len(l.lstrip(" "))


def _ends_cont(line: str) -> bool:
    s = line.rstrip()
    for t in CONT_END:
        if s.endswith(t):
            if t.isalpha() or t in ("fun",):
                return re.search(r"(?<![\w.'])" + re.escape(t) + r"$", s) is not None
            return True
    return False


def parse(body: str):
    """(head, col, steps) of the body's top tactic block: head = the text up to the first step line (the `by` line), col = the block's
    column, steps = [text of each step (its lines joined with newlines, no trailing newline)], or None."""
    if body is None or "--" in body or "/-" in body or "\t" in body:
        return None
    m = HEAD_RE.match(body)
    if not m:
        return None
    head, rest = body[:m.end()], body[m.end():]
    lines = rest.rstrip("\n").split("\n")
    nonempty = [l for l in lines if l.strip()]
    if not nonempty:
        return None
    col = len(nonempty[0]) - len(nonempty[0].lstrip(" "))
    if col == 0:
        return None
    steps: list[list[str]] = []
    prev = None
    for l in lines:
        if not l.strip():
            if steps:
                steps[-1].append(l)
            continue
        ind = len(l) - len(l.lstrip(" "))
        if ind < col:
            return None
        s = l.strip()
        new = ind == col and not s.startswith(CONT_START) and not (prev is not None and _ends_cont(prev))
        if new:
            steps.append([l])
        else:
            if not steps:
                return None
            steps[-1].append(l)
        prev = l
    return head, col, ["\n".join(x).rstrip() for x in steps]


def probe_body(head: str, col: int, steps: list[str]) -> str:
    pad = " " * col
    out = [head.rstrip("\n")]
    for k, s in enumerate(steps):
        out.append(f'{pad}trace "{MARK}{k}"; trace_state')
        out.append(s)
    out.append(f'{pad}trace "{MARK}{len(steps)}"; trace_state')
    return "\n".join(out) + "\n"


def parse_probe(messages, n: int) -> list[int] | None:
    """g[0..n] from the probe compile's messages (None when any reading is missing): the marker `trace` and the `trace_state` of one
    probe line share the line (Lean groups messages by kind, so pairing is by position; sequential pairing without positions)."""
    g: dict[int, int] = {}
    mark_at: dict[int, int] = {}
    states: list[tuple] = []
    for m in messages or []:
        if m.get("severity") not in (None, "information", "info"):
            continue
        t = K.msg_text(m)
        line = (m.get("pos") or {}).get("line")
        mm = re.fullmatch(rf"\s*{MARK}(\d+)\s*", t)
        if mm:
            if isinstance(line, int):
                mark_at[line] = int(mm.group(1))
            states.append(("M", int(mm.group(1))))
        else:
            states.append(("S", line, sum(1 for ln in t.split("\n") if ln.startswith("⊢"))))
    if mark_at:
        for x in states:
            if x[0] == "S" and x[1] in mark_at and mark_at[x[1]] not in g:
                g[mark_at[x[1]]] = x[2]
    else:
        cur = None
        for x in states:
            if x[0] == "M":
                cur = x[1]
            elif cur is not None and cur not in g:
                g[cur] = x[2]; cur = None
    if any(k not in g for k in range(n + 1)):
        return None
    return [g[k] for k in range(n + 1)]


def blocks_from(g: list[int], p: int, floor: int):
    """Goal blocks of the steps from p until the count reaches `floor`: [(a, b, closed)] (steps a..b-1 close `closed` goals), and the
    end index e (g[e] == floor), or None when the count never reaches floor cleanly."""
    out = []
    a, n = p, len(g) - 1
    j = p
    while j < n and g[a] > floor:
        start = g[a]
        j = a
        while j < n and g[j + 1] >= start:
            j += 1
        if j >= n:
            return None
        after = g[j + 1]
        if after < floor:
            return None
        out.append((a, j + 1, start - after))
        a = j + 1
    if g[a] != floor:
        return None
    return out, a


def _join_step(sub: list[str]) -> str | None:
    sub = [x.strip() for x in sub if x.strip()]
    if not sub or any(NOLINE.search(x) for x in sub):
        return None
    return " ".join(sub)


def oneline(step: str) -> str | None:
    """The step as one line usable as a combinator argument, or None (layout-sensitive). A `·` bullet gives its content (its steps
    joined with `; ` in parentheses when there are several)."""
    s = step.strip("\n")
    st = s.strip()
    if st.startswith("·"):
        lines = [l for l in s.split("\n") if l.strip()]
        first = lines[0].strip()[1:].strip()
        rest = lines[1:]
        if not first:
            if not rest:
                return None
            first, rest = rest[0].strip(), rest[1:]
        ccol = min((_ind(l) for l in rest), default=None)
        groups = [[first]]
        prev = first
        for l in rest:
            if _ind(l) == ccol and not l.strip().startswith(CONT_START) and not _ends_cont(prev):
                groups.append([l])
            else:
                groups[-1].append(l)
            prev = l
        parts = [_join_step(g) for g in groups]
        if any(p is None for p in parts):
            return None
        parts = [re.sub(r"^(?:all_goals|any_goals)\s+", "", p) for p in parts]
        return parts[0] if len(parts) == 1 else "(" + "; ".join(parts) + ")"
    m = re.match(r"(?:case\s+(?P<tag>[^\s=]+)|next)(?P<names>(?:\s+[^\s=]+)*)\s*=>\s*(?P<t>\S.*)$", st, re.S)
    if m:   # a `case tag xs => T` / `next xs => T` arm whose names T does not mention: T (Lean's goal order, tag dropped)
        t = None if "\n" in m.group("t").strip() else _join_step([m.group("t")])
        names = [x for x in m.group("names").split() if x != "_"]
        if t is None or any(re.search(r"(?<![\w.'])" + re.escape(x) + r"(?![\w'])", t) for x in names):
            return None
        return re.sub(r"^(?:all_goals|any_goals)\s+", "", t)
    if re.match(r"(?:case|next)\b", st):
        return None
    s = _join_step(st.split("\n"))
    if s is None:
        return None
    s = re.sub(r"^(?:all_goals|any_goals)\s+", "", s)
    return s or None


def block_text(steps: list[str], a: int, b: int) -> str | None:
    parts = [oneline(steps[k]) for k in range(a, b)]
    if any(x is None for x in parts):
        return None
    if len(parts) == 1:
        return parts[0]
    return "(" + "; ".join(parts) + ")"


def _alts(texts: list[str]) -> list[str]:
    c = Counter(texts)
    order = sorted(c, key=lambda t: (-c[t], texts.index(t)))
    return order


def _wrap(t: str) -> str:
    return t if not re.search(r"<;>|\bfirst\b|\|", t) or t.startswith("(") else f"({t})"


def merges_block(col: int, steps: list[str], g: list[int]) -> list[tuple[str, str, str]]:
    """[(variant, new block text, note)] of the merge rewrites of ONE tactic block (its steps and goal counts g[0..n])."""
    pad = " " * col
    n = len(steps)
    out: dict[str, tuple[str, str, str]] = {}

    def emit(variant, new_steps, note):
        b = "\n".join(new_steps)
        if b not in out:
            out[b] = (variant, b, note)

    def combos(texts):
        alts = _alts(texts)
        res = [(t, f"one block ({texts.count(t)}x of {len(texts)})") for t in alts]
        if 2 <= len(alts) <= MAX_ALTS:
            res.append(("first " + " ".join("| " + t for t in alts), f"first over {len(alts)} blocks"))
        return res

    if len(g) != n + 1 or g[n] != 0:
        return []
    # tail: all_goals over the rest of the block
    for p in range(1, n):
        if g[p] < 2:
            continue
        r = blocks_from(g, p, 0)
        if r is None:
            continue
        bl, e = r
        if e != n or len(bl) < 2:
            continue
        texts = [block_text(steps, a, b) for a, b, _ in bl]
        if any(t is None for t in texts):
            continue
        for t, note in combos(texts):
            emit("goalmerge:tail", steps[:p] + [f"{pad}all_goals {t}"], f"steps {p}..{n - 1} ({len(bl)} blocks) -> all_goals: {note}")
    # split: S <;> T
    for i in range(n):
        d = g[i + 1] - g[i]
        if d < 1:
            continue
        floor = g[i] - 1
        r = blocks_from(g, i + 1, floor)
        if r is None:
            continue
        bl, e = r
        if len(bl) < 2 or any(c != 1 for _, _, c in bl):
            continue
        texts = [block_text(steps, a, b) for a, b, _ in bl]
        if any(t is None for t in texts):
            continue
        S = steps[i].rstrip()
        if NOLINE.search(S) or S.lstrip().startswith(("·", "case ", "next ")):
            continue
        for t, note in combos(texts):
            emit("goalmerge:split", steps[:i] + [f"{S} <;> {t}"] + steps[e:], f"split step {i} + {len(bl)} blocks -> <;>: {note}")
    # prefix: every block of a split starts with the same steps P -> `S <;> P` once, the blocks keep the rest
    for i in range(n):
        if g[i + 1] - g[i] < 1:
            continue
        r = blocks_from(g, i + 1, g[i] - 1)
        if r is None:
            continue
        bl, e = r
        if len(bl) < 2 or any(c != 1 for _, _, c in bl):
            continue
        S = steps[i].rstrip()
        if NOLINE.search(S) or S.lstrip().startswith(("·", "case ", "next ")):
            continue
        L = 0
        while all(b - a > L + 1 for a, b, _ in bl) and len({steps[a + L].strip() for a, _, _ in bl}) == 1:
            L += 1
        if L == 0:
            continue
        P = block_text(steps, bl[0][0], bl[0][0] + L)
        if P is None:
            continue
        rest = [steps[k] for a, b, _ in bl for k in range(a + L, b)]
        emit("goalmerge:prefix", steps[:i] + [f"{S} <;> {P}"] + rest + steps[e:], f"split step {i}: common prefix of {L} steps in {len(bl)} blocks")
    # hoist: a group of L steps that OPENS >= 2 goal blocks (of a split, or of a tail) -> one `any_goals G` where the blocks start
    # (any_goals keeps a goal unchanged where G fails; Lean decides whether the other goals survive G)
    regions = []
    for i in range(n):
        if g[i + 1] - g[i] >= 1:
            r = blocks_from(g, i + 1, g[i] - 1)
            if r is not None:
                regions.append((i + 1, r[0], f"split step {i}", i))
    for p in range(1, n):
        if g[p] >= 2:
            r = blocks_from(g, p, 0)
            if r is not None and r[1] == n:
                regions.append((p, r[0], f"tail from {p}", None))
    hoisted = set()
    for at, bl, what, si in regions:
        if len(bl) < 2:
            continue
        for L in (1, 2, 3):
            groups: dict[tuple, list] = {}
            for a, b, _ in bl:
                if b - a >= L:
                    groups.setdefault(tuple(steps[k].strip() for k in range(a, a + L)), []).append((a, b))
            for key, occ in groups.items():
                if len(occ) < 2 or len(occ) == len(bl) and all(b - a > L for a, b in occ):
                    continue   # (a common prefix of every block is the `prefix` variant)
                T = block_text(steps, occ[0][0], occ[0][0] + L)
                if T is None or T.startswith(("·", "case ", "next ")):
                    continue
                drop = frozenset(k for a, _ in occ for k in range(a, a + L))
                if drop in hoisted or min(drop) < at:
                    continue
                hoisted.add(drop)
                new_steps = []
                for k in range(n):
                    if k == at:
                        new_steps.append(f"{pad}any_goals {T}")
                    if k not in drop:
                        new_steps.append(steps[k])
                emit("goalmerge:hoist", new_steps, f"{what}: {L} steps opening {len(occ)} of {len(bl)} blocks -> any_goals")
                S = steps[si].rstrip() if si is not None else None
                if S is not None and not NOLINE.search(S) and not S.lstrip().startswith(("·", "case ", "next ")) and "\n" not in S:
                    tt = T if T.startswith("(") else f"({T})" if re.search(r"\s", T) else T
                    alt = [x for k, x in enumerate(steps) if k not in drop and k != si]
                    alt.insert(si, f"{S} <;> try {tt}")
                    emit("goalmerge:hoist", alt, f"{what}: {L} steps opening {len(occ)} of {len(bl)} blocks -> <;> try")
    # hoist-inner: a 1-2 step group found INSIDE >= 2 goal blocks (not at their start) -> deleted there + `any_goals (G)` at the
    # region start (it then runs before the blocks' earlier steps: Lean decides whether they commute)
    for at, bl, what, si in regions:
        if len(bl) < 2:
            continue
        for L in (1, 2):
            groups: dict[tuple, list] = {}
            for a, b, _ in bl:
                for j in range(a + 1, b - L):   # inside: not the opening step, not the block's last step
                    key = tuple(steps[k].strip() for k in range(j, j + L))
                    lst = groups.setdefault(key, [])
                    if not lst or lst[-1][1] != a:
                        lst.append((j, a))
            for key, occ in groups.items():
                if len(occ) < 2:
                    continue
                T = block_text(steps, occ[0][0], occ[0][0] + L)
                if T is None or T.startswith(("·", "case ", "next ")) or re.match(r"(?:intro|rintro|intros|obtain|rcases|cases|induction|rename_i|set|let|have)\b", T.lstrip("(")):
                    continue   # binders / splits / names: moving them changes what later steps see
                drop = frozenset(k for j, _ in occ for k in range(j, j + L))
                if drop in hoisted:
                    continue
                hoisted.add(drop)
                new_steps = []
                for k in range(n):
                    if k == at:
                        new_steps.append(f"{pad}any_goals {T}")
                    if k not in drop:
                        new_steps.append(steps[k])
                emit("goalmerge:hoistin", new_steps, f"{what}: {L} steps inside {len(occ)} of {len(bl)} blocks -> any_goals [inner]")
    # iterate: a run of identical consecutive step groups (always the same tactic program)
    for a in range(n):
        for ln in range(1, (n - a) // 2 + 1):
            grp = [steps[k].strip() for k in range(a, a + ln)]
            r = 1
            while a + (r + 1) * ln <= n and [steps[k].strip() for k in range(a + r * ln, a + (r + 1) * ln)] == grp:
                r += 1
            if r < 2:
                continue
            T = block_text(steps, a, a + ln)
            if T is None or (ln > 1 and T.count("(") == 0):
                continue
            emit("goalmerge:iterate", steps[:a] + [f"{pad}iterate {r} {T}"] + steps[a + r * ln:], f"steps {a}..{a + r * ln - 1}: {r} x {ln} steps")
    return list(out.values())


def merges(head: str, col: int, steps: list[str], g: list[int]) -> list[tuple[str, str, str]]:
    """[(variant, new body, note)] for the top block (head + the block's new text)."""
    return [(v, head + b + "\n", note) for v, b, note in merges_block(col, steps, g)]


# ------------------------------------------------------------------------------------------------------------------------------ nested
BAL_O, BAL_C = "([{⟨⦃", ")]}⟩⦄"


def _ind(l: str) -> int:
    return len(l) - len(l.lstrip(" "))


def _balanced(text: str) -> bool:
    d = 0
    for ch in text:
        if ch in BAL_O:
            d += 1
        elif ch in BAL_C:
            d -= 1
            if d < 0:
                return False
    return d == 0


def _scan(lines: list[str], lo: int, hi: int, col: int):
    """Step line ranges [(a, b)] of the block lines[lo:hi] at column col (trailing blank lines excluded), or None."""
    steps, prev = [], None
    for j in range(lo, hi):
        l = lines[j]
        if not l.strip():
            continue
        if _ind(l) < col:
            return None
        s = l.strip()
        if _ind(l) == col and not s.startswith(CONT_START) and not (prev is not None and _ends_cont(prev)):
            steps.append([j, j + 1])
        else:
            if not steps:
                return None
            steps[-1][1] = j + 1
        prev = l
    return [tuple(x) for x in steps]


BULLET_RE = re.compile(r"^(?P<pad> *)· (?P<rest>\S.*)$")


def split_bullets(body: str) -> str:
    """`<pad>· tac` whose bullet goes on over more lines -> `<pad>·` + `<pad>  tac` (same proof; the bullet's content becomes a block
    the probe can instrument)."""
    lines = body.split("\n")
    out = []
    for j, l in enumerate(lines):
        m = BULLET_RE.match(l)
        if m:
            pad = m.group("pad")
            nxt = next((x for x in lines[j + 1:] if x.strip()), None)
            if nxt is not None and _ind(nxt) == len(pad) + 2 and not _ends_cont(l):
                out.append(pad + "·")
                out.append(pad + "  " + m.group("rest"))
                continue
        out.append(l)
    return "\n".join(out)


def join_bullets(body: str) -> str:
    return re.sub(r"(?m)^( *)·\n\1  (?=\S)", r"\1· ", body)


def find_blocks(body: str):
    """(lines, blocks): lines = body.split("\n"); blocks = [(depth, lo, hi, col, steps)] for the top tactic block and every nested
    block that opens after a line ending in `by` / `=>` on a deeper-indented new line and closes by dedent (bracket-balanced)."""
    if body is None or "--" in body or "/-" in body or "\t" in body:
        return None
    m = HEAD_RE.match(body)
    if not m:
        return None
    lines = split_bullets(body.rstrip("\n")).split("\n")
    # line 0 is the `by` line (HEAD_RE ends at its newline)
    first = next((j for j in range(1, len(lines)) if lines[j].strip()), None)
    if first is None or _ind(lines[first]) == 0:
        return None
    out = []

    def rec(lo, hi, col, depth):
        st = _scan(lines, lo, hi, col)
        if not st:
            return
        out.append((depth, lo, st[-1][1], col, st))
        for a, b in st:
            j = a
            while j < b:
                l = lines[j].rstrip()
                if re.search(r"(?<![\w.'])by$", l) or l.strip() == "·" or (l.endswith("=>") and re.match(r"\s*(?:\||case\b|next\b)", l)):
                    k = next((x for x in range(j + 1, b) if lines[x].strip()), None)
                    if k is not None and _ind(lines[k]) > _ind(lines[j]):
                        c2 = _ind(lines[k])
                        e2 = k
                        while e2 < b and (not lines[e2].strip() or _ind(lines[e2]) >= c2):
                            e2 += 1
                        while e2 > k and not lines[e2 - 1].strip():
                            e2 -= 1
                        if _balanced("\n".join(lines[k:e2])):
                            rec(k, e2, c2, depth + 1)
                        j = e2
                        continue
                j += 1

    rec(first, len(lines), _ind(lines[first]), 0)
    return lines, out


def probe_text_all(lines: list[str], blocks) -> str:
    """The body with `trace "<MARK><b>_<k>"; trace_state` before every step of every block and after each block's last step."""
    before: dict[int, list[str]] = {}
    after: dict[int, list[tuple[int, str]]] = {}
    for bi, (depth, lo, hi, col, st) in enumerate(blocks):
        pad = " " * col
        for k, (a, b) in enumerate(st):
            before.setdefault(a, []).append(f'{pad}trace "{MARK}{bi}_{k}"; trace_state')
        after.setdefault(hi - 1, []).append((-depth, f'{pad}trace "{MARK}{bi}_{len(st)}"; trace_state'))
    out = []
    for j, l in enumerate(lines):
        out.extend(before.get(j, []))
        out.append(l)
        out.extend(x for _, x in sorted(after.get(j, []), key=lambda t: t[0]))
    return "\n".join(out) + "\n"


def parse_probe_all(messages, blocks) -> dict[int, list[int]]:
    """{block index: g[0..n]} for the blocks whose every reading arrived (pairing by line, as parse_probe)."""
    mark_at, states = {}, []
    for m in messages or []:
        if m.get("severity") not in (None, "information", "info"):
            continue
        t = K.msg_text(m)
        line = (m.get("pos") or {}).get("line")
        mm = re.fullmatch(rf"\s*{MARK}(\d+)_(\d+)\s*", t)
        if mm:
            if isinstance(line, int):
                mark_at[line] = (int(mm.group(1)), int(mm.group(2)))
        elif isinstance(line, int):
            states.append((line, sum(1 for ln in t.split("\n") if ln.startswith("⊢"))))
    got: dict[tuple, int] = {}
    for line, c in states:
        if line in mark_at and mark_at[line] not in got:
            got[mark_at[line]] = c
    out = {}
    for bi, (_, _, _, _, st) in enumerate(blocks):
        if all((bi, k) in got for k in range(len(st) + 1)):
            out[bi] = [got[(bi, k)] for k in range(len(st) + 1)]
    return out


def all_merges(body: str, lines: list[str], blocks, gs: dict) -> list[tuple[str, str, str]]:
    """[(variant, new body, note)] over every block with goal counts."""
    out = {}
    for bi, g in gs.items():
        depth, lo, hi, col, st = blocks[bi]
        steps = ["\n".join(lines[a:b]).rstrip() for a, b in st]
        if g[-1] != 0:
            continue
        for v, nb, note in merges_block(col, steps, g):
            new = join_bullets("\n".join(lines[:lo] + nb.split("\n") + lines[hi:])) + "\n"
            if new not in out:
                out[new] = (v, new, f"block {bi} (depth {depth}): {note}")
    return list(out.values())


SCREEN_N = 15


def prio(note: str) -> int:
    """Screen order class of a candidate (lower first): 0 every block has the same text, 1 `first` over the blocks / prefix /
    iterate, 2 a text shared by >= 2 blocks used for all, 3 one block's text used for all (rarely closes the others)."""
    if "[inner]" in (note or ""):
        return 2
    m = re.search(r"one block \((\d+)x of (\d+)\)", note or "")
    if not m:
        return 1
    k, n = int(m.group(1)), int(m.group(2))
    return 0 if k == n else 2 if k >= 2 else 3


def plain_text(statement: str, bodies: list[str]) -> str | None:
    """Renamed copies, each after a `#print "<MARK>C<i>"` marker (core Lean: no import needed)."""
    out = []
    for i, b in enumerate(bodies):
        r = MS.renamed(statement, i)
        if r is None:
            return None
        out.append(f'#print "{MARK}C{i}"\n' + r.rstrip() + " :=" + b.rstrip() + "\n")
    out.append(f'#print "{MARK}C{len(bodies)}"\n')
    return "theorem lraGMDummy : True := trivial\n\n" + "\n".join(out)


def parse_plain(messages, n: int) -> dict:
    """{i: {"ok": bool}}: copy i is ok when its marker and the next one were printed and no error (or sorry warning) lies between."""
    marks: dict[int, int] = {}
    errs: list[int] = []
    for m in messages or []:
        t = K.msg_text(m).strip()
        line = (m.get("pos") or {}).get("line")
        mm = re.fullmatch(rf"{MARK}C(\d+)", t)
        if mm and isinstance(line, int):
            marks[int(mm.group(1))] = line
        elif m.get("severity") == "error" or "sorry" in t:
            if isinstance(line, int):
                errs.append(line)
            else:
                return {}
    out = {}
    for i in range(n):
        if i in marks and i + 1 in marks:
            a, b = marks[i], marks[i + 1]
            out[i] = {"ok": not any(a <= e < b for e in errs)}
    return out


# ------------------------------------------------------------------------------------------------------------------------------ op API
def has_sites(proof: str, statement: str) -> bool:
    body = split_declaration(proof, statement)
    fb = find_blocks(body) if body is not None else None
    return bool(fb) and sum(len(b[4]) for b in fb[1]) >= 3


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict | None:
    try:
        return _query(proof, statement, run, versions=versions, ctx=ctx, log=log)
    except Exception as e:  # noqa: BLE001  (a failure proposes nothing)
        if log:
            log(f"goalmerge: query failed ({type(e).__name__}: {str(e)[:120]})")
        return None


def _query(proof: str, statement: str, run, *, versions=None, ctx=None, log=None) -> dict | None:
    body = split_declaration(proof, statement)
    fb = find_blocks(body) if body is not None else None
    if not fb:
        return None
    lines, blocks = fb
    if sum(len(b[4]) for b in blocks) < 3:
        return None
    vs = list(versions or [None])
    r = run(statement.rstrip() + " :=" + probe_text_all(lines, blocks), vs[0])
    gs = parse_probe_all(getattr(r, "messages", None), blocks)
    if 0 not in gs and len(blocks) > 1:   # a probe line broke the parse somewhere: the top block alone
        blocks = [b for b in blocks if b[0] == 0]
        r = run(statement.rstrip() + " :=" + probe_text_all(lines, blocks), vs[0])
        gs = parse_probe_all(getattr(r, "messages", None), blocks)
    if not gs:
        if log:
            log(f"goalmerge: probe gave no complete goal counts (ok={getattr(r, 'ok', None)}; {len(blocks)} blocks)")
        return None
    t0 = count_tokens(body)
    cands = [(v, b, note) for v, b, note in all_merges(body, lines, blocks, gs) if count_tokens(b) < t0]
    cands.sort(key=lambda x: (prio(x[2]), count_tokens(x[1])))
    cands = cands[:MAX_CANDS]
    g = {bi: gs[bi] for bi in sorted(gs)}
    if not cands:
        if log:
            log(f"goalmerge: {len(blocks)} blocks, counts for {len(gs)}, no candidate")
        return {"goalmerge": {"g": g, "screened": [], "key": K.proof_key(proof)}}
    exchange = (ctx or {}).get("exchange")
    screened = []
    hb_ok = None
    for f in range(2):
        chunk = cands[f * SCREEN_N:(f + 1) * SCREEN_N]
        if not chunk:
            break
        txt = MS.text(statement, [body] + [b for _, b, _ in chunk])
        rd = None
        if txt is not None and hb_ok is not False:
            rr = run(txt, vs[0])
            rd = MS.parse(getattr(rr, "messages", None), len(chunk) + 1)
            hb_ok = bool((rd.get(0) or {}).get("ok"))
            if not hb_ok:
                rd = None
        if rd is None:   # no meta library in this file's imports: plain renamed copies, ok / not ok only
            txt = plain_text(statement, [b for _, b, _ in chunk])
            if txt is None:
                break
            rr = run(txt, vs[0])
            rd = parse_plain(getattr(rr, "messages", None), len(chunk))
            ctl = None
        else:
            ctl = rd.pop(0)
            rd = {k - 1: v for k, v in rd.items()}
        for j, (v, b, note) in enumerate(chunk):
            x = rd.get(j) or {}
            if x.get("ok"):
                pred = MS.predicted(ctl, body, b, x, exchange) if ctl else float(t0 - count_tokens(b))
                screened.append({"variant": v, "body": b, "note": note, "pred": pred, "hb": x.get("hb")})
        if screened:
            break
    if log:
        log(f"goalmerge: {len(blocks)} blocks, counts for {len(gs)}, cands={len(cands)} screened_ok={len(screened)}")
    return {"goalmerge": {"g": g, "screened": screened, "key": K.proof_key(proof)}}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    try:
        q = (ctx or {}).get("goalmerge")
        if not q or q.get("key") != K.proof_key(proof):
            return []
        sc = sorted(q.get("screened") or [], key=lambda x: -(x["pred"] if x["pred"] is not None else -1e18))
        out = []
        for x in sc:
            out.append({"op": x["variant"], "decl": statement.rstrip() + " :=" + x["body"].rstrip(), "note": f"{x['note']}; pred {x['pred']}"})
        return out[: (max_per_op or 8)]
    except Exception:  # noqa: BLE001
        return []
