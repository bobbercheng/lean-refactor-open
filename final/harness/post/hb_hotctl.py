#!/usr/bin/env python3
"""Lane op `hb_hotctl` (post-step v4, branch open-post-v4-hbhotctl, 2026-11-04): profile-guided elaboration controls on a proof's most
expensive tactic steps (the heartbeat lens H).

  query       one profile compile per round: the proof with a marker tactic before every tactic-start line (it logs
              IO.getNumHeartbeats) and an end-of-block marker, between `#eval` heartbeat sandwiches; consecutive firings give each step's
              heartbeats. The query text opens with a dummy theorem (it absorbs the file prefix's trailing `... in` combinators). The
              marker is an `elab` tactic defined in the query text; in a `module` file (no `elab` there) it is a `run_tac do ...`, whose
              constant cost is measured by a doubled first marker and subtracted from every step. When the profile does not compile, the
              markers go at the top block only, then nowhere (the global candidates alone). Markers are only ever in the query text.
  sites       the steps that cost at least SITE_SHARE of the reference heartbeats, at most MAX_SITES, hottest first
  menu        one-line edits of a site's first line: `with_reducible_and_instances ` / `with_reducible ` prefixes (after a bullet), the
              head swaps exact / refine / apply, `have h := e` -> `have h := by exact e`, `simp only` -> `dsimp only` / `simp_rw`,
              `rw` / `rewrite` -> `simp only`, `let` / `set` -> `have`, and the closers norm_num -> norm_num1 / simp, nlinarith ->
              linarith, ring / ring_nf -> ring1, abel / abel_nf -> abel1, rfl -> exact rfl, decide -> decide +kernel; a block step (one whose nested steps are profiled: a bullet,
              `case` / `next` / `| ..` arm, `have .. := by` ..) ranks by its block's cost and gets the control on its whole block; global: every tactic-start `exact` -> `refine`, and the whole proof under `by with_reducible`
              / `by with_reducible_and_instances` (after `by unhygienic`'s `unhygienic`)
  screen      argon_hbelab's batch screen files (imported read-only): Mode 1 (`#eval` elabCommand sandwiches) or Mode 2 (plain
              multi-theorem compile, `module` files), at most MAX_COPIES copies per file (the control included) and MAX_FILES files; a
              candidate is kept when its predicted gain is positive (heartbeats saved minus tokens added at the row's exchange rate,
              argon_hbelab._predicted)
  combo       the best kept edit per line, all applied at once, read in one more file; proposed first when it reads higher than the
              best single edit
  budget      at most MAX_COMPILES compiles per round; no query when the input's compile took more than MAX_COMPILE_S, and none started
              while the row's wall left is below the lane reserve (open_post.v3_reserve_s); adoption only through the post-step's gate

Generic Lean-syntax edits only: no row name, table or proof text; sites are chosen by measured per-step heartbeat share, not by text.
Model-free, deterministic budgets, $0."""
from __future__ import annotations

import hashlib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from harness.post import argon_hbelab as A  # noqa: E402  (read-only: _screen_text / _parse_screen, _plain_check_text / _parse_plain_check, _screen_budget, _predicted)
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "hb_hotctl"
MAX_COMPILES = 5          # per round: the profile (1-2), the screen files, the combo file
MAX_FILES = 3             # screen files per round
MAX_COPIES = 16           # copies per screen file, the control included
MAX_SITES = 16
SITE_SHARE = 0.0015       # a step is a site when it costs at least this share of the reference heartbeats (VM1 A/B on the v3 p2
                          # output, 2026-11-04: 0.0015 / 16 sites +5.26 vs 0.003 / 12 sites +5.10 paired, 750 vs 716 compiles)
MAX_COMPILE_S = 120.0     # no query when the input's primary compile took longer
RESERVE_MIN_S, RESERVE_MULT = 900.0, 40.0   # = open_post.v3_reserve_s: no compile starts while the row wall left is below this
CAL, END = 99999, 88888   # the calibration marker (doubled first marker) and the end-of-block marker
TAG = "LRAHHC"

ELAB_DEF = ('elab "lra_hhc_mark " n:num : tactic => do\n'
            '  let h ← IO.getNumHeartbeats\n'
            f'  Lean.logInfo (Lean.toMessageData ("{TAG} " ++ toString n.getNat ++ " " ++ toString h))\n')

# lines that never start a tactic step (continuations, arms, term lines, calc steps, trailing clauses)
NO_START = ("|", "<;>", "<|>", ")", "]", "⟩", "}", "at ", "using", "then", "else", ":=", "with ", "termination_by", "decreasing_by",
            "where", "fun ", "fun\t", "λ", ".", "←", "+", "*", "=", "$", "<|", "|>", "·", "_", ",", "↦", "from ")
CONT_END = ("<;>", "<|>", "<|", "|>", "$", ",", ":=", "↦", "←", "+", "=", "∧", "∨", "→", "↔")
CONT_WORD = re.compile(r"(?<![\w'.])(?:fun|from)$")   # keyword endings (not an identifier such as `hfun`)
TAIL_KW = ("termination_by", "decreasing_by", "where")
# a `with_reducible[_and_instances]` prefix goes on any tactic head except these structural ones (blocks, arms, the prefixes themselves)
NO_PREFIX = ("case", "case'", "next", "match", "conv", "conv_lhs", "conv_rhs", "with_reducible", "with_reducible_and_instances",
             "intro", "intros", "rename_i", "clear", "done", "skip", "sorry", "trivial", "exfalso", "left", "right", "assumption")


def _key(proof: str) -> str:
    return hashlib.sha256((proof or "").rstrip().encode()).hexdigest()[:16]


def _depth(s: str) -> int:
    d = 0
    for ch in s:
        if ch in "([{⟨":
            d += 1
        elif ch in ")]}⟩":
            d -= 1
    return d


def _code(ln: str) -> str:
    return re.sub(r"--.*", "", ln)


def _ind(ln: str) -> int:
    return len(ln) - len(ln.lstrip(" "))


def _split(body: str) -> tuple[int, list[str]]:
    lead = len(body) - len(body.lstrip("\n"))
    return lead, body[lead:].split("\n")


def _join(lead: int, lines: list[str]) -> str:
    return "\n" * lead + "\n".join(lines)


def marker(ind: int, k: int, kind: str) -> str:
    if kind == "runtac":
        return " " * ind + f'run_tac do let h ← IO.getNumHeartbeats; Lean.logInfo (Lean.toMessageData ("{TAG} {k} " ++ toString h))'
    return " " * ind + f"lra_hhc_mark {k}"


_CONV = re.compile(r"(?:·\s*)?conv(?:_lhs|_rhs)?(?![\w'])")


def _opens_block(st: str) -> bool:
    """A depth-0 line after which the next deeper line opens a tactic block (`by`, `do`, `case .. =>` / `next =>` / `| .. =>` arms,
    a lone bullet, `by unhygienic`); never a `conv` block or a `fun .. =>` term."""
    if _CONV.match(st):
        return False
    arrow = st.endswith("=>") and st.startswith(("case ", "case' ", "next", "| ")) and "fun " not in st and "λ" not in st
    if st.endswith("=>") and not arrow:
        return False
    return st.endswith((" by", " do", " unhygienic", " with_reducible", " with_reducible_and_instances")) or st in ("by", "·") or arrow


def _continues(prev: str) -> bool:
    """The previous depth-0 line leaves its step open (a binary combinator, an operator, `:=`, a `fun .. =>`), so a next line at the same
    column continues it."""
    return prev.endswith(CONT_END) or bool(CONT_WORD.search(prev)) or (prev.endswith("=>") and not _opens_block(prev))


def tactic_starts(body: str, top_only: bool = False) -> tuple[list[tuple[int, int]], int | None, int]:
    """[(line index, column)] of the tactic-start lines of a `by` body (lines after the first; the first line's own tactics are not
    instrumented), the top block's column, and the index of the first trailing clause line (`termination_by` / `decreasing_by` /
    `where` at depth 0 and at most the top column; len(lines) when none). No start inside brackets, `conv` blocks, `|` arms' heads,
    `<;>` / operator continuations or `fun .. =>` term lines."""
    lead, lines = _split(body)
    first = _code(lines[0]).strip()
    if not first.startswith("by"):
        return [], None, len(lines)
    starts: list[tuple[int, int]] = []
    stack: list[int] = []
    depth = _depth(_code(lines[0]))
    pending = depth == 0 and _opens_block(first)
    prev = first
    conv_ind = None   # inside a `conv` block opened by a line at this indentation
    cut = len(lines)
    for i in range(1, len(lines)):
        ln = lines[i]
        code = _code(ln)
        st = code.strip()
        if not st:
            continue
        ind = _ind(ln)
        if depth == 0 and re.match(r"(?:termination_by|decreasing_by|where)(?![\w'])", st) and (not stack or ind <= stack[0]):
            cut = i
            break
        start = False
        if depth == 0:
            if conv_ind is not None and ind > conv_ind:
                pass   # a conv-mode line: never a tactic start
            else:
                conv_ind = None
                cont = False
                if pending:
                    if not stack or ind > stack[-1]:
                        stack.append(ind)
                    pending = False
                else:
                    cont = _continues(prev)
                while stack and ind < stack[-1]:
                    stack.pop()
                if stack and ind == stack[-1] and not cont:
                    if st.startswith("·"):
                        start = True
                    elif st != "with" and not st.startswith(NO_START):
                        start = True
                if top_only and len(stack) != 1:
                    start = False
        if start:
            starts.append((i, ind))
        depth += _depth(code)
        if depth == 0:
            if conv_ind is None and _CONV.match(st) and st.endswith("=>"):
                conv_ind = ind
            elif conv_ind is None:
                mb = re.match(r"·\s+", st)
                if mb and len(st) > len(mb.group(0)) and not top_only:
                    stack.append(ind + len(mb.group(0)))   # the bullet's own block: its next lines
                if _opens_block(st):
                    pending = True
        prev = st
    top = stack[0] if stack else (starts[0][1] if starts else None)
    return starts, top, cut


def instrument(body: str, top_only: bool = False, kind: str = "elab") -> tuple[str, list[tuple[int, int, str]]] | None:
    """The body with markers (query text only): a doubled first marker (CAL) before the first start, marker k before the k-th
    tactic-start line, an END marker at the top column after the block (before a trailing clause). Returns (body, [(k, line index,
    line text)]) or None (no start line)."""
    lead, lines = _split(body)
    starts, top, cut = tactic_starts(body, top_only)
    if not starts or top is None:
        return None
    at = {i: col for i, col in starts}
    out: list[str] = []
    marks: list[tuple[int, int, str]] = []
    k = 0
    for i, ln in enumerate(lines):
        if i == cut:
            out.append(marker(top, END, kind))
            marks.append((END, i, "<end of tactic block>"))
        if i in at:
            if k == 0:
                out.append(marker(at[i], CAL, kind))
            out.append(marker(at[i], k, kind))
            marks.append((k, i, lines[i].strip()))
            k += 1
        out.append(ln)
    if cut >= len(lines):
        while out and not out[-1].strip():
            out.pop()
        out.append(marker(top, END, kind))
        marks.append((END, len(lines), "<end of tactic block>"))
    return _join(lead, out), marks


def _eval(tag: str) -> str:
    return '#eval show IO Unit from do let h ← IO.getNumHeartbeats; IO.println s!"%s_%s\\t{h}"\n' % (TAG, tag)


def profile_text(statement: str, body_instr: str, kind: str) -> str:
    """The profile query: a dummy theorem, the marker definition (elab kind), an `#eval` calibration pair around a trivial declaration,
    then the instrumented declaration between `#eval` heartbeat reads."""
    sep = "" if body_instr.startswith((" ", "\n")) else " "
    decl = statement.rstrip() + " :=" + sep + body_instr.rstrip() + "\n"
    head = "theorem lraHhcDummy : True := trivial\n" + (ELAB_DEF if kind == "elab" else "")
    return (head + _eval("S2") + "set_option Elab.async false in\ntheorem lraHhcDummy2 : True := trivial\n" + _eval("E2")
            + _eval("S") + "set_option Elab.async false in\n" + decl + _eval("E"))


def parse_profile(messages, marks: list[tuple[int, int, str]]) -> dict | None:
    """{"segs": [(k, line index, text, cost)] hottest first (heartbeats in thousands, one marker's cost subtracted per firing),
    "marker": one marker's cost, "total": the declaration's heartbeats (thousands), "fires"} or None (no firing read)."""
    fires: list[tuple[int, int]] = []
    tags: dict = {}
    for m in messages or ():
        for ln in str(m.get("data") or "").split("\n"):
            p = ln.strip().split()
            if len(p) == 3 and p[0] == TAG and p[1].isdigit() and p[2].isdigit():
                fires.append((int(p[1]), int(p[2])))
            elif ln.startswith(TAG + "_") and "\t" in ln:
                a, b = ln.strip().split("\t")[:2]
                if b.isdigit():
                    tags[a[len(TAG) + 1:]] = int(b)
    if len(fires) < 2:
        return None
    agg: dict = {}
    cnt: dict = {}
    for (a, ha), (_b, hb) in zip(fires, fires[1:]):
        agg[a] = agg.get(a, 0) + (hb - ha)
        cnt[a] = cnt.get(a, 0) + 1
    cal = (agg.pop(CAL, 0) / cnt.pop(CAL)) if CAL in cnt else 0.0
    txt = {k: (li, t) for k, li, t in marks}
    segs = []
    for k, v in agg.items():
        if k in (END, CAL) or k not in txt:
            continue
        segs.append((k, txt[k][0], txt[k][1], max(0.0, (v - cnt[k] * cal) / 1000.0)))
    segs.sort(key=lambda s: (-s[3], s[0]))
    total = None
    if all(x in tags for x in ("S", "E", "S2", "E2")):
        total = (tags["E"] - tags["S"] - (tags["E2"] - tags["S2"])) / 1000.0
    return {"segs": segs, "marker": cal / 1000.0, "total": total, "fires": len(fires)}


def block_costs(segs, lines: list[str]) -> dict:
    """{line index: the step's cost plus the costs of the profiled steps nested under it (the following steps indented deeper than its
    line, up to the first one that is not)}; a one-line step's block cost is its own."""
    own: dict = {}
    for s in segs:
        own[s[1]] = own.get(s[1], 0.0) + s[3]
    order = sorted(own)
    out = {}
    for a, li in enumerate(order):
        col = _ind(lines[li]) if 0 <= li < len(lines) else 0
        tot = own[li]
        for lj in order[a + 1:]:
            if not 0 <= lj < len(lines) or _ind(lines[lj]) <= col:
                break
            tot += own[lj]
        out[li] = tot
    return out


def hot_sites(segs, ref_hb, share: float = SITE_SHARE, top: int = MAX_SITES, lines: list[str] | None = None) -> list[tuple]:
    """The profiled steps whose cost (with `lines`: their block cost, block_costs) is at least `share` of the reference heartbeats
    (thousands), hottest first, at most `top`: [(k, line index, text, cost, own cost)]."""
    if not ref_hb:
        return []
    inc = block_costs(segs, lines) if lines is not None else {}
    ranked = [(s[0], s[1], s[2], inc.get(s[1], s[3]), s[3]) for s in segs]
    if lines is not None:
        ranked += [(-1, li, lines[li].strip(), c, 0.0) for li, c in arm_costs(segs, lines).items()]
    ranked.sort(key=lambda s: (-s[3], s[1]))
    return [s for s in ranked if s[3] >= share * float(ref_hb)][:top]


def arm_costs(segs, lines: list[str]) -> dict:
    """{line index: the summed costs of the profiled steps nested under it} for the `| .. =>` arm lines that open a block (no marker
    goes before an arm, so they have no cost of their own)."""
    own: dict = {}
    for s in segs:
        own[s[1]] = own.get(s[1], 0.0) + s[3]
    out = {}
    for li, ln in enumerate(lines):
        st = _code(ln).strip()
        if not (st.startswith("| ") and st.endswith("=>")) or "fun " in st or "λ" in st:
            continue
        col, tot = _ind(ln), 0.0
        for lj in range(li + 1, len(lines)):
            if not lines[lj].strip():
                continue
            if _ind(lines[lj]) <= col:
                break
            tot += own.get(lj, 0.0)
        if tot > 0:
            out[li] = tot
    return out


# ------------------------------------------------------------------------------------------------------------------------------ menu
def block_variants(line: str) -> list[tuple[str, str]]:
    """Whole-block forms of a step that opens a block of profiled steps -> [(tag, new text)]: `case .. =>` / `next =>` / a lone `·`
    get the control appended (its block follows on deeper lines); a bullet `· X` becomes `· <control>` with X on its own line at the
    bullet's content column (the control's tactic sequence is then the whole bullet block). Other block steps (`have .. := by`,
    `all_goals` ..) are wrapped whole by the one-line prefix (variants)."""
    ind = _ind(line)
    s = _code(line).rstrip()[ind:]
    out: list[tuple[str, str]] = []
    if (s.startswith(("case ", "case' ", "next", "| ")) and s.endswith("=>")) or s == "·":
        for tag, w in (("blk:withredinst", "with_reducible_and_instances"), ("blk:withred", "with_reducible")):
            out.append((tag, line.rstrip() + " " + w))
        return out
    mb = re.match(r"·\s+", s)
    if mb and len(s) > mb.end():
        col = ind + mb.end()
        for tag, w in (("blk:withredinst", "with_reducible_and_instances"), ("blk:withred", "with_reducible")):
            out.append((tag, " " * ind + "· " + w + "\n" + " " * col + line.rstrip()[col:]))
    return out


def variants(line: str, next_line: str | None = None) -> list[tuple[str, str]]:
    """Generic one-line edits of a step's first line -> [(tag, new line)], in screen priority order."""
    ind = _ind(line)
    s = line[ind:].rstrip()
    bullet = ""
    mb = re.match(r"·\s+", s)
    if mb:
        bullet, s = mb.group(0), s[mb.end():]
    m = re.match(r"[A-Za-z_][\w']*", s)
    h = m.group(0) if m else ""
    pre = " " * ind + bullet
    rest = s[len(h):]
    closed = _depth(_code(s)) == 0 and (next_line is None or not next_line.strip() or _ind(next_line) <= ind)
    out: list[tuple[str, str]] = []
    if h and h not in NO_PREFIX:
        out.append(("withredinst", pre + "with_reducible_and_instances " + s))
        out.append(("withred", pre + "with_reducible " + s))
    if h == "exact":
        out.append(("exact>refine", pre + "refine" + rest))
        out.append(("exact>apply", pre + "apply" + rest))
    elif h == "refine":
        out.append(("refine>apply", pre + "apply" + rest))
    elif h == "apply":
        out.append(("apply>exact", pre + "exact" + rest))
        out.append(("apply>refine", pre + "refine" + rest))
    elif h == "have" and closed:
        mm = re.match(r"have (.*?):= (.+)$", s)
        if mm and not mm.group(2).lstrip().startswith("by") and " from " not in mm.group(2):
            out.append(("have>byexact", pre + f"have {mm.group(1)}:= by exact {mm.group(2)}"))
    elif h == "simp" and s.startswith("simp only ["):
        out.append(("simponly>dsimponly", pre + "d" + s))
        out.append(("simponly>simp_rw", pre + "simp_rw" + s[len("simp only"):]))
    elif h in ("rw", "rewrite") and rest.lstrip().startswith("["):
        out.append((f"{h}>simponly", pre + "simp only" + rest))
    elif h in ("let", "set") and ":=" in s and not re.search(r"\swith\s", s):
        out.append((f"{h}>have", pre + "have" + rest))
    elif h == "norm_num" and not rest.strip().startswith(("+", "(")):
        if "[" not in rest:
            out.append(("norm_num>norm_num1", pre + "norm_num1" + rest))
        out.append(("norm_num>simp", pre + "simp" + rest))
    elif h == "nlinarith":
        out.append(("nlinarith>linarith", pre + "linarith" + rest))
    elif h in ("ring", "ring_nf") and not rest.strip():
        out.append((f"{h}>ring1", pre + "ring1"))
    elif h in ("abel", "abel_nf") and not rest.strip():
        out.append((f"{h}>abel1", pre + "abel1"))
    elif h == "rfl" and not rest.strip():
        out.append(("rfl>exact", pre + "exact rfl"))
    elif h == "decide" and not rest.strip():
        out.append(("decide>kernel", pre + "decide +kernel"))
    return out


def global_variants(body: str) -> list[tuple[str, str]]:
    """Whole-proof edits -> [(tag, new body)]: every tactic-start `exact` -> `refine`, and the proof under `by with_reducible` /
    `by with_reducible_and_instances`."""
    lead, lines = _split(body)
    out: list[tuple[str, str]] = []
    first = lines[0].strip() if lines else ""
    if first in ("by", "by unhygienic") and len(lines) > 1:
        for w in ("with_reducible_and_instances", "with_reducible"):
            out.append(("G:" + w, _join(lead, [lines[0].rstrip() + " " + w] + lines[1:])))
    gl = [lines[0]] + [re.sub(r"^(\s*(?:· )?)exact ", r"\1refine ", x) for x in lines[1:]]
    if gl != lines:
        out.append(("G:exact>refine", _join(lead, gl)))
    return out


def _full_decl(statement: str, body: str) -> str:
    sep = "" if body.startswith(("\n", " ", "\t")) else " "
    return f"{statement.rstrip()} :={sep}{body.rstrip()}\n"


def screen_list(body: str, sites) -> list[dict]:
    """The candidates to screen, in priority order: each site's menu (hottest site first; a block site's whole-block forms first), the
    global edits after the third site. A site's candidate replaces its one line (the "new" text may span lines)."""
    lead, lines = _split(body)
    b0 = count_tokens(body)
    out: list[dict] = []
    seen = {body.rstrip()}

    def add(tag, li, new, nb, cost):
        if nb.rstrip() in seen:
            return
        seen.add(nb.rstrip())
        out.append({"tag": tag, "line": li, "new": new, "body": nb, "dtok": count_tokens(nb) - b0, "cost": cost})
    glob = global_variants(body)
    for n, s in enumerate(sites):
        if n == 3:
            for tag, nb in glob:
                add(tag, -1, None, nb, 0.0)
        li = s[1]
        if not 0 < li < len(lines):
            continue
        nxt = next((x for x in lines[li + 1:] if x.strip()), None)
        block = len(s) > 4 and s[3] > s[4]
        for tag, nl in (block_variants(lines[li]) if block else []) + variants(lines[li], nxt):
            add(tag, li, nl, _join(lead, lines[:li] + [nl] + lines[li + 1:]), s[3])
    if len(sites) <= 3:
        for tag, nb in glob:
            add(tag, -1, None, nb, 0.0)
    return out


SCREEN_SLACK_HB = 1       # the screen file and the meter read a few heartbeats apart (a +2 screen reading passed the gate as +4)


def gate_ready(dh: int, dtok: int, pred: float, ref) -> bool:
    """Whether a screened edit can pass the post-step's accept gate (scorer.accept.decide) on its own, with the screen's slack: it saves
    a token or HB_EPS - SCREEN_SLACK_HB heartbeats (thousands), and it dominates (no token added, no heartbeat lost) or its predicted
    gain is at least half of MIN_GAIN exact points (pred in heartbeat thousands; score gain = pred / ref * 100 / 3)."""
    from scorer.accept import HB_EPS, MIN_GAIN
    if not (dtok <= -1 or dh >= HB_EPS - SCREEN_SLACK_HB) or pred <= 0:
        return False
    if dtok <= 0 and dh >= 0:
        return True
    return not ref or pred / float(ref) * 100.0 / 3.0 >= MIN_GAIN / 2.0


def combo_body(body: str, kept: list[dict], limit: int | None = None) -> tuple[str, list[dict]] | None:
    """The best kept edit per line (line >= 0), all applied at once (with `limit`: only the `limit` best of them); None when fewer
    than two lines have one."""
    best: dict = {}
    for c in kept:
        if c["line"] >= 0 and (c["line"] not in best or c["pred"] > best[c["line"]]["pred"]):
            best[c["line"]] = c
    if limit is not None:
        if len(best) <= limit:
            return None
        best = {c["line"]: c for c in sorted(best.values(), key=lambda c: (-c["pred"], c["line"]))[:limit]}
    if len(best) < 2:
        return None
    lead, lines = _split(body)
    nl = list(lines)
    for li, c in best.items():
        nl[li] = c["new"]
    return _join(lead, nl), [best[k] for k in sorted(best)]


# ------------------------------------------------------------------------------------------------------------------------------ query
def _file_facts(run, version) -> tuple[bool | None, str]:
    """(whether the row's file is a `module` file (no `elab` definitions there; None when unknown), the `open .. in` combinators among
    the declaration's trailing modifiers as plain `open ..` lines). The query texts open with a dummy theorem that takes the file
    prefix's trailing modifiers, so the declaration's own `open .. in` scopes are re-opened for the rest of the query text (the
    meter measures the declaration with them)."""
    meter = getattr(run, "meter", None)
    row = getattr(meter, "row", None) or {}
    if not row:
        return None, ""
    if row.get("source") == "putnambench" or not row.get("file_path"):
        return False, ""
    try:
        from scorer import compile as C
        core, mods = C.split_modifiers(C.file_prefix(row, version or (meter.versions[0])))
        opens = "".join(" ".join(m.group(1).split()) + "\n" for m in re.finditer(r"(open\s+[\w.\s]+?)\s+in\b", mods))
        return bool(C._MODULE_LINE.match(core)), opens
    except Exception:  # noqa: BLE001  (unknown: the elab marker first, no scopes)
        return None, ""


def with_opens(text: str, opens: str) -> str:
    """`opens` (whole `open ..` lines) right after the query text's first line (its dummy theorem); a Mode-2 file's line spans are
    measured from its `#check` line, which moves down with everything after it."""
    if not opens:
        return text
    i = text.find("\n") + 1
    return text[:i] + opens + text[i:]


_KIND: dict = {}   # statement key -> the marker kind whose profile read (later rounds of the row start with it)
_MODE: dict = {}   # statement key -> the screen mode whose control read


def has_sites(proof: str, statement: str) -> bool:
    body = split_declaration(proof, statement)
    if body is None:
        return False
    try:
        return bool(tactic_starts(body)[0]) or bool(global_variants(body))
    except Exception:  # noqa: BLE001
        return False


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    ctx = dict(ctx or {})
    say = log or (lambda *a: None)
    body = split_declaration(proof, statement)
    if body is None or A._renamed_decl(statement, body, 0) is None:
        return ctx
    cs = ctx.get("compile_s")
    if isinstance(cs, (int, float)) and float(cs) > MAX_COMPILE_S:
        say(f"{FAMILY}: skipped (input compile {float(cs):.0f} s > {MAX_COMPILE_S:.0f} s)")
        return ctx
    bud = getattr(run, "budget", None)
    reserve = max(RESERVE_MIN_S, RESERVE_MULT * float(cs or 120.0))
    used = [0]

    def can(n: int = 1) -> bool:
        if used[0] + n > MAX_COMPILES:
            return False
        try:
            return bud is None or bud.left_s() >= reserve
        except Exception:  # noqa: BLE001
            return True

    def go(text):
        used[0] += 1
        return run(text, (versions or [None])[0])

    vs = versions or [None]
    ref = getattr(getattr(run, "meter", None), "ref_hb", None)
    module, opens = _file_facts(run, vs[0])
    # the elab marker first; in a `module` file (or an unknown one) whose imports cannot define it, the run_tac marker once; a later
    # round of the same row starts with the kind that read before
    skey = _key(statement)
    kinds = ["elab"] if module is False else ["elab", "runtac"]
    if _KIND.get(skey) in kinds:
        kinds = [_KIND[skey]] + [k for k in kinds if k != _KIND[skey]]
    prof, level, kind = None, "none", "elab"
    for top_only in (False, True):
        if prof is not None:
            break
        for kd in (kinds if not top_only else [kind]):
            if prof is not None or not can(1) or (kd == "runtac" and not can(2)):
                break
            got = instrument(body, top_only=top_only, kind=kd)
            if got is None:
                break
            bi, marks = got
            r = go(with_opens(profile_text(statement, bi, kd), opens))
            kind = kd
            if getattr(r, "ok", False):
                p = parse_profile(getattr(r, "messages", None), marks)
                if p is not None and p["segs"]:
                    prof, level = p, ("top" if top_only else "full")
                    _KIND[skey] = kd
            if prof is None:
                errs = list(getattr(r, "errors", None) or [])
                why = " ".join(str(errs[0]).split())[:160] if errs else "no reading"
                say(f"{FAMILY}: profile ({'top' if top_only else 'full'}, {kd}) did not read: {why}")
    if ref is None and prof is not None:
        ref = prof.get("total")
    sites = hot_sites(prof["segs"], ref, lines=_split(body)[1]) if prof else []
    cands = screen_list(body, sites)
    if not cands:
        say(f"{FAMILY}: profile {level}, {len(sites)} site(s), no candidate")
        return ctx
    exchange = ctx.get("exchange")
    per_file = max(2, min(MAX_COPIES, A._screen_budget(ctx)))
    mode = "plain" if (prof is not None and kind == "runtac") else "eval"   # no elab definitions here: Mode 1's #eval cannot run either
    mode = _MODE.get(skey, mode)
    kept: list[dict] = []
    files = 0
    i = 0
    while i < len(cands) and files < MAX_FILES and can(2 if sites else 1):
        chunk = cands[i:i + per_file - 1]
        rd, how = _screen(statement, body, [c["body"] for c in chunk], mode, go, can, opens)
        if how is None:
            break
        mode = how
        files += 1
        if ((rd or {}).get(0) or {}).get("ok"):
            _MODE[skey] = how
        i += len(chunk)
        ctl = (rd or {}).get(0) or {}
        if not ctl.get("ok") or not isinstance(ctl.get("hb"), int):
            break
        for k, c in enumerate(chunk, 1):
            rk = (rd or {}).get(k) or {}
            if rk.get("ok") and isinstance(rk.get("hb"), int):
                pr = A._predicted(int(ctl["hb"]), int(c["dtok"]), int(rk["hb"]), exchange)
                if pr > 0:
                    kept.append(dict(c, pred=pr, hb=int(rk["hb"]), ctl=int(ctl["hb"])))
    kept.sort(key=lambda c: (-c["pred"], c["line"], c["tag"]))
    # proposed alone only when it can pass the gate (a token or HB_EPS heartbeats saved, MIN_GAIN points unless it dominates); the
    # smaller ones still go into the combo, whose sum can pass
    lone = [c for c in kept if gate_ready(c["ctl"] - c["hb"], c["dtok"], c["pred"], ref)]
    out = [_cand(statement, c["body"], c["tag"], f"{c['tag']} line {c['line']} predicted {c['pred']:+.0f}") for c in lone]
    combo_note = ""
    best_single = lone[0]["pred"] if lone else 0.0
    tried = set()
    for parts_wanted in (None, 2):
        cb = combo_body(body, kept, limit=parts_wanted)
        if cb is None or cb[0] in tried or not can(1):
            continue
        cbody, parts = cb
        tried.add(cbody)
        rd, how = _screen(statement, body, [cbody], mode, go, can, opens)
        c0, c1 = (rd or {}).get(0) or {}, (rd or {}).get(1) or {}
        if c0.get("ok") and c1.get("ok") and isinstance(c0.get("hb"), int) and isinstance(c1.get("hb"), int):
            dt = count_tokens(cbody) - count_tokens(body)
            pr = A._predicted(int(c0["hb"]), dt, int(c1["hb"]), exchange)
            combo_note += f"{', ' if combo_note else ''}combo of {len(parts)} predicted {pr:+.0f}"
            if pr > 0 and gate_ready(int(c0["hb"]) - int(c1["hb"]), dt, pr, ref):
                cand = _cand(statement, cbody, "combo", f"combo ({'+'.join(p['tag'] for p in parts)}) predicted {pr:+.0f}")
                out.insert(0 if pr > best_single else min(1, len(out)), cand)
                if pr > best_single:
                    break   # the full combo (or the pair) reads best: no second combo
        else:
            combo_note += f"{', ' if combo_note else ''}combo of {len(parts)} did not compile"
    say(f"{FAMILY}: profile {level}{' (run_tac)' if kind == 'runtac' and prof is not None else ''}, {len(sites)} site(s), {len(cands)} candidate(s), "
        f"{i} screened in {files} file(s) ({mode}), {len(kept)} kept{', ' + combo_note if combo_note else ''}; {used[0]} compile(s)")
    if stats is not None:
        stats.update({f"{FAMILY}_level": level, f"{FAMILY}_sites": len(sites), f"{FAMILY}_kept": len(kept), f"{FAMILY}_compiles": used[0]})
    ctx[f"{FAMILY}_for"] = _key(proof)
    ctx[f"{FAMILY}_cands"] = out
    return ctx


def _cand(statement: str, body: str, tag: str, note: str) -> dict:
    return {"op": f"{FAMILY}:{tag}", "decl": _full_decl(statement, body), "note": note}


def _screen(statement, body, bodies, mode, go, can, opens=""):
    """One batch screen file of [control] + bodies in `mode`; Mode 1 falls back to Mode 2 (once) when its control does not read.
    Returns ({index: {"ok", "hb"}}, the mode used) or (None, None) when nothing could be compiled."""
    if mode == "eval":
        txt = A._screen_text(statement, [body] + bodies)
        if txt is not None:
            r = go(with_opens(txt, opens))
            rd = A._parse_screen(getattr(r, "messages", None), len(bodies) + 1)
            if (rd.get(0) or {}).get("ok"):
                return rd, "eval"
        if not can(1):
            return None, None
    built = A._plain_check_text(statement, [body] + bodies)
    if built is None:
        return None, None
    ptxt, spans = built
    r = go(with_opens(ptxt, opens))
    return A._parse_plain_check(getattr(r, "messages", None), spans), "plain"


def candidates(proof: str, statement: str, *, exchange=None, max_per_op: int | None = None, ctx=None) -> list[dict]:
    """The query's screened proposals for this proof (nothing without a query: unscreened edits would only spend reads)."""
    ctx = ctx or {}
    if ctx.get(f"{FAMILY}_for") != _key(proof):
        return []
    out = list(ctx.get(f"{FAMILY}_cands") or [])
    return out if max_per_op is None else out[:max_per_op]
