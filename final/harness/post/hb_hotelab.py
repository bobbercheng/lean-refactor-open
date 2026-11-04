#!/usr/bin/env python3
"""Post-step v4 op `hb_hotelab`: argon_hbelab's own elaboration-cost rewrite families, re-targeted to the proof's profiled hot steps.

argon_hbelab (v3, unchanged and imported read-only here) builds a candidate pool of generic rewrites (`rw` -> `rewrite`, `simp only` ->
`dsimp only`, `unfold` -> `dsimp only`, `set` / `let` -> `have`, `simp_all` -> `simp [*]`, Simp.Config / Grind.Config flags, the
pre-order `↓` marker, ...) and screens it in text / priority order up to a cap: (per_file - 1) x files copies in its one-file heartbeat
screen (30 at most; 15 or fewer when the row compiles in over 35 s; 23 in its plain-check mode). On long proofs the pool is larger than
the cap, so the rewrites of the steps that actually cost the heartbeats are often never read. This op:

  1. profile   one compile of the current proof with a marker tactic before every tactic-start line (a logging `elab`; a `run_tac`
               marker on a file that cannot define one, its own constant cost calibrated by a doubled first marker and subtracted);
               consecutive marker readings give each step's heartbeats. Fallback (at most three compiles): the other marker kind,
               markers on the top-level block only; else no profile and no candidates. The markers exist only in this query text, never in a candidate.
  2. select    hbelab's pool (`_collect_candidates`) minus the part hbelab screens itself on this row (the same window rule as hbelab's
               query, from the same compile seconds), plus hbelab's simp-config / pre-order families on hot simp sites that its pool
               leaves out (it emits config flags for its six statically heaviest simp sites and at most three `↓` per list); keep the
               candidates whose first edit lies in a step costing at least HOT_SHARE of the reference heartbeats, ordered by that step's
               cost. The Grind.Config flag family is left out (measured dry on profiled hot `grind` steps).
  3. screen    hbelab's own screens, imported read-only: Mode 1 (`#eval` + `elabCommand` heartbeat sandwiches, `_screen_text` /
               `_parse_screen`), or Mode 2 (`_plain_check_text` / `_parse_plain_check`) when Mode 1 does not read on the row's file;
               at most MAX_SCREEN copies in at most MAX_FILES files; a copy is a winner when hbelab's `_predicted` (heartbeats saved minus
               tokens added at the row's exchange rate) is positive.
               The profile and screen copies carry the `.. in` combinators the row's compile attaches to the declaration
               (harness/open_post.attached_in, e.g. an `open X in`), which hbelab's own copies leave out.
               A copy a readable screen measured as no gain is remembered per statement (its old line -> new line); a later round
               of the row does not screen that same edit again (no compile at all when nothing new is left).
  4. propose   hbelab's `_build_winner_dicts`: merged config flags per site, a greedy per-line combination of the winners, then the
               winners best first (op names re-tagged `hb_hotelab:*`).

Model-free, deterministic, $0. Reads only the proof, the statement and the row's own environment (compiles on its primary pin, its
reference heartbeats through the meter); no row names, tables or proof text. Every token a candidate adds is one argon_hbelab
already adds. Lane interface (harness/open_post._gen_lane): has_sites(proof, statement) / query(proof, statement, run, versions=,
ctx={compile_s, exchange, inc_hb}, stats=, log=) / candidates(proof, statement, ctx=<query dict>)."""
from __future__ import annotations

import bisect
import hashlib
import re
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scorer.tokenize import count_tokens, split_declaration  # noqa: E402
from harness.post import argon_hbelab as HB  # noqa: E402  (read-only: none of its names or state is modified here)

FAMILY = "hb_hotelab"
HOT_SHARE = 0.003        # a step is hot when it costs at least this share of the reference heartbeats (0.3 H-points)
MAX_SCREEN = 30          # copies screened per round
MAX_FILES = 3            # screen files per round (Mode 1); Mode 2 files hold up to PLAIN_PER_FILE copies
PLAIN_PER_FILE = HB.MAX_PLAIN_VARIANTS - 1
MAX_COMPILE_S = 120.0    # a row whose input compiles slower than this is left alone (each screen copy re-elaborates the proof)
SKIP_KINDS = ("grind_config",)   # open83 census (2026-11-04): Grind.Config flags on profiled hot grind steps, 0 positive of 117 copies
CAL_MARK, END_MARK = 99999, 88888

_MARK_DEF = (
    "theorem lraHotelabDummy : True := trivial\n"
    'elab "lra_hotelab_mark " n:num : tactic => do\n'
    "  let h ← IO.getNumHeartbeats\n"
    '  Lean.logInfo (Lean.toMessageData ("LRAHOTM " ++ toString n.getNat ++ " " ++ toString h))\n'
)
_NO_START = ("|", "<;>", ")", "]", "⟩", "}", "at ", "using", "then", "else", ":=", "with ", "termination_by", "decreasing_by", "fun ",
             "λ", ".", "←", "+", "*", "=", "$", "<|", "·")
_PUSH_END = (" by", "=>", " do")
_NO_CMD_ELAB: set[str] = set()   # statements whose Mode 1 screen did not read (this op's own memory; hbelab's is not touched)
_LOSERS: dict[str, set] = {}     # statement -> line edits a readable screen already measured as not predicted to gain (later rounds skip
_LOSERS_LOCK = threading.Lock()  # them: the same old line -> new line again; a row's rounds run on one thread, rows on others)


def _key(text: str) -> str:
    return hashlib.sha256((text or "").rstrip().encode()).hexdigest()[:16]


# ------------------------------------------------------------------------------------------------------------------------------ profile
def _depth(s: str) -> int:
    d = 0
    for ch in s:
        if ch in "([{⟨":
            d += 1
        elif ch in ")]}⟩":
            d -= 1
    return d


def _mark(ind: int, k: int, runtac: bool) -> str:
    if runtac:
        return " " * ind + ('run_tac do let h ← IO.getNumHeartbeats; Lean.logInfo (Lean.toMessageData ("LRAHOTM %d " ++ toString h))' % k)
    return " " * ind + f"lra_hotelab_mark {k}"


def instrument(body: str, top_only: bool = False, runtac: bool = False):
    """`body` (the text after `:=`) with a marker line before every tactic-start line of its tactic blocks (top_only: of the outermost
    block only), a calibration marker doubling the first one, and an end marker. Returns (new_body, [(k, line_index, line_text)]) with
    line indices into body.lstrip('\\n').split('\\n'), or None (not a `by` block, or no marker placed). No marker goes before `|` arms,
    `<;>` / term continuations, `fun ... =>` lines or inside `conv` blocks."""
    lead = len(body) - len(body.lstrip("\n"))
    lines = body[lead:].split("\n")
    first = lines[0].strip()
    if not first.startswith("by"):
        return None
    out, marks, stack = [lines[0]], [], []
    depth = _depth(re.sub(r"--.*", "", lines[0]))
    pending = first == "by" or first.endswith(_PUSH_END) or first.endswith(" unhygienic")
    k = 0
    for i in range(1, len(lines)):
        ln = lines[i]
        code = re.sub(r"--.*", "", ln)
        st = code.strip()
        if not st:
            out.append(ln)
            continue
        ind = len(ln) - len(ln.lstrip(" "))
        start = False
        if depth == 0:
            if pending:
                if not stack or ind > stack[-1]:
                    stack.append(ind)
                pending = False
            while stack and ind < stack[-1]:
                stack.pop()
            if stack and ind == stack[-1] and st != "with" and not any(st.startswith(p) for p in _NO_START):
                start = True
            if stack and ind == stack[-1] and st.startswith("·"):
                start = True
            if top_only and len(stack) != 1:
                start = False
        if start:
            if k == 0:
                out.append(_mark(ind, CAL_MARK, runtac))
            out.append(_mark(ind, k, runtac))
            marks.append((k, i, st))
            k += 1
        out.append(ln)
        depth += _depth(code)
        if depth == 0:
            if st.startswith("· ") and not top_only:
                stack.append(ind + 2)
            arrow_ok = st.endswith("=>") and st.startswith(("case ", "next", "| ")) and "fun " not in st and "λ" not in st
            if (st.endswith((" by", " do")) or arrow_ok or st == "·" or st == "by") and not (st.endswith("=>") and not arrow_ok):
                pending = "conv" not in st
    if not marks:
        return None
    top = min(len(x) - len(x.lstrip(" ")) for x in out if x.strip().startswith(("lra_hotelab_mark", "run_tac do let h")))
    out.append(_mark(top, END_MARK, runtac))
    return "\n" * lead + "\n".join(out), marks


def profile_text(statement: str, body_instr: str, runtac: bool, attached: str = "") -> str:
    """The profile compile's text (after the row's file prefix): a dummy theorem that absorbs the prefix's trailing `.. in`
    combinators, the marker `elab` (not for run_tac markers), then the declaration with the combinators the row's compile attaches to
    it (`attached`, one per line) and `Elab.async false`."""
    sep = "" if body_instr.startswith((" ", "\n")) else " "
    head = "theorem lraHotelabDummy : True := trivial\n" if runtac else _MARK_DEF
    return head + "\n" + attached + "set_option Elab.async false in\n" + statement.rstrip() + " :=" + sep + body_instr.rstrip() + "\n"


def parse_fires(messages) -> list[tuple[int, int]]:
    fires = []
    for m in messages or ():
        for ln in str((m or {}).get("data") or "").split("\n"):
            p = ln.strip().split()
            if len(p) == 3 and p[0] == "LRAHOTM" and p[1].isdigit() and p[2].isdigit():
                fires.append((int(p[1]), int(p[2])))
    return fires


def step_costs(fires: list[tuple[int, int]], marks: list) -> dict[int, float]:
    """{line_index: heartbeats (thousands, the meter's unit) between a marker's firings and the next firing}, the marker's own cost
    (the calibration segment, per firing) subtracted; the end marker's and the calibration segment are dropped."""
    agg: dict[int, int] = {}
    cnt: dict[int, int] = {}
    for (a, ha), (_b, hb) in zip(fires, fires[1:]):
        agg[a] = agg.get(a, 0) + (hb - ha)
        cnt[a] = cnt.get(a, 0) + 1
    cal = agg.pop(CAL_MARK, 0) / max(1, cnt.pop(CAL_MARK, 1))
    agg.pop(END_MARK, None)
    line_of = {k: i for k, i, _t in marks}
    out: dict[int, float] = {}
    for k, v in agg.items():
        if k in line_of:
            li = line_of[k]
            out[li] = out.get(li, 0.0) + max(0.0, (v - cal * cnt.get(k, 1)) / 1000.0)
    return out


def _profile_once(statement, body, run, version, runtac, top, stats, attached):
    """One profile compile: (step costs or None, whether any marker fired)."""
    got = instrument(body, top_only=top, runtac=runtac)
    if got is None:
        return None, False
    bi, marks = got
    r = run(profile_text(statement, bi, runtac, attached), version)
    fires = parse_fires(getattr(r, "messages", None))
    if stats is not None:
        stats["profile_compiles"] = stats.get("profile_compiles", 0) + 1
    if getattr(r, "ok", False) and len(fires) >= 2:
        if stats is not None:
            stats["profile_level"] = ("top" if top else "full") + ("/run_tac" if runtac else "/elab")
        return step_costs(fires, marks), True
    return None, bool(fires)


def profile(statement: str, body: str, run, version, cmd_ok: bool = True, stats: dict | None = None, attached: str = ""):
    """(per-line step costs of `body`, marker kind that read) or (None, None); at most three compiles. The logging `elab` marker on the
    full instrumentation (when the row's file can define one, cmd_ok); when a marker fired but the text did not compile, the same kind on
    the top-level block only; when none fired, the `run_tac` marker on the full instrumentation (then, if one fired, top-level only);
    when no marker of either kind fired, the first kind on the top-level block only."""
    kinds = (False, True) if cmd_ok else (True,)
    for runtac in kinds:
        costs, fired = _profile_once(statement, body, run, version, runtac, False, stats, attached)
        if costs is not None:
            return costs, ("run_tac" if runtac else "elab")
        if fired:
            costs, _f = _profile_once(statement, body, run, version, runtac, True, stats, attached)
            return (costs, ("run_tac" if runtac else "elab")) if costs is not None else (None, None)
    costs, _f = _profile_once(statement, body, run, version, kinds[0], True, stats, attached)
    return (costs, ("run_tac" if kinds[0] else "elab")) if costs is not None else (None, None)


def attached_of(run) -> str:
    """The `.. in` combinators the row's compile attaches to the declaration (harness/open_post.attached_in, read-only), '' without."""
    meter = getattr(run, "meter", None)
    if meter is None:
        return ""
    try:
        from harness.open_post import attached_in
        return attached_in(meter) or ""
    except Exception:  # noqa: BLE001  (no prefix: none)
        return ""


def screen_text(statement: str, bodies: list[str], attached: str = "") -> str | None:
    """hbelab's Mode 1 screen text (its `_screen_text`), each copy's source preceded by the attached combinators."""
    if not attached:
        return HB._screen_text(statement, bodies)
    chunks = ["theorem lraArgonDummy : True := trivial\n"]
    for i, b in enumerate(bodies):
        got = HB._renamed_decl(statement, b, i)
        if got is None:
            return None
        src, rel = got
        chunks.append(HB._EVAL_TEMPLATE.replace("__LRA_SRC__", HB._lean_str(attached + src)).replace("__LRA_IDX__", str(i))
                      .replace("__LRA_NAME_EXPR__", HB._lean_name_expr(rel)))
    return "".join(chunks)


def plain_check_text(statement: str, bodies: list[str], attached: str = ""):
    """hbelab's Mode 2 text (its `_plain_check_text`), each declaration preceded by the attached combinators; (text, spans)."""
    if not attached:
        return HB._plain_check_text(statement, bodies)
    if not bodies:
        return None
    warm = HB._renamed_decl(statement, bodies[0], 999)
    if warm is None:
        return None
    att = attached.rstrip("\n").split("\n")
    lines = ["theorem lraArgonDummy : True := trivial", "#check @lraArgonDummy", "set_option Elab.async false"]
    lines += att + ["set_option maxHeartbeats 400000 in"] + warm[0].rstrip("\n").split("\n")
    spans = []
    for i, b in enumerate(bodies):
        got = HB._renamed_decl(statement, b, i)
        if got is None:
            return None
        src, rel = got
        lines.append(f'#eval show IO Unit from do let h ← IO.getNumHeartbeats; IO.println s!"LRAHB_S\\t{i}\\t{{h}}"')
        start = len(lines) + 1
        lines += att + ["set_option maxHeartbeats 400000 in"] + src.rstrip("\n").split("\n")
        lines.append(f'#eval show IO Unit from do let h ← IO.getNumHeartbeats; IO.println s!"LRAHB_E\\t{i}\\t{{h}}"')
        lines.append(f"#check @{rel}")
        spans.append((start, len(lines)))
    return "\n".join(lines) + "\n", spans


# ------------------------------------------------------------------------------------------------------------------------------ select
def _line_starts(body: str) -> list[int]:
    lead = len(body) - len(body.lstrip("\n"))
    starts, o = [], lead
    for ln in body[lead:].split("\n"):
        starts.append(o)
        o += len(ln) + 1
    return starts


def step_of(pos: int, starts: list[int], marked: list[int]) -> int | None:
    """The marked line index of the step containing offset `pos`: the last marked line at or before pos's line."""
    li = bisect.bisect_right(starts, pos) - 1
    j = bisect.bisect_right(marked, li) - 1
    return marked[j] if j >= 0 else None


def hbelab_window(ctx: dict, plain: bool) -> int:
    """How many of hbelab's pool candidates its own query screens on this row (its window rule, from the same compile seconds; plain:
    its Mode 2, when its Mode 1 screen does not read on the row's file). On a row whose file attaches `.. in` combinators that hbelab's
    copies lose, the window is still left to hbelab (v4_rescreen re-runs hbelab's own screen there with the combinators)."""
    if plain:
        return HB.MAX_PLAIN_VARIANTS - 1
    per = HB._screen_budget(ctx)
    cs = ctx.get("compile_s")
    files = 1 if isinstance(cs, (int, float)) and float(cs) > 35.0 else HB.MAX_SCREEN_FILES
    return (per - 1) * files


def _kind(c) -> str:
    return c.op.split(":")[-1]


def extra_candidates(body: str, statement: str, pool) -> list:
    """hbelab's simp-config and pre-order families at every simp site (hbelab emits config flags at its six statically heaviest simp
    sites only, and at most three `↓` per list): the ones its pool lacks, built with hbelab's own site rules and flag table."""
    mask = HB._mask(body)
    pairs = HB._pairs(body, mask)
    fb = HB._first_by(body, mask)
    if fb < 0:
        return []
    tok0 = count_tokens(body)
    seen = {body.rstrip()} | {c.body.rstrip() for c in pool}
    raw = []
    for m in HB._SIMP_HEAD_RE.finditer(body):
        i, head = m.start(1), m.group(1)
        if not HB._tac_pos(body, mask, i, fb) or HB._in_conv(body, mask, i):
            continue
        if i + len(head) < len(body) and body[i + len(head)] == "?":
            continue
        info = HB._parse_simp_prefix(body, mask, pairs, m.end(1))
        if info is None:
            continue
        if not info["cfgs"]:
            for fi, (setting, desc) in enumerate(HB.SIMP_FLAGS.get(head, ())):
                if setting[1:] in info["options"]:
                    continue
                raw.append((f"{HB.FAMILY}:simp_config", ((m.end(1), 0, " " + setting),), f"{head} {setting} ({desc})", 20 + fi))
        if head in ("simp", "simpa", "simp_all") and info["args"] is not None:
            lb, rb = info["args"]
            for x, y in HB._arg_spans(body, mask, pairs, lb + 1, rb - 1):
                arg = body[x:y].strip()
                if not arg or arg[0] in "↓↑-*" or arg.startswith("<-"):
                    continue
                clean = arg.lstrip("← ")
                if HB._PREORDER_HINT.search(clean):
                    raw.append((f"{HB.FAMILY}:preorder", ((x, 0, "↓"),), f"preorder ↓{clean[:28]}", 28))
    out = []
    for op, edits, note, prio in raw:
        nb = HB.apply_edits(body, edits)
        if nb.rstrip() in seen:
            continue
        seen.add(nb.rstrip())
        out.append(HB.EditCand(op=op, edits=edits, body=nb, decl=HB._full_decl(statement, nb), note=note,
                               dtok=count_tokens(nb) - tok0, prio=prio))
    return out


def beyond_window(body: str, statement: str, ctx: dict, plain: bool | None) -> list:
    """The candidates hbelab's own query does not screen on this row: its pool past its window (plain None: the smaller of its two
    windows) plus the extra hot-site families, without the skipped kinds; in pool order (extras last)."""
    pool = HB._collect_candidates(body, statement)
    win = min(hbelab_window(ctx, False), hbelab_window(ctx, True)) if plain is None else hbelab_window(ctx, plain)
    rest = [c for c in pool[win:] if _kind(c) not in SKIP_KINDS]
    return rest + [c for c in extra_candidates(body, statement, pool) if _kind(c) not in SKIP_KINDS]


def select_hot(cands: list, body: str, costs: dict[int, float], threshold: float, limit: int = MAX_SCREEN) -> list:
    """The candidates whose first edit lies in a step costing >= threshold, by that step's cost (most expensive first, then in order)."""
    starts = _line_starts(body)
    marked = sorted(costs)
    got = []
    for idx, c in enumerate(cands):
        if not c.edits:
            continue
        li = step_of(min(e[0] for e in c.edits), starts, marked)
        if li is None or costs.get(li, 0.0) < threshold:
            continue
        got.append((-costs[li], idx, c))
    got.sort(key=lambda x: (x[0], x[1]))
    return [c for _, _, c in got[:limit]]


# ------------------------------------------------------------------------------------------------------------------------------ lane API
def has_sites(proof: str, statement: str) -> bool:
    """Pure: hbelab's pool has candidates past the smallest possible window, or a simp site has an extra family candidate."""
    body = split_declaration(proof, statement)
    if body is None:
        return False
    try:
        pool = HB._collect_candidates(body, statement)
        if any(_kind(c) not in SKIP_KINDS for c in pool[1:]):
            return True
        return bool(extra_candidates(body, statement, pool))
    except Exception:  # noqa: BLE001
        return False


def _screen_mode1(statement, body0, chunk_list, run, version, exchange, attached="", measured=None):
    scored, ok_any, files = [], False, 0
    for f_idx, chunk in chunk_list:
        txt = screen_text(statement, [body0] + [c.body for c in chunk], attached)
        if txt is None:
            break
        r = run(txt, version)
        files += 1
        rd = HB._parse_screen(getattr(r, "messages", None), len(chunk) + 1)
        ctl = rd.get(0) or {"ok": False}
        if not ctl.get("ok"):
            if not rd and not ok_any:
                return None, files   # Mode 1 does not read here
            break
        ok_any = True
        if measured is not None:
            measured.extend(chunk)   # a readable control: every copy of this file was measured (a copy that did not read lost)
        for k, c in enumerate(chunk, 1):
            rk = rd.get(k) or {"ok": False}
            if rk.get("ok"):
                pr = HB._predicted(int(ctl["hb"]), c.dtok, int(rk["hb"]), exchange)
                if pr > 0:
                    scored.append((pr, f_idx + k, c))
    return scored, files


def _screen_mode2(statement, body0, chunk_list, run, version, exchange, attached="", measured=None):
    scored, files = [], 0
    for f_idx, chunk in chunk_list:
        built = plain_check_text(statement, [body0] + [c.body for c in chunk], attached)
        if built is None:
            break
        txt, spans = built
        r = run(txt, version)
        files += 1
        rd = HB._parse_plain_check(getattr(r, "messages", None), spans)
        ctl = rd.get(0) or {"ok": False}
        if not ctl.get("ok") or not isinstance(ctl.get("hb"), int):
            break
        if measured is not None:
            measured.extend(chunk)
        for k, c in enumerate(chunk, 1):
            rk = rd.get(k) or {"ok": False}
            if rk.get("ok") and isinstance(rk.get("hb"), int):
                pr = HB._predicted(int(ctl["hb"]), c.dtok, int(rk["hb"]), exchange)
                if pr > 0:
                    scored.append((pr, f_idx + k, c))
    return scored, files


def edit_sig(body: str, c) -> tuple | None:
    """A candidate's line edit independent of where the line sits: (kind, ((old line, new line), ...)); None when lines move."""
    old, new = body.split("\n"), c.body.split("\n")
    if len(old) != len(new):
        return None
    return (_kind(c), tuple((a, b) for a, b in zip(old, new) if a != b))


def _losers(skey: str) -> set:
    with _LOSERS_LOCK:
        return set(_LOSERS.get(skey) or ())


def _note_losers(skey: str, body: str, measured: list, winners: list) -> None:
    won = {id(c) for c in winners}
    sigs = {edit_sig(body, c) for c in measured if id(c) not in won}
    sigs.discard(None)
    if sigs:
        with _LOSERS_LOCK:
            _LOSERS.setdefault(skey, set()).update(sigs)


def _chunks(cands: list, per: int, files: int) -> list:
    return [(i, cands[i:i + per]) for i in range(0, len(cands), per)][:files]


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    ctx = dict(ctx or {})
    st = stats if stats is not None else {}
    say = log or (lambda *a: None)
    body0 = split_declaration(proof, statement)
    if body0 is None or HB._renamed_decl(statement, body0, 0) is None:
        return ctx
    cs = ctx.get("compile_s")
    if isinstance(cs, (int, float)) and float(cs) > MAX_COMPILE_S:
        return ctx
    skey = _key(statement)
    lost = _losers(skey)

    def fresh(cands):   # an edit an earlier round of this row already screened as a loser is not screened again
        return [c for c in cands if edit_sig(body0, c) not in lost] if lost else cands
    if not fresh(beyond_window(body0, statement, ctx, None)):
        return ctx   # nothing (new) past either of hbelab's windows: no compile
    attached = attached_of(run)
    cmd_ok = skey not in _NO_CMD_ELAB and skey not in HB._NO_CMD_ELAB   # hbelab's memory is read, never written
    version = (versions or [None])[0]
    costs, kind = profile(statement, body0, run, version, cmd_ok=cmd_ok, stats=st, attached=attached)
    if not costs:
        say(f"{FAMILY}: no profile")
        return ctx
    if kind == "run_tac" and cmd_ok:
        _NO_CMD_ELAB.add(skey)   # the file cannot define an `elab`: hbelab's Mode 1 does not read here either
    meter = getattr(run, "meter", None)
    base = getattr(meter, "ref_hb", None) or ctx.get("inc_hb")
    if not base:
        return ctx
    thr = HOT_SHARE * float(base)
    exchange = ctx.get("exchange")
    scored, files, mode, nhot, nbeyond, measured = None, 0, "eval_hb", 0, 0, []
    if skey not in _NO_CMD_ELAB:
        cands = fresh(beyond_window(body0, statement, ctx, False))
        hot = select_hot(cands, body0, costs, thr)
        nbeyond, nhot = len(cands), len(hot)
        if hot:
            per = HB._screen_budget(ctx) - 1
            scored, files = _screen_mode1(statement, body0, _chunks(hot, per, MAX_FILES), run, version, exchange, attached, measured)
            if scored is None:
                _NO_CMD_ELAB.add(skey)
        else:
            scored = []
    if scored is None:
        mode = "plain_hb"
        cands = fresh(beyond_window(body0, statement, ctx, True))
        hot = select_hot(cands, body0, costs, thr)
        nbeyond, nhot = len(cands), len(hot)
        scored, f2 = _screen_mode2(statement, body0, _chunks(hot, PLAIN_PER_FILE, max(1, MAX_FILES - files)), run, version,
                                   exchange, attached, measured) if hot else ([], 0)
        files += f2
    st.update(beyond=nbeyond, hot=nhot, mode=mode, files=files)
    if not nhot:
        say(f"{FAMILY}: {nbeyond} candidate(s) past hbelab's window, none on a hot step")
        return ctx
    scored.sort(key=lambda x: (-x[0], x[1]))
    winners = [c for _, _, c in scored]
    _note_losers(skey, body0, measured, winners)
    dicts = HB._build_winner_dicts(proof, statement, body0, winners) if winners else []
    out = []
    for d in dicts:
        op = str(d.get("op") or "")
        out.append(dict(d, op=FAMILY + ":" + (op.split(":", 1)[1] if ":" in op else op)))
    st.update(winners=len(winners))
    say(f"{FAMILY}: {nbeyond} past hbelab's window, {nhot} on hot steps, screened in {files} file(s) ({mode}), "
        f"{len(winners)} winner(s), {len(out)} proposal(s)")
    ctx[FAMILY + "_for"] = _key(proof)
    ctx[FAMILY + "_cands"] = out
    return ctx


def candidates(proof: str, statement: str, *, exchange=None, max_per_op: int | None = None, ctx=None) -> list[dict]:
    """The query's screened proposals for this exact proof; nothing without them (no unscreened reads)."""
    ctx = ctx or {}
    if ctx.get(FAMILY + "_for") != _key(proof):
        return []
    out = list(ctx.get(FAMILY + "_cands") or [])
    return out if max_per_op is None else out[:max_per_op]
