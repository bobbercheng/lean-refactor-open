"""Driver v2 round 2 levers (docs/cc_driver_v2.md §8-§9, docs/opus_pass2_deep_dive.md R1-R5; 2026-10-12). Pure functions: no Lean, no git,
no model, no I/O beyond the workspace files a caller hands in. Used by prompt v2 (harness/prompt_v2.py), the v2 check path (harness/inrun.py)
and the driver (harness/agent_claude_code.py --prompt v2); unit-tested in harness/test_cc_levers.py.
  axis()           R1: points left on L and on H (against the measured floor) and the row's token<->heartbeat exchange rate: agent.py:926-936's
                   formula on the scorer's own helpers (scorer/* is not edited); heartbeat-first when >= 2 H points are left (floor-based, not
                   "H below L": rows under 2k hb top out near H 75)
  progress()       R2: checks this session and since its last new best; the stop rule (no finish before 8 checks without a new best, none
                   while >= 2 H points are left)
  heartbeat_map()  R1: the HEARTBEAT MAP block from a heartbeat_profile result (cached per proof sha), shown when >= 2 H points are left
  unverified_claims_v2(), notes_digest()    R5: the v2 claim filter (optimal|optimum|near.optimal|as short as; a limit claim needs a COMPILED
                   `[tested: ...]`), and a notes digest that keeps head and tail (v1 cut the newest entries: 4 of 10 p5 prompts)
  facts_sheet(), digest_v2(), escalate()    R3: the from-reference facts sheet (no Lean block over 2 lines), the v2 workspace digest, and the
                   escalation rule (the previous session gained < 0.5 -> from the reference, best kept)
Round-2 review (2026-10-12): the Lean-line rule knows the common Mathlib tactics and, through reindent(), flush-left code; the facts sheet strips
the notes' Lean before cutting them, keeps the Next ideas under the cap and no longer points to notes.md; no escalation on a gate under
ESCALATE_MIN_GATE.
Reviewer (2026-10-12, docs/cc_driver_v2.md §11; agent_claude_code.py --review):
  proof_sha()      the sha a review is bound to (the profile cache's key: sha256 of the proof text without trailing space)
  review_facts()   the reviewer's facts: checks by outcome and error class, the last attempts, winning-edit numbers, the notes' Failed / Next lines
                   and their unverified claims, no Lean block over 2 lines
  lint_review()    the saved review: Lean blocks over 2 lines (fenced, indented, flush-left or one inline-code span per line) and claims of
                   optimality (opt_claim(): the proof, a part of it or one axis) removed, capped
  review_header(), parse_review()   review.md's first line (best sha, run, time, lint counts)
  facts_sheet(head=...)   the same sheet with another first line (hx --claude-fresh-facts: a fresh lineage's view of the main lineage)
Failed-move registry (2026-10-13, docs/opus_pass2_deep_dive.md §3: failing checks that repeat an error already seen rose from 1% (p2) to 56%
(p5); notes stop exact resubmits, not the same move on a new candidate; agent.py / agent_claude_code.py --failed-moves, off by default):
  move_of(), attach_move()   a failed check's edit against the closer of its parents (stored best, reference): the changed lines, abstracted
                   (identifiers kept, literals and whitespace normalized) into a signature, plus the parent lines it touches; a rewrite is no move
  refutes()        a REAL compile refutation only: a failed check whose first error is a positioned Lean diagnostic, not a timeout / heartbeat
                   limit, a transport or process error (lean exit, lock, rate / usage limit), a statement or forbidden-construct refusal
  registry(), failed_moves_block()   moves grouped by (signature, first error class), refuted at >= FM_MIN_REFUTE refutations from as many
                   separate tool calls whose touched lines are all still in the base (the stored best or the session's candidate): a change of
                   the best in those lines reopens the move (void_stale(): for good, a revert does not bring the old count back); a signature
                   that later won (ledger wins) or an insertion already in the base is never refuted; text-less attempts (older records, the v2
                   check path before it records moves) count only for unknown names (qualified, or a ledger dead name), since the last new best
                   and only when the session starts from that best; the block is <= FM_CAP chars, one line per move, no Lean block over 2 lines
Review fixes (2026-10-13): environment failures (import / olean, line 1 of the compiled file, a first error above the declaration) and the
`… in` modifier's prefix are handled in refutes(); touched lines are keyed with their neighbour and occurrence; error-only entries have their
own header (UNKNOWN NAMES); failed_moves_render() returns the number of rows shown (runs[].failed_moves)."""
from __future__ import annotations

import collections, hashlib, re

H_FIRST = 2.0          # H points left (against the floor) from which heartbeats come first and the session may not finish (R1/R2)
STALL = 8              # checks without a new best before a session may finish (R2; the relay's "at least 8 checks" rule)
ESCALATE_GAIN = 0.5    # R3: a resumed session that gained less than this escalates the next one to a from-reference scout
ESCALATE_MIN_CHECKS = 4   # ... when it made at least this many checks (a trailing few-turn session is no evidence of a plateau)
ESCALATE_MIN_GATE = 1.4  # review 2026-10-12: no from-reference restart on a trailing gate (~$0.17 per check at xhigh: < 8 checks cannot rebuild
#                          an L 80+ best; pass 1 needed ~$2.68); the session resumes with the lever review instead
NOTES_CAP, NOTES_HEAD = 3000, 1000   # v1 digest: notes[:3000]
FACTS_CAP, FACTS_LINE = 2200, 180
REVIEW_CAP, REVIEW_FACTS_CAP = 3500, 2400   # the saved review (also its block in the next prompt) and the reviewer's facts


# ---- R1 / R2 instruments ---------------------------------------------------------------------------------------------------------------
def axis(ref_tokens, ref_hb, tokens, heartbeats, floor=None) -> dict | None:
    """agent.py's lean_check `axis` (Tier 1, panel R1) for the v2 tools: points left on each axis (upper bounds: no proof reaches 0 tokens;
    H against the floor once heartbeat_profile measured it) and the exchange rate between the axes on this row."""
    if not ref_tokens or not ref_hb or tokens is None or heartbeats is None:
        return None
    lp = round(tokens / ref_tokens * 100 / 3, 2); hp = round(max(0, heartbeats - (floor or 0)) / ref_hb * 100 / 3, 2)
    first = hp >= H_FIRST
    return {"points_left_length": lp, "points_left_heartbeats": hp, "heartbeat_floor": floor,
            "one_token_equals_heartbeats": round(ref_hb / ref_tokens, 1), "points_per_token": round(100 / (3 * ref_tokens), 4),
            "points_per_1k_heartbeats": round(100000 / (3 * ref_hb), 3), "work_on": "heartbeats" if first else "tokens",
            "note": ("points left are upper bounds (no proof reaches 0 tokens); "
                     + ("H is measured against the floor (heartbeat_profile.py)" if floor else
                        "heartbeat floor not measured yet: run heartbeat_profile.py (H points left are then exact)")
                     + (f"; {hp} H points left: heartbeats first (heartbeat_profile.py, then goal_map.py on the costliest block)" if first else ""))}


def progress(attempts: list, run_id, h_left=None) -> dict:
    """R2 counters for this session (its run id): checks, checks since its last new best (leantools sets an attempt's `score` only on a new
    best), and whether the stop rule lets it finish (h_left: H points left of the stored best)."""
    mine = [a for a in attempts if a.get("run_id") == run_id]
    since = 0
    for a in reversed(mine):
        if a.get("ok") and a.get("score") is not None:
            break
        since += 1
    hb = h_left is not None and h_left >= H_FIRST
    may = since >= STALL and not hb
    why = ("you may finish after normalize_check.py and notes.md" if may else
           f"keep going: {h_left} H points are left on the stored best" if hb else
           f"keep going: {since} of {STALL} checks without a new best")
    return {"checks_this_session": len(mine), "checks_since_new_best": since, "may_finish": may, "stop_rule": why}


def heartbeat_map(prof: dict | None, min_points: float = H_FIRST, max_blocks: int = 8) -> str:
    """The HEARTBEAT MAP block from a harness/profile.py result, or "" when it is missing, failed or leaves < min_points H points."""
    if not prof or not prof.get("ok") or prof.get("total") is None:
        return ""
    pl = prof.get("points_left_heartbeats")
    if pl is None and prof.get("floor") is not None and prof.get("reference"):
        pl = round((prof["total"] - prof["floor"]) / prof["reference"] * 100 / 3, 2)
    if pl is None or pl < min_points:
        return ""
    blocks = [b for b in (prof.get("blocks") or []) if b.get("heartbeats")][:max_blocks]
    lines = [f"HEARTBEAT MAP of candidate.lean (heartbeat_profile at session start: total {prof['total']} hb, floor {prof.get('floor')} hb = the "
             f"statement with a `sorry` body, local reference {prof.get('reference')} hb; about {pl} H points left above the floor, so heartbeats "
             "come first). Costliest blocks (candidate.lean lines, nested blocks under the costliest step):"]
    lines += [f"  lines {b.get('lines')}: {b['heartbeats']} hb  {str(b.get('text') or '')[:90]}" for b in blocks]
    if not blocks:
        lines.append("  (no block costs measured: run heartbeat_profile.py on the first compiling candidate)")
    return "\n".join(lines)


# ---- R5 claims and notes ---------------------------------------------------------------------------------------------------------------
V2_CLAIM_RE = re.compile(r"\b(optimal|optimum|near.optimal|as short as)\b", re.I)
LIMIT_RE = re.compile(r"\b(optimal|optimum|near.optimal|as short as|floor|minimal|minimum|tight|best possible|no further|"
                      r"cannot be (?:shorter|improved|reduced)|can't be (?:shorter|improved|reduced))\b", re.I)
TESTED_RE = re.compile(r"\[tested\b:?([^\]]*)\]?", re.I)
COMPILED_RE = re.compile(r"lean_check|variants|lean_run|lean_mine|normalize_check|heartbeat_profile|compil|\bcheck|\berror|\bfail|\bok\b|"
                         r"\bscore|\bhb\b|heartbeat", re.I)
RULE_RE = re.compile(r"statement|byte-for-byte|forbidden|sorry|axiom|native_decide", re.I)


def unverified_claims_v2(notes: str, limit: int = 8) -> list[str]:
    """v1's unverified_claims (agent.py:72, words from its _CLAIM_RE, which other lines share and is not edited) plus the R5 words
    optimal|optimum|near.optimal|as short as; a LIMIT claim (optimal, floor, minimal, tight, as short as, ...) counts as tested only when its
    `[tested: ...]` names a compile (a tool, an error, a score), not a count on paper (warm-up: 0 of 6 optimality claims flagged, all beaten)."""
    from harness.agent import _CLAIM_RE
    out = []
    for line in notes.splitlines():
        s = line.strip(" -*#>\t")
        if not (30 <= len(s) <= 220) or not (_CLAIM_RE.search(s) or V2_CLAIM_RE.search(s)) or RULE_RE.search(s):
            continue
        tags = TESTED_RE.findall(s)
        if tags and not (LIMIT_RE.search(s) and not any(COMPILED_RE.search(t) for t in tags)):
            continue
        if s not in out:
            out.append(s)
    return out[:limit]


def notes_digest(notes: str, cap: int = NOTES_CAP, head: int = NOTES_HEAD) -> str:
    """notes.md for the prompt: whole when it fits, else its head and its newest tail (line boundaries) with the omitted span named."""
    if len(notes) <= cap:
        return notes
    h = notes[:head]
    h = h[:h.rfind("\n")] if "\n" in h else h
    t = notes[len(notes) - (cap - len(h) - 90):]
    t = t[t.find("\n") + 1:] if "\n" in t else t
    return f"{h}\n[... {len(notes) - len(h) - len(t)} chars of older notes omitted here: Read notes.md for them ...]\n{t}"


_FENCE = re.compile(r"```[^\n]*\n(.*?)(?:```|\Z)", re.S)
_LEAN_WORDS = ("simp", "simp_all", "simpa", "dsimp", "grind", "omega", "aesop", "exact", "refine", "apply", "rw", "rwa", "intro", "rintro", "obtain",
               "rcases", "cases", "induction", "have", "show", "calc", "constructor", "use", "linarith", "nlinarith", "norm_num", "decide", "unfold",
               "all_goals", "any_goals", "first", "try", "case", "next", "fun_induction", "subst", "ext", "funext", "positivity", "ring", "field_simp",
               "trivial", "rfl", "assumption", "contradiction", "exfalso", "tauto", "ring_nf", "split", "split_ifs", "by_cases", "by_contra", "conv",
               "gcongr", "congr", "specialize", "generalize", "set", "let", "suffices", "change", "convert", "nomatch", "nofun", "fun_prop", "solve_by_elim",
               # round-2 review (2026-10-12): common tactics the first list missed (a flush-left or indented run of them passed the leak lint and the
               # facts-sheet strip); with these every word of discover.TACTICS is listed except `fun` / `only` (prose at a line start)
               "intros", "push_cast", "norm_cast", "exact_mod_cast", "assumption_mod_cast", "rw_mod_cast", "simp_rw", "nth_rewrite", "nth_rw", "rewrite",
               "erw", "left", "right", "interval_cases", "fin_cases", "mod_cases", "bv_decide", "zify", "qify", "push_neg", "linear_combination", "abel",
               "ac_rfl", "symm", "trans", "choose", "lift", "refine'", "apply_fun", "rename_i", "clear", "revert", "injection", "infer_instance",
               "exacts", "haveI", "letI", "contrapose", "contrapose!", "by_contra!", "wlog", "induction'", "cases'", "simp_arith", "norm_num1",
               "native_decide", "constructorm", "casesm", "split_ands", "exists", "existsi", "subst_vars", "simpa?", "simp?", "exact?", "apply?", "rw?")
_LEAN_START = re.compile(r"^\s*(?:[·•]\s*)?(?:" + "|".join(re.escape(w) for w in sorted(set(_LEAN_WORDS), key=len, reverse=True))
                         + r")(?![\w'])(?!\s*(?:->|→|:\s|was|is|fails|failed))")
_LEAN_SYM = re.compile(r":=|⟨|⊢|=>|<;>|←")
_DECL_START = re.compile(r"^\s*(theorem|lemma|example)\b|:=\s*by\s*$")


def leanish(line: str) -> bool:
    """A line that reads as Lean code, not prose: an indented tactic line / Lean symbols outside a list bullet, or a declaration head."""
    s = line.strip()
    if not s:
        return False
    if _DECL_START.search(line):
        return True
    if line[:1] not in " \t" or s[0] in "-*+#>" or re.match(r"\d+[.)]\s", s):
        return False
    return bool(_LEAN_START.match(line) or _LEAN_SYM.search(s))


def reindent(text: str) -> str:
    """Every non-blank line indented by two spaces (review 2026-10-12: indentation is no evidence in notes; flush-left Lean lines read as code
    too). Bullets and headers stay prose (leanish looks past the indentation)."""
    return "\n".join("  " + l.strip() if l.strip() else "" for l in text.split("\n"))


def _fence_lines(body: str) -> int:
    return sum(1 for l in body.split("\n") if l.strip())


def lean_block_lines(text: str) -> int:
    """Length of the longest Lean block: a fenced block's non-blank lines, or a run of consecutive Lean-looking lines."""
    longest = 0
    for m in _FENCE.finditer(text):
        longest = max(longest, _fence_lines(m.group(1)))
    run = 0
    for line in _FENCE.sub("\n", text).split("\n"):
        run = run + 1 if leanish(line) else 0
        longest = max(longest, run)
    return longest


def lean_lines(text: str) -> int:
    """All Lean-looking lines of a text, consecutive or not (fenced non-blank lines plus Lean-looking lines outside fences)."""
    return sum(_fence_lines(m.group(1)) for m in _FENCE.finditer(text)) + sum(1 for l in _FENCE.sub("\n", text).split("\n") if leanish(l))


def strip_lean_blocks(text: str, max_lines: int = 2) -> str:
    """Lean blocks longer than max_lines (fenced, or runs of Lean-looking lines) replaced by a one-line marker (the facts-sheet lint)."""
    def fence(m):
        n = _fence_lines(m.group(1))
        return m.group(0) if n <= max_lines else f"[Lean block of {n} lines omitted]"
    out, run = [], []
    for line in _FENCE.sub(fence, text).split("\n") + [""]:
        if leanish(line):
            run.append(line); continue
        out += run if len(run) <= max_lines else [f"[Lean block of {len(run)} lines omitted]"]
        run = []; out.append(line)
    return "\n".join(out[:-1])


_FAIL_HEAD = re.compile(r"fail|dead|tried|negative|do not|don't|doesn't|not work|reject|broke|avoid", re.I)
_NEXT_HEAD = re.compile(r"\bnext\b|todo|idea|plan|to try|open question", re.I)
_HEADER = re.compile(r"^\s*(?:#{1,6}\s+(.+?)|\*\*(.+?)\*\*:?|([A-Z][A-Za-z /'-]{2,40}):)\s*$")
_FAIL_LINE = re.compile(r"\[tested[^\]]*(?:fail|error|worse|no gain|not|slower|higher)|\bFAIL", re.I)


def notes_sections(notes: str) -> tuple[list[str], list[str]]:
    """(Failed lines, Next lines) of notes.md: lines under headers that name failures / next steps, plus tested-negative lines elsewhere."""
    failed, nxt, cur = [], [], None
    for line in notes.split("\n"):
        m = _HEADER.match(line)
        if m:
            h = next(g for g in m.groups() if g)
            cur = "fail" if _FAIL_HEAD.search(h) else "next" if _NEXT_HEAD.search(h) else None
            continue
        s = line.rstrip()
        if not s.strip():
            continue
        if cur == "fail" or (cur is None and _FAIL_LINE.search(s)):
            failed.append(s)
        elif cur == "next":
            nxt.append(s)
    return failed, nxt


ERR_CLASSES = (("unknown name", r"unknown (?:identifier|constant|namespace)|does not contain|unknown tactic"),
               ("rewrite failed", r"rewrite.{0,20}failed|did not find an occurrence|motive is not type correct"),
               ("type mismatch", r"type mismatch|has type|application type"),
               ("unsolved goals", r"unsolved goals"),
               ("no progress / no goals", r"made no progress|failed to simplify|no goals"),
               ("arith closer failed", r"linarith failed|omega could not|nlinarith|positivity failed|decide failed|norm_num failed"),
               ("timeout / heartbeats", r"maximum recursion|heartbeats|timeout|timed out|deterministic"),
               ("statement / forbidden", r"statement differs|forbidden"),
               ("syntax", r"unexpected token|expected|unknown syntax|parse"))


def error_class(err) -> str:
    e = str(err or "")
    return next((c for c, rx in ERR_CLASSES if re.search(rx, e, re.I)), "other")


def _cap(text: str, cap: int) -> str:
    if len(text) <= cap:
        return text
    t = text[:cap - 30]
    return t[:t.rfind("\n")] + "\n  (older facts omitted)"   # review 2026-10-12: no pointer to notes.md (it holds the earlier sessions' Lean)


def error_lines(bad: list, k: int = 8) -> list[str]:
    """Failed checks by error class, the k most common, with up to two one-line examples each (the facts sheet's and the reviewer's)."""
    cls: collections.Counter = collections.Counter(); ex: dict = {}
    for a in bad:
        c = error_class(a.get("error")); cls[c] += 1
        e = re.sub(r"\s+", " ", str(a.get("error") or "")).strip()[:110]
        if e and e not in ex.setdefault(c, []) and len(ex[c]) < 2:
            ex[c].append(e)
    return [f"  {c}: {n}" + ("".join(f"\n    e.g. {e}" for e in ex.get(c, []))) for c, n in cls.most_common(k)]


def _notes_facts(notes: str) -> tuple[list[str], list[str]]:
    """The notes' Failed / Next lines with their Lean blocks removed BEFORE the cut (short fenced code stays as plain lines)."""
    return notes_sections(re.sub(r"(?m)^[ \t]*```[^\n]*\n?", "", strip_lean_blocks(reindent(notes))))


FACTS_HEAD = ("FACTS SHEET (this problem's earlier sessions; facts only, no proof text: this session starts from the reference on purpose; build "
              "your own compiling architecture before you open best.lean or notes.md):")
# hx --claude-fresh-facts (2026-10-12, docs/cc_driver_v2.md §11): a fresh lineage (empty workspace) sees the main lineage's facts, never its proof
FRESH_FACTS_HEAD = ("FACTS SHEET (the MAIN lineage of this problem; facts only, no proof text: this fresh lineage starts from the reference in an "
                    "empty workspace on purpose; build your own compiling architecture; the main lineage's best below is the score to beat):")


def facts_sheet(state: dict, notes: str, cap: int = FACTS_CAP, head: str = FACTS_HEAD) -> str:
    """R3: what a from-reference session needs from the earlier ones, without their proof text: the stored best's numbers, failed checks by
    error class (one-line examples), notes' Failed / Next lines; Lean blocks over 2 lines removed. Review 2026-10-12: the notes' Lean blocks
    are removed BEFORE the sections are cut (a cut through a fence made the rest of the sheet one "block"), flush-left code counts, and over the
    cap the oldest Failed lines go first, so the Next ideas survive; nothing points to notes.md. `head`: the first line (FRESH_FACTS_HEAD for a
    fresh lineage, hx --claude-fresh-facts)."""
    b = state.get("best") or {}; at = state.get("attempts") or []
    lines = [head]
    if b.get("proof") or float(b.get("score") or 33.33) > 33.34:
        lmh = f" (L {b.get('L')}, H {b.get('H')}, Z {b.get('Z')})" if b.get("L") is not None else ""
        lines.append(f"- stored best, kept unless you beat it: score {b.get('score')}{lmh}, {b.get('tokens')} tokens, {b.get('heartbeats')} heartbeats")
    bad = [a for a in at if not a.get("ok")]
    lines.append(f"- {len(at)} earlier checks ({len(at) - len(bad)} compiled, {len(bad)} failed)" + (": failed by error class" if bad else ""))
    lines += error_lines(bad)
    failed, nxt = _notes_facts(notes)
    failed = [x.strip()[:FACTS_LINE] for x in failed[-14:]]; nxt = [x.strip()[:FACTS_LINE] for x in nxt[-8:]]

    def sheet() -> str:
        out = list(lines)
        if failed:
            out += ["- notes, Failed (do not repeat without a new reason):"] + ["  " + x for x in failed]
        if nxt:
            out += ["- notes, Next ideas:"] + ["  " + x for x in nxt]
        return strip_lean_blocks("\n".join(out))
    text = sheet()
    while len(text) > cap and (len(failed) > 3 or len(nxt) > 3):   # oldest Failed lines first, then the oldest Next ideas
        if len(failed) > 3:
            failed = failed[1:]
        else:
            nxt = nxt[1:]
        text = sheet()
    return _cap(text, cap)


def digest_v2(ws, facts: bool = False, current_run: str | None = None, n: int = 8) -> str:
    """Workspace.digest (agent.py:137) for prompt v2: the same header, attempts, WINNING EDITS and dead names; the notes as notes_digest (head
    and tail) with the v2 claim filter; the earlier-run count without the current session; facts=True (a from-reference session): the facts
    sheet instead of the notes and the winning-edit diffs (no Lean from the stored best)."""
    st = ws.state; b = st["best"]; at = st["attempts"]
    earlier = [r for r in st.get("runs", []) if r.get("run_id") != current_run] if current_run else st.get("runs", [])
    lines = [f"Prior work on this problem: {len(at)} checked attempts over {len(earlier)} earlier run(s). Best so far: score {b['score']} "
             f"(tokens {b.get('tokens')}, heartbeats {b.get('heartbeats')}); "
             + ("it is stored, NOT in candidate.lean (this session starts from the reference)." if facts else "candidate.lean holds it.")]
    if at:
        lines.append("Most recent attempts (tokens, heartbeats, outcome):")
        for a in at[-n:]:
            lines.append(f"  - tok={a.get('tokens')} hb={a.get('heartbeats')} {'OK score=' + str(a.get('score')) if a.get('ok') else 'FAIL: ' + str(a.get('error', ''))[:140]}")
    wins = sorted((st.get("ledger") or {}).get("wins", []), key=lambda w: -w.get("d_score", 0))[:6]
    if wins and not facts:
        lines.append("WINNING EDITS from earlier runs (harness log, verbatim; the current best may have lost some after a restructure: "
                     "check each and re-apply what still fits):")
        for w in wins:
            lines.append(f"  [{w.get('run_id')} check {w.get('check')}: {w.get('d_score'):+} score, {w.get('d_tokens'):+} tokens, {w.get('d_heartbeats'):+} hb]\n"
                         + "\n".join("    " + l for l in (w.get("diff") or "").splitlines()[:12]))
    elif wins:
        lines.append(f"WINNING EDITS: {len((st.get('ledger') or {}).get('wins', []))} recorded on the stored best's lineage (not shown here: build "
                     "your own architecture first).")
    dead = (st.get("ledger") or {}).get("dead_names") or []
    if dead:
        lines.append("NAMES THAT DO NOT EXIST in this environment (unknown in earlier runs' compiles; do not use them): "
                     + ", ".join(f"`{x}`" for x in dead[:15]))
    try:
        notes = (ws.root / "notes.md").read_text().strip()
    except OSError:
        notes = ""
    if facts:
        if at or len(notes.splitlines()) > 1:
            lines.append(facts_sheet(st, notes))
    elif len(notes.splitlines()) > 1:
        lines.append("Your notes.md from earlier runs" + (" (head and newest tail):\n" if len(notes) > NOTES_CAP else ":\n") + notes_digest(notes))
        claims = unverified_claims_v2(notes)
        if claims:
            lines.append("UNVERIFIED CLAIMS in these notes (cycle 36: the panel review found claims of this kind wrong on six problems: "
                         "'unavoidable', 'is the floor', 'grind never fires forward', 'set needed', 'a failed apply costs ~110 hb', 'tight'; each "
                         "blocked the move that later won; on the warm-up every claimed optimum was beaten). Treat them as hypotheses, not facts: a "
                         "limit claim (optimal, as short as, floor, minimal) counts only with a COMPILED check in its tag. If one blocks your most "
                         "promising idea, test it with one cheap check first, and write the result back as `[tested: <what you ran> -> <result>]`:\n"
                         + "\n".join("  ? " + c for c in claims))
    return "\n".join(lines)


def escalate(prior: list, attempts: list | None = None, threshold: float = ESCALATE_GAIN, gate: float | None = None,
             fresh: list | None = None) -> bool:
    """R3: the previous session of this lineage (prior = earlier runs entries, oldest first) gained < threshold over at least
    ESCALATE_MIN_CHECKS checks -> start this one from the reference with the facts sheet. Never right after a scout / escalated session
    (alternation, so a lineage is not stuck in from-reference sessions) and never without that session's best_before/best_after (v1 runs).
    Review 2026-10-12: never on a gate under ESCALATE_MIN_GATE (gate = this session's G; None = ungated), and never right after a fresh
    lineage or a rescue (fresh = state.json fresh_lineages: hx merges those into the main state without a runs[] entry, so the last entry is
    the session BEFORE them; the fresh lineage was itself a from-reference session, and an adopted one is still climbing)."""
    if gate is not None and gate < ESCALATE_MIN_GATE:
        return False
    last = next((r for r in reversed(prior) if not r.get("skipped")), None)
    if not last or last.get("mode") in ("scout", "escalated") or last.get("best_before") is None or last.get("best_after") is None:
        return False
    if any(str(f.get("t") or "") >= str(last.get("ended") or last.get("started") or "") for f in (fresh or [])):
        return False
    if attempts is not None and sum(1 for a in attempts if a.get("run_id") == last.get("run_id")) < ESCALATE_MIN_CHECKS:
        return False
    return float(last["best_after"]) - float(last["best_before"]) < threshold


# ---- the reviewer (2026-10-12, docs/cc_driver_v2.md §11, docs/opus_pass2_deep_dive.md R3: a fresh review naming
# concrete edits beat the Opus line on 10/10 targeted warm-up problems) ---------------------------------------------------------------------
def proof_sha(text: str | None) -> str:
    """The sha a review is bound to: the heartbeat-profile cache's key (sha256 of the proof without trailing whitespace, 12 hex)."""
    return hashlib.sha256((text or "").rstrip().encode()).hexdigest()[:12]


def review_facts(state: dict, notes: str, n: int = 8, cap: int = REVIEW_FACTS_CAP) -> str:
    """What the reviewer gets from the problem's records (it reads best.lean itself): checks by outcome and error class, the last n attempts,
    the winning edits' numbers (no diffs), the notes' Failed / Next lines and their unverified claims; no Lean block over 2 lines."""
    at = state.get("attempts") or []; bad = [a for a in at if not a.get("ok")]
    runs = [r for r in state.get("runs") or [] if r.get("kind") != "review" and not r.get("skipped")]
    lines = [f"FACTS from this problem's records ({len(at)} checks kept, {len(at) - len(bad)} compiled, {len(bad)} failed, over {len(runs)} "
             "executor session(s)):"]
    if bad:
        lines += ["- failed checks by error class:"] + error_lines(bad, 6)
    if at:
        lines.append("- last attempts (tokens, heartbeats, outcome):")
        lines += [f"  - tok={a.get('tokens')} hb={a.get('heartbeats')} "
                  + ("OK score=" + str(a.get("score")) if a.get("ok") else "FAIL: " + re.sub(r"\s+", " ", str(a.get("error", "")))[:140]) for a in at[-n:]]
    wins = sorted((state.get("ledger") or {}).get("wins", []), key=lambda w: -w.get("d_score", 0))[:6]
    if wins:
        lines.append("- winning edits so far (score, tokens, heartbeats; already in the best's lineage): "
                     + "; ".join(f"{w.get('d_score'):+} / {w.get('d_tokens'):+} / {w.get('d_heartbeats'):+}" for w in wins))
    failed, nxt = _notes_facts(notes)
    if failed:
        lines += ["- notes, Failed (tested negatives: propose one again only with a new reason):"] + ["  " + x.strip()[:FACTS_LINE] for x in failed[-12:]]
    if nxt:
        lines += ["- notes, Next ideas (not tested yet):"] + ["  " + x.strip()[:FACTS_LINE] for x in nxt[-8:]]
    claims = unverified_claims_v2(notes)
    if claims:
        lines += ["- UNVERIFIED CLAIMS in the notes (hypotheses, not facts; a lever may test one: every claimed optimum on the warm-up was beaten):"]
        lines += ["  ? " + c[:FACTS_LINE] for c in claims]
    return _cap(strip_lean_blocks("\n".join(lines)), cap)


# a claim that the proof, a part of it or one axis cannot improve (the reviewer is told never to make one; such lines are removed from the saved
# review). Review 2026-10-12: any subject before the copula, as LIMIT_RE ("the token count is essentially optimal", "lines 3-5 are already
# optimal", "the heartbeat count is at its floor", "everything else is already tight"). Not claims: a negated one ("not optimal", "far from
# optimal"), one about a lever's own risk / change / cost / gain or a bound of the mathematics ("the risk is minimal"), a noun phrase ("a minimal
# edit", "a minimum of 3").
_OPT_WORD = r"(?:near.)?(?:optimal|optimum|minimal|minimum|tight)|at (?:its|their|the) (?:floor|minimum|optimum)|best possible"
_OPT_COPULA = re.compile(r"(\w+)(?:\s+(?:is|are|looks?|seems?|appears?|stays?|remains?)|'s)\s+((?:[\w'-]+\s+){0,3}?)(?:" + _OPT_WORD
                         + r")\b(?!\s+(?:of|edit|edits|change|changes|fix|diff|rewrite|tweak)\b)", re.I)
_OPT_FIXED = re.compile(r"\bas short as (?:possible|it gets|it can be)\b|\b(?:cannot|can't|can not) be (?:shortened|shorter|improved|reduced|"
                        r"beaten|cut|trimmed)\b|\bno (?:further|more) (?:room|gains?|improvements?|savings?)\b", re.I)
_OPT_EXEMPT = frozenset(("risk", "risks", "change", "changes", "edit", "edits", "diff", "impact", "effect", "overhead", "downside", "chance",
                         "cost", "costs", "saving", "savings", "gain", "gains", "difference", "breakage", "bound", "bounds", "inequality",
                         "estimate", "let"))
_OPT_NEG = frozenset(("not", "never", "far", "hardly", "no", "nowhere"))
_LEVER_LINE = re.compile(r"(?m)^\s*(?:#{1,4}\s*)?(?:\*\*)?(?:lever\s*)?\d{1,2}[.):]", re.I)
CLAIM_MARK = "[claim of optimality removed: no limit claim counts without a compiled check]"
# a line that is one inline-code span, bare or as a list item (review 2026-10-12: a Lean block written one `span` per line or per bullet)
_CODE_LINE = re.compile(r"\s*(?:[-*+]\s+)?`([^`]+)`\s*[.,;]?\s*")


def opt_claim(line: str) -> bool:
    """True when the line claims that the proof, a part of it or one axis is optimal / minimal / tight / at its floor / cannot be improved."""
    if _OPT_FIXED.search(line):
        return True
    for m in _OPT_COPULA.finditer(line):
        if m.group(1).lower() not in _OPT_EXEMPT and not _OPT_NEG & set(m.group(2).lower().split()):
            return True
    return False


def lint_review(text: str, max_lines: int = 2, cap: int = REVIEW_CAP) -> tuple[str, dict]:
    """The reviewer's answer as saved (review.md) and shown to the next session: Lean blocks longer than max_lines (fenced, or runs of
    Lean-looking lines whatever their indentation: the facts-sheet / leak-lint rule; a line that is one inline-code span, bare or as a list
    item, counts by its code) and claims of optimality replaced by one-line markers, capped at a line boundary. Returns (text, counts)."""
    st = {"levers": 0, "blocks_removed": 0, "claims_removed": 0, "truncated": False}

    def fence(m):
        k = _fence_lines(m.group(1))
        if k <= max_lines:
            return m.group(0)
        st["blocks_removed"] += 1
        return f"[Lean block of {k} lines omitted]"
    out, run = [], []
    for line in _FENCE.sub(fence, (text or "").strip()).split("\n") + [None]:
        m = _CODE_LINE.fullmatch(line) if line is not None else None
        code = m.group(1) if m else line
        if line is not None and not line.lstrip().startswith("```") and leanish("  " + code.strip()):
            run.append(line); continue
        if len(run) > max_lines:
            out.append(f"[Lean block of {len(run)} lines omitted]"); st["blocks_removed"] += 1
        else:
            out += run
        run = []
        if line is None:
            break
        if opt_claim(line):
            out.append(CLAIM_MARK); st["claims_removed"] += 1
        else:
            out.append(line)
    body = "\n".join(out).strip()
    if len(body) > cap:
        body = body[:cap - 30]; body = body[:body.rfind("\n")] + "\n(review truncated)"; st["truncated"] = True
    st["levers"] = len(_LEVER_LINE.findall(body))
    return body, st


REVIEW_TAG = "<!-- lra-review "


def review_header(sha: str, run_id, t: str, stats: dict, partial: bool = False) -> str:
    """review.md's first line: the best sha it reviewed (the next prompt shows the review only for that sha), the run, the time, lint counts."""
    return (f"{REVIEW_TAG}best_sha={sha} run={run_id} t={t} levers={stats.get('levers', 0)} blocks_removed={stats.get('blocks_removed', 0)} "
            f"claims_removed={stats.get('claims_removed', 0)} partial={int(partial)} -->")


def parse_review(text: str) -> tuple[dict, str] | None:
    """(header fields, body) of a review.md, or None when its first line is not a review header."""
    head, _, body = (text or "").partition("\n")
    if not head.startswith(REVIEW_TAG):
        return None
    return dict(re.findall(r"(\w+)=(\S+)", head[len(REVIEW_TAG):].replace("-->", ""))), body.strip()


# ---- failed-move registry (2026-10-13, docs/opus_pass2_deep_dive.md §3; agent.py / agent_claude_code.py --failed-moves, off by default) ----
# Measured waste: failing checks that hit an error already seen in an earlier pass rose 1% -> 19% -> 22% -> 56% (p2..p5), and 34 of 50 resumed
# sessions re-grepped names their notes already listed. Notes stop byte-identical resubmits (0 of 584), not the same edit on a new candidate:
# the registry is the harness's own record of edits that failed, enforced from state.json, never from the model's prose.
FM_MIN_REFUTE = 2      # real compile refutations, from as many separate tool calls, before a move is listed (one failure can be a slip
                       # elsewhere in the candidate; literals are normalized, so two literal variants in one batch are one refutation, review 2026-10-13)
FM_CAP = 1200          # the block's cap (the facts sheet's style: one line per move, no Lean block over 2 lines)
FM_MAX_LINES = 8       # changed lines (removed + added) above which a failed check is a rewrite, not a move
FM_MAX_SHARE = 0.6     # ... or this share of both texts' lines (inrun.ledger_win's rewrite rule)
FM_SHOW = 64           # characters of each side of a move in the block
FM_HEAD = ("REFUTED MOVES (do not retry without a new reason; harness record, not notes): each edit below failed in at least {n} separate checks "
           "with the same first error class, and the lines it edits are still in candidate.lean (once those lines change, a move is open again):")
# review 2026-10-13: an error-only entry has no edit and no line check, so it does not sit under FM_HEAD's claim; only names (a generic message
# such as `unsolved goals` or `linarith failed` merges unrelated edits and would discourage a whole tactic family)
FM_HEAD_NAMES = ("UNKNOWN NAMES (failed checks with no recorded edit): Lean rejected each name below in at least {n} separate checks since the "
                 "last new best (or it is a known missing name); search for the exact name before using it again:")
_FM_SKIP = ("timeout / heartbeats", "statement / forbidden")   # a timeout or a refusal says nothing about the move itself
# review 2026-10-13: an import / olean failure is a positioned message (1:0) but says nothing about the move: the environment
_FM_ENV = re.compile(r"object file|unknown module prefix|unknown package|could not resolve import|no such file|no directory|failed to load|"
                     r"import\b.{0,60}\bnot found|\.olean\b", re.I)
_FM_MOD = re.compile(r"^\s*\(with the preceding `… in` modifier applied[^)]*\)\s*")   # scorer/compile.py's prefix on a plain compile's errors
_RAW_LINE = re.compile(r"^\s*(\d+):\d+:")
_QNAME = re.compile(r"'(\S+?)'(?=[\s.,:;)]|$)")
_LIT_STR = re.compile(r'"(?:[^"\\\n]|\\.)*"')
_LIT_NUM = re.compile(r"(?<![\w'.₀-₉])\d+(?:\.\d+)?(?![\w'₀-₉])")
_LCOMMENT = re.compile(r"\s*--.*$")
_POS = re.compile(r"^\s*(?:\d+:\d+:|line \d+(?: `[^`\n]*`)?, col \d+:)\s*")


def _code(line: str) -> str:
    """A proof line as a move sees it: the line comment dropped, whitespace (indentation included) collapsed."""
    return re.sub(r"\s+", " ", _LCOMMENT.sub("", line or "")).strip()


def abstract_code(line: str) -> str:
    """A proof line in a move signature: identifiers kept, string and number literals normalized (`"_"`, `#`), whitespace collapsed."""
    return _LIT_NUM.sub("#", _LIT_STR.sub('"_"', _code(line)))


def _lines(text: str | None) -> list[str]:
    return [l for l in (text or "").split("\n") if _code(l)]


def _lkey(line: str) -> str:
    """A line's content key: its exact content (whitespace collapsed), so an edit of a literal in it is a change."""
    return hashlib.sha256(_code(line).encode()).hexdigest()[:8]


def _ckeys(lines: list) -> list[str]:
    """Each line's key in its text: its content (whitespace collapsed) with the previous code line's and its occurrence among equal (previous,
    line) pairs. Review 2026-10-13: content-only keys missed a change of one of two equal lines (`· omega`); a change of the line before also
    reopens a move now, the safe side."""
    out, seen, prev = [], collections.Counter(), ""
    for l in lines:
        c = _code(l); seen[(prev, c)] += 1
        out.append(hashlib.sha256(f"{prev}\n{c}\n{seen[(prev, c)]}".encode()).hexdigest()[:8]); prev = c
    return out


def line_keys(text: str | None) -> set:
    """The touch keys a text holds (a move is open again once one of its touched keys is missing from the base)."""
    return set(_ckeys(_lines(text)))


def _has_run(seq: list, keys: list) -> bool:
    n = len(seq)
    return bool(n) and any(keys[i:i + n] == seq for i in range(len(keys) - n + 1))


def _sig(rem: list, add: list, anchors: list = ()) -> str:
    s = " ⏎ ".join(abstract_code(l) for l in rem) + " => " + " ⏎ ".join(abstract_code(l) for l in add)
    if anchors:
        s += " @ " + " ⏎ ".join(abstract_code(l) for l in anchors)
    return hashlib.sha256(s.encode()).hexdigest()[:12]


def _q(line: str) -> str:
    c = _code(line).replace("`", "'")
    return "`" + (c if len(c) <= FM_SHOW else c[:FM_SHOW - 1] + "…") + "`"


def move_of(parents, text: str) -> dict | None:
    """A failed check's edit as a move, against the closer of its parents ((kind, text) pairs: the stored best, the reference): the changed
    lines (blank and comment-only lines ignored), abstracted into a signature (removed lines => added lines, plus the neighbours of a pure
    insertion), the keys of the parent lines it touches (_ckeys), a one-line display. None for no parent, no change, or a rewrite (more than
    FM_MAX_LINES changed lines, or over FM_MAX_SHARE of both texts' lines: a new architecture is not a move). Review 2026-10-13: `sig0` is the
    signature without the insertion's neighbours (a ledger win's diff has none), `seq` a single insertion's content keys with the line before
    it (an insertion the base already holds is applied, not refuted)."""
    import difflib
    new = _lines(text); pick = None
    for kind, par in parents:
        if not par:
            continue
        old = _lines(par); rem, add, anchors, idx, ops, seq = [], [], [], set(), [], []
        sm = difflib.SequenceMatcher(None, [_code(l) for l in old], [_code(l) for l in new], autojunk=False)
        for op, i1, i2, j1, j2 in sm.get_opcodes():
            if op == "equal":
                continue
            ops.append(op); rem += old[i1:i2]; add += new[j1:j2]; idx.update(range(i1, i2))
            if op == "insert":
                anchors += old[max(0, i1 - 1):i1 + 1]; idx.update(range(max(0, i1 - 1), min(len(old), i1 + 1)))
                seq = [_lkey(l) for l in old[max(0, i1 - 1):i1] + new[j1:j2]]
        n = len(rem) + len(add)
        if pick is None or n < pick[0]:
            pick = (n, kind, old, rem, add, anchors, idx, seq if ops == ["insert"] else [])
    if pick is None:
        return None
    n, kind, old, rem, add, anchors, idx, seq = pick
    if n == 0 or n > FM_MAX_LINES or n > FM_MAX_SHARE * (len(old) + len(new)):
        return None
    more = lambda xs: f" (+{len(xs) - 1} line{'s' if len(xs) > 2 else ''})" if len(xs) > 1 else ""
    if rem and add:
        show = f"replace {_q(rem[0])}{more(rem)} with {_q(add[0])}{more(add)}"
    elif rem:
        show = f"delete {_q(rem[0])}{more(rem)}"
    else:
        show = f"insert {_q(add[0])}{more(add)}" + (f" after {_q(anchors[0])}" if anchors else "")
    ck = _ckeys(old)
    return {"sig": _sig(rem, add, anchors), "sig0": _sig(rem, add), "show": show, "touch": sorted({ck[i] for i in idx}), "par": kind,
            **({"seq": seq} if seq else {})}


def void_stale(state: dict, best: str | None) -> int:
    """The revert rule (review 2026-10-13): a move measured against the stored best whose touched lines the best has since lost is open again
    for good: its attempts are marked void, so a best that later restores those lines does not bring the old count back. Called on the check
    path with the best of that moment (a best found by a check is the parent of the next check, so a best that lived between two checks is
    seen). Moves against the reference are left alone (the reference never changes). Returns how many were voided."""
    if not best:
        return 0
    keys = line_keys(best); k = 0
    for a in state.get("attempts") or []:
        m = a.get("move")
        if isinstance(m, dict) and m.get("sig") and m.get("par") == "best" and not m.get("void") and not set(m.get("touch") or []) <= keys:
            m["void"] = True; k += 1
    return k


def error_line(error, head_lines: int) -> int | None:
    """The first error's line relative to the declaration (raw `N:C:` positions only; None for a relabelled or unpositioned error)."""
    m = _RAW_LINE.match(str(error or ""))
    return int(m.group(1)) - int(head_lines) if m else None


def record_move(state: dict, parents, text: str, call=None, eline: int | None = None) -> dict:
    """A failed check's move as the check path records it (agent.py: into the attempt record before it is appended; attach_move(): onto the
    appended one): stale moves are voided first (void_stale() against the 'best' parent), then the move ({} for a rewrite) with the tool call
    it came from (`call`: one batch is one refutation) and the first error's line relative to the declaration (`eline` < 1: above the
    declaration, the environment, not the move)."""
    void_stale(state, dict(parents).get("best"))
    m = move_of(parents, text) or {}
    if m and call is not None:
        m["call"] = str(call)
    if m and isinstance(eline, int):
        m["eline"] = eline
    return m


def attach_move(state: dict, parents, text: str, call=None, eline: int | None = None) -> bool:
    """The check path's hook (the caller holds the state lock and has just recorded the check): the newest attempt, when it is this text's
    (sha256 of the text or of the text without trailing whitespace: agent.py and leantools hash differently) and it failed, gets its
    move. A refusal before compiling records no attempt, so the sha test keeps the move off an older attempt. True when one was attached."""
    at = state.get("attempts") or []
    if not at or not text:
        return False
    a = at[-1]
    if a.get("ok") or a.get("move") or a.get("sha") not in {hashlib.sha256(t.encode()).hexdigest()[:12] for t in (text, text.rstrip())}:
        return False
    m = record_move(state, parents, text, call=call, eline=eline)
    a["move"] = m   # {}: no move (a rewrite): the registry skips it instead of grouping it by its error alone
    return bool(m)


def _err_text(e) -> str:
    return _FM_MOD.sub("", str(e or ""))


def refutes(a: dict) -> bool:
    """A REAL compile refutation: a failed check whose first error is a positioned Lean diagnostic (`N:C:` or the relabelled `line n, col C:`,
    after scorer/compile.py's `… in` modifier prefix) outside the timeout / heartbeat-limit and statement / forbidden classes. Never: a compile
    that worked but did not beat the best (ok), a process or transport failure (`lean exit ...`, a lock, a rate or usage limit: no position), a
    check with no error text, an environment failure (review 2026-10-13: an import / olean message, a raw position on line 1 of the compiled
    file (its header), a first error the check path placed above the declaration (move `eline` < 1))."""
    e = _err_text(a.get("error"))
    if a.get("ok") or not _POS.match(e) or error_class(e) in _FM_SKIP or _FM_ENV.search(e):
        return False
    r = _RAW_LINE.match(e); m = a.get("move") if isinstance(a.get("move"), dict) else {}
    if r and int(r.group(1)) <= 1:
        return False
    return not (isinstance(m.get("eline"), int) and m["eline"] < 1)


def _err_head(e) -> str:
    return _LIT_NUM.sub("#", re.sub(r"\s+", " ", _POS.sub("", _err_text(e)))).strip()[:90]


def _norm_text(t: str | None) -> str:
    return "\n".join(_code(l) for l in _lines(t))


def _best_epoch(state: dict, base: str) -> tuple[str, bool]:
    """(t of the newest new best, whether error-only entries apply to `base`). The epoch is the newest of: a scored attempt, the attempt whose
    sha is the stored best's, an adopted fresh lineage (hx merge_fresh_state adopts a best without an attempt here). Review 2026-10-13: a stored
    best with none of these (adopted elsewhere) or a base other than the stored best (from-reference, a relay seed) makes them stale."""
    at = state.get("attempts") or []
    t = max([str(a.get("t") or "") for a in at if a.get("ok") and a.get("score") is not None] or [""])
    best = (state.get("best") or {}).get("proof")
    if not best:
        return t, True   # never improved: the session starts from the reference, the text every failed check edited
    shas = {hashlib.sha256(x.encode()).hexdigest()[:12] for x in (best, best.rstrip(), best.rstrip() + "\n")}
    hit = [str(a.get("t") or "") for a in at if a.get("ok") and a.get("sha") in shas]   # its first compile (a later re-check is no new best)
    fl = [str(f.get("t") or "") for f in state.get("fresh_lineages") or [] if f.get("adopted")]
    return max([t] + ([min(hit)] if hit else []) + fl), bool(hit or fl) and _norm_text(base) == _norm_text(best)


def _win_sig(diff) -> str | None:
    ls = (diff or "").splitlines()
    rem = [l[1:] for l in ls if l.startswith("-") and not l.startswith("---") and _code(l[1:])]
    add = [l[1:] for l in ls if l.startswith("+") and not l.startswith("+++") and _code(l[1:])]
    return _sig(rem, add) if rem or add else None


def registry(state: dict, base: str | None = None, min_refute: int = FM_MIN_REFUTE) -> list[dict]:
    """The refuted moves of a problem's state.json against `base` (the text the session starts from; default the stored best's proof), most
    refuted first. Moves (attempts with a `move`) group by (signature, first error class) and count only real refutations (refutes()) whose
    touched lines are all still in `base`, from at least `min_refute` separate tool calls (move `call`; an attempt without one is its own
    call); never listed: a void move (void_stale), a signature that won (ledger wins, matched without an insertion's neighbours), a single
    insertion the base already holds. Text-less attempts (no `move` key) count only for the `unknown name` class (review 2026-10-13: a
    generic message merges unrelated edits), grouped by normalized error head: a ledger dead name always (the environment does not change);
    otherwise a lemma-like name (with `.` or `_`, an unknown constant, or a tactic: a bare `h₁` / `hx` is a local hypothesis, about the
    candidate, not the environment), after the newest new best, and only when `base` is that
    best (_best_epoch()). Entries: kind ('move' | 'error'), n (refutations), calls, cls, show, err, t; moves first, the most refuted first."""
    at = state.get("attempts") or []; led = state.get("ledger") or {}
    if base is None:
        base = (state.get("best") or {}).get("proof") or ""
    keys = line_keys(base); plain = [_lkey(l) for l in _lines(base)]
    won = {_win_sig(w.get("diff")) for w in led.get("wins") or []} - {None}
    dead = [str(x) for x in led.get("dead_names") or [] if x]
    t_best, same = _best_epoch(state, base)
    groups: dict = {}
    for i, a in enumerate(at):
        if not refutes(a):
            continue
        cls = error_class(_err_text(a.get("error"))); head = _err_head(a.get("error")); t = str(a.get("t") or ""); m = a.get("move")
        if isinstance(m, dict) and m.get("sig"):
            if (m.get("void") or m["sig"] in won or m.get("sig0") in won or not set(m.get("touch") or []) <= keys
                    or (m.get("seq") and _has_run(list(m["seq"]), plain))):
                continue
            k = ("move", m["sig"], cls); call = m.get("call") or f"#{i}"
        elif m is None:
            if cls != "unknown name":
                continue
            nm = _QNAME.search(head)
            if not any(re.search(r"(?<![\w.])" + re.escape(d) + r"(?!\w|\.\w|''|'\w)", head) for d in dead):
                if not same or t <= t_best or (nm and not re.search(r"[._]", nm.group(1)) and not head.startswith("unknown constant")):
                    continue
            k = ("error", head, cls); call = f"#{i}"
        else:
            continue   # an attempt whose edit was a rewrite: no move to refute
        g = groups.setdefault(k, {"kind": k[0], "n": 0, "calls": set(), "cls": cls, "show": "", "err": "", "t": "", "i": -1})
        g["n"] += 1; g["calls"].add(call)
        if (t, i) >= (g["t"], g["i"]):
            g.update({"t": t, "i": i, "err": head, "show": (m or {}).get("show", "")})
    out = sorted((g for g in groups.values() if len(g["calls"]) >= min_refute), key=lambda g: (g["t"], g["i"]), reverse=True)   # newest first ...
    out.sort(key=lambda g: (g["kind"] != "move", -g["n"]))   # ... within moves first, the most refuted first
    for g in out:
        g.pop("i", None); g["calls"] = len(g["calls"])
    return out


def failed_moves_render(state: dict, base: str | None = None, cap: int = FM_CAP) -> tuple[str, int]:
    """(the block, the number of entries it shows): REFUTED MOVES (FM_HEAD) then UNKNOWN NAMES (FM_HEAD_NAMES), one line each, the most refuted
    first, trimmed from the end to the cap with a 'more not shown' line; no Lean block over 2 lines (every entry is a bullet, code only as
    inline spans); ("", 0) when nothing is refuted. The count is what runs[].failed_moves records (review 2026-10-13: not the registry's size)."""
    reg = registry(state, base)
    if not reg:
        return "", 0
    rows = [(g["kind"], (f"- {g['n']}x [{g['cls']}] {g['show']}: {g['err']}" if g["kind"] == "move" else f"- {g['n']}x {g['err']}")[:FACTS_LINE + 60])
            for g in reg]
    k = len(rows)
    while True:
        kept = rows[:k]; out = []
        for kind, head in (("move", FM_HEAD), ("error", FM_HEAD_NAMES)):
            if any(r[0] == kind for r in kept):
                out += [head.format(n=FM_MIN_REFUTE)] + [r[1] for r in kept if r[0] == kind]
        text = "\n".join(out + ([f"- ({len(rows) - k} more not shown)"] if k < len(rows) else []))
        if len(text) <= cap or k <= 1:
            break
        k -= 1
    text = strip_lean_blocks(_cap(text, cap))
    return text, len(re.findall(r"(?m)^- \d+x ", text))


def failed_moves_block(state: dict, base: str | None = None, cap: int = FM_CAP) -> str:
    """The REFUTED MOVES block of the prompt ("" when nothing is refuted): failed_moves_render()'s text."""
    return failed_moves_render(state, base, cap)[0]
