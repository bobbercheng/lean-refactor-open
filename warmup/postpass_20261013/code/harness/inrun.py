#!/usr/bin/env python3
"""In-run learning for the Claude Code driver v2 (2026-10-12, the internal-set log 19:35Z: allowed on an internal evaluation set and the
internal pool when nothing leaves the run; docs/cc_driver_v2.md §7-§9, docs/opus_pass2_deep_dive.md R1/R2/R7).
  locked_check()  the v2 check path (harness/tools/_lra_v2.py, harness/hb_polish.py): leantools.lean_check under the state lock, plus
                  (a) the winning edit in state.json ledger.wins (agent.py:970-978's record, with discover's body diff and sha, so
                  discover --ledger-only never adds it twice; targeted edits only, as discover writes), (R1) `axis` and (R2) `progress`
  build()         (c) the run-level techniques file <work-root>/_run_techniques.json from the line's own work root and runs: edit patterns
                  confirmed on >= 2 problems (the tactic/lemma-level change with the problems' identifiers stripped), operational fixes (tool and
                  permission errors that a session got past), closer prices per toolchain (heartbeat_profile blocks measured in this run) and
                  notes tagged GENERAL that pass the leak lint; never discover's raw `pooled` counts (R7: generic tokens)
  leak_lint()     no Lean block longer than 2 lines, no problem name, no identifier that occurs in only one problem's files
  render()        the RUN TECHNIQUES block of prompt v2 (capped, 1.5k chars)
Review 2026-10-12 (round 2): the lint counts every Lean-looking line of a note whatever its indentation (> 2 rejects) with the wider tactic list
of cc_levers, and plain words that are names declared in one problem's files; each note keeps its (hashed) source workspaces so render()
leaves the viewer's own notes out; a damaged gzip trajectory is skipped and counted; state.json is written atomically.
Transfer lane (2026-10-12, docs/cc_driver_v2.md §12, harness/transfer.py): build() carries the lane's TRANSFER HITS
(<work-root>/_transfer/mechanisms.json, linted again) and render() shows them after the edit patterns; the lane banks through its own
pre-checked commit (ledger_win / append_win / write_state from here).
Nothing is written outside the work root, nothing leaves the run, and the CLI prints counts only (no problem names).
    python3 harness/inrun.py --work-root harness/hwork/internalpool-ccA2 --runs internalpool-hx-ccA2-r1,internalpool-hx-ccA2-r2
"""
from __future__ import annotations

import argparse, collections, gzip, hashlib, json, os, re, statistics, sys, time, zlib
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness import cc_levers as LV  # noqa: E402

TECH_FILE = "_run_techniques.json"
TECH_CAP = 1500
MIN_PROBLEMS = 2   # an edit pattern is a technique only when it won on at least this many problems
KEEP_WORDS = {"at", "with", "using", "only", "by", "fun", "λ", "=>", "←", "→", "⊢", "in", "then", "else", "if", "match", "from", "show", "this", "_",
              "?_", "..", "True", "False", "Or.inl", "Or.inr", "And.intro", "rfl"}
CLOSERS = ("grind", "simp_all", "simpa", "simp", "dsimp", "omega", "aesop", "decide", "norm_num", "linarith", "nlinarith", "positivity",
           "ring_nf", "ring", "tauto", "fun_prop", "field_simp", "exact?", "rfl", "trivial", "assumption", "contradiction")
_CLOSER_RE = re.compile(r"^(?:[·•]\s*)?(?:(?:all_goals|any_goals)\s+)?(" + "|".join(re.escape(c) for c in CLOSERS) + r")(?![\w'?!])")
ID_RE = re.compile(r"[A-Za-z_][\w'!?₀-₉]*(?:\.[A-Za-z_\d][\w'!?₀-₉]*)*")
GENERAL_RE = re.compile(r"\bGENERAL\b")


def _tactics() -> set:
    from harness.discover import TACTICS
    return TACTICS


def dirname(name: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", name)


# ---- (a) the per-problem ledger, R1 axis and R2 progress on the v2 check path ------------------------------------------------------------
def ledger_win(name: str, prev: dict, new: dict, run_id, check) -> dict:
    """The winning edit prev -> new as agent.py records it (d_score, d_tokens, d_heartbeats, diff <= 700 chars), with discover.py's proof-body
    diff, sha and kind (a rewrite: the first best over the reference, or a diff over 60% of the lines)."""
    from harness.discover import diff as _diff, body as _body
    from harness.leantools import ROWS, HBS
    row = ROWS[name]; ref = not prev.get("proof")
    a, b = _body(prev.get("proof") or row["src"], row), _body(new["proof"], row)
    d = _diff(a, b)
    w = {"run_id": run_id, "check": check, "d_score": round(float(new["score"]) - float(prev.get("score") or 33.33), 2),
         "d_tokens": int(new.get("tokens") or 0) - (row["proof_length"] if ref else int(prev.get("tokens") or row["proof_length"])),
         "d_heartbeats": int(new.get("heartbeats") or 0) - (int(HBS.get(name) or 0) if ref else int(prev.get("heartbeats") or 0)),
         "diff": "\n".join(d)[:700], "source": "v2-check",
         "kind": "rewrite" if ref or len(d) > 0.6 * (len(a.splitlines()) + len(b.splitlines())) else "edit"}
    w["sha"] = hashlib.sha256(w["diff"].encode()).hexdigest()[:12]
    return w


def append_win(state: dict, w: dict) -> bool:
    """Targeted edits only (a rewrite is the stored best's lineage itself), deduplicated by sha, the newest 30 kept (discover's ledger rule)."""
    led = state.setdefault("ledger", {}); wins = led.setdefault("wins", [])
    if w.get("kind") != "edit" or w["sha"] in {x.get("sha") for x in wins}:
        return False
    wins.append(w); led["wins"] = wins[-30:]
    return True


def instruments(res: dict, name: str, state: dict, run_id) -> None:
    """R1 `axis` (for the checked candidate when it compiled) and R2 `progress` (the stop rule against the stored best's H points left)."""
    from harness.leantools import ROWS, HBS
    from scorer.score import local_reference_heartbeats
    rt = ROWS[name]["proof_length"]; rh = local_reference_heartbeats(name) or HBS.get(name); fl = state.get("hb_floor")
    if res.get("ok"):
        ax = LV.axis(rt, rh, res.get("tokens"), res.get("heartbeats"), fl)
        if ax:
            res["axis"] = ax
    b = state.get("best") or {}
    bax = LV.axis(rt, rh, b.get("tokens"), b.get("heartbeats"), fl) if b.get("proof") else None
    res["progress"] = LV.progress(state.get("attempts", []), run_id, bax["points_left_heartbeats"] if bax else None)


def write_state(sp: Path, state: dict) -> None:
    """state.json written atomically (review 2026-10-12: a gate kill, a post-pass timeout or a ladder stop can SIGKILL a check mid-write; a torn
    state.json loses the problem's ledger and best)."""
    tmp = sp.with_name(f".{sp.name}.tmp-{os.getpid()}")
    tmp.write_text(json.dumps(state, ensure_ascii=False, indent=1)); os.replace(tmp, sp)


def locked_check(w: Path, name: str, text: str, prov: dict, vpath: Path | None, lock_wait: float = 1700.0) -> dict:
    """One candidate through the normal lean_check path (scored, recorded, a verified record and best.lean on a new best), holding the state
    lock for the whole read-compile-write; the ledger win and the instruments are added in the same write. The ledger and the instruments
    never fail a check."""
    from harness import leantools as LT   # looked up at call time: the selftests stub leantools.lean_check
    from harness.statelock import state_lock
    with state_lock(w, timeout=lock_wait):
        sp = w / "state.json"
        state = json.loads(sp.read_text()) if sp.exists() else {"problem": name, "best": {"score": 33.33, "proof": None}, "attempts": [], "runs": []}
        prev = dict(state.get("best") or {})
        res = LT.lean_check(name, text, state, prov, vpath)
        run_id = prov.get("run_id")
        if res.get("new_best") and (state.get("best") or {}).get("proof"):
            try:
                append_win(state, ledger_win(name, prev, state["best"], run_id, sum(1 for a in state.get("attempts", []) if a.get("run_id") == run_id)))
            except Exception:  # noqa: BLE001
                pass
        try:
            instruments(res, name, state, run_id)
        except Exception:  # noqa: BLE001
            pass
        write_state(sp, state)
        if (state.get("best") or {}).get("proof"):
            (w / "best.lean").write_text(state["best"]["proof"].rstrip() + "\n")
    return res


# ---- (c) leak lint ----------------------------------------------------------------------------------------------------------------------
def code_idents(text: str) -> set:
    """Identifier-like tokens of a note: everything inside backticks, and outside them the tokens that read as code (with `_`, `.`, `'`, a
    digit, or camelCase); plain prose words are not identifiers."""
    out = set()
    for m in re.finditer(r"`([^`]*)`", text):
        out |= set(ID_RE.findall(m.group(1)))
    for t in ID_RE.findall(re.sub(r"`[^`]*`", " ", text)):
        if "_" in t or "." in t or "'" in t or re.search(r"\d", t) or re.search(r"[a-z][A-Z]", t):
            out.add(t)
    return {t.rstrip(".") for t in out if len(t.rstrip(".")) > 2}


def ident_index(files: dict) -> dict:
    """identifier (and the last component of a dotted one) -> the problems whose files contain it; files: problem -> [paths]."""
    owner: dict = {}
    for n, paths in files.items():
        seen = set()
        for p in paths:
            try:
                seen |= set(ID_RE.findall(Path(p).read_text(errors="replace")))
            except OSError:
                pass
        for t in seen | {t.split(".")[-1] for t in seen if "." in t}:
            owner.setdefault(t, set()).add(n)
    return owner


DECL_RE = re.compile(r"^[ \t]*(?:@\[[^\]\n]*\][ \t]*)?(?:(?:private|protected|noncomputable|partial|unsafe|nonrec|scoped|local)[ \t]+)*"
                     r"(?:def|theorem|lemma|abbrev|structure|inductive|class|instance|opaque|axiom)[ \t]+([A-Za-z_][\w'!?₀-₉]*(?:\.[\w'!?₀-₉]+)*)", re.M)


def declared_names(files: dict) -> set:
    """Names declared (def / theorem / lemma / abbrev / structure / inductive / class / instance / opaque / axiom) in the problems' files, and
    the last component of a dotted one (review 2026-10-12: plain-word names such as `Admissible` or `frob` are identifiers too)."""
    out = set()
    for paths in files.values():
        for p in paths:
            try:
                for m in DECL_RE.finditer(Path(p).read_text(errors="replace")):
                    out |= {m.group(1), m.group(1).split(".")[-1]}
            except OSError:
                pass
    return out


def name_terms(names, rows: dict | None = None) -> set:
    """Strings that identify a problem: its full name, its work-dir name, its short name when that reads as an identifier (`_`, a digit, a
    prime, camelCase, or >= 12 chars: `progress` alone is a word), and its file's stem."""
    out = set()
    for n in names:
        out |= {n, dirname(n)}
        short = n.split(".")[-1]
        if len(short) >= 4 and (re.search(r"[_\d']|[a-z][A-Z]", short) or len(short) >= 12):
            out.add(short)
        fp = ((rows or {}).get(n) or {}).get("file_path") or ""
        stem = Path(fp).stem
        if len(stem) >= 5:
            out.add(stem)
    return out


def leak_lint(text: str, terms: set, owner: dict, safe: set | None = None, declared: set | None = None) -> str | None:
    """None when a note may cross problems, else the reason: 'lean-block' (more than 2 Lean lines, consecutive or not, whatever their
    indentation: the rendered note is one line, so 3 code lines are a proof fragment), 'problem-name', or 'single-problem-identifier' (an
    identifier that occurs in exactly one problem's files: in backticks or code-like, or a plain word that is a name declared in the
    problems' files, e.g. `Admissible`)."""
    if LV.lean_lines(LV.reindent(text)) > 2:
        return "lean-block"
    for t in terms:
        if re.search(r"(?<![\w.'])" + re.escape(t) + r"(?![\w'])", text):
            return "problem-name"
    safe = safe if safe is not None else (_tactics() | KEEP_WORDS)
    for ident in code_idents(text):
        if ident in safe:
            continue
        if any(len(owner.get(k, ())) == 1 for k in {ident, ident.split(".")[-1]}):
            return "single-problem-identifier"
    for w in set(re.findall(r"(?<![\w.'])[A-Za-z][\w']{3,}(?![\w'])", re.sub(r"`[^`]*`", " ", text))) & (declared or set()):
        if w not in safe and len(owner.get(w, ())) == 1:
            return "single-problem-identifier"
    return None


def general_entries(notes: str) -> list[str]:
    """Notes entries tagged GENERAL: the tagged line plus its continuation (deeper-indented lines, a fenced block) up to a blank line, the next
    bullet or header at its level, or the next GENERAL tag."""
    L = notes.split("\n"); out = []; i = 0
    ind = lambda s: len(s) - len(s.lstrip())
    while i < len(L):
        if not GENERAL_RE.search(L[i]):
            i += 1; continue
        ent = [L[i]]; j = i + 1; fence = False
        while j < len(L):
            s = L[j].strip()
            if s.startswith("```"):
                fence = not fence; ent.append(L[j]); j += 1; continue
            if not fence and (not s or GENERAL_RE.search(L[j]) or (re.match(r"(#{1,6}\s|[-*+]\s|\d+[.)]\s)", s) and ind(L[j]) <= ind(L[i]))):
                break
            ent.append(L[j]); j += 1
        out.append("\n".join(ent)); i = j
    return out


def clean_general(entry: str) -> str:
    s = re.sub(r"^\s*(?:[-*+]|\d+[.)])?\s*(?:\*\*)?\[?GENERAL\]?(?:\*\*)?\s*[:\-—]?\s*", "", entry.strip())
    return re.sub(r"\s+", " ", s).strip()[:300]


# ---- (c) techniques ---------------------------------------------------------------------------------------------------------------------
def _diff_sides(diff: str) -> tuple[list, list]:
    ls = (diff or "").splitlines()
    return [l for l in ls if l.startswith("-")], [l for l in ls if l.startswith("+")]


def lib_names_added(diff: str) -> set:
    from harness.discover import features, LIB_NAME
    minus, plus = _diff_sides(diff)
    fa, fr = features(plus), features(minus)
    return {f[6:] for f in fa if f.startswith("lemma:") and fa[f] > fr[f] and LIB_NAME.match(f[6:])}


def abstract_line(line: str, keep: set) -> str:
    """A diff line with every token that is not a tactic, a keyword, punctuation or a shared library name replaced by `_`."""
    from scorer.tokenize import tokens
    tac = _tactics()
    out = [t if (t in tac or t in KEEP_WORDS or t in keep or not re.search(r"[\w']", t)) else "_" for t in tokens(line)]
    return re.sub(r"_(?: _)+", "_", " ".join(out))[:80]


def tactic_seq(lines: list, cap: int = 6) -> list:
    """The tactic tokens of diff lines in order, consecutive repeats collapsed, at most `cap`."""
    from scorer.tokenize import tokens
    tac = _tactics(); seq = []
    for l in lines:
        for t in tokens(l[1:]):
            if t in tac and (not seq or seq[-1] != t):
                seq.append(t)
    return seq[:cap]


def pattern_of(diff: str, keep: set = frozenset()) -> tuple[str | None, str]:
    """(pattern, example) of a winning edit: the tactic sequence of its removed lines -> that of its added lines (e.g. `simp -> simp only`,
    `have omega exact -> exact omega`), plus the shared library names it added; the example is its first removed and added lines
    abstracted. (None, "") when only the problem's own identifiers changed."""
    from scorer.tokenize import tokens
    minus, plus = _diff_sides(diff)
    tac = _tactics()
    rem, add = tactic_seq(minus), tactic_seq(plus)
    libs = sorted(lib_names_added(diff) & set(keep))
    if rem == add and not libs:
        return None, ""
    key = f"{' '.join(rem) or '(nothing)'} -> {' '.join(add) or '(nothing)'}" + (f" + {', '.join(libs)}" if libs else "")
    ex = []
    for side, lines in (("-", minus), ("+", plus)):
        cand = next((l for l in lines if any(t in tac for t in tokens(l[1:]))), None)
        if cand:
            ex.append(f"{side} {abstract_line(cand[1:].strip(), keep)}")
    return key, " / ".join(ex)


_OPS = (("compound", r"contains multiple operations",
         "one command per Bash call: no `&&`, `;` or pipes into commands outside the allowed set; run each tool and grep as its own call"),
        ("sed-write", r"sed command requires approval", "only `sed -n` (read-only); change files with Edit / Write"),
        ("outside-dirs", r"was blocked\. For security|outside the working directories",
         "read and search only the workspace and the source trees named in the task (absolute paths); keep scratch files in the workspace, not /tmp"),
        ("redirect", r"[Oo]utput redirection|file redirect", "no shell redirects (`>`, `2>&1`, `| tee`): write files with Write / Edit; tool output comes back directly"),
        ("cd", r"change[sd]? director|'cd'", "never `cd`: you are already in the workspace"),
        ("shell-expansion", r"can't be checked before it runs|expansion obfuscation|dynamic directory",
         "no shell variables, `$(...)`, subshells, braces or loops: write each command out literally"),
        ("stale-read", r"modified since read", "Read a file again after a tool rewrote it (variants, lean_mine and normalize_check update candidate.lean) before you Edit it"),
        ("files-only", r"no such file in the workspace|cannot stat|No such file", "the tools take workspace file names only: create the file with Write first, never pass the problem name"),
        ("statement", r"statement differs", "copy the statement byte-for-byte from original.lean, then `:=`"),
        ("lock", r"lock busy|still compiling", "one compile at a time: batch alternatives in one lean_check_variants.py call instead of parallel calls"),
        ("timeout", r"timed out|Command timed out", "long tools (heartbeat_profile, lean_mine, normalize_check) take minutes: run them alone, never in parallel"),
        # review 2026-10-12: Claude Code's Edit / Write refuse an existing file not Read in the session (candidate.lean is shown inline; cp'd
        # variant files); before "approval", whose words it does not carry
        ("not-read", r"has not been read yet|Read it first before",
         "Read a file once before you Edit it (Edit refuses a file not Read in this session); create a new variant file with Write"),
        ("approval", r"requires approval|denied|not allowed|haven't granted|[Pp]ermission",
         "a command outside the allowed set was refused: use the tool scripts and the read-only shell set (grep, rg, ls, cat, head, tail, sed -n, wc, cp, diff)"))


def _sessions(f: Path, bad: list | None = None):
    """The Claude Code sessions in one trajectory file (the driver appends one header + stream per session). Review 2026-10-12: a truncated or
    corrupt gzip member (a driver killed while it appended its session) raises EOFError / zlib.error, which are not OSErrors: the file is
    read up to the damage, counted in `bad`, and the post-batch step goes on."""
    op = gzip.open if f.suffix == ".gz" else open
    cur = None
    try:
        with op(f, "rt", errors="replace") as h:
            for line in h:
                try:
                    d = json.loads(line)
                except ValueError:
                    continue
                if d.get("type") == "header":
                    if cur is not None:
                        yield cur
                    cur = []
                elif cur is not None:
                    cur.append(d)
    except (OSError, EOFError, zlib.error):
        if bad is not None:
            bad.append(f.name)
        return
    if cur is not None:
        yield cur


def ops_fixes(runs: list, runs_dir: Path, bad: list | None = None) -> list[dict]:
    """Operational fixes: error classes of tool results (permission denials, tool errors) that a session hit and then got past (a later
    result of the same tool without an error), counted in sessions. Only the class and a canned fix leave this function: never command or
    error text (they carry paths and problem names). Unreadable trajectory files go into `bad` (counted, never named in the output)."""
    seen: dict = collections.defaultdict(lambda: [0, 0])   # class -> [sessions hit, sessions resolved]
    for r in runs:
        for f in sorted((runs_dir / r / "trajectories").glob("*.jsonl*")):
            for ev in _sessions(f, bad):
                tools, hit, fixed = {}, {}, set()
                for d in ev:
                    msg = d.get("message") if isinstance(d.get("message"), dict) else {}
                    blocks = msg.get("content") if isinstance(msg.get("content"), list) else []
                    for b in blocks:
                        if not isinstance(b, dict):
                            continue
                        if d.get("type") == "assistant" and b.get("type") == "tool_use":
                            tools[b.get("id")] = b.get("name")
                        elif d.get("type") == "user" and b.get("type") == "tool_result":
                            tool = tools.get(b.get("tool_use_id"), "?")
                            c = b.get("content"); t = c if isinstance(c, str) else json.dumps(c, ensure_ascii=False)
                            cls = next((k for k, rx, _f in _OPS if re.search(rx, t)), None) if (b.get("is_error") or re.search(
                                r"no such file in the workspace|statement differs|lock busy|still compiling", t)) else None
                            if cls:
                                hit.setdefault(cls, tool)
                            else:
                                fixed |= {k for k, tl in hit.items() if tl == tool}
                for k in hit:
                    seen[k][0] += 1; seen[k][1] += k in fixed
    fix = {k: f for k, _rx, f in _OPS}
    return sorted(({"class": k, "fix": fix[k], "sessions": s, "resolved": n} for k, (s, n) in seen.items() if n),
                  key=lambda x: (-x["sessions"], x["class"]))[:6]


def closer_prices(caches: dict, toolchain_of) -> dict:
    """Median heartbeats of a one-line closer block (heartbeat_profile blocks cached in this run's states), per toolchain; n >= 2 blocks."""
    pts: dict = collections.defaultdict(set)
    for name, cache in caches.items():
        tc = toolchain_of(name)
        for prof in (cache or {}).values():
            for b in (prof or {}).get("blocks") or []:
                try:
                    a, z = (int(x) for x in str(b.get("lines")).split("-"))
                except ValueError:
                    continue
                m = _CLOSER_RE.match(str(b.get("text") or "").strip())
                if z == a and m and b.get("heartbeats") and b["heartbeats"] > 0 and ";" not in str(b.get("text")):
                    pts[(tc, m.group(1))].add((name, b.get("lines"), b["heartbeats"]))
    out: dict = {}
    for (tc, c), s in sorted(pts.items()):
        if len(s) >= 2:
            out.setdefault(tc, {})[c] = {"median_hb": int(statistics.median(h for _n, _l, h in s)), "n": len(s)}
    return out


def _toolchain(name: str) -> str:
    try:
        from harness.leantools import ROWS
        from probe.verify_candidates import newest_first
        return newest_first(ROWS[name]["version_info"])[0]
    except Exception:  # noqa: BLE001
        return "?"


def build(work_root, runs: list, runs_dir: Path | None = None, toolchain_of=None, rows: dict | None = None) -> dict:
    """The run-level techniques of one line (work root) from its own states, notes and the listed runs' trajectories."""
    wr = Path(work_root); runs_dir = runs_dir or ROOT / "probe/runs"; toolchain_of = toolchain_of or _toolchain
    if rows is None:
        try:
            from harness.leantools import ROWS as rows
        except Exception:  # noqa: BLE001
            rows = {}
    probs = {}
    for st in sorted(wr.glob("*/state.json")):
        try:
            s = json.loads(st.read_text())
        except (OSError, ValueError):
            continue
        probs[s.get("problem") or st.parent.name] = (st.parent, s)
    files = {n: [d / "original.lean", d / "context.lean"] for n, (d, _s) in probs.items()}
    owner, declared = ident_index(files), declared_names(files)
    terms = name_terms(probs, rows)
    # edit patterns: library names count only when added in winning edits of >= 2 problems
    edits = [(n, w) for n, (_d, s) in probs.items() for w in (s.get("ledger") or {}).get("wins", []) if w.get("kind", "edit") == "edit"]
    lib = collections.defaultdict(set)
    for n, w in edits:
        for nm in lib_names_added(w.get("diff") or ""):
            lib[nm].add(n)
    keep = {nm for nm, ps in lib.items() if len(ps) >= MIN_PROBLEMS}
    safe = _tactics() | KEEP_WORDS | keep   # names in winning edits of >= 2 problems are not one problem's identifiers
    agg = collections.defaultdict(lambda: {"problems": set(), "wins": 0, "ds": [], "dt": [], "dh": [], "ex": ""})
    for n, w in edits:
        key, ex = pattern_of(w.get("diff") or "", keep)
        if key is None:
            continue
        g = agg[key]; g["problems"].add(n); g["wins"] += 1
        g["ds"].append(float(w.get("d_score") or 0)); g["dt"].append(int(w.get("d_tokens") or 0)); g["dh"].append(int(w.get("d_heartbeats") or 0))
        if not g["ex"] and ex and leak_lint(ex, terms, owner, safe, declared) is None:
            g["ex"] = ex
    pats = [{"pattern": k, "problems": len(g["problems"]), "wins": g["wins"], "d_score": round(statistics.mean(g["ds"]), 2),
             "d_tokens": round(statistics.mean(g["dt"]), 1), "d_heartbeats": round(statistics.mean(g["dh"])), "example": g["ex"]}
            for k, g in agg.items() if len(g["problems"]) >= MIN_PROBLEMS and leak_lint(k, terms, owner, safe, declared) is None]
    pats.sort(key=lambda p: (-p["problems"], -p["d_score"]))
    # GENERAL notes through the leak lint; each kept note remembers the (hashed) workspaces it came from, so render() leaves a viewer's own
    # notes out (review 2026-10-12: a fresh lineage of P saw P's own main-lineage notes, labelled as other problems')
    notes, srcs, rejected, have = [], [], collections.Counter(), {}
    for n, (d, _s) in probs.items():
        try:
            txt = (d / "notes.md").read_text()
        except OSError:
            continue
        for ent in general_entries(txt):
            why = leak_lint(ent, terms, owner, None, declared)
            if why:
                rejected[why] += 1; continue
            c = clean_general(ent)
            if c and c.lower() not in have:
                have[c.lower()] = len(notes); notes.append(c); srcs.append([src_key(d.name)])
            elif c and src_key(d.name) not in srcs[have[c.lower()]]:
                srcs[have[c.lower()]].append(src_key(d.name))
    bad: list = []
    ops = ops_fixes(runs, runs_dir, bad)
    return {"built": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "problems": len(probs), "runs": len(runs),
            "patterns": pats[:8], "ops": ops, "closer_prices": closer_prices({n: s.get("profile_cache") for n, (_d, s) in probs.items()}, toolchain_of),
            "notes": notes[:12], "note_src": srcs[:12], "rejected_notes": dict(rejected), "unreadable_trajectories": len(bad),
            "transfer": transfer_hits(wr, terms, owner, declared)}


def transfer_hits(work_root, terms: set, owner: dict, declared: set) -> list[dict]:
    """The transfer lane's TRANSFER HITS entries (<work-root>/_transfer/mechanisms.json `feedback`, harness/transfer.py), linted again here, so a
    rebuilt techniques file keeps them; [] without a lane."""
    try:
        fb = json.loads((Path(work_root) / "_transfer" / "mechanisms.json").read_text()).get("feedback") or []
    except (OSError, ValueError, AttributeError):
        return []
    return [x for x in fb if isinstance(x, dict) and x.get("pattern") and leak_lint(str(x["pattern"]), terms, owner, None, declared) is None][:8]


def src_key(ws_dirname: str) -> str:
    """A workspace's source tag in the techniques file: a short hash of its directory name (no problem name in the file)."""
    return hashlib.sha256(ws_dirname.encode()).hexdigest()[:10]


def write(work_root, tech: dict) -> Path:
    """<work-root>/_run_techniques.json; refuses any other place (nothing leaves the run)."""
    wr = Path(work_root).resolve(); p = (wr / TECH_FILE).resolve()
    if p.parent != wr or not wr.is_dir():
        raise ValueError(f"run techniques go into the line's work root only, not {p}")
    tmp = p.with_name(f".{p.name}.tmp-{os.getpid()}")   # atomic: the transfer lane rewrites the same file (its TRANSFER HITS) between batches
    tmp.write_text(json.dumps(tech, ensure_ascii=False, indent=1)); os.replace(tmp, p)
    return p


def render(tech: dict | None, cap: int = TECH_CAP, exclude: str | None = None) -> str:
    """The RUN TECHNIQUES block of prompt v2 (empty when there is nothing to show), at most `cap` chars. exclude: the viewing workspace's
    directory name; GENERAL notes that came only from it are left out (leave-one-out: they are its own notes, not other problems')."""
    if not tech:
        return ""
    if exclude is not None and tech.get("note_src"):
        me = src_key(exclude); src = tech["note_src"]
        tech = dict(tech, notes=[x for k, x in enumerate(tech.get("notes") or []) if k >= len(src) or set(src[k]) != {me}])
    L = ["RUN TECHNIQUES (pooled from this run's own sessions across this line's problems; general patterns, not answers: check before relying on them):"]
    if tech.get("patterns"):
        L.append("- winning edit patterns confirmed on >= 2 problems (removed -> added; mean per win: score, tokens, heartbeats):")
        L += [f"  {p['pattern']}: {p['problems']} problems, {p['wins']} wins, {p['d_score']:+} score, {p['d_tokens']:+} tok, {p['d_heartbeats']:+} hb"
              + (f"; e.g. {p['example']}" if p.get("example") else "") for p in tech["patterns"]]
    if tech.get("transfer"):   # harness/transfer.py (docs/cc_driver_v2.md §12)
        L.append("- TRANSFER HITS (mechanisms the transfer lane compiled into strictly better bests of this line's rows; $A, $B stand for names "
                 "of your own proof; mean score gain per hit):")
        L += [f"  {t['pattern']}: {t.get('hits')} hit(s) on {t.get('rows')} row(s), {float(t.get('d_score') or 0):+}" for t in tech["transfer"]]
    if tech.get("closer_prices"):
        L.append("- closer prices measured in this run (heartbeats of one call, median of n profiled blocks):")
        L += [f"  {tc}: " + ", ".join(f"`{c}` {v['median_hb']} (n={v['n']})" for c, v in d.items()) for tc, d in tech["closer_prices"].items()]
    if tech.get("ops"):
        L.append("- operational fixes (errors sessions of this run hit and got past):")
        L += [f"  {o['fix']} ({o['sessions']} sessions)" for o in tech["ops"]]
    if tech.get("notes"):
        L.append("- GENERAL notes from other problems' sessions:")
        L += [f"  * {x}" for x in tech["notes"]]
    if len(L) == 1:
        return ""
    text = "\n".join(L)
    if len(text) > cap:
        text = text[:cap - 14]; text = text[:text.rfind("\n")] + "\n  (truncated)"
    return text


def load(work_root) -> dict | None:
    try:
        return json.loads((Path(work_root) / TECH_FILE).read_text())
    except (OSError, ValueError):
        return None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--work-root", required=True, help="the line's work root (relative to the checkout, or absolute)")
    ap.add_argument("--runs", default="", help="comma-separated run ids of this line (their trajectories give the operational fixes)")
    ap.add_argument("--runs-dir", default=None, help="default <checkout>/probe/runs")
    a = ap.parse_args()
    wr = ROOT / a.work_root
    runs = [r.strip() for r in a.runs.split(",") if r.strip()]
    tech = build(wr, runs, Path(a.runs_dir) if a.runs_dir else None)
    p = write(wr, tech)
    rj = tech["rejected_notes"]
    print(f"run techniques: {len(tech['patterns'])} edit pattern(s) on >= {MIN_PROBLEMS} problems, {len(tech['ops'])} operational fix(es), "
          f"{sum(len(v) for v in tech['closer_prices'].values())} closer price(s) over {len(tech['closer_prices'])} toolchain(s), "
          f"{len(tech['notes'])} GENERAL note(s) kept, {sum(rj.values())} rejected by the leak lint {rj or ''}; "
          f"{tech['problems']} problems, {len(runs)} runs -> {a.work_root.rstrip('/')}/{p.name}"
          + (f"; {tech['unreadable_trajectories']} unreadable trajectory file(s) skipped" if tech.get("unreadable_trajectories") else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
