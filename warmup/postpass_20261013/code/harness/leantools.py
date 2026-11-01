"""Shared Lean tool implementations used by harness/agent.py (tool-use API) and
harness/tools/*.py (CLI wrappers for Claude Code's Bash tool). Both paths record
compiling candidates identically, with provenance supplied by the caller."""
from __future__ import annotations

import hashlib, json, os, re, subprocess, time, uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
import sys
sys.path.insert(0, str(ROOT))
from scorer.tokenize import split_declaration, count_tokens, remove_comments  # noqa: E402
from scorer.forbidden import check_forbidden  # noqa: E402
from scorer.compile import compile_putnam, compile_project, file_prefix, split_modifiers, MEASURE_ELAB, ELAN_BIN, env_dir, project_env_dir  # noqa: E402
from scorer.score import len_pct, hb_pct_local, compat_pct, problem_score  # noqa: E402
from probe.verify_candidates import newest_first  # noqa: E402
from scorer.memgate import run_lean  # noqa: E402

ROWS = {json.loads(l)["name"]: json.loads(l) for l in (ROOT / "data/benchmark_warmup.jsonl").open() if l.strip()}
HBS = {json.loads(l)["name"]: json.loads(l)["heartbeat"] for l in (ROOT / "data/benchmark_heartbeats.jsonl").open() if l.strip()}


def digest_error(e: str, limit: int = 700) -> str:
    """One-line compiler-error digest that never drops the goal. Lean's `unsolved goals` prints every
    hypothesis before `⊢`; on big-context problems (Electromagnetism: ~550 chars of hypotheses in a
    1024-char message) the old 400-char prefix cut ended inside the hypotheses and the model never saw
    the goal. Keep the location/message head, elide the hypotheses, keep each `⊢ goal` in full."""
    e1 = re.sub(r"\s+", " ", e).strip()
    if len(e1) <= limit or "⊢" not in e1:
        return e1[:limit]
    m = re.search(r" \S+ : ", e1)
    head = e1[:m.start()] if m and m.start() < 160 else e1[:80]
    goals = [g.strip() for g in re.findall(r"⊢ (.*?)(?= case \S+ |$)", e1)]
    return (head + " … [hypotheses omitted] " + " ‖ ".join("⊢ " + g for g in goals))[:limit]


def comp(row, decl, version, count=True):
    if row["source"] == "putnambench":
        return compile_putnam(row["header"], decl, version, count=count, timeout=900)
    return compile_project(row, decl, version, count=count, timeout=900)


def head_line_count(row, primary) -> int:
    if row["source"] == "putnambench":
        return (row["header"].rstrip() + "\n\n" + MEASURE_ELAB + "set_option Elab.async false in\narena_measure\n").count("\n")
    core, mods = split_modifiers(file_prefix(row, primary))
    return (core.rstrip("\n") + "\n\n" + MEASURE_ELAB + "set_option Elab.async false in\narena_measure\n" + mods).count("\n")


# Cycle 49: newer Lean rejects `grind [hx]` for a local hypothesis hx ("redundant parameter `hx`, `grind` uses local hypotheses
# automatically"): 68 failed compiles in the dev trajectories and 4 of 8 failures on a held-out Fsub problem. Mechanical fix: drop the
# name from the grind list and recompile once.
_REDUNDANT_GRIND = re.compile(r"redundant parameter `([^`]+)`, `grind` uses local hypotheses automatically")


def fix_redundant_grind(decl: str, errors: list[str]) -> tuple[str | None, list[str]]:
    """(fixed declaration, removed names) when every error is a redundant-grind-parameter error, else (None, [])."""
    names = [m.group(1) for e in errors for m in [_REDUNDANT_GRIND.search(e)] if m]
    if not names or len(names) != len(errors):
        return None, []
    drop = {v for n in set(names) for v in (n, f"← {n}", f"→ {n}", f"<- {n}", f"-> {n}")}

    def strip(m: re.Match) -> str:
        keep = [x.strip() for x in m.group(2).split(",") if x.strip() and x.strip() not in drop]
        return m.group(1).rstrip() + (" [" + ", ".join(keep) + "]" if keep else "")
    out = re.sub(r"(\bgrind\??(?:\s+only)?\s*)\[([^\[\]]*)\]", strip, decl)
    return (out if out != decl else None), sorted(set(names))


# Cycle 50: wrong names are the second-largest error class in the dev runs ("Unknown identifier" 25 + "Invalid field … does not
# contain" 10 of 589 errors) and the model never calls lean_search. Attach the closest real declaration names to such errors: an index
# of every theorem/lemma/def/abbrev/instance name in the problem's environment (project + .lake/packages incl. Mathlib; ~245k names,
# built by ripgrep in < 1 s, cached per environment).
_NAME_IDX: dict[str, dict[str, list[tuple[str, str]]]] = {}
_DECL_RX = r"^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec|noncomputable|public)\s+)*(?:theorem|lemma|def|abbrev|instance)\s+([^\s:({\[]+)"
_UNKNOWN_RX = re.compile(r"(?:[Uu]nknown (?:identifier|constant)|does not contain) (?:`([^`\s]+)`|'([^\s]+?)'(?=[\s.,:;)]|$))")


def _name_index(root: Path) -> dict[str, list[tuple[str, str]]]:
    key = str(root)
    if key not in _NAME_IDX:
        idx: dict[str, list[tuple[str, str]]] = {}
        try:
            out = subprocess.run(["rg", "-L", "--hidden", "--no-ignore", "-N", "--with-filename", "-o", "-r", "$1", "--glob", "*.lean",
                                  "--glob", "!**/.lake/build/**", "--glob", "!**/LRAScratch/**", _DECL_RX, str(root)],
                                 capture_output=True, text=True, timeout=60).stdout
        except Exception:  # noqa: BLE001
            out = ""
        for line in out.splitlines():
            f, _, nm = line.rpartition(":")
            if nm:
                idx.setdefault(nm.split(".")[-1], []).append((nm, os.path.relpath(f, root)))
        _NAME_IDX[key] = idx
    return _NAME_IDX[key]


def suggest_names(row: dict, version: str, errors: list[str], limit: int = 6) -> dict[str, list[str]]:
    """{unknown name: ["candidate (file)", …]} for unknown-identifier / missing-field errors; empty when nothing matches."""
    import difflib
    root = (env_dir(version) if row["source"] == "putnambench" else project_env_dir(row["source"], version))
    wanted = []
    for e in errors:
        for m in _UNKNOWN_RX.finditer(e):
            n = m.group(1) or m.group(2)
            if n and n not in wanted:
                wanted.append(n)
    if not wanted:
        return {}
    idx = _name_index(root); out = {}
    for n in wanted[:3]:
        parts = n.split("."); last = parts[-1]; ns = [p.lower() for p in parts[:-1]]
        keys = [last] if last in idx else []
        pool = [k for k in idx if abs(len(k) - len(last)) <= max(4, len(last) // 3) and (k[:3] == last[:3] or any(p and p in k for p in last.split("_") if len(p) > 3))]
        keys += [k for k in difflib.get_close_matches(last, pool, n=limit, cutoff=0.75) if k != last]
        # rank: exact last component first, then by how many namespace parts of the wanted name occur in the written name or file path
        ents = [(k != last, -sum(p in (nm + "/" + f).lower() for p in ns), nm, f) for k in keys for nm, f in idx[k]]
        cands = [f"{nm} ({f})" for _, _, nm, f in sorted(ents, key=lambda e: (e[0], e[1]))]
        if cands:
            out[n] = list(dict.fromkeys(cands))[:limit]
    return out


# Cycle 53: "Tactic `rewrite` failed: Did not find an occurrence of the pattern" is the largest compile-error class (49 of 589 errors in
# the dev runs; 14 of 141 errors before the first improvement in the held-out A/B). The usual causes are mechanical: the rule is needed
# right-to-left, the pattern sits under a binder (simp_rw), or it matches only up to reducible unfolding (erw / simp only). Try those
# alternatives for the first failing rewrite and keep the first one that makes the WHOLE declaration compile.
_RW_FAIL = re.compile(r"^(\d+):(\d+): Tactic `(?:rewrite|rw)` failed: (?:Did not find an occurrence of the pattern|motive is not type correct)")
_RW_TAC = re.compile(r"\b(rw|rewrite|rwa)(\s*)\[")


def _split_rules(body: str) -> list[tuple[int, int]]:
    """(start, end) spans of the top-level comma-separated rules inside a rewrite list body."""
    spans, depth, start = [], 0, 0
    for i, ch in enumerate(body):
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif ch == "," and depth == 0:
            spans.append((start, i)); start = i + 1
    spans.append((start, len(body)))
    return spans


def rw_alternatives(decl: str, errors: list[str], head_lines: int) -> list[tuple[str, str]]:
    """Candidate repairs (description, full declaration) for the FIRST error when it is a failed rewrite; [] otherwise."""
    m = _RW_FAIL.match(errors[0]) if errors else None
    if not m:
        return []
    ln, col = int(m.group(1)) - head_lines, int(m.group(2))
    lines = decl.split("\n")
    if not 1 <= ln <= len(lines):
        return []
    line = lines[ln - 1]
    tacs = [t for t in _RW_TAC.finditer(line) if t.start() <= col]
    if not tacs:
        return []
    t = tacs[-1]; open_i = t.end() - 1; depth, close_i = 0, None
    for i in range(open_i, len(line)):
        depth += line[i] in "([{⟨"; depth -= line[i] in ")]}⟩"
        if depth == 0:
            close_i = i; break
    if close_i is None:
        return []
    body = line[open_i + 1:close_i]; spans = _split_rules(body)
    out = []

    def with_line(new_line: str) -> str:
        return "\n".join(lines[:ln - 1] + [new_line] + lines[ln:])
    rel = col - (open_i + 1)   # Lean reports the column of the failing rule inside the list
    k = next((j for j, (a, b) in enumerate(spans) if a <= rel <= b), None)
    if k is not None:
        a, b = spans[k]; rule = body[a:b]; core = rule.strip()
        flipped = core[1:].lstrip() if core.startswith("←") else "← " + core
        new_body = body[:a] + rule.replace(core, flipped, 1) + body[b:]
        out.append((f"rule `{core}` reversed", with_line(line[:open_i + 1] + new_body + line[close_i:])))
    if t.group(1) in ("rw", "rewrite"):
        for kw in ("simp_rw", "erw", "simp only"):
            out.append((f"`{t.group(1)}` -> `{kw}`", with_line(line[:t.start()] + kw + t.group(2) + line[t.end() - 1:])))
    return out


# Cycle 54: a tactic that "made no progress" (simp 20, simp_all 3 of 1,030 errors in today's trajectories) or that runs after the goal
# is closed ("No goals to be solved", 11) changes nothing, so deleting its line leaves the proof state identical, and the proof gets
# shorter. Only whole lines (plus their continuation lines) that start with the failing tactic are deleted; bullets and case arms stay.
_NOOP_FAIL = re.compile(r"^(\d+):(\d+): (?:`?[\w_?]+(?: only)?`? (?:failed to simplify|made no progress)|No goals to be solved|no goals to be proved)")


def noop_line_deletion(decl: str, errors: list[str], head_lines: int) -> tuple[str, str] | None:
    """(description, declaration without the no-op line) for the FIRST error when it is a no-progress / no-goals error, else None."""
    m = _NOOP_FAIL.match(errors[0]) if errors else None
    if not m:
        return None
    ln, col = int(m.group(1)) - head_lines, int(m.group(2))
    lines = decl.split("\n")
    if not 2 <= ln <= len(lines):          # never touch the statement's first line
        return None
    line = lines[ln - 1]; body = line.lstrip(); ind = len(line) - len(body)
    if col != ind or not body or body.startswith(("·", "case ", "next ", "|", "--")) or ":=" in body.split("--")[0] and "by" not in body:
        return None
    prev = next((l for l in reversed(lines[:ln - 1]) if l.strip()), "")
    p_ind = len(prev) - len(prev.lstrip())
    if ind > p_ind and not prev.rstrip().endswith(("by", "=>", "with", "·", "do")) and not prev.lstrip().startswith(("·", "case ", "next ", "|")):
        return None                          # a continuation line of the previous tactic, not a tactic of its own
    end = ln
    while end < len(lines) and lines[end].strip() and len(lines[end]) - len(lines[end].lstrip()) > ind:
        end += 1                             # continuation lines of the same tactic
    return f"deleted no-op line `{body[:50]}`", "\n".join(lines[:ln - 1] + lines[end:])


# Cycle 55 tested a closer battery for "unsolved goals" (inline `<;> first | grind | simp_all | omega | aesop` or a final
# `all_goals …` line on the failing block): 0 of 24 real failures from the dev runs were rescued (most sit in term-mode `by` blocks
# inside a line), so it was reverted.


# Cycle 56 (E3 integration, its typing-gate message built from the compile instead of a footprint): a candidate that compiles on the
# primary toolchain but not on an older listed one came back as `compat: {v: false}` with no reason, and inside lean_check_variants
# not even that. 10 of 1,261 compatibility checks in the readable trajectories failed (fold 4x: `Polynomial.eval_finsetSum` is missing
# at v4.29.0; 1995 a3 4x, 1964 a4, fiberwise), each costing 11-22 points. Say why: the first errors at that toolchain (candidate
# lines) and, for missing names, the closest names that do exist there.
def compat_failure(row: dict, version: str, errors: list[str]) -> dict:
    hl = head_line_count(row, version); errs = []
    for e in errors[:2]:
        m = re.match(r"(\d+):(\d+): ", e)
        errs.append(digest_error(f"candidate line {int(m.group(1)) - hl}, col {m.group(2)}: {e[m.end():]}" if m and int(m.group(1)) > hl else e, 400))
    out = {"errors": errs}
    sug = suggest_names(row, version, errors)
    if sug:
        out["did_you_mean_here"] = sug
    return out


def compat_note(primary: str, failures: dict, Z: float, score: float, provisional: float) -> str:
    return (f"compiles on {primary} but not on {', '.join(failures)}, so Z = {Z:.0f} and the score is {score} instead of {provisional}. "
            "compat_failures shows why. Keep the idea, but use only names and tactics that exist on every listed toolchain "
            "(did_you_mean_here lists names that do exist there).")


# Cycle 58 (E2's one actionable recommendation): a single `simp?` compile prunes unused lemmas from existing `only` lists; it was behind
# E2's largest held-out gain (insertionSort 303 -> 285 tokens, 59.29 -> 61.26). Every `simp/simp_all/dsimp only [...]` site becomes its `?`
# form, Lean's "Try this" lists (the union over repeated invocations under `<;>`/all_goals) replace the written lists, and the caller keeps the
# result only if it compiles and scores higher (simp? sometimes prints a list that does not replay). Sites that never ran keep their list.
_ONLY_SITE = re.compile(r"\b(simp_all|simp|dsimp)(\s+only\s*\[)")
_ONLY_PROBE = re.compile(r"\b(simp_all|simp|dsimp)\?(\s+only\s*\[)")
_TRY_THIS = re.compile(r"^Try (?:this|these):\s*(?:\[apply\]\s*)?", re.S)


def _bracket_items(t: str, i: int) -> tuple[int, list[str]] | None:
    """For the '[' at t[i]: (index after the matching ']', top-level items)."""
    depth, cur, items = 0, "", []
    for j in range(i, len(t)):
        ch = t[j]
        if ch in "[(⟨{":
            depth += 1
            if depth == 1:
                continue
        elif ch in "])⟩}":
            depth -= 1
            if depth == 0:
                return j + 1, items + ([cur.strip()] if cur.strip() else [])
        if ch == "," and depth == 1:
            items.append(cur.strip()); cur = ""
        else:
            cur += ch
    return None


def simp_prune(decl: str, compile_fn, head_lines: int) -> tuple[str, int] | None:
    """(declaration with Lean's suggested `only` lists, lemmas dropped) when simp? shortens at least one list, else None."""
    sites = list(_ONLY_SITE.finditer(decl))
    if not sites:
        return None
    probe = _ONLY_SITE.sub(lambda m: m.group(1) + "?" + m.group(2), decl)
    r = compile_fn(probe)
    if not r.ok:
        return None
    pos = {}
    for k, m in enumerate(_ONLY_PROBE.finditer(probe)):   # Lean reports each suggestion at the start of its `simp?`
        pos[(probe.count("\n", 0, m.start()) + 1 + head_lines, m.start() - (probe.rfind("\n", 0, m.start()) + 1))] = k
    sugg: dict[int, list[str]] = {}
    for msg in r.messages:
        d = str(msg.get("data", "")); p = msg.get("pos") or {}
        k = pos.get((p.get("line"), p.get("column")))
        if k is None or not _TRY_THIS.match(d):
            continue
        t = _TRY_THIS.sub("", d, count=1); b = t.find("[")
        got = _bracket_items(t, b) if b >= 0 else (0, [])
        if got is not None:
            sugg.setdefault(k, [])
            sugg[k] += [x for x in got[1] if x not in sugg[k]]
    out, dropped = decl, 0
    for k in sorted(sugg, reverse=True):   # right to left, so earlier indices stay valid
        m = sites[k]; lb = m.end() - 1; got = _bracket_items(decl, lb)
        if got is None or len(sugg[k]) >= len(got[1]):
            continue
        only_end = m.start(2) + m.group(2).index("only") + 4
        new = (" [" + ", ".join(sugg[k]) + "]") if sugg[k] else ""
        out = out[:only_end] + new + out[got[0]:]
        dropped += len(got[1]) - len(sugg[k])
    return (out, dropped) if dropped else None


# Cycle 57: the prompt says later upstream commits may hold a simplified proof (R2 allows porting them), and the model then spends shell
# turns on `git log -p` / `git show` in the project clone: 798 such calls in 568 readable trajectories, 7-19% of the turns of cold and
# fresh passes. Do that lookup once at run start: the theorem as it stands at upstream HEAD (or that it is unchanged / gone), and the
# commits that touched its file since the pinned commit.
_TOPLEVEL = re.compile(r"^(?:@\[|/--|(?:private |protected |noncomputable |nonrec |public )*(?:theorem|lemma|def|abbrev|instance|example|structure"
                       r"|inductive|class)\b|end\b|namespace\b|section\b|open\b|variable\b|attribute\b|set_option\b|#)", re.M)


def upstream_digest(row: dict, primary: str, limit: int = 3500) -> str:
    gm = ROOT / "envs" / f"{row['source']}.git-main"
    if row["source"] == "putnambench" or not gm.exists():
        return ""

    def git(*a: str) -> str | None:
        try:
            p = subprocess.run(["git", "-C", str(gm), *a], capture_output=True, text=True, timeout=60)
        except Exception:  # noqa: BLE001
            return None
        return p.stdout if p.returncode == 0 else None
    pins = {k: v for d in row["version_info"] for k, v in d.items()} if isinstance(row["version_info"], list) else dict(row["version_info"])
    pin = pins.get(primary)
    if not pin:   # held-out rows carry no commit: the primary environment's checkout is the pinned state
        try:
            pin = subprocess.run(["git", "-C", str(ROOT / "envs" / f"{row['source']}-{primary}"), "rev-parse", "HEAD"],
                                 capture_output=True, text=True, timeout=30).stdout.strip()
        except Exception:  # noqa: BLE001
            pin = ""
    if not pin or git("merge-base", "--is-ancestor", pin, "HEAD") is None:
        return ""   # the clone has no history after the pinned state: say nothing rather than show an older version as "later"
    head = (git("log", "-1", "--format=%h %cs") or "?").strip()
    short = row["name"].split(".")[-1]
    rx = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|nonrec|noncomputable|public)\s+)*(?:theorem|lemma)\s+(?:\S*\.)?"
                    + re.escape(short) + r"(?=[\s:({\[]|$)", re.M)
    path = row["file_path"]; src = git("show", f"HEAD:{path}")
    if src is None or not rx.search(src):   # moved or renamed: the declaration anywhere at HEAD
        hits = [h.split(":", 1)[1] for h in (git("grep", "-l", "-E", r"^[[:space:]]*(theorem|lemma)[[:space:]]+([^[:space:]]*\.)?" + re.escape(short) + r"([[:space:]:({]|$)",
                                                  "HEAD", "--", "*.lean") or "").split() if ":" in h]
        path = hits[0] if len(hits) == 1 else path
        src = git("show", f"HEAD:{path}") if len(hits) == 1 else None
    commits = [c[:90] for c in (git("log", "--format=%h %cs %s", f"{pin}..HEAD", "--", path) or "").splitlines()]
    hist = f"{len(commits)} upstream commit(s) touched {path} since the pinned commit" + (": " + "; ".join(commits[:5]) if commits else "")
    m = rx.search(src) if src else None
    if not m:
        return (f"UPSTREAM (precomputed from the project's git history): `{short}` no longer exists at upstream HEAD ({head}): renamed or deleted, "
                f"nothing to port directly. {hist}.")
    nxt = _TOPLEVEL.search(src, src.index("\n", m.start()) + 1 if "\n" in src[m.start():] else len(src))
    decl = src[m.start():nxt.start() if nxt else len(src)].rstrip()
    norm = lambda s: re.sub(r"\s+", " ", remove_comments(s)).strip()
    if norm(decl) == norm(row["src"]):
        return (f"UPSTREAM (precomputed from the project's git history): `{short}` is unchanged at upstream HEAD ({head}); {hist}. "
                "There is no later upstream simplification of this proof to port: do not spend turns on git log for it.")
    body = split_declaration(decl, row["statement"])
    same_stmt = body is not None
    toks = count_tokens(body if same_stmt else decl.split(":=", 1)[-1])
    note = (f"`{short}` at upstream HEAD ({head}) differs from the reference: its proof is {'' if same_stmt else 'about '}{toks} tokens vs "
            f"{row['proof_length']} in the reference{'' if same_stmt else ' (the statement changed too)'}. {hist}.")
    if toks >= row["proof_length"]:
        return f"UPSTREAM (precomputed from the project's git history): {note} It is not shorter, so there is little to port."
    return (f"UPSTREAM (precomputed from the project's git history; porting later upstream proofs is allowed): {note} It may use newer "
            f"definitions or lemma names: port it to the pinned toolchains rather than copying blindly. The HEAD version:\n```lean\n{decl[:limit]}\n```"
            + ("\n(truncated)" if len(decl) > limit else ""))


def lean_check(name: str, decl: str, state: dict, provenance: dict, verified_path: Path | None) -> dict:
    """Compile `decl` for problem `name`; update `state` (best + attempts); append a
    verified record when it beats the current best. Returns the tool result dict."""
    row = ROWS[name]; versions = newest_first(row["version_info"]); primary = versions[0]
    body = split_declaration(decl.rstrip(), row["statement"])
    if body is None:
        return {"ok": False, "errors": ["statement differs from the reference statement (must be byte-for-byte identical, followed by :=)"]}
    bad = check_forbidden(decl)
    if bad:
        return {"ok": False, "errors": [f"forbidden construct: {bad}"]}
    toks = count_tokens(body); r = comp(row, decl, primary); auto_fixed = None
    if not r.ok:
        _fixed, _names = fix_redundant_grind(decl, r.errors)
        if _fixed:
            _r2 = comp(row, _fixed, primary)
            if _r2.ok:
                decl, r = _fixed, _r2; toks = count_tokens(split_declaration(decl.rstrip(), row["statement"]) or body)
                auto_fixed = f"removed redundant grind parameter(s) {', '.join(_names)} (grind uses local hypotheses automatically)"
    if not r.ok and not auto_fixed:   # cycle 54: delete no-op lines, up to 3 rounds (a deletion can expose the next no-op)
        _cur, _done = decl, []
        for _round in range(3):
            _d = noop_line_deletion(_cur, r.errors if _round == 0 else _r2.errors, head_line_count(row, primary))
            if not _d:
                break
            _cur = _d[1]; _done.append(_d[0]); _r2 = comp(row, _cur, primary)
            if _r2.ok:
                decl, r = _cur, _r2; toks = count_tokens(split_declaration(decl.rstrip(), row["statement"]) or body)
                auto_fixed = "; ".join(_done)
                break
    if not r.ok and not auto_fixed:
        for _how, _cand in rw_alternatives(decl, r.errors, head_line_count(row, primary)):
            _r2 = comp(row, _cand, primary)
            if _r2.ok:
                decl, r = _cand, _r2; toks = count_tokens(split_declaration(decl.rstrip(), row["statement"]) or body)
                auto_fixed = f"failed rewrite repaired: {_how}"
                break
    hl = head_line_count(row, primary); hints = []
    for m in r.messages:
        if m.get("severity") != "warning":
            continue
        d = str(m.get("data", "")); ln = (m.get("pos") or {}).get("line", 0) - hl
        if ln >= 1 and ("does nothing" in d or "unused" in d.lower() or "would suffice" in d):
            hints.append(f"line {ln}: " + re.sub(r"\s+", " ", d.split("Note:")[0]).strip()[:140])
    hints = list(dict.fromkeys(hints))[:12]
    attempt = {"sha": hashlib.sha256(decl.encode()).hexdigest()[:12], "tokens": toks, "heartbeats": r.heartbeats, "ok": r.ok,
               "error": (digest_error(r.errors[0], 300) if r.errors else None), "run_id": provenance.get("run_id"),
               "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
    state.setdefault("attempts", []).append(attempt); state["attempts"] = state["attempts"][-200:]
    res = {"ok": r.ok, "tokens": toks, "ref_tokens": row["proof_length"], "heartbeats": r.heartbeats, "ref_heartbeats": HBS.get(name),
           "warnings": r.warnings, "errors": [digest_error(e) for e in r.errors[:5]], "linter_hints": hints}
    if auto_fixed:
        res.update({"auto_fixed": auto_fixed, "fixed_decl": decl})
    if not r.ok:
        _sug = suggest_names(row, primary, r.errors)
        if _sug:
            res["did_you_mean"] = _sug
    if r.ok:
        L = len_pct(row["proof_length"], toks); H = hb_pct_local(name, r.heartbeats, HBS.get(name))
        provisional = problem_score(True, L, H, 100.0)
        res.update({"length_reduction_pct": round(L, 2), "heartbeat_reduction_pct": round(H, 2), "predicted_score_if_compatible": provisional, "reference_score": 33.33})
        best = state.setdefault("best", {"score": 33.33, "proof": None})
        if provisional > best.get("score", 33.33):
            compat = {primary: True}; failures = {}
            for v in versions[1:]:
                rv = comp(row, decl, v, count=False); compat[v] = rv.ok
                if not rv.ok:
                    failures[v] = compat_failure(row, v, rv.errors)
            Z = compat_pct(compat); sc = problem_score(True, L, H, Z)
            res.update({"compat": compat, "score": sc})
            if failures:
                res.update({"compat_failures": failures, "compat_note": compat_note(primary, failures, Z, sc, provisional)})
            if sc > best.get("score", 33.33):
                state["best"] = {"score": sc, "proof": decl, "tokens": toks, "heartbeats": r.heartbeats, "L": round(L, 2), "H": round(H, 2), "Z": Z, "compat": compat}
                attempt["score"] = sc
                if verified_path:
                    verified_path.parent.mkdir(parents=True, exist_ok=True)
                    with verified_path.open("a") as f:
                        f.write(json.dumps({"problem": name, "sha256": attempt["sha"][:16], "proof": decl, "tokens": toks, "ref_tokens": row["proof_length"],
                                            "heartbeats": r.heartbeats, "primary": primary, "primary_ok": True, "compat": compat, "L": round(L, 2), "H": round(H, 2), "Z": Z,
                                            "score": sc, "provenance": provenance}, ensure_ascii=False) + "\n")
                res["new_best"] = True
    return res


def lean_run(name: str, code: str) -> str:
    row = ROWS[name]; primary = newest_first(row["version_info"])[0]
    if row["source"] == "putnambench":
        wd = env_dir(primary); head = row["header"].rstrip() + "\n\n"
    else:
        wd = project_env_dir(row["source"], primary); head = file_prefix(row, primary).rstrip("\n") + "\n\n"
    scratch = wd / "LRAScratch"; scratch.mkdir(exist_ok=True)
    f = scratch / f"s_{uuid.uuid4().hex[:10]}.lean"; f.write_text(head + code.rstrip() + "\n")
    env = dict(os.environ, PATH=f"{ELAN_BIN}:{os.environ.get('PATH','')}")
    try:
        pr = run_lean(["lake", "env", "lean", "--json", f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}", str(f.relative_to(wd))], cwd=wd, env=env, capture_output=True, text=True, timeout=300)
    except subprocess.TimeoutExpired:
        f.unlink(missing_ok=True); return "error: timed out after 300s"
    f.unlink(missing_ok=True)
    off = head.count("\n"); out = []
    for line in pr.stdout.splitlines():
        if not line.startswith("{"):
            continue
        try:
            m = json.loads(line)
        except json.JSONDecodeError:
            continue
        ln = (m.get("pos") or {}).get("line", 0) - off
        if ln >= 1:
            out.append(f"[{m.get('severity')}] line {ln}: {m.get('data','')}")
    return ("\n".join(out) if out else f"(no messages; exit {pr.returncode})")[:12000]
