#!/usr/bin/env python3
"""Lemma search: ranked library-lemma suggestions for a candidate proof (panel Tier 1 item 3, 2026-10-08).

The panels found that the biggest single jumps came from knowing that a library lemma exists (variational
`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero`, fiberwise `card_le_mul_card_image_of_maps_to`, a4
`Finite.exists_lt_map_eq_of_forall_mem`, Inits' unused siblings ...) and that Flash never finds them. This module asks the
library from five angles and merges the answers:

  a. exact  `exact?` (and `apply?`) at the goals of the candidate: have/case/bullet bodies replaced in place (batched, Lean recovers
            after a failed nested block), plus suffix probes for plain top-level steps; "Try this" suggestions are harvested.
            Dead-branch probe: every exfalso/contradiction block is tried with each bare closer lemma the proof uses elsewhere.
  b. name   keyword name search: keywords from the goal targets (after ⊢), the statement and the lemma names the candidate already
            uses; every `theorem|lemma` of the environment (project + Mathlib + deps + Lean core, indexed with ripgrep) is ranked by
            idf-weighted overlap of its name segments, then re-ranked by typeclass/hypothesis overlap with the statement and by
            conclusion-symbol overlap with the goals. Extensions of used lemmas (`card_le_card` -> `card_le_card_of_surjOn`) and
            `exists_*` lemmas matching the properties of a hand-built witness (`let φ : ContDiffBump x := ⟨…⟩`) get a bonus.
  c. sibling  declarations of the theorem's own file prefix ranked by symbol overlap with the statement; flags those the reference
            proof does not use.
  d. attr   `@[simp]`, `@[grind …]` and `@[to_fun]` lemmas (with the generated `fun_*` names) of the file and its in-project imports
            that mention the goals' head symbols; ∃-conclusion / `@[grind →]` lemmas get the note "pass as grind [→ name]".
  e. induction  `0 < n` / `a ≤ n` / `n ≠ 0` hypotheses or `induction` on ℕ suggest `Nat.le_induction`, `Nat.strong_induction_on`, ...
Every suggested name is verified with one `#check @name` compile (pp.fullNames) in the problem's environment and reported with its
signature. Compiles go through mine.lean_run, so through the memory gate; at most 2 run at a time.

    python3 harness/lemma_search.py <problem> <candidate.lean> [--top 10] [--json] [--no-probes] [--budget 180] [-v]

Env: LRA_LEMMA_CACHE (index cache dir, default /tmp/lra-lemma-index), LRA_LS_DEPTH (goal-trace depth, default 4),
LRA_LS_MEMO=1 (memoise compiles on disk; ranking development only). Benchmark: probe/lemma_recall/run.py; notes: docs/lemma_search.md.
"""
from __future__ import annotations

import argparse, hashlib, json, math, os, pickle, re, subprocess, sys, threading, time
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "harness")]

from mine import ROWS, lean_run, outer_blocks, body_lines  # noqa: E402
from goals import instrument  # noqa: E402
from scorer.compile import env_dir, project_env_dir, file_prefix, split_modifiers  # noqa: E402
from probe.verify_candidates import newest_first  # noqa: E402

CACHE = Path(os.environ.get("LRA_LEMMA_CACHE", "/tmp/lra-lemma-index"))
ELAN = Path.home() / ".elan" / "toolchains"
MAX_PAR = 2

# --------------------------------------------------------------------------------------------------------------------------------
# environment and declaration index
# --------------------------------------------------------------------------------------------------------------------------------


def primary_version(row: dict) -> str:
    return newest_first(row["version_info"])[0]


def env_root(row: dict) -> Path:
    v = primary_version(row)
    return env_dir(v) if row["source"] == "putnambench" else project_env_dir(row["source"], v)


def source_roots(row: dict) -> dict[str, list[Path]]:
    """{"project": [...], "deps": [...], "core": [...]}: the .lean trees whose declarations are in scope for this problem."""
    root = env_root(row)
    skip = {"LRAScratch", "LRAProbe", "scripts", "docs", "Cache", "DownstreamTest", "MathlibTest", "Archive", "Counterexamples",
            "LongestPole", "widget", "home_page", "blueprint", "editors", "Examples", "Tools", "scratch"}
    proj = [d for d in sorted(root.iterdir()) if d.is_dir() and not d.name.startswith(".") and d.name not in skip
            and d.name[:1].isupper() and not re.search(r"Tests?$|TestExtra$", d.name) and any(d.rglob("*.lean"))]
    deps = []
    pk = root / ".lake" / "packages"
    if pk.is_dir():
        for p in sorted(pk.iterdir()):
            if p.name in {"doc-gen4", "leansqlite", "MD4Lean", "BibtexQuery", "UnicodeBasic", "Cli", "checkdecls", "LeanSearchClient"}:
                continue
            subs = [d for d in p.iterdir() if d.is_dir() and d.name[:1].isupper() and not d.name.startswith(".")
                    and not re.search(r"Tests?$", d.name) and d.name not in skip]
            deps.extend(subs)
    tc = (root / "lean-toolchain").read_text().strip() if (root / "lean-toolchain").exists() else ""
    tcdir = ELAN / tc.replace("/", "--").replace(":", "---")
    core = [tcdir / "src" / "lean" / d for d in ("Init", "Std") if (tcdir / "src" / "lean" / d).is_dir()]
    return {"project": proj, "deps": deps, "core": core}


_DECL = re.compile(r"^\s*((?:@\[[^\]]*\]\s*)*)((?:(?:private|protected|nonrec|noncomputable|public|scoped)\s+)*)(theorem|lemma)\s+([^\s(:{\[⦃]+)")
_NS = re.compile(r"^\s*namespace\s+(\S+)")
_SEC = re.compile(r"^\s*(?:(?:noncomputable|public|private)\s+)*section\b")
_END = re.compile(r"^\s*end\b\s*(\S*)")
_MUT = re.compile(r"^\s*mutual\b")
_ATTR = re.compile(r"^\s*@\[(.*)\]\s*$")
RG_PATTERNS = [r"^\s*namespace\s", r"^\s*end\b", r"^\s*mutual\b", r"^\s*((noncomputable|public|private)\s+)*section\b", r"^\s*@\[",
               r"^\s*(@\[[^\]]*\]\s*)*((private|protected|nonrec|noncomputable|public|scoped)\s+)*(theorem|lemma)\s+\S"]


def _parse_lines(lines, file: str, out: list) -> None:
    """lines: iterable of (lineno, text) in file order -> append decl entries {name, short, file, line, attrs, private}."""
    stack: list[tuple[str, list[str]]] = []
    pending: tuple[int, str] | None = None
    for no, text in lines:
        m = _DECL.match(text)
        if m:
            attrs = m.group(1) or ""
            if pending and no - pending[0] <= 4:
                attrs = pending[1] + " " + attrs
            pending = None
            short = m.group(4)
            if short.startswith("_root_."):
                full = short[len("_root_."):]
            else:
                ns = [c for kind, comps in stack if kind == "ns" for c in comps]
                full = ".".join(ns + [short])
            out.append({"name": full, "short": short, "file": file, "line": no, "attrs": attrs.strip(),
                        "private": "private" in (m.group(2) or "")})
            continue
        m = _ATTR.match(text)
        if m:
            pending = (no, "@[" + m.group(1) + "]"); continue
        m = _NS.match(text)
        if m:
            stack.append(("ns", m.group(1).split("."))); continue
        if _SEC.match(text) or _MUT.match(text):
            stack.append(("sec", [])); continue
        m = _END.match(text)
        if m and stack:
            stack.pop()


_BUILD_LOCKS: dict[str, threading.Lock] = {}
_LOCKS_GUARD = threading.Lock()


def build_index(row: dict) -> list[dict]:
    """All theorem/lemma declarations in scope, with fully qualified names (namespace tracking), cached per environment."""
    roots = source_roots(row)
    allr = [(k, p) for k, ps in roots.items() for p in ps]
    key = hashlib.sha1(json.dumps([str(p) for _, p in allr]).encode()).hexdigest()[:16]
    # Cycle 75: the agent's workers are threads of ONE process, and the tmp name carried only the pid, so on a fresh machine two workers
    # building the same index raced on one tmp file and the loser failed ("No such file or directory: .../index_<key>.tmp<pid>": A100 pass
    # 7). One build per key per process; the others wait for it and read the cache.
    with _LOCKS_GUARD:
        lock = _BUILD_LOCKS.setdefault(key, threading.Lock())
    with lock:
        return _build_index_locked(allr, key)


def _build_index_locked(allr: list, key: str) -> list[dict]:
    CACHE.mkdir(parents=True, exist_ok=True)
    cf = CACHE / f"index_{key}.pkl"
    if cf.exists():
        try:
            return pickle.loads(cf.read_bytes())
        except Exception:  # noqa: BLE001
            pass
    kind_of = {str(p): k for k, p in allr}
    cmd = ["rg", "-n", "--no-heading", "--with-filename", "-g", "*.lean"]
    for pat in RG_PATTERNS:
        cmd += ["-e", pat]
    cmd += [str(p) for _, p in allr]
    pr = subprocess.run(cmd, capture_output=True, text=True)
    by_file: dict[str, list] = defaultdict(list)
    for l in pr.stdout.splitlines():
        try:
            f, no, text = l.split(":", 2)
        except ValueError:
            continue
        by_file[f].append((int(no), text))
    out: list[dict] = []
    for f, ls in by_file.items():
        ls.sort()
        start = len(out)
        _parse_lines(ls, f, out)
        k = next((kind_of[r] for r in kind_of if f.startswith(r + "/")), "deps")
        for e in out[start:]:
            e["kind"] = k
    tmp = cf.with_suffix(f".tmp{os.getpid()}-{threading.get_ident()}")   # unique per writer, also across processes
    tmp.write_bytes(pickle.dumps(out)); tmp.replace(cf)
    return out


_FILES: dict[str, list[str]] = {}


def _file_lines(f: str) -> list[str]:
    if f not in _FILES:
        try:
            _FILES[f] = Path(f).read_text(errors="replace").split("\n")
        except OSError:
            _FILES[f] = []
    return _FILES[f]


def source_signature(e: dict, max_lines: int = 14) -> str:
    """The declaration text from its line up to `:=` (or `where`/`|` line), whitespace-collapsed."""
    ls = _file_lines(e["file"])
    i = e["line"] - 1
    buf = []
    for l in ls[i: i + max_lines]:
        k = l.find(":=")
        if k >= 0:
            buf.append(l[:k]); break
        if buf and re.match(r"^\s*(\||where\b)", l):
            break
        buf.append(l)
    return re.sub(r"\s+", " ", " ".join(buf)).strip()


# --------------------------------------------------------------------------------------------------------------------------------
# keywords
# --------------------------------------------------------------------------------------------------------------------------------

_IDENT = re.compile(r"[A-Za-z_Ͱ-Ͽᴀ-ᶿ][\w'!?Ͱ-Ͽ₀-ₜᵢ-ᵪ]*(?:\.[A-Za-z_][\w'!?]*)*")
_SYM = [("∫", "integral"), ("∑", "sum"), ("∏", "prod"), ("≤", "le"), ("≥", "le"), ("<", "lt"), (">", "lt"), ("≠", "ne"),
        ("∈", "mem"), ("∉", "mem"), ("⊆", "subset"), ("⊂", "ssubset"), ("''", "image"), ("⁻¹'", "preimage"), ("∃", "exists"),
        ("∀", "forall"), ("•", "smul"), ("^", "pow"), ("∪", "union"), ("∩", "inter"), ("∅", "empty"), ("⁻¹", "inv"),
        ("¬", "not"), ("∘", "comp"), ("⟪", "inner"), ("‖", "norm"), ("𝓝", "nhds"), ("#", "card"), ("∂", "deriv"),
        ("∣", "dvd"), ("%", "mod"), ("√", "sqrt"), ("⋃", "iUnion"), ("⋂", "iInter"), ("×ˢ", "prod"), ("↑", "coe")]
_PAT = [(re.compile(r"\b0\s*<|>\s*0\b"), "pos"), (re.compile(r"\b0\s*≤|≥\s*0\b"), "nonneg"), (re.compile(r"≠\s*0\b"), "nonzero"),
        (re.compile(r"(?<![=<>≤≥≠:])=(?![=>])"), "eq"), (re.compile(r"\s\+\s"), "add"), (re.compile(r"\s\*\s"), "mul"),
        (re.compile(r"\s-\s"), "sub"), (re.compile(r"\s/\s"), "div"), (re.compile(r"∃!"), "existsUnique")]
SYNONYMS = {"support": ["tsupport"], "tsupport": ["support"], "hasCompactSupport": ["tsupport", "compact"],
            "nonzero": ["ne", "zero"], "ncard": ["card"], "toFinset": ["card"], "biUnion": ["card"], "pos": ["lt"],
            "nonneg": ["le"], "injective": ["injOn"], "surjective": ["surjOn"], "range": ["image"], "image": ["surjOn", "maps"], "infinite": ["finite"],
            "finite": ["infinite"], "exists": [], "le": [], "lt": []}
STOP = {"of", "iff", "the", "a", "an", "h", "mk", "def", "apply", "this", "x", "y", "n", "m", "i", "j", "k", "f", "g", "s", "t",
        "u", "v", "e", "p", "q", "r", "c", "d", "b", "fun", "by", "at", "with", "to", "is", "in", "_", "u_1", "u_2", "inst",
        "Type", "Prop", "Sort", "true", "false", "left", "right", "symm", "trans", "mp", "mpr", "1", "2", "val", "property",
        "elim", "intro", "rec", "le_refl", "id", "and", "or", "not", "eq", "ne", "coe"}
WEAK = {"eq", "ne", "and", "or", "not", "coe", "forall", "add", "mul", "sub"}   # kept as keywords but at half weight
BASIC = {"le", "lt", "eq", "ne", "add", "sub", "mul", "div", "pos", "nonneg", "neg", "zero", "one", "two", "succ", "pred", "pow",
         "nat", "int", "real", "cast", "self", "not", "and", "or", "exists", "forall", "mem", "coe", "gt", "ge", "inv", "abs",
         "set", "list", "finset", "option", "some", "none", "fin", "smul", "nonzero", "left", "right", "comm", "assoc", "cancel"}


def _lower_first(s: str) -> str:
    return s[:1].lower() + s[1:] if s else s


def _segments(ident: str) -> list[str]:
    """`Finset.card_le_mul_card_image_of_maps_to` -> finset card le mul card image maps to; camelCase parts stay whole."""
    out = []
    comps = [c for c in ident.split(".") if c and not c.isdigit()]
    for k, c in enumerate(comps):
        if "_" in c:
            out.extend(x for x in c.split("_") if x)
        else:
            out.append(_lower_first(c))
    return [x for x in out if x and not x.isdigit()]


def keywords(text: str, local: set[str] | frozenset = frozenset()) -> Counter:
    kw: Counter = Counter()
    for sym, k in _SYM:
        n = len(re.findall(r"\s''\s", text)) if sym == "''" else text.count(sym)
        if n:
            kw[k] += n
    for rx, k in _PAT:
        n = len(rx.findall(text))
        if n:
            kw[k] += n
    for ident in _IDENT.findall(text):
        if ident.split(".")[0] in local or ident in _LEAN_KW:
            continue
        for s in _segments(ident):
            if s not in STOP and len(s) > 1:
                kw[s] += 1
    return kw


def _first_goal_target(state: str) -> tuple[str, str]:
    """(hypotheses text, target text) of the first goal of a trace_state dump."""
    goals = [g for g in re.split(r"\n\s*\n", state.strip()) if g.strip()]
    if not goals or "⊢" not in goals[0]:
        return "", ""
    hyps, tgt = goals[0].rsplit("⊢", 1)
    return hyps, tgt


def _typeclasses(text: str) -> set[str]:
    """Typeclass names in instance binders `[Foo α]`, `[inst : Foo α]`, `[μ.IsOpenPosMeasure]`."""
    out = set()
    for b in re.findall(r"\[([^\[\]]+)\]", text):
        b = re.sub(r"^\s*\w+\s*:\s*", "", b).strip()
        m = re.match(r"([\w.']+)", b)
        if m and m.group(1)[:1] not in "0123456789@":
            nm = m.group(1).split(".")[-1]
            if nm[:1].isupper():
                out.add(nm)
    return out


_LEAN_KW = {"theorem", "lemma", "fun", "by", "at", "with", "using", "only", "then", "else", "if", "match", "do", "let", "have", "show",
            "from", "exact", "apply", "intro", "intros", "obtain", "rcases", "rintro", "cases", "induction", "generalizing", "simp",
            "simp_all", "grind", "aesop", "omega", "rfl", "rw", "rwa", "erw", "refine", "use", "left", "right", "constructor",
            "case", "all_goals", "any_goals", "first", "next", "subst", "calc", "conv", "enter", "suffices", "this", "Type", "Prop",
            "Sort", "fun_prop", "norm_num", "linarith", "nlinarith", "positivity", "tauto", "ring", "field_simp", "congr", "ext",
            "funext", "specialize", "exists", "refine'", "split", "unfold", "dsimp", "simpa", "exfalso", "contradiction", "by_contra",
            "by_cases", "push_neg", "set", "change", "trivial", "assumption", "repeat", "try", "focus", "nofun", "nomatch",
            "classical", "decide", "rename_i", "exacts", "apply?", "exact?", "trace_state", "sorry", "open", "in", "where",
            "true", "false", "True", "False", "and", "or", "not", "fin_cases", "interval_cases", "gcongr", "bound", "infer_instance",
            "inferInstance", "Nat", "Int", "Real", "List", "Set", "Finset", "Option", "Bool", "Prod", "Fin", "ENat", "ENNReal", "NNReal"}


def bound_names(text: str) -> set[str]:
    """Names bound in the text: binders `(a b : T)`, `{a : T}`, `[inst : C]`, `∀ a b,`, `∃ x,`, `fun x =>`, goal-context lines
    `a b : T`, pattern binders `⟨a, b⟩`, `| succ n ih =>`, `intro a b`, `obtain ⟨…⟩`, `have h :`, `case X a b =>`."""
    out: set[str] = set()
    for grp in re.findall(r"[({⦃\[]\s*([^(){}\[\]:]+?)\s*:", text):
        out.update(x for x in grp.split() if re.match(r"^[^\W\d][\w'₀-₉]*$", x))
    for grp in re.findall(r"(?:∀|∃!?|fun|λ)\s+([^,:=(]+?)\s*(?:,|=>|:|↦)", text):
        out.update(x for x in re.split(r"[\s()⟨⟩]+", grp) if re.match(r"^[^\W\d][\w'₀-₉]*$", x))
    for line in text.split("\n"):
        m = re.match(r"^\s*([^\W\d][\w'₀-₉]*(?:\s+[^\W\d][\w'₀-₉]*)*)\s*:\s", line)
        if m and not re.match(r"^\s*(theorem|lemma|have|show|def|case|example|instance)\b", line):
            out.update(m.group(1).split())
    for grp in re.findall(r"⟨([^⟨⟩]*)⟩", text):
        out.update(x for x in re.split(r"[\s,]+", grp) if re.match(r"^[^\W\d][\w'₀-₉]*$", x))
    for grp in re.findall(r"(?:\|\s*\w+|intro|intros|rintro|rename_i|case\s+\S+|next)\s+([^\n=:]*?)(?:=>|$)", text, re.M):
        out.update(x for x in grp.split() if re.match(r"^[^\W\d][\w'₀-₉]*$", x))
    for grp in re.findall(r"(?:have|obtain|set|let|generalize)\s+([^\W\d][\w'₀-₉]*)", text):
        out.add(grp)
    return {x for x in out if x not in _LEAN_KW or len(x) <= 2}


_PROJ = {"mp", "mpr", "symm", "le", "lt", "ne", "ne'", "trans", "elim", "out", "1", "2", "resolve_left", "resolve_right", "mono",
         "trans_le", "trans_lt", "le_of_eq", "ge", "not_lt", "not_le", "imp", "of_eq", "eq", "toFun", "inj", "injective", "ext"}


def global_names(text: str, local: set[str]) -> list[str]:
    """Identifiers in a proof fragment that may be global constants: not keywords, not bound names (dot-notation on a local
    `h.card_le_card` contributes its field name). #check filters the rest."""
    out = []
    for t in _IDENT.findall(text):
        comps = [c for c in t.rstrip(".").split(".") if c and not c.isdigit()]
        if not comps:
            continue
        if comps[0] in local:
            if len(comps) >= 2 and ("_" in comps[-1] or len(comps[-1]) > 4):
                out.append(comps[-1])
            continue
        while len(comps) >= 2 and comps[-1] in _PROJ:          # foo.mp, foo.symm, foo.le -> foo
            comps = comps[:-1]
        if len(comps) == 1 and (comps[0] in _LEAN_KW or len(comps[0]) <= 2):
            continue
        out.append(".".join(comps))
    return list(dict.fromkeys(out))


def split_statement(stmt: str) -> tuple[str, str]:
    """(binders, conclusion) at the declaration's top-level colon."""
    s = re.sub(r":=\s*(by)?\s*$", "", stmt.strip())
    m = re.search(r"(?:theorem|lemma)\s+\S+", s)
    i = m.end() if m else 0
    depth = 0
    pairs = {"(": 1, "[": 1, "{": 1, "⦃": 1, "⟨": 1, ")": -1, "]": -1, "}": -1, "⦄": -1, "⟩": -1}
    while i < len(s):
        ch = s[i]
        depth += pairs.get(ch, 0)
        if ch == ":" and depth == 0 and s[i + 1: i + 2] != "=":
            return s[:i], s[i + 1:]
        i += 1
    return s, ""


def _hyp_kinds(text: str) -> set[str]:
    """Head words of explicit hypotheses `(h : Continuous f)` -> {continuous}."""
    out = set()
    for b in re.findall(r"\(\s*[\w'₀-₉ ]+\s*:\s*([^()]+?)\)", text):
        m = re.match(r"[¬\s]*([A-Za-z][\w.']*)", b)
        if m:
            out.add(_lower_first(m.group(1).split(".")[-1]))
    return out


# --------------------------------------------------------------------------------------------------------------------------------
# compile helpers
# --------------------------------------------------------------------------------------------------------------------------------


def _prelude(row: dict, hb: int | None = 1000000) -> str:
    """Code put before the candidate: a sink declaration absorbing a trailing docstring/attribute of the file prefix (otherwise
    `set_option … in` right after a docstring is a parse error), the prefix's `open … in` modifiers, and a heartbeat budget."""
    out = ""
    mods = ""
    if row["source"] != "putnambench":
        try:
            _, mods = split_modifiers(file_prefix(row, primary_version(row)))
        except Exception:  # noqa: BLE001
            mods = ""
    if mods.strip():
        out += "theorem lra_ls_sink : True := trivial\n\n"
        out += "".join(m + " in\n" for m in re.findall(r"open\s+[\w.\s]+?(?=\s+in\b)", mods))
    if hb:
        out += f"set_option maxHeartbeats {hb} in\n"
    return out


def _run(name: str, code: str, timeout: int) -> list[dict]:
    """lean_run, optionally memoised on disk (LRA_LS_MEMO=1, for ranking development: same code -> same messages)."""
    memo = None
    if os.environ.get("LRA_LS_MEMO") == "1":
        memo = CACHE / "runs" / (hashlib.sha1((name + "\0" + code).encode()).hexdigest() + ".json")
        if memo.exists():
            return json.loads(memo.read_text())
    try:
        out = lean_run(name, code, timeout=timeout)
    except Exception as ex:  # noqa: BLE001
        return [{"severity": "error", "line": 0, "data": f"lean_run failed: {ex}"}]
    if memo is not None and not any(m["data"] == "timeout" for m in out):
        memo.parent.mkdir(parents=True, exist_ok=True)
        memo.write_text(json.dumps(out))
    return out


_TRY = re.compile(r"(?:\[apply\]\s*)?((?:exact|refine|apply|rw|simp|simpa|exacts|use|constructor|intro|omega|linarith)\b[^\n]*)")


def _try_this_all(msgs: list[dict], line: int) -> list[str]:
    out = []
    for m in msgs:
        if m["severity"] in ("information", "info") and m["line"] == line and "Try this" in m["data"]:
            body = m["data"].split("Try this:", 1)[1]
            got = []
            for l in body.split("\n"):
                l = re.sub(r"^\[apply\]\s*", "", l.strip())
                l = re.sub(r"^\(expose_names;\s*(.*)\)\s*(--.*)?$", r"\1", l)      # apply? wraps suggestions that use inaccessible names
                l = re.sub(r"\s*--.*$", "", l)
                mm = _TRY.match(l)
                if mm:
                    got.append(re.sub(r"\s+", " ", mm.group(1)).strip())
            if not got and body.strip():
                got.append(re.sub(r"\s*--.*", "", re.sub(r"\s+", " ", body)).strip()[:300])
            out.extend(got)
    return list(dict.fromkeys(out))


def _shorten(sig: str) -> str:
    """Drop namespace prefixes of two or more components (`Cslib.LambdaCalculus.LocallyNameless.Fsub.Term` -> `Term`)."""
    return re.sub(r"(?<![\w.])(?:[A-Z][\w']*\.){2,}(?=[\w'])", "", sig)


def check_names(name: str, row: dict, cands: list[str], timeout: int = 300) -> dict[str, dict]:
    """#check @c for every candidate in one compile -> {candidate: {"full": fully qualified name, "sig": signature}}."""
    cands = [c for c in dict.fromkeys(cands) if c and re.match(r"^[\w.'!?Ͱ-Ͽ₀-ₜ]+$", c)][:220]
    if not cands:
        return {}
    pre = _prelude(row, hb=None)
    code = pre + "set_option pp.fullNames true\nset_option pp.proofs false\n" + "\n".join(f"#check @{c}" for c in cands) + "\n"
    off = pre.count("\n") + 2
    msgs = _run(name, code, timeout)
    by_line: dict[int, list[dict]] = defaultdict(list)
    for m in msgs:
        by_line[m["line"]].append(m)
    out = {}
    for i, c in enumerate(cands, 1):
        ms = by_line.get(off + i, [])
        if any(m["severity"] == "error" for m in ms):
            continue
        info = [m["data"] for m in ms if m["severity"] in ("information", "info")]
        if not info:
            continue
        d = info[0]
        mm = re.match(r"@?([^\s:]+)\s*:\s*(.*)", d, re.S)
        if not mm or not re.match(r"^[^\W\d][\w.'!?₀-₉]*$", mm.group(1)):
            continue
        sig = re.sub(r"\s+", " ", mm.group(2)).strip()
        if re.search(r"(→|^)\s*(Prop|Type\b[^→]*|Sort\b[^→]*)$", sig):          # a definition (predicate / type former), not a lemma
            continue
        out[c] = {"full": mm.group(1), "sig": sig, "short_sig": _shorten(sig)}
    return out


# --------------------------------------------------------------------------------------------------------------------------------
# (a) exact? / apply? at goals
# --------------------------------------------------------------------------------------------------------------------------------

_SHORT_CLOSER = re.compile(r"^(exact|apply|simp|simp_all|omega|rfl|linarith|positivity|norm_num|aesop|grind|tauto|trivial|decide|"
                           r"assumption|contradiction|ring|field_simp|fun_prop|constructor|nofun|rwa?|simpa)\b")


def _block_body(body: list[str], b: dict) -> list[str]:
    hl = b["header"].count("\n") + 1
    first = body[b["start"]]
    lines = body[b["start"] + hl - 1: b["end"]]
    # text after the header on its first line (e.g. `· exact foo`, `have h : T := by simp`) is part of the body
    head_last = b["header"].split("\n")[-1].strip()
    if lines:
        rest0 = lines[0].strip()
        rest0 = rest0[len(head_last):].strip() if rest0.startswith(head_last) else (rest0 if hl == 1 and b["kind"] != "have" else "")
        if b["kind"] == "have":
            k = lines[0].find(":=")
            rest0 = re.sub(r"^by\b", "", lines[0][k + 2:].strip()).strip() if k >= 0 else ""
        lines = ([rest0] if rest0 else []) + lines[1:]
    return [l for l in lines if l.strip() and not l.strip().startswith("--")]


def _is_short(body_text: list[str]) -> bool:
    return len(body_text) <= 1 and (not body_text or (len(body_text[0].strip()) <= 40 and bool(_SHORT_CLOSER.match(body_text[0].strip()))))


def plan_probes(decl: str, statement: str, max_probes: int = 12) -> list[dict]:
    """Probe compiles: each {"kind", "decl": replaced declaration, "targets": [(decl line of the closer, original block line, block
    text, tactic)]}. Batches: top-level blocks with exact?, depth-2 blocks with exact?, the largest top-level blocks with apply?,
    and suffix probes (rest of the top-level proof replaced by exact?) for the last plain steps."""
    bl = body_lines(decl, statement) if decl.find(statement) >= 0 else body_lines(decl, "")
    if bl is None:
        return []
    head, body = bl
    probes = []
    top = [b for b in outer_blocks(body) if not _is_short(_block_body(body, b))]

    def batch(blocks, tac, kind, base_body, off):
        if not blocks:
            return
        new, targets, i = [], [], 0
        starts = {b["start"]: b for b in blocks}
        while i < len(base_body):
            if i in starts:
                b = starts[i]
                hl = b["header"].split("\n")
                new.extend(hl[:-1]); new.append(f"{hl[-1]} {tac}")
                targets.append({"line": len(head) + off + len(new), "orig_line": len(head) + off + b["start"] + 1,
                                "block": "\n".join(base_body[b["start"]:b["end"]])[:400], "tactic": tac})
                i = b["end"]
            else:
                new.append(base_body[i]); i += 1
        return new, targets

    r = batch(top, "exact?", "exact-top", body, 0)
    if r:
        probes.append({"kind": "exact?", "decl": "\n".join(head + r[0]), "targets": r[1]})
    # depth 2: blocks one level inside each top-level block, all in one compile
    inner_new, inner_targets, i = [], [], 0
    tops = {b["start"]: b for b in outer_blocks(body)}
    while i < len(body):
        if i in tops and tops[i]["end"] - i > 2:
            b = tops[i]
            sub = body[i + 1:b["end"]]
            subs = [s for s in outer_blocks(sub) if not _is_short(_block_body(sub, s))]
            inner_new.append(body[i])
            if subs:
                r2 = batch(subs, "exact?", "exact-inner", sub, 0)
                for t in r2[1]:
                    t["line"] += len(inner_new) ; t["orig_line"] += i + 1
                inner_new.extend(r2[0]); inner_targets.extend(r2[1])
            else:
                inner_new.extend(sub)
            i = b["end"]
        else:
            inner_new.append(body[i]); i += 1
    if inner_targets:
        probes.append({"kind": "exact?", "decl": "\n".join(head + inner_new), "targets": inner_targets})
    # apply? on the 3 largest top-level blocks
    big = sorted(top, key=lambda b: -(b["end"] - b["start"]))[:3]
    if big:
        r = batch(sorted(big, key=lambda b: b["start"]), "apply?", "apply-top", body, 0)
        probes.append({"kind": "apply?", "decl": "\n".join(head + r[0]), "targets": r[1]})
    # suffix probes: the rest of the proof from a top-level plain step, replaced by exact?
    if body:
        base = min(len(l) - len(l.lstrip(" ")) for l in body if l.strip())
        steps = [k for k, l in enumerate(body) if l.strip() and len(l) - len(l.lstrip(" ")) == base
                 and not re.match(r"^\s*(--|\||·|case\b|next\b|<;>)", l)]
        blocks_at = {b["start"] for b in outer_blocks(body)}
        plain = [k for k in steps if k not in blocks_at or True]
        cands = []
        for k in reversed(plain[1:]):             # never the whole proof (k = first step): useless on real theorems
            rest = [l for l in body[k:] if l.strip()]
            if len(rest) == 1 and _is_short([rest[0]]):
                continue
            cands.append(k)
        for k in cands[: max(0, max_probes - len(probes))][:5]:
            ind = " " * base
            new = body[:k] + [ind + "exact?"]
            probes.append({"kind": "exact?", "decl": "\n".join(head + new),
                           "targets": [{"line": len(head) + k + 1, "orig_line": len(head) + k + 1,
                                        "block": "\n".join(body[k:])[:400], "tactic": "exact? (rest of proof)"}]})
    closer = plan_closer_probe(decl, statement, head, body)
    if closer:
        probes = probes[: max_probes - 1] + [closer]
    return probes[:max_probes]


_DEAD = re.compile(r"\b(exfalso|contradiction|absurd|False\.elim|nomatch|nofun|by_contra)\b")


def plan_closer_probe(decl: str, statement: str, head: list[str], body: list[str], max_variants: int = 10) -> dict | None:
    """Dead-branch probe (panel, extractedOldExprInVars: the `exfalso; cases …` branch was closed by `apply List.nil_subset`, a lemma
    the proof already used elsewhere; `panic!` reduces to `default`). For every bullet/case block (depth ≤ 2) that argues by
    contradiction, try each bare closer lemma the proof applies elsewhere (`apply L` / `exact L`) and `rfl`/`trivial`. All variants
    go into ONE compile as renamed copies of the declaration; a variant succeeds when no error falls inside its block."""
    m = re.search(r"(theorem|lemma)\s+([^\s(:{\[]+)", decl)
    if not m:
        return None
    closers = list(dict.fromkeys(re.findall(r"(?:apply|exact)\s+([A-Za-z_][\w.']*[\w'])\s*$", "\n".join(body), re.M)))
    closers = [c for c in closers if "." in c or "_" in c][:6] + ["rfl", "trivial"]
    dead = []
    for b in outer_blocks(body):
        blk = body[b["start"]:b["end"]]
        if b["kind"] in ("bullet", "case") and _DEAD.search("\n".join(blk)) and len(blk) >= 2:
            dead.append((b, body))
        if b["end"] - b["start"] > 2:                       # one level down
            sub = body[b["start"] + 1:b["end"]]
            for s_ in outer_blocks(sub):
                sblk = sub[s_["start"]:s_["end"]]
                if s_["kind"] in ("bullet", "case") and _DEAD.search("\n".join(sblk)) and len(sblk) >= 2:
                    dead.append(({**s_, "start": s_["start"] + b["start"] + 1, "end": s_["end"] + b["start"] + 1}, body))
    if not dead or not closers:
        return None
    variants, chunks, line = [], [], 0
    for k, (b, bd) in enumerate([(b, bd) for b, bd in dead for _ in [0]]):
        for c in closers:
            if len(variants) >= max_variants:
                break
            hl = b["header"].split("\n")
            new_body = bd[:b["start"]] + hl[:-1] + [f"{hl[-1]} {'apply ' + c if c not in ('rfl', 'trivial') else c}"] + bd[b["end"]:]
            d = "\n".join(head + new_body)
            d = d[:m.start(2)] + m.group(2) + f"_lra{len(variants)}" + d[m.end(2):]
            text = "set_option maxHeartbeats 400000 in\n" + d + "\n\n"
            blk_line = line + 1 + len(head) + b["start"] + len(hl)        # 1-based line of the closer within the joined code
            variants.append({"closer": c, "line": blk_line, "orig_line": len(head) + b["start"] + 1,
                             "block": "\n".join(bd[b["start"]:b["end"]])[:300]})
            chunks.append(text)
            line += text.count("\n")
    return {"kind": "closer", "decl": "".join(chunks), "variants": variants, "targets": []}


def run_probe(name: str, row: dict, p: dict, deadline: float, timeout: int = 150) -> list[dict]:
    """One probe compile -> [{line, orig_line, block, tactic, suggestion, probe}]."""
    if time.time() > deadline:
        return []
    pre = _prelude(row)
    off = pre.count("\n")
    msgs = _run(name, pre + p["decl"], min(timeout, max(30, int(deadline - time.time()))))
    out = []
    if p["kind"] == "closer":
        err_lines = {m["line"] - off for m in msgs if m["severity"] == "error"}
        if any(m["data"] == "timeout" for m in msgs):
            return []
        for v in p["variants"]:
            if v["line"] not in err_lines and not any(v["line"] - 1 <= l <= v["line"] + 1 for l in err_lines):
                tac = v["closer"] if v["closer"] in ("rfl", "trivial") else f"apply {v['closer']}"
                out.append({"line": v["line"], "orig_line": v["orig_line"], "block": v["block"], "tactic": tac,
                            "suggestion": tac, "probe": "closer"})
        return out
    for t in p["targets"]:
        for s in _try_this_all(msgs, off + t["line"]):
            out.append({**t, "suggestion": s, "probe": p["kind"]})
    return out


# --------------------------------------------------------------------------------------------------------------------------------
# goal trace
# --------------------------------------------------------------------------------------------------------------------------------


def trace_goals(name: str, row: dict, decl: str, depth: int = 2) -> list[dict]:
    """[{line, tactic, hyps, target}] — like goals.goal_map but with the full first goal (no digest), for keyword extraction."""
    inst = instrument(decl, row["statement"], depth)
    if inst is None:
        return []
    code, probes = inst
    pre = _prelude(row)
    off = pre.count("\n")
    msgs = _run(name, pre + code, 300)
    by_line: dict[int, list[str]] = defaultdict(list)
    for m in msgs:
        if m["severity"] in ("information", "info"):
            by_line[m["line"] - off].append(m["data"])
    out = []
    for p in probes:
        st = "\n".join(by_line.get(p["at"], []))
        if not st or st.startswith("no goals"):
            continue
        h, t = _first_goal_target(st)
        out.append({"line": p["line"], "tactic": p["tactic"], "hyps": h, "target": re.sub(r"\s+", " ", t).strip()})
    return out


# --------------------------------------------------------------------------------------------------------------------------------
# main search
# --------------------------------------------------------------------------------------------------------------------------------

_GENERIC = re.compile(r"^(And|Or|Iff|Eq|Ne|Not|HEq|Exists|False|True|Function|Classical|Decidable|Bool|id|absurd|congr\w*|funext|"
                      r"and_\w+|or_\w+|iff_\w+|eq_\w+|ne_\w+|not_\w+|exists_prop|of_eq_true|le_refl|le_rfl|le_of_eq|lt_irrefl|"
                      r"cast_\w+|Subsingleton|propext|trivial|rfl|Nat\.le\.refl|forall_\w+|imp_\w+|ite_\w+|dite_\w+|dif_\w+|if_\w+)\b")


def _decl_name(statement: str) -> str:
    m = re.search(r"(?:theorem|lemma)\s+([^\s(:{\[]+)", statement)
    return m.group(1) if m else ""


def _resolve_used(used: list[str], by_name: dict, by_suffix: dict) -> dict[str, dict]:
    out = {}
    for u in used:
        es = by_name.get(u) or by_suffix.get(u.split(".")[-1], [])
        es = [e for e in es if e["name"] == u or e["name"].endswith("." + u)]
        if es:
            out[u] = es[0]
    return out


def _sig_of_text(lines: list[str], i: int, max_lines: int = 14) -> str:
    buf = []
    for l in lines[i: i + max_lines]:
        k = l.find(":=")
        if k >= 0:
            buf.append(l[:k]); break
        if buf and re.match(r"^\s*(\||where\b)", l):
            break
        buf.append(l)
    return re.sub(r"\s+", " ", " ".join(buf)).strip()


def _ids(text: str, local: set) -> set[str]:
    """Global-looking identifiers (last component) of a signature, minus bound names."""
    return {i.split(".")[-1] for i in global_names(text, local)} - STOP


def search(name: str, decl: str, top: int = 10, probes: bool = True, budget: float = 180.0, log=lambda *a: None, debug: dict | None = None) -> dict:
    t0 = time.time()
    deadline = t0 + budget
    row = ROWS[name]
    statement = row["statement"]
    stats = {"compiles": 0}
    wdir = ROOT / "harness" / "work" / re.sub(r"[^A-Za-z0-9_.-]", "_", name)     # the agent's workspace naming

    # ---- index (CPU) ----------------------------------------------------------------------------------------------------------
    idx = build_index(row)
    by_name: dict[str, list[dict]] = defaultdict(list)
    by_suffix: dict[str, list[dict]] = defaultdict(list)
    for e in idx:
        by_name[e["name"]].append(e)
        by_suffix[e["name"].split(".")[-1]].append(e)
    log(f"index {len(idx)} decls in {time.time() - t0:.1f}s")

    # ---- compiles: goal trace and exact?/apply? probes, at most MAX_PAR at a time ---------------------------------------------
    plan = plan_probes(decl, statement) if probes else []
    hits: list[dict] = []
    with ThreadPoolExecutor(MAX_PAR) as ex:
        fg = ex.submit(trace_goals, name, row, decl, int(os.environ.get("LRA_LS_DEPTH", "4")))
        fps = [ex.submit(run_probe, name, row, p, deadline - 30) for p in plan]
        goals = fg.result()
        for f in fps:
            hits.extend(f.result())
    stats["compiles"] += 1 + len(plan)
    log(f"trace {len(goals)} goals; probes {len(plan)} compiles, {len(hits)} suggestions at {time.time() - t0:.0f}s")

    # ---- context: locals, used names, keyword bag ----------------------------------------------------------------------------
    binders, concl = split_statement(statement)
    local = bound_names(statement) | bound_names(decl) | {x for g in goals for x in bound_names(g["hyps"])}
    proof = decl.split(statement, 1)[-1] if statement in decl else decl
    used = global_names(proof, local)
    used_res = _resolve_used(used, by_name, by_suffix)
    used_full = {e["name"] for e in used_res.values()}
    used_short = {u.split(".")[-1] for u in used}
    used_dirs = {str(Path(e["file"]).parent) for e in used_res.values()}
    ref_text = (wdir / "original.lean").read_text() if (wdir / "original.lean").exists() else row.get("src", "")
    ref_used = {u.split(".")[-1] for u in global_names(ref_text.split(statement, 1)[-1], local | bound_names(ref_text))}

    goal_kw: Counter = Counter()
    for g in goals:
        goal_kw.update(keywords(g["target"], local))
    stmt_kw = keywords(statement, local)
    used_kw: Counter = Counter()
    for u in used:
        for s in _segments(u):
            if s not in STOP and len(s) > 1:
                used_kw[s] += 1
    K: Counter = Counter()
    for src, w in ((goal_kw, 1.0), (stmt_kw, 1.0), (used_kw, 0.8)):
        for k, n in src.items():
            K[k] += w * (0.5 + min(n, 3) / 3)
    for k in list(K):
        for syn in SYNONYMS.get(k, []):
            K[syn] = max(K[syn], K[k] * 0.6)
    for k in list(K):
        if k in WEAK:
            K[k] *= 0.5
    own_name = _decl_name(statement)
    for s in _segments(own_name):            # the theorem's own name words name the result, not the tools
        if s in K:
            K[s] *= 0.6
    pre_text = ""
    if row["source"] != "putnambench":
        try:
            pre_text = file_prefix(row, primary_version(row))
        except Exception:  # noqa: BLE001
            pre_text = (wdir / "context.lean").read_text() if (wdir / "context.lean").exists() else ""
    stmt_tc = _typeclasses(binders)
    for v in re.findall(r"^variable\b(.*(?:\n[ \t]+.*)*)", pre_text, re.M):
        stmt_tc |= _typeclasses(v)
    stmt_hyp = _hyp_kinds(binders) | {_lower_first(x) for g in goals[:1] for x in re.findall(r":\s*([A-Z]\w+)", g["hyps"])}

    # ---- (b) name search -----------------------------------------------------------------------------------------------------
    N = len(idx)
    df: Counter = Counter()
    segs_of: list[set] = []
    for e in idx:
        ss = set(_segments(e["name"])) - STOP
        segs_of.append(ss)
        df.update(ss)

    def idf(s):
        return math.log((N + 1) / (1 + df.get(s, 0)))

    scored = []
    Kk = set(K)
    rare_df = max(50, int(0.012 * N))
    # stems of used lemmas with a relation word: `card_le_card` -> its extensions `card_le_card_of_surjOn`, ...
    used_stems = {u.split(".")[-1] for u in used_full | set(used) if len(u.split(".")[-1].split("_")) >= 2}
    # hand-built witnesses: `let φ : ContDiffBump x := ⟨…⟩` -> properties used of φ -> `exists_<props>` lemmas
    wit = {}
    for m in re.finditer(r"(?:let|set|have)\s+([^\W\d][\w'₀-₉]*)\s*(?::\s*([^\n]+?))?\s*:=\s*[⟨{]", proof):
        v, ty = m.group(1), (m.group(2) or "")
        props: Counter = Counter()
        for s_ in _segments(ty.split()[0]) if ty.strip() else []:
            props[s_] += 1
        for t in re.findall(rf"(?<![\w.]){re.escape(v)}\.([A-Za-z_][\w']*)", proof):
            for s_ in _segments(t):
                props[s_] += 1
        for line in proof.split("\n"):
            if re.search(rf"(?<![\w.]){re.escape(v)}(?![\w'])", line):
                for g_ in global_names(line, local):
                    if g_.split(".")[0][:1].isupper() and "." in g_ and _segments(g_.split(".")[0])[:1] == _segments(ty.split()[0])[:1] if ty.strip() else False:
                        for s_ in _segments(g_.split(".")[-1]):
                            props[s_] += 1
        props = Counter({k: n for k, n in props.items() if k not in STOP and len(k) > 1})
        for k in list(props):
            for syn in SYNONYMS.get(k, []):
                props[syn] += 0
                props[syn] = max(props[syn], 1)
        if props:
            wit[v] = (ty.strip(), props)
    for e, ss in zip(idx, segs_of):
        if e["private"] or "deprecated" in e["attrs"]:
            continue
        last = e["name"].split(".")[-1]
        m = ss & Kk
        reason = ""
        if last.startswith("exists_") and wit:
            best_w = None
            for v, (ty, props) in wit.items():
                mw = ss & set(props)
                if len(mw - BASIC) >= 2:
                    strong = sum(idf(x) for x in mw - BASIC)
                    ratio = sum(idf(x) for x in mw) / (sum(idf(x) for x in ss - {"exists"}) or 1)
                    scw = strong * ratio ** 1.5 * 5
                    if best_w is None or scw > best_w[0]:
                        best_w = (scw, v, ty, mw)
            if best_w:
                scored.append((best_w[0], e, f"existence lemma for the hand-built `{best_w[1]}{' : ' + best_w[2][:40] if best_w[2] else ''}` "
                                              f"(its {', '.join(sorted(best_w[3]))})"))
                continue
        if len(m) < 2:
            continue
        if not any(df.get(x, 0) <= rare_df and K[x] >= 0.75 and x not in BASIC for x in m):   # one distinctive word, not only le/exists/list
            continue
        matched = sum(idf(x) * min(K[x], 2.0) for x in m)
        total = sum(idf(x) for x in ss) or 1.0
        cov = sum(idf(x) for x in m) / total
        sc = matched * (cov ** 0.8)
        if str(Path(e["file"]).parent) in used_dirs:
            sc *= 1.25
        stem = next((u for u in used_stems if last.startswith(u + "_") and last != u), None)
        if stem:
            sc *= 1.6; reason = f"extends `{stem}` (used in the candidate)"
        if e["name"] in used_full:
            sc *= 0.5
        scored.append((sc, e, reason))
    scored.sort(key=lambda x: -x[0])
    goal_concl_kw = set(goal_kw) | set(keywords(concl, local))
    name_hits = []
    seen_var = set()
    for sc, e, reason in scored[:300]:
        var = re.sub(r"(_left|_right|'+|₀|_of_\w+)$", "", e["name"])          # one per left/right/primed variant family
        if (var, sc) in seen_var:
            continue
        seen_var.add((var, sc))
        sig = source_signature(e)
        tcs = _typeclasses(sig)
        tc_ov = (len(tcs & stmt_tc) / len(tcs)) if tcs else 0.5
        lb, lc = split_statement(sig)
        ck_ = set(keywords(lc or sig, bound_names(sig))) - WEAK
        c_ov = len(ck_ & goal_concl_kw) / max(1, len(ck_))
        hk = _hyp_kinds(lb)
        h_ov = len(hk & stmt_hyp) / max(1, len(hk)) if hk else 0.0
        name_hits.append((sc * (0.6 + 0.4 * tc_ov + 0.4 * c_ov + 0.3 * h_ov), e, sorted(set(_segments(e["name"])) & Kk), tcs & stmt_tc, reason))
    name_hits.sort(key=lambda x: -x[0])
    name_hits = [x for x in name_hits if x[0] >= 12.0]          # absolute floor: two weak words never make a suggestion
    if debug is not None:
        debug.update(K=dict(K), idf={k: idf(k) for k in K}, scored=[(round(x[0], 2), x[1]["name"]) for x in scored[:400]],
                     name_hits=[(round(x[0], 2), x[1]["name"], x[2], x[4]) for x in name_hits[:80]], goals=goals, hits=hits, used=used, wit=wit)
    name_hits = name_hits[:40]

    def best_goal_line(sig: str):
        ck_ = set(keywords(split_statement(sig)[1] or sig)) - WEAK
        best, bl = 0, None
        for g in goals:
            ov = len(ck_ & set(keywords(g["target"], local)))
            if ov > best:
                best, bl = ov, g
        return (bl["line"], bl["target"][:160]) if bl else (None, None)

    # ---- (c) siblings --------------------------------------------------------------------------------------------------------
    sib_hits = []
    if pre_text:
        sib: list[dict] = []
        _parse_lines(enumerate(pre_text.split("\n"), 1), "<prefix>", sib)
        plines = pre_text.split("\n")
        nrm = lambda xs: {x.rstrip("'") for x in xs}          # foo' is a variant of foo (updatedStates' / updatedStates)
        stmt_ids = nrm(_ids(statement.split(own_name, 1)[-1], local))
        concl_ids = nrm(_ids(concl, local))
        rows_ = []
        sdf: Counter = Counter()
        for e in sib:
            sig = _sig_of_text(plines, e["line"] - 1)
            sl = bound_names(sig)
            body_sig = sig.split(e["short"], 1)[-1]
            all_ids = nrm(_ids(body_sig, sl))
            sb, sc_ = split_statement(sig)
            parts = re.split(r"\s→\s", sc_) if sc_ else [""]
            final = parts[-1]
            hyp_ids = nrm(_ids(sb.split(e["short"], 1)[-1] + " " + " ".join(parts[:-1]), sl)) & stmt_ids
            fin_ids = nrm(_ids(final, sl)) & stmt_ids
            ids = all_ids & stmt_ids
            cids = nrm(_ids(sc_, sl)) & concl_ids
            rows_.append((e, sig, ids, cids, all_ids, hyp_ids, fin_ids))
            sdf.update(ids)
        nS = max(1, len(sib))
        for k, (e, sig, ids, cids, all_ids, hyp_ids, fin_ids) in enumerate(rows_):
            if not ids or e["short"] == own_name.split(".")[-1]:
                continue
            sidf = lambda i: math.log((nS + 1) / (1 + sdf[i])) + 0.2
            w = sum(sidf(i) for i in ids) + 1.5 * sum(sidf(i) for i in cids)
            w *= (len(ids) / max(1, len(all_ids))) ** 0.5          # precision: few symbols foreign to the statement
            if hyp_ids and fin_ids and (fin_ids - hyp_ids):           # bridge: statement symbol A in, statement symbol B out
                w *= 1.4
            unused_ref = e["short"].split(".")[-1] not in ref_used
            unused_cand = e["short"].split(".")[-1] not in used_short
            if unused_ref:
                w *= 1.3
            sib_hits.append((w, e, sig, sorted(ids), sorted(cids), unused_ref, unused_cand))
        sib_hits.sort(key=lambda x: -x[0])
        sib_hits = sib_hits[:25]

    # ---- (d) attribute index -------------------------------------------------------------------------------------------------
    attr_hits = []
    proj_files: set[str] = set()
    own_file = ""
    if row["source"] != "putnambench":
        root = env_root(row)
        start = root / row["file_path"]
        own_file = str(start)
        todo, seen = [start], set()
        while todo and len(seen) < 800:
            f = todo.pop()
            if f in seen or not f.exists():
                continue
            seen.add(f)
            for imp in re.findall(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)", f.read_text(errors="replace"), re.M):
                p = root / (imp.replace(".", "/") + ".lean")
                if p.exists():
                    todo.append(p)
        proj_files = {str(f) for f in seen}
    goal_heads: Counter = Counter()
    for g in goals:
        for i in _ids(g["target"], local):
            goal_heads[i] += 1
    for i in _ids(concl, local):
        goal_heads[i] += 1
    for e in idx:
        if e["file"] not in proj_files or not re.search(r"\b(simp|grind|to_fun)\b", e["attrs"]) or e["private"]:
            continue
        if e["short"] == own_name.split(".")[-1]:
            continue
        sig = source_signature(e)
        ov = _ids(sig.split(e["short"], 1)[-1], bound_names(sig)) & set(goal_heads)
        names = [e["name"]]
        if "to_fun" in e["attrs"]:
            ns, last = e["name"].rsplit(".", 1) if "." in e["name"] else ("", e["name"])
            names = [(ns + "." if ns else "") + "fun_" + last, e["name"]]
        for nm in names:
            w = sum(1 + math.log(1 + goal_heads[i]) for i in ov)
            note = ""
            is_fun = nm.split(".")[-1].startswith("fun_")
            if is_fun and e["short"].split(".")[-1] in used_short:
                w += 50
                note = f"λ-form of `{e['name']}` (used in the candidate): applies to `fun x => …` directly, no `change`/`show`"
            elif is_fun:
                note = f"generated by @[to_fun] from `{e['name']}`"
            if "grind" in e["attrs"]:
                lc = split_statement(sig)[1] or sig
                ga = re.search(r"grind[^\],]*", e["attrs"]).group(0)
                if "→" in ga or "∃" in lc:
                    note = (note + "; " if note else "") + f"pass as grind [→ {nm}]"
                else:
                    note = (note + "; " if note else "") + f"@[{ga}]"
            elif "simp" in e["attrs"] and not note:
                note = "@[simp]"
            if len(ov) < 2 and w < 50:                       # one shared symbol (`length`, `Value`) is noise
                continue
            if e["file"] == own_file:
                w *= 1.3
            attr_hits.append((w, nm, e, sorted(ov), note))
    attr_hits.sort(key=lambda x: -x[0])
    attr_hits = attr_hits[:25]

    # ---- (e) induction hints -------------------------------------------------------------------------------------------------
    ind_hits = []
    hyp_text = binders + "\n" + "\n".join(g["hyps"] for g in goals[:1]) + "\n" + concl.split(",")[0]
    pos_hyp = re.search(r"(\b0\s*<\s*[\w']+|[\w']+\s*>\s*0\b|[\w']+\s*≠\s*0\b|\b1\s*≤\s*[\w']+|[\w']+\s*≥\s*1\b)", hyp_text)
    le_hyp = re.search(r"([\w']+\s*≤\s*[\w']+|[\w']+\s*≥\s*[\w']+)", hyp_text)
    nat_vars = set()
    for grp, ty in re.findall(r"[({∀]\s*([^(){}:,]+?)\s*:\s*(ℕ|Nat)\b", statement + "\n" + "\n".join(g["hyps"] for g in goals[:1])):
        nat_vars.update(grp.split())
    for grp in re.findall(r"^\s*([^\n:]+?)\s*:\s*ℕ\s*$", "\n".join(g["hyps"] for g in goals), re.M):
        nat_vars.update(grp.split())
    ind_m = [m for m in re.finditer(r"^\s*induction\s+([\w']+)", decl, re.M) if m.group(1) in nat_vars]
    uses_ind = bool(ind_m) or re.search(r"\bNat\.rec\b|\bstrongRecOn\b|\bstrong_induction|\bNat\.le_induction", decl)
    if pos_hyp or uses_ind:
        ind_line = decl[: ind_m[0].start()].count("\n") + 1 + (1 if decl[ind_m[0].start()] == "\n" else 0) if ind_m else None
        why0 = f"hypothesis `{pos_hyp.group(1)}`" if pos_hyp else "the proof inducts on ℕ"
        order = []
        if pos_hyp:
            order += [("Nat.le_induction", f"{why0}: `0 < n` is `1 ≤ n`; `refine Nat.le_induction ?_ (fun n hn ih => ?_)` starts at 1 and drops the impossible zero case"),
                      ("Nat.pos_induction", why0), ("Nat.le_induction_on", why0)]
        if uses_ind:
            order += [("Nat.le_induction", "induction from a lower bound (matches `m ≤ n` / `0 < n` hypotheses)"),
                      ("Nat.strong_induction_on", "the proof inducts on ℕ: strong induction gives every smaller case at once"),
                      ("Nat.strongRecOn", "term-mode strong induction"), ("Nat.twoStepInduction", "recurrences that look two steps back")]
        if le_hyp and not pos_hyp:
            order += [("Nat.decreasingInduction", f"hypothesis `{le_hyp.group(1)}`")]
        seen_i = set()
        for nm, w in order:
            if nm not in seen_i:
                seen_i.add(nm); ind_hits.append((nm, w, ind_line))

    # ---- (a) exact?/apply? hits: head lemma of each suggestion ---------------------------------------------------------------
    exact_rows = []
    for h in hits:
        names_ = [n for n in global_names(h["suggestion"], local) if not _GENERIC.match(n)]
        if h["probe"] == "apply?":
            if not names_:
                continue
            ss = set(_segments(names_[0])) - STOP
            sc = sum(idf(s) * min(K[s], 2.0) for s in (ss & Kk) - BASIC)
            if sc <= 0:                                          # apply? lists every lemma that unifies; keep the on-topic ones
                continue
            exact_rows.append((0.5 + sc, h, names_))
        else:
            exact_rows.append(((110.0 if h["probe"] == "closer" else 100.0) - (10 if not names_ else 0), h, names_))
    exact_rows.sort(key=lambda x: -x[0])
    per_probe: Counter = Counter()
    kept = []
    for sc, h, names_ in exact_rows:
        key = (h["probe"], h["orig_line"])
        if h["probe"] == "apply?" and per_probe[key] >= 3:
            continue
        per_probe[key] += 1
        kept.append((sc, h, names_))

    # ---- verify names with #check --------------------------------------------------------------------------------------------
    to_check = ([n for _, _, ns in kept for n in ns[:3]] + [x[1]["name"] for x in name_hits[:30]]
                + [e["name"] for _, e, *_ in sib_hits[:15]] + [e["short"] for _, e, *_ in sib_hits[:15]]
                + [nm for _, nm, *_ in attr_hits[:15]] + [nm for nm, *_ in ind_hits])
    checked = check_names(name, row, to_check)
    stats["compiles"] += 1
    log(f"checked {len(checked)}/{len(set(to_check))} names at {time.time() - t0:.0f}s")
    ck = checked.get

    comps: dict[str, list[dict]] = {"exact": [], "name": [], "sibling": [], "attr": [], "induction": []}
    for sc, h, names_ in kept:
        good = [n for n in names_ if ck(n)]
        closes = h["probe"] in ("exact?", "closer")
        what = "closes the goal" if closes else "applies (goals remain)"
        if h["probe"] == "closer":
            why = (f"dead-branch probe: `{h['suggestion']}` closes the contradiction block at line {h['orig_line']} "
                   f"({len(h['block'].splitlines())} lines) — a lemma the proof already uses elsewhere")
        else:
            why = f"`{h['probe']}` at line {h['orig_line']} {what}: `{h['suggestion'][:200]}`" + (" — replaces the block" if closes else "")
        base = {"source": f"exact ({h['probe']})", "line": h["orig_line"], "tactic": h["suggestion"][:300], "why": why}
        if not good:
            if closes and "⋯" not in h["suggestion"] and len(h["suggestion"]) > 6:
                comps["exact"].append({"name": "", "signature": "", **base})
            continue
        for n in good[:1 if not closes else 2]:
            comps["exact"].append({"name": ck(n)["full"], "signature": ck(n)["short_sig"][:400], **base})
    for sc, e, msegs, tcs, reason in name_hits:
        c = ck(e["name"])
        if not c:
            continue
        ln, gt = best_goal_line(c["sig"])
        why = reason if reason.startswith("existence") else f"name matches {', '.join(msegs)}" + (f"; {reason}" if reason else "")
        if tcs:
            why += f"; typeclasses shared with the statement: {', '.join(sorted(tcs))}"
        if gt:
            why += f"; goal at line {ln}: ⊢ {gt[:120]}"
        if e["name"] in used_full:
            why += " (already used in the candidate)"
        comps["name"].append({"name": c["full"], "signature": c["short_sig"][:400], "source": "name", "line": ln, "why": why, "score": round(sc, 2)})
    for w, e, sig, ids, cids, unused_ref, unused_cand in sib_hits:
        c = ck(e["name"]) or ck(e["short"])
        if not c:
            continue
        flag = []
        if unused_ref:
            flag.append("NOT used in the reference proof")
        if not unused_cand:
            flag.append("already used in the candidate")
        comps["sibling"].append({"name": c["full"], "signature": c["short_sig"][:400], "source": "sibling", "line": None,
                                 "why": f"same file, line {e['line']}; shares {', '.join(ids[:8])} with the statement"
                                        + (f" ({', '.join(cids[:5])} in the conclusion)" if cids else "") + ("; " + "; ".join(flag) if flag else ""),
                                 "score": round(w, 2)})
    for w, nm, e, ov, note in attr_hits:
        c = ck(nm)
        if not c:
            continue
        ln, gt = best_goal_line(c["sig"])
        comps["attr"].append({"name": c["full"], "signature": c["short_sig"][:400], "source": "attr", "line": ln,
                              "why": f"{e['attrs'][:60]} in {Path(e['file']).name}; mentions {', '.join(ov[:6]) or '—'}" + (f"; {note}" if note else ""),
                              "score": round(w, 2)})
    for nm, why, ln in ind_hits:
        c = ck(nm)
        if c:
            comps["induction"].append({"name": c["full"], "signature": c["short_sig"][:400], "source": "induction", "line": ln, "why": why})
    for k in comps:
        seen_n, keep = set(), []
        for d in comps[k]:
            key = d["name"] or d.get("tactic")
            if key not in seen_n:
                seen_n.add(key); keep.append(d)
        comps[k] = keep

    # ---- merge: per-component priority decaying with rank (round-robin-like), confident items first --------------------------
    base_p = {"exact": 1.0, "induction": 0.97 if pos_hyp else 0.55, "sibling": 0.94, "name": 0.93, "attr": 0.8}
    pri = []
    for k, items in comps.items():
        for r, d in enumerate(items):
            p = base_p[k] * (0.85 ** r)
            if k == "attr" and d.get("score", 0) >= 50:
                p = 0.99
            if k == "exact" and not d["name"]:
                p *= 0.9
            if k == "exact" and "apply?" in d["source"]:      # unifies, but leaves goals: weaker than a ranked name hit
                p *= 0.75
            pri.append((p, k, r, d))
    pri.sort(key=lambda x: -x[0])
    merged, where = [], {}
    for p, k, r, d in pri:
        key = d["name"] or d.get("tactic")
        if key in where:
            m = merged[where[key]]
            if k not in m["source"]:
                m["source"] += f"+{k}"
            continue
        where[key] = len(merged)
        merged.append(dict(d))
    return {"problem": name, "runtime_s": round(time.time() - t0, 1), "compiles": stats["compiles"], "goals": len(goals),
            "suggestions": merged[:top], "components": {k: v[:top] for k, v in comps.items()},
            "keywords": [k for k, _ in sorted(K.items(), key=lambda x: -x[1] * idf(x[0]))[:25]]}


def render(res: dict) -> str:
    lines = [f"lemma_search {res['problem']}  ({res['runtime_s']} s, {res['compiles']} compiles, {res['goals']} goals traced)"]
    for i, s in enumerate(res["suggestions"], 1):
        where = f" [line {s['line']}]" if s.get("line") else ""
        lines.append(f"{i:2}. {s['name'] or s.get('tactic', '')}{where}  <{s['source']}>")
        if s.get("signature"):
            lines.append(f"      : {s['signature'][:220]}")
        lines.append(f"      why: {s['why'][:260]}")
        if s.get("tactic") and s["name"]:
            lines.append(f"      try: {s['tactic'][:200]}")
    return "\n".join(lines)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("problem"); ap.add_argument("file")
    ap.add_argument("--top", type=int, default=10); ap.add_argument("--json", action="store_true")
    ap.add_argument("--no-probes", action="store_true", help="skip the exact?/apply? compiles")
    ap.add_argument("--budget", type=float, default=180.0); ap.add_argument("-v", action="store_true")
    a = ap.parse_args()
    name = a.problem
    if name not in ROWS:
        alt = [n for n in ROWS if re.sub(r"[^A-Za-z0-9_.-]", "_", n) == name]
        if not alt:
            sys.exit(f"unknown problem {name}")
        name = alt[0]
    res = search(name, Path(a.file).read_text(), a.top, not a.no_probes, a.budget, log=(lambda *x: print(*x, file=sys.stderr)) if a.v else (lambda *x: None))
    print(json.dumps(res, ensure_ascii=False, indent=1) if a.json else render(res))


if __name__ == "__main__":
    main()
