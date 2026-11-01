#!/usr/bin/env python3
"""Transfer lane: a SIMPLE portfolio transfer next to grinding (2026-10-12 ~23:10 UTC: grinding gives ~+0.8 per $5 Fable session on
an internal evaluation set; add a simple complementary version of the NeuroGolf portfolio-transfer idea. The reference system (docs/neurogolf_lessons.md
"Portfolio-Transfer ... fit and expected value") is not rebuilt: its essential cores only; docs/cc_driver_v2.md §12). CPU only, no model call.
  (1) mechanism-first transfer  every winning mechanism found on one row is challenged on every row:
        rule      a one- or two-line rewrite mined from state.json ledger.wins (this work root and every --mine-root): the identifiers of the
                  old side become consistent wildcards ($A, $B, ...; tactic names, keywords, notation and numerals stay literal); a name only the
                  new side has stays literal when >= 2 rows' files have it or it reads as a library name no single row owns, else the rule is
                  dropped (it could not be bound); `span` = the changed token span of a one-line rule, applied inside any line; `delete` = a
                  deleted single tactic line
        closer    the terminal closer lines of every row's current best (grind / simp_all / omega / all_goals ... / `<;>`), abstracted the same
                  way, tried in place of each terminal tactic line of the target (the leaf sites lean_mine never probes), wildcards bound from
                  that line; a closer without wildcards that lean_mine does not try is also tried at its goal blocks and as the whole proof
        operator  hb_polish certificates and the lexer normalizer (their own functions: harness/hb_polish.py, harness/normalize.py)
  (2) fair all-row coverage     rows least-scanned first (slices received), --jobs rows at a time, a bounded time slice per row; each (mechanism,
                                best sha) pair is tried MAX_CANDS candidates per visit, later visits going on from where it stopped, until
                                every candidate was tried: <root>/_transfer/dispositions.jsonl (counts only). A row with a session in progress
                                (an open runs[] entry) or an unused review is left alone until it ends
  (3) strict promotion          candidates compile through leantools.lean_check on a scratch state (no lock, nothing recorded); only a strictly
                                better score with Z unchanged (no listed toolchain lost) is banked: that checked result itself, written under
                                the state lock (no compile while it is held) with the ledger win and the verified record, and only while the
                                row's best is still the one the candidate was built from and no session is in progress
  (4) feedback                  after every sweep <root>/_transfer/mechanisms.json and a TRANSFER HITS section in <root>/_run_techniques.json
                                (inrun.render): the mechanisms with >= 1 hit as abstract patterns that pass inrun's leak lint (the line's own rows)
Not in scope: grammar repair, review gates, evidence boards, waves, LLM proposers. No proof text is stored outside the workspaces (mechanisms are
abstract lines of at most two lines); stdout is counts only, rows as row#k (k = index among the work root's sorted workspace directories).
Review 2026-10-12: the bank no longer recompiles under the lock (a pin lost in that second compile could bank, and a long hold made the CC
driver's 120 s ledger write go unlocked); live rows and unused reviews are skipped; infrastructure failures (timeout, killed compile) record
nothing; hunks glued by the hunk-free diff are split again; closers go to leaf sites; a --mine-root never brings in a internal set or this line's
own problems; the feedback lint uses the line's own rows.
    python3 harness/transfer.py --work-root R [--mine-root R2 ...] [--jobs 4] [--sweeps 1] [--max-hours 2] [--rows-file F] [--dry-run]
    python3 harness/transfer.py --work-root R --follow [--poll-min 10] [--max-hours 12]     next to a live ladder (between a row's sessions)
    python3 harness/transfer.py --work-root R --canary SPEC.json                            SPEC {"source", "target"[, "target_best"]}: warm-up
"""
from __future__ import annotations

import argparse, calendar, collections, concurrent.futures as cf, contextlib, fcntl, hashlib, itertools, json, os, re, shutil, signal, sys, tempfile
import threading, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness import inrun  # noqa: E402
from harness import cc_levers as LV  # noqa: E402

XDIR = "_transfer"
MAX_CANDS = 4          # candidates per visit of a (mechanism, best) pair; the next visit goes on from there
MAX_PAIR = 48          # candidates of one (mechanism, best) pair at most: the all-sites form (2-3 sites), then single sites
MAX_CLOSER_WILD = 2    # a closer with more wildcards than this is too specific to bind from another row's block
CLOSER_NAMES = 3       # names of the target line / block a closer's wildcards are bound from
LOCK_WAIT = 120.0      # the bank's state-lock wait (bounded: 2026-10-11); the bank itself holds it for one read-modify-write
LIVE_H = 3.0           # an open runs[] entry younger than this is a session in progress (older: a driver that died)
INFRA_STRIKES = 2      # a pair whose compiles failed for infrastructure reasons this often is recorded anyway (a real timeout)
GRACE_S = 90.0         # after SIGTERM: running compiles get this long, then the lane's own compile processes are killed
DIFF_CAP = 700         # ledger wins keep diff[:700]: a diff this long lost its tail, so its last group is dropped
BINDERS = frozenset(("have", "haveI", "let", "letI", "set", "obtain", "intro"))   # a name after these is used later in the proof
KINDS = ("operator", "rule", "delete", "span", "closer")
OPS = ("hb_polish", "normalize")
OP_TEXT = {"hb_polish": "hb_polish certificates: bare simp / simp_all / simpa / dsimp / grind replaced by the `only` list Lean prints for its `?` form",
           "normalize": "lexer normalizer: `fun x =>` as `λx =>`, a trailing `(fun ...)` argument bare, `f (g x)` as `f $ g x` (normalize_check.py)"}
ANCHOR_OPS = frozenset((":=", "=>", "<;>", "←", "·", "⟨", "|", "<|", "$", "•", "λ", "?_", "▸", "∘", "↦"))
EXTRA_KW = {"by", "at", "with", "using", "only", "fun", "have", "show", "from", "this", "then", "else", "if", "match", "let", "in", "do", "haveI",
            "letI", "Type", "Prop", "Sort", "True", "False", "true", "false", "generalizing", "where", "calc", "conv", "arg", "enter", "lhs", "rhs",
            "rename_i", "next", "case", "fun_induction", "induction", "classical", "exacts", "nofun", "nomatch", "termination_by", "decreasing_by"}
_LEX = re.compile(r"(?P<id>[^\W\d][\w'!?₀-₉]*(?:\.[\w'₀-₉][\w'!?₀-₉]*)*)|(?P<num>\d+(?:\.\d+)?)|"
                  r"(?P<op>⁻¹|<;>|:=|=>|<\||\|>|->|<-|\.\.|::|\?_|\S)")
_PREFIX = re.compile(r"^(?:·\s*|(?:case|next)\b[^=\n]*=>\s*|by\s+)")
_KW: list = []


def keywords() -> frozenset:
    """Tokens that are never wildcards: tactic names (discover, cc_levers, inrun, mine, normalize lists) and Lean keywords."""
    if not _KW:
        from harness.discover import TACTICS
        from harness.normalize import KEYWORDS
        from harness.mine import _KEYWORDS
        _KW.append(frozenset(TACTICS | inrun.KEEP_WORDS | set(LV._LEAN_WORDS) | KEYWORDS | _KEYWORDS | set(inrun.CLOSERS) | EXTRA_KW))
    return _KW[0]


def _lib_name(t: str) -> bool:
    from harness.discover import LIB_NAME
    return bool(LIB_NAME.match(t))


def _now() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def _atomic(p: Path, obj) -> None:
    tmp = p.with_name(f".{p.name}.tmp-{os.getpid()}-{threading.get_ident()}")
    tmp.write_text(json.dumps(obj, ensure_ascii=False, indent=1)); os.replace(tmp, p)


def _read(p: Path):
    try:
        return json.loads(p.read_text())
    except (OSError, ValueError):
        return None


# ---- lexing and abstraction ---------------------------------------------------------------------------------------------------------------
def lex(line: str) -> list[tuple]:
    """(kind, text, start, end) tokens of one line, its `--` tail dropped; kind id / num / op (λ is an op, also glued as in `λx`)."""
    s = line.split("--", 1)[0]; out = []; i = 0
    while i < len(s):
        if s[i].isspace():
            i += 1; continue
        m = _LEX.match(s, i); t = m.group()
        if m.lastgroup == "id" and t[0] == "λ":
            out.append(("op", "λ", i, i + 1)); i += 1; continue
        out.append((m.lastgroup, t, i, m.end())); i = m.end()
    return out


def shared_name(t: str, owner: dict) -> bool:
    """A lemma-style name (with `_` or `.`, or capitalized and >= 4 chars; never a short local like `h`, `s'`, `M`, `key`) that may stay literal
    in a mechanism: in >= 2 rows' files, or a library-style name (`Nat.succ_le_of_lt`) none of whose namespace / last component one row owns.
    A dotted name with a lowercase head (`i.isLt`, `h.symm`) is a projection of a local, never shared."""
    if not ("_" in t.strip("_") or "." in t or (t[:1].isupper() and len(t) >= 4)) or ("." in t and not t[:1].isupper()):
        return False
    n, parts = len(owner.get(t, ())), t.split(".")
    return n >= 2 or (_lib_name(t) and n != 1 and all(len(owner.get(p, ())) != 1 for p in (parts[0], parts[-1])))


def _balance(lines: list) -> tuple:
    """Open minus close brackets per kind over lexed lines: a mechanism must keep the balance of what it replaces (`exact (` -> `exact`, cut
    from a rule whose `)` sat on the next line, can never compile anywhere)."""
    return tuple(sum((t[1] == o) - (t[1] == c) for toks in lines for t in toks if t[0] == "op") for o, c in zip("([{⟨", ")]}⟩"))


def _anchor(p: tuple) -> bool:
    """A literal token that makes a pattern specific: a keyword / tactic / shared name (not `_`), or a structural symbol."""
    return (p[0] == "id" and len(p[1]) >= 2) or (p[0] == "op" and p[1] in ANCHOR_OPS)


def _template(line: str, toks: list, names: dict) -> list:
    """The line's text from its first to its last token as segments: literal text, or a wildcard index where a bound identifier stood."""
    if not toks:
        return []
    seg, pos = [], toks[0][2]
    for k, t, a, b in toks:
        if k == "id" and t in names:
            if a > pos:
                seg.append(line[pos:a])
            seg.append(names[t]); pos = b
    if toks[-1][3] > pos:
        seg.append(line[pos:toks[-1][3]])
    return seg


def fill(tpl: list, bind: dict) -> str:
    return "".join(x if isinstance(x, str) else bind[x] for x in tpl)


def show(tpl: list) -> str:
    """A template for people and prompts: wildcard k as $A, $B, ..."""
    return "".join(x if isinstance(x, str) else "$" + chr(65 + x % 26) for x in tpl)


def _sig(pat: list) -> str:
    return " ".join(f"${p[1]}" if p[0] == "w" else p[1] for p in pat)


def _new_mech(kind: str, key: str, **kw) -> dict:
    return dict({"id": hashlib.sha256(f"{kind}\x1f{key}".encode()).hexdigest()[:12], "kind": kind, "src": set(), "wins": 0}, **kw)


def abstract(kind: str, old: list[str], new: list[str], owner: dict) -> dict | None:
    """A rule / span / delete mechanism from old -> new lines, or None: identity after abstraction, a new-side name that is neither bound by the
    old side nor shared, a blank line, no literal anchor (a keyword, tactic, shared name or structural symbol) on the old side, or a
    substitution of one of the row's own terms by a lemma (the new side brings a name in and drops an old-side name: `exact $A` -> `apply
    List.Subset.refl` holds only where $A was that lemma). `bind`: the wildcards right after a binder (`have $A` -> `haveI`) that the new side
    drops; a site whose name is used elsewhere in the proof is not a site."""
    kw = keywords(); lo = [lex(l) for l in old]; ln = [lex(l) for l in new]
    if not lo or any(not t for t in lo) or (kind != "span" and any(not t for t in ln)):
        return None
    names: dict = {}
    for toks in lo:
        for k, t, *_ in toks:
            if k == "id" and t not in kw:
                names.setdefault(t, len(names))
    brought = False
    for toks in ln:
        for k, t, *_ in toks:
            if k == "id" and t not in kw and t not in names:
                if not shared_name(t, owner):
                    return None
                brought = True
    kept = {names[t] for toks in ln for k, t, *_ in toks if k == "id" and t in names}
    if brought and set(names.values()) - kept:
        return None
    bind = sorted({names[toks[j + 1][1]] for toks in lo for j in range(len(toks) - 1)
                   if toks[j][1] in BINDERS and toks[j + 1][1] in names and names[toks[j + 1][1]] not in kept})
    ab = lambda toks: [("w", names[t]) if k == "id" and t in names else (k, t) for k, t, *_ in toks]
    pat, newp = [ab(t) for t in lo], [ab(t) for t in ln]
    base = _indent(old[0])
    rel = [0] if kind == "span" else [_indent(l) - base for l in old]
    nrel = [0] * len(new) if kind == "span" else [_indent(l) - base for l in new]
    ko = "\n".join(f"{r}:{_sig(p)}" for r, p in zip(rel, pat)); kn = "\n".join(f"{r}:{_sig(p)}" for r, p in zip(nrel, newp))
    if ko == kn or not any(_anchor(p) for P in pat for p in P) or _balance(lo) != _balance(ln):
        return None
    return _new_mech(kind, f"{ko}\x1e{kn}", pat=pat, rel=rel, nrel=nrel, nw=len(names), bind=bind,
                     old=[_template(l, t, names) for l, t in zip(old, lo)], new=[_template(l, t, names) for l, t in zip(new, ln)])


def span_of(o: str, n: str, owner: dict) -> dict | None:
    """The changed token span of a one-line rule (common prefix and suffix trimmed, widened to >= 2 old tokens), as an in-line mechanism; None
    when the span is the whole line (the line rule covers it)."""
    to, tn = lex(o), lex(n)
    if not to:
        return None
    p = 0
    while p < min(len(to), len(tn)) and to[p][1] == tn[p][1]:
        p += 1
    s = 0
    while s < min(len(to), len(tn)) - p and to[-1 - s][1] == tn[-1 - s][1]:
        s += 1
    a, b, c, d = p, len(to) - s, p, len(tn) - s
    while b - a < 2 and (a > 0 or b < len(to)):
        if a > 0:
            a -= 1; c -= 1
        if b - a < 2 and b < len(to):
            b += 1; d += 1
    if b - a < 2 or (a == 0 and b == len(to)):
        return None
    return abstract("span", [o[to[a][2]:to[b - 1][3]]], [n[tn[c][2]:tn[d - 1][3]] if d > c else ""], owner)


def groups(diff: str) -> list[tuple[list, list]]:
    """(removed lines, added lines) groups of a ledger diff (unified, n=0, hunk headers dropped): a '-' after '+' lines starts a new group."""
    out, cur = [], None
    for l in (diff or "").splitlines():
        if l.startswith("-"):
            if cur is None or cur[1]:
                cur = ([], []); out.append(cur)
            cur[0].append(l[1:])
        elif l.startswith("+"):
            if cur is None:
                cur = ([], []); out.append(cur)
            cur[1].append(l[1:])
        else:
            cur = None
    return out


def _words(line: str) -> set:
    return {t for k, t, *_ in lex(line) if k == "id"}


def _split(old: list, new: list) -> list[tuple[list, list]]:
    """A 2 -> 1 or 1 -> 2 group as one change, or as two when the diff glued separate hunks (its @@ headers are dropped): when exactly one line
    of the two-line side shares no word with the other side, it is a lone deletion (or insertion, which is no mechanism) next to a one-line
    change."""
    two, one = (old, new[0]) if len(old) == 2 else (new, old[0])
    alone = [k for k in (0, 1) if not _words(two[k]) & _words(one)]
    if len(alone) != 1:
        return [(old, new)]
    k = alone[0]
    pair = ([two[1 - k]], [one]) if len(old) == 2 else ([one], [two[1 - k]])
    return [pair] + ([([two[k]], [])] if len(old) == 2 else [])


def mine_win(w: dict, owner: dict) -> list[dict]:
    """Mechanisms of one ledger win (targeted edits only; a rewrite is a whole new proof): single-line and contiguous two-line replacements, their
    in-line spans, and the deletion of a single tactic line."""
    if (w.get("kind") or "edit") != "edit":
        return []
    diff = w.get("diff") or ""; gs = groups(diff)
    if len(diff) >= DIFF_CAP:
        gs = gs[:-1]
    out = []
    for old, new in [p for g in gs for p in (_split(*g) if sorted(map(len, g)) == [1, 2] else [g])]:
        if len(old) == 1 and not new:
            m = abstract("delete", old, [], owner)
            if m and m["pat"][0][0][0] == "id":   # a tactic line: it starts with a keyword
                out.append(m)
        elif 1 <= len(old) <= 2 and 1 <= len(new) <= 2:
            out += [m for m in (abstract("rule", old, new, owner), span_of(old[0], new[0], owner) if len(old) == len(new) == 1 else None) if m]
    return out


def _combinator(tac: str) -> bool:
    return "<;>" in tac or tac.startswith(("all_goals", "any_goals"))


def terminal_lines(lines: list[str]) -> list[tuple[int, str]]:
    """(line index, tactic) of the terminal tactic lines of a proof body: no continuation below, a whole tactic (it starts with a keyword and
    keeps the bracket balance), no `have`, and either a goal combinator (all_goals / any_goals / `<;>`, which close goals wherever they stand)
    or the end of its block (the last line, a dedent next, or a one-line bullet / case / by). The tactic is the line's text after its
    `·` / `case … =>` / `by` prefix (a comment dropped)."""
    out = []; kw = keywords()
    for i, l in enumerate(lines):
        s = l.split("--", 1)[0].rstrip(); st = s.strip()
        if not st:
            continue
        nxt = next((x for x in lines[i + 1:] if x.split("--", 1)[0].strip()), None); ind = _indent(s)
        if nxt is not None and _indent(nxt) > ind:
            continue
        tac = st
        while _PREFIX.match(tac):
            tac = _PREFIX.sub("", tac, count=1).strip()
        toks = lex(tac)
        if not toks or ":=" in tac or toks[0][1] not in kw or any(_balance([toks])):
            continue
        if _combinator(tac) or nxt is None or _indent(nxt) < ind or _PREFIX.match(st):
            out.append((i, tac))
    return out


def closer_lines(body: str) -> list[str]:
    """The closer tactics of a proof body: its terminal lines that are goal combinators or closers (inrun.CLOSERS)."""
    return [t for _i, t in terminal_lines(body.split("\n")) if _combinator(t) or inrun._CLOSER_RE.match(t)]


def closer_mech(tac: str, owner: dict) -> dict | None:
    """A closer mechanism: every identifier that is not a keyword or a shared name becomes a wildcard (at most MAX_CLOSER_WILD of them)."""
    kw = keywords(); toks = lex(tac); names: dict = {}
    for k, t, *_ in toks:
        if k == "id" and t not in kw and not shared_name(t, owner):
            names.setdefault(t, len(names))
    if not toks or len(names) > MAX_CLOSER_WILD:
        return None
    pat = [("w", names[t]) if k == "id" and t in names else (k, t) for k, t, *_ in toks]
    return _new_mech("closer", _sig(pat), pat=None, new=[_template(tac, toks, names)], nw=len(names))


def describe(m: dict) -> str:
    """One line per mechanism (the TRANSFER HITS entries): abstract, $A / $B for names from the viewer's own proof."""
    if m["kind"] == "operator":
        return OP_TEXT[m["op"]]
    if m["kind"] == "closer":
        return f"closer `{show(m['new'][0])}` in place of a goal's last tactic"
    old = " ⏎ ".join(show(t) for t in m["old"]); new = " ⏎ ".join(show(t) for t in m["new"])
    if m["kind"] == "delete":
        return f"delete the line `{old}`"
    if m["kind"] == "span":
        return f"inside a line `{old}` -> " + (f"`{new}`" if new else "(nothing)")
    return f"`{old}` -> `{new}`"


# ---- application --------------------------------------------------------------------------------------------------------------------------
def _match(pat: list, toks: list, bind: dict) -> dict | None:
    if len(pat) != len(toks):
        return None
    b, kw = dict(bind), keywords()
    for p, t in zip(pat, toks):
        if p[0] == "w":
            if t[0] != "id" or t[1] in kw or b.setdefault(p[1], t[1]) != t[1]:
                return None
        elif p[1] != t[1]:
            return None
    return b


def line_sites(m: dict, lines: list[str]) -> list[tuple]:
    """(first line, binding) of every non-overlapping place the rule's old lines match (whole lines, same relative indentation)."""
    L = [lex(l) for l in lines]; k = len(m["pat"]); out = []; i = 0
    while i + k <= len(lines):
        b: dict | None = {}
        for j in range(k):
            if not L[i + j] or _indent(lines[i + j]) - _indent(lines[i]) != m["rel"][j]:
                b = None; break
            b = _match(m["pat"][j], L[i + j], b)
            if b is None:
                break
        if b is not None and m["kind"] == "delete":   # never orphan a deleted tactic's continuation lines
            nxt = next((l for l in lines[i + 1:] if l.strip()), None)
            b = None if nxt is not None and _indent(nxt) > _indent(lines[i]) else b
        if b is not None:
            out.append((i, b)); i += k
        else:
            i += 1
    return out


def span_sites(m: dict, lines: list[str]) -> list[tuple]:
    pat = m["pat"][0]; k = len(pat); out = []
    for i, l in enumerate(lines):
        toks = lex(l); j = 0
        while j + k <= len(toks):
            b = _match(pat, toks[j:j + k], {})
            if b is not None:
                out.append((i, toks[j][2], toks[j + k - 1][3], b)); j += k
            else:
                j += 1
    return out


def _cut(line: str, a: int, e: int, txt: str) -> str:
    left, right = line[:a], line[e:]
    if txt:
        return left + txt + right
    if not left.strip():
        return left + right.lstrip(" ")
    if left.endswith(" ") and (not right or right[0] in " )]}⟩,"):
        left = left.rstrip(" ")
    return left + right


def apply_sites(m: dict, lines: list[str], sites: list) -> list[str]:
    new = list(lines)
    if m["kind"] == "span":
        for i, a, e, b in sorted(sites, key=lambda s: (s[0], s[1]), reverse=True):
            new[i] = _cut(new[i], a, e, fill(m["new"][0], b) if m["new"] else "")
        return new
    for i, b in sorted(sites, key=lambda s: s[0], reverse=True):
        base = _indent(lines[i])
        new[i:i + len(m["pat"])] = [" " * max(0, base + r) + fill(t, b) for t, r in zip(m["new"], m["nrel"])]
    return new


def rule_cands(m: dict, decl: str, stmt: str, cap: int = MAX_PAIR) -> list[str]:
    """Candidates of a rule / delete / span on one proof: all sites at once (when there are 2 or 3; with more, one bad site would sink it),
    then each site alone, in text order; at most cap. A site whose binder name (m['bind']) is used elsewhere in the proof is skipped."""
    from scorer.tokenize import split_declaration
    d = decl.rstrip(); body = split_declaration(d, stmt)
    if body is None:
        return []
    head, lines = d[: len(d) - len(body)], body.split("\n")
    sites = (span_sites if m["kind"] == "span" else line_sites)(m, lines)
    if m.get("bind"):
        uses = collections.Counter(t for l in lines for k, t, *_ in lex(l) if k == "id")
        per = collections.Counter(p[1] for P in m["pat"] for p in P if p[0] == "w")
        sites = [s for s in sites if all(uses[s[-1][k]] <= per[k] for k in m["bind"])]
    out = []
    for c in ([sites] if 2 <= len(sites) <= 3 else []) + [[s] for s in sites]:
        txt = head + "\n".join(apply_sites(m, lines, c))
        if txt.rstrip() != d and txt not in out:
            out.append(txt)
        if len(out) >= cap:
            break
    return out


def _names_of(text: str, k: int = CLOSER_NAMES) -> list[str]:
    kw = keywords(); out: list = []
    for l in text.split("\n"):
        out += [t for kd, t, *_ in lex(l) if kd == "id" and t not in kw and t not in out]
    return out[:k]


def _closer_texts(m: dict, text: str, cap: int) -> list[str]:
    if not m["nw"]:
        return [fill(m["new"][0], {})]
    return [fill(m["new"][0], dict(enumerate(p))) for p in itertools.islice(itertools.permutations(_names_of(text), m["nw"]), cap)]


def closer_cands(m: dict, decl: str, stmt: str, cap: int = MAX_PAIR) -> list[str]:
    """Candidates of a closer on one proof, kept only when they save tokens, largest saving first, at most cap: the closer in place of each
    terminal tactic line (terminal_lines: the leaf sites harness/mine.py never probes), wildcards bound from that line's names; then, for a
    closer without wildcards that lean_mine does not try itself (mine.DEFAULT_CLOSERS), the whole body of each outermost goal block
    (mine.outer_blocks / mine._replace) and the whole proof."""
    from harness import mine as MN
    from scorer.tokenize import count_tokens
    sp = MN.body_lines(decl.rstrip(), stmt)
    if sp is None:
        return []
    head, body = sp; leaf, wide = [], []
    for i, tac in terminal_lines(body):
        line = body[i].split("--", 1)[0].rstrip()
        leaf += [(count_tokens(tac) - count_tokens(c), i, line[:len(line) - len(tac)] + c) for c in _closer_texts(m, tac, cap) if c != tac]
    if not m["nw"] and fill(m["new"][0], {}) not in MN.DEFAULT_CLOSERS:
        blocks = MN.outer_blocks(body); c = fill(m["new"][0], {})
        for idx, b in enumerate(blocks):
            wide.append((count_tokens("\n".join(body[b["start"]:b["end"]])) - count_tokens(f"{b['header'].strip()} {c}"),
                         MN._replace(head, body, blocks, lambda k, idx=idx: c if k == idx else None)[0]))
        wide.append((count_tokens("\n".join(body)) - count_tokens(c),
                     "\n".join(head[:-1] + [re.sub(r":=\s*by\s*$", lambda _m: f":= by {c}", head[-1])])))
    out = []
    for txt in ([("\n".join(head + body[:i] + [l] + body[i + 1:])) for s, i, l in sorted(leaf, key=lambda x: (-x[0], x[1])) if s > 0]
                + [t for s, t in sorted(wide, key=lambda x: -x[0]) if s > 0]):
        if txt not in out:
            out.append(txt)
        if len(out) >= cap:
            break
    return out


# ---- the lane -----------------------------------------------------------------------------------------------------------------------------
def workspaces(root: Path) -> list[dict]:
    """The rows of a work root (directories with a state.json), sorted by directory name; i is the row#k index of the counts-only output."""
    out = []
    for i, st in enumerate(sorted(Path(root).glob("*/state.json"), key=lambda p: p.parent.name)):
        s = _read(st)
        out.append({"i": i, "dir": st.parent, "key": inrun.src_key(st.parent.name), "problem": (s or {}).get("problem") or st.parent.name,
                    "state": s})
    return out


def zpct(compat) -> float:
    from scorer.score import compat_pct
    return compat_pct(compat) if isinstance(compat, dict) else 100.0


def verdict(res: dict, best: dict) -> float | None:
    """The candidate's full score when it may bank (strict promotion), else None: it compiled, its full score (Z included) is strictly above the
    best's, and its Z is not below the best's (no listed toolchain lost; a best without Z counts as Z 100)."""
    if not res.get("ok") or res.get("score") is None or not isinstance(res.get("compat"), dict):
        return None
    bz = float(best["Z"]) if best.get("Z") is not None else zpct(best.get("compat"))
    if float(res["score"]) <= float(best.get("score") or 33.33) + 1e-9 or zpct(res["compat"]) < bz - 1e-9:
        return None
    return float(res["score"])


def _infra(res: dict) -> bool:
    """A compile that failed for infrastructure reasons, not the candidate's: a timeout (also the memgate's give-up) or a killed process, on the
    primary or a listed toolchain."""
    errs = list(res.get("errors") or []) + [e for f in (res.get("compat_failures") or {}).values() for e in (f or {}).get("errors") or []]
    return any(str(e) == "timeout" or str(e).startswith("lean exit -") for e in errs)


def live(state: dict, w: Path, now: float | None = None) -> str | None:
    """Why a row is not the lane's to change now, or None: 'session' (its last runs[] entry has no `ended` / `skipped` / `best_after` and
    started less than LIVE_H ago: the CC driver appends it before the prompt is built, the reviewer included, and closes it in its ledger
    write; a reviewer saves the state it loaded, so a bank in between would be undone) or 'review' (a paid review bound to the current best
    that no executor session has used yet: a new best would void it)."""
    runs = state.get("runs") or []; r = runs[-1] if runs else {}
    if r and not (r.get("ended") or r.get("skipped") or "best_after" in r):
        try:
            t = calendar.timegm(time.strptime(str(r.get("started")), "%Y-%m-%dT%H:%M:%SZ"))
        except ValueError:
            t = None
        if t is not None and (now if now is not None else time.time()) - t < LIVE_H * 3600:
            return "session"
    try:
        from harness.prompt_v2 import review_for
        if review_for(Path(w), state):
            return "review"
    except Exception:  # noqa: BLE001  (no review machinery: nothing to protect)
        pass
    return None


def default_precheck(name: str, decl: str, best_score: float, prov: dict) -> dict:
    """leantools.lean_check on a scratch state whose best is the row's score: the compile, the score and (when it beats the best) every listed
    toolchain, with nothing recorded and no lock held. A new best carries `_bank`: the scratch state's best and attempt and the verified
    record lean_check wrote for it, which the bank commits as they are."""
    from harness import leantools as LT   # looked up at call time: the tests stub leantools.lean_check
    st = {"best": {"score": best_score, "proof": None}, "attempts": []}
    with tempfile.TemporaryDirectory(prefix="lra-transfer-pre-") as td:
        vp = Path(td) / "verified.jsonl"
        res = LT.lean_check(name, decl, st, prov, vp)
        rec = vp.read_text().strip() if vp.exists() else None
    if res.get("new_best") and st["best"].get("proof"):
        res["_bank"] = {"best": st["best"], "attempt": st["attempts"][-1] if st["attempts"] else None, "record": rec}
    return res


def default_bank(w: Path, name: str, res: dict, prov: dict, vpath, sha: str) -> dict:
    """Bank a pre-checked result without compiling again (review 2026-10-12: a second compile under the lock could lose a pin and still bank,
    and held the lock for minutes): under the state lock, only while the stored best is still the proof with this sha, no session is in
    progress and the result still passes verdict(); then the best, the attempt, the ledger win, state.json, best.lean and the verified record.
    {'skipped': why} otherwise."""
    from harness.statelock import state_lock
    b = res.get("_bank") or {}
    if not b.get("best"):
        return {"skipped": "no checked result"}
    with state_lock(w, timeout=LOCK_WAIT):
        sp = w / "state.json"; state = json.loads(sp.read_text())
        cur = state.get("best") or {}
        if LV.proof_sha(cur.get("proof")) != sha:
            return {"skipped": "changed"}
        why = live(state, w)
        if why:
            return {"skipped": "live", "why": why}
        if verdict(res, cur) is None:
            return {"skipped": "not better"}
        state["best"] = dict(b["best"])
        if b.get("attempt"):
            state.setdefault("attempts", []).append(dict(b["attempt"])); state["attempts"] = state["attempts"][-200:]
        run_id = prov.get("run_id")
        try:
            inrun.append_win(state, inrun.ledger_win(name, cur, state["best"], run_id,
                                                     sum(1 for a in state.get("attempts", []) if a.get("run_id") == run_id)))
        except Exception:  # noqa: BLE001  (the ledger never fails a bank)
            pass
        inrun.write_state(sp, state)
        (w / "best.lean").write_text(state["best"]["proof"].rstrip() + "\n")
        if vpath and b.get("record"):
            Path(vpath).parent.mkdir(parents=True, exist_ok=True)
            with Path(vpath).open("a") as f:
                f.write(b["record"] + "\n")
    return {"ok": True, "new_best": True, "score": state["best"]["score"]}


def set_tag(root) -> str | None:
    """`internal` / `internalpool` ... when a work root belongs to a internal held-out set or the internal pool (a path component, `work_` stripped, starts
    with it), else None."""
    for part in reversed(Path(root).resolve().parts):
        m = re.match(r"(internal\d*|internalpool)", part.removeprefix("work_"))
        if m:
            return m.group(1)
    return None


def _op_hb_polish(name: str, decl: str, best: dict) -> str | None:
    from harness.hb_polish import polish
    base = ({"ok": True, "score": best["score"], "Z": best["Z"], "L": best.get("L"), "H": best.get("H"), "tokens": best.get("tokens"),
             "heartbeats": best.get("heartbeats")} if best.get("Z") is not None and best.get("score") is not None else None)
    r = polish(name, decl, base=base)
    return r.get("proof") if r.get("status") == "improved" else None


def _op_normalize(name: str, decl: str, best: dict) -> str | None:
    from harness.normalize import normalize
    r = normalize(name, decl, log=lambda *a, **k: None)
    return r.get("proof") if r.get("status") == "improved" else None


OP_FNS = {"hb_polish": _op_hb_polish, "normalize": _op_normalize}


class Lane:
    """One work root's transfer lane. Every compile path is injectable (precheck, bank, op_fns): the tests stub leantools.lean_check."""

    def __init__(self, root, *, mine_roots=(), jobs: int = 4, slice_s: float = 900.0, deadline: float | None = None, run_id: str | None = None,
                 rows_filter=None, mine_rows=None, ops=OPS, max_cands: int = MAX_CANDS, precheck=None, bank=None, op_fns=None, clock=time.time,
                 log=print, write: bool = True, vpath=None, stop: threading.Event | None = None):
        self.root = Path(root); self.xd = self.root / XDIR; self.mine_roots = [Path(r) for r in mine_roots]
        tag = set_tag(self.root)
        for r in self.mine_roots:   # review 2026-10-12: a internal set or the internal pool is never mined into another set's line (discover's rule)
            if set_tag(r) and set_tag(r) != tag:
                raise ValueError(f"--mine-root of set {set_tag(r)} refused for a work root of {'set ' + tag if tag else 'no internal set'}")
        self.jobs, self.slice_s, self.max_cands, self.clock, self.log, self.write = max(1, jobs), slice_s, max_cands, clock, log, write
        self.deadline = deadline if deadline is not None else clock() + 7200.0
        rid = f"{self.root.name.removeprefix('work_')}-xfer"
        self.run_id = run_id or (rid if not tag or rid.startswith(tag) else f"{tag}-{rid}")
        if tag and not self.run_id.startswith(("internal", "internalpool")):   # the run prefix is what discover / envelope skip
            raise ValueError(f"a run id on set {tag} must start with internal / internalpool")
        self.vpath = vpath if vpath is not None else ROOT / "probe/runs" / self.run_id / "verified.jsonl"
        self.rows_filter = set(rows_filter) if rows_filter is not None else None
        self.mine_rows = set(mine_rows) if mine_rows is not None else None
        self.ops = tuple(ops); self.precheck = precheck or default_precheck; self.bank = bank or default_bank
        self.op_fns = dict(OP_FNS, **(op_fns or {})); self.stop = stop or threading.Event()
        self._lk = threading.Lock(); self.mechs: dict = {}; self.sweeps = 0; self.unjoined = False
        self.rows, self.owner, self.line_index = [], {}, ({}, set(), set())
        self.done, self.hits, self.apps = set(), collections.defaultdict(list), collections.Counter()
        self.pairs, self.offset, self.infra = collections.Counter(), {}, collections.Counter()
        for d in self._jsonl("dispositions.jsonl"):   # `all` 0: the pair's candidates from `next` on are still to try
            k = (d.get("m"), d.get("b"))
            if d.get("all", 1):
                self.done.add(k); self.offset.pop(k, None)
            else:
                self.offset[k] = max(self.offset.get(k, 0), int(d.get("next") or 0))
            self.apps[d.get("m")] += int(d.get("ok") or 0); self.pairs[d.get("m")] += 1
        for h in self._jsonl("hits.jsonl"):
            self.hits[h.get("m")].append((h.get("row"), float(h.get("d") or 0)))
        self.rowstat = _read(self.xd / "rows.json") or {}

    def _jsonl(self, fn: str) -> list:
        out = []
        try:
            for l in (self.xd / fn).read_text().splitlines():
                try:
                    out.append(json.loads(l))
                except ValueError:
                    pass
        except OSError:
            pass
        return out

    def _append(self, fn: str, rec: dict) -> None:
        if self.write:
            self.xd.mkdir(exist_ok=True)
            with (self.xd / fn).open("a") as f:
                f.write(json.dumps(rec, ensure_ascii=False) + "\n")

    def halted(self) -> bool:
        return self.stop.is_set() or self.clock() >= self.deadline

    # -- mining
    def mine(self) -> dict:
        """Mechanisms from this root's and the mine roots' ledger wins and current bests, deduplicated by their normalized hash. A mine root's
        workspace of a problem this root also has is skipped (its best and wins are another line's proof of the same problem). The identifier
        index of every mined row decides which literal names a mechanism may carry; the feedback lint uses the line's own rows only."""
        from harness.leantools import ROWS
        from scorer.tokenize import split_declaration
        self.rows = workspaces(self.root); mine_own = {w["problem"] for w in self.rows}
        every = self.rows + [w for r in self.mine_roots for w in workspaces(r) if w["problem"] not in mine_own]
        files: dict = {}
        for w in every:
            files.setdefault(w["problem"], [w["dir"] / "original.lean", w["dir"] / "context.lean"])
        self.owner = inrun.ident_index(files)
        line = {n: files[n] for n in mine_own}   # problem names: every mined row's (stricter than inrun.transfer_hits' line-only list)
        self.line_index = (inrun.ident_index(line), inrun.declared_names(line), inrun.name_terms(list(files), ROWS))
        mechs: dict = {}

        def add(m, key, win):
            g = mechs.setdefault(m["id"], m); g["src"].add(key); g["wins"] += win
        for op in self.ops:
            add(_new_mech("operator", op, op=op, nw=0), "*", 0)
        for w in every:
            if self.mine_rows is not None and w["problem"] not in self.mine_rows:
                continue
            s = w["state"] or {}
            for win in (s.get("ledger") or {}).get("wins") or []:
                for m in mine_win(win, self.owner):
                    add(m, w["key"], 1)
            best, row = (s.get("best") or {}).get("proof"), ROWS.get(w["problem"])
            body = split_declaration(best.rstrip(), row["statement"]) if best and row else None
            for tac in closer_lines(body) if body else []:
                m = closer_mech(tac, self.owner)
                if m:
                    add(m, w["key"], 0)
        self.mechs = mechs
        return mechs

    def order(self) -> list[dict]:
        """Mechanisms with hits first (transfer of what already won elsewhere), then operators, rules, deletes, spans, closers; more source rows
        and wins first within a kind."""
        return sorted(self.mechs.values(), key=lambda m: (-len(self.hits.get(m["id"], ())), KINDS.index(m["kind"]), -len(m["src"]), -m["wins"], m["id"]))

    def candidates(self, m: dict, decl: str, stmt: str) -> list[str]:
        """The pair's whole candidate list (at most MAX_PAIR, deterministic for a best): try_pair takes max_cands of them per visit."""
        if m["kind"] == "closer":
            return closer_cands(m, decl, stmt)
        return rule_cands(m, decl, stmt)

    # -- one (mechanism, best) pair
    def try_pair(self, row: dict, m: dict, best: dict, sha: str, stmt: str, seen: dict, c: collections.Counter) -> str:
        """One visit: the pair's next max_cands candidates. 'none' (nothing to try), 'tried' (every candidate done), 'more' (candidates left for
        a later visit), 'banked', 'changed' (the best moved under the lane), 'live' (a session started), 'halt' (stopped) or 'busy' (state lock,
        or a compile that failed for infrastructure reasons); the last four record nothing."""
        name = row["problem"]; decl = best["proof"]; pk = (m["id"], sha); score = float(best.get("score") or 33.33)
        prov = {"kind": "closed-dev-only", "model": "transfer@cpu", "run_id": self.run_id, "mode": "transfer", "mechanism": m["id"],
                "mechanism_kind": m["kind"]}
        with self._lk:
            off = self.offset.get(pk, 0)
        winner, compiled = None, 0
        try:
            if m["kind"] == "operator":
                if self.halted():
                    return "halt"
                compiled = 1   # the operator's own compiles
                proof = self.op_fns[m["op"]](name, decl, best)
                cands = [proof] if proof and proof.rstrip() != decl.rstrip() else []
            else:
                cands = self.candidates(m, decl, stmt)
                if not cands:
                    return "none"
            batch = cands[off:off + self.max_cands]
            for cand in batch:
                if self.halted():
                    return "halt"
                key = (sha, hashlib.sha256(cand.encode()).hexdigest())
                if key not in seen:   # the same text from another mechanism on the same best is compiled once
                    res = self.precheck(name, cand, score, prov); compiled += 1
                    if _infra(res):
                        with self._lk:
                            self.infra[pk] += 1; strikes = self.infra[pk]
                        if strikes < INFRA_STRIKES:
                            c["infra"] += 1; return "busy"
                    seen[key] = (verdict(res, best), res)
                sc, res = seen[key]
                if sc is not None and (winner is None or sc > winner[0]):
                    winner = (sc, res)
            if self.halted():
                return "halt"
            gain = None
            if winner:
                r = self.bank(row["dir"], name, winner[1], prov, self.vpath, sha)
                if r.get("skipped") == "live":
                    c["live"] += 1; return "live"
                if r.get("skipped") == "changed":
                    return "changed"
                if r.get("new_best"):   # any other refusal (`not better`: the stored best's numbers moved under the same proof) is a miss
                    gain = round(float(r.get("score") or 0) - score, 2)
        except TimeoutError:
            c["lock_busy"] += 1; return "busy"
        except Exception as e:  # noqa: BLE001  (one pair's failure never stops the lane; the class only: messages carry paths and names)
            c["errors"] += 1; c[f"error:{type(e).__name__}"] += 1; return "tried"
        nxt = off + len(batch); full = gain is not None or nxt >= len(cands)
        with self._lk:
            if full:
                self.done.add(pk); self.offset.pop(pk, None)
            else:
                self.offset[pk] = nxt
            self.apps[m["id"]] += compiled; self.pairs[m["id"]] += 1
            c["pairs"] += 1; c["candidates"] += len(batch); c["compiled"] += compiled
            self._append("dispositions.jsonl", {"m": m["id"], "k": m["kind"], "b": sha, "row": row["key"], "cand": len(batch), "ok": compiled,
                                                "next": nxt, "all": int(full), "hit": int(gain is not None), "d": gain, "t": _now()})
            if gain is not None:
                self.hits[m["id"]].append((row["key"], gain)); c["hits"] += 1; c["gain"] += gain; c[f"hit:{m['kind']}"] += 1
                self._append("hits.jsonl", {"m": m["id"], "k": m["kind"], "row": row["key"], "i": row["i"], "d": gain, "t": _now()})
                self.log(f"transfer hit: row#{row['i']} {m['kind']} {gain:+.2f}")
        return "banked" if gain is not None else ("tried" if full else "more")

    # -- one row's slice
    def run_slice(self, row: dict) -> collections.Counter:
        """Mechanisms in order on the row's current best until the slice ends: a pair with candidates left is visited again after the others; a
        new best (banked here or by a session) starts over on it. A row with a session in progress or an unused review is left alone."""
        from harness.leantools import ROWS
        c: collections.Counter = collections.Counter(); t0 = self.clock(); seen: dict = {}
        if row["problem"] not in ROWS:
            c["not_in_rows"] += 1; return c
        stmt = ROWS[row["problem"]]["statement"]; order = self.order()
        while not self.halted():
            state = _read(row["dir"] / "state.json") or {}; best = state.get("best") or {}
            if not best.get("proof"):
                c["no_best"] += 1; break
            if live(state, row["dir"]):
                c["live"] += 1; break
            sha = LV.proof_sha(best["proof"]); again = more = stop = False
            for m in order:
                if self.halted() or self.clock() - t0 >= self.slice_s:
                    c["cut"] += 1; stop = True; break
                with self._lk:
                    if (m["id"], sha) in self.done:
                        continue
                cur = _read(row["dir"] / "state.json")   # before every pair: a session that started, or a best that moved, ends this pass
                if cur is not None and live(cur, row["dir"]):
                    c["live"] += 1; stop = True; break
                if cur is not None and LV.proof_sha((cur.get("best") or {}).get("proof")) != sha:
                    again = True; break
                r = self.try_pair(row, m, best, sha, stmt, seen, c)
                if r in ("banked", "changed"):
                    again = True; break   # a new best: every mechanism is pending on it again
                if r in ("halt", "busy", "live"):
                    stop = True; break
                more |= r == "more"
            if stop or not (again or more):
                break
        if c["pairs"]:
            with self._lk:
                rs = self.rowstat.setdefault(row["key"], {"slices": 0, "pairs": 0, "hits": 0})
                rs["slices"] += 1; rs["pairs"] += c["pairs"]; rs["hits"] += c["hits"]
        return c

    def scan_rows(self) -> list[dict]:
        rows = [r for r in self.rows if self.rows_filter is None or r["problem"] in self.rows_filter]
        return sorted(rows, key=lambda r: ((self.rowstat.get(r["key"]) or {}).get("slices", 0), r["i"]))   # least-scanned first

    def sweep(self) -> collections.Counter:
        """Mine, then give every row (least-scanned first) one slice, --jobs rows at a time; feedback written after the sweep. Every wait is
        bounded: by the deadline, then GRACE_S, after which the lane's own compile processes are killed."""
        self.mine(); self.sweeps += 1; tot: collections.Counter = collections.Counter()
        rows = self.scan_rows(); ex = cf.ThreadPoolExecutor(self.jobs)
        futs = [ex.submit(self.run_slice, r) for r in rows]
        t_stop = None
        while True:
            dn, nd = cf.wait(futs, timeout=1.0)
            if not nd:
                break
            if self.halted() and t_stop is None:
                t_stop = time.time()
                for f in nd:
                    f.cancel()
            if t_stop is not None and time.time() - t_stop > GRACE_S:
                tot["killed_compiles"] += kill_until_quiet(); self.unjoined = True; break
        ex.shutdown(wait=False, cancel_futures=True)
        for f in futs:
            if f.done() and not f.cancelled() and f.exception() is None:
                tot.update(f.result()); tot["rows"] += 1
            elif f.done() and not f.cancelled():
                tot["errors"] += 1
        tot["gain"] = round(tot["gain"], 2)
        self.write_outputs()
        return tot

    def dry_run(self) -> collections.Counter:
        """Mining and matching only: (mechanism, best) pairs pending and their candidates; no compile, nothing written."""
        from harness.leantools import ROWS
        self.mine(); c: collections.Counter = collections.Counter()
        for row in self.scan_rows():
            best = ((_read(row["dir"] / "state.json") or {}).get("best") or {})
            if row["problem"] not in ROWS or not best.get("proof"):
                c["skipped"] += 1; continue
            c["rows"] += 1; sha = LV.proof_sha(best["proof"]); stmt = ROWS[row["problem"]]["statement"]; n = 0
            for m in self.mechs.values():
                if (m["id"], sha) in self.done:
                    c["pairs_done"] += 1; continue
                k = 1 if m["kind"] == "operator" else max(0, len(self.candidates(m, best["proof"], stmt)) - self.offset.get((m["id"], sha), 0))
                if k:
                    c["pairs_pending"] += 1; c["candidates"] += k; c[f"pending:{m['kind']}"] += 1; n += 1
            c["rows_with_pending"] += bool(n)
        return c

    # -- feedback
    def feedback(self) -> tuple[list, collections.Counter]:
        """TRANSFER HITS entries: mechanisms with >= 1 hit (most hits first), each through inrun's leak lint over the line's own rows (no Lean
        block > 2 lines, no problem name, no identifier only one of the line's rows has: what inrun.transfer_hits checks again on a rebuild)."""
        out, rej = [], collections.Counter(); owner, declared, terms = self.line_index
        for m in sorted(self.mechs.values(), key=lambda m: (-len(self.hits.get(m["id"], ())), m["id"])):
            h = self.hits.get(m["id"]) or []
            if not h:
                break
            txt = describe(m); why = inrun.leak_lint(txt, terms, owner, None, declared)
            if why:
                rej[why] += 1; continue
            out.append({"pattern": txt, "kind": m["kind"], "hits": len(h), "rows": len({r for r, _d in h}),
                        "d_score": round(sum(d for _r, d in h) / len(h), 2)})
        return out[:8], rej

    def write_outputs(self) -> None:
        if not self.write or not self.mechs:
            return
        self.xd.mkdir(exist_ok=True)
        fb, rej = self.feedback()
        ms = []
        for m in self.order():
            h = self.hits.get(m["id"]) or []
            ms.append({"id": m["id"], "kind": m["kind"], "pattern": describe(m), "sources": len(m["src"] - {"*"}), "wins": m["wins"],
                       "hits": len(h), "rows_hit": len({r for r, _d in h}), "applications": self.apps[m["id"]], "pairs": self.pairs[m["id"]],
                       "d_score": round(sum(d for _r, d in h) / len(h), 2) if h else None})
        _atomic(self.xd / "mechanisms.json", {"built": _now(), "rows": len(self.rows), "sweeps": self.sweeps, "mechanisms": ms, "feedback": fb,
                                              "rejected_feedback": dict(rej)})
        _atomic(self.xd / "rows.json", self.rowstat)
        write_techniques(self.root, fb)


def write_techniques(root: Path, fb: list) -> None:
    """The TRANSFER HITS entries into <root>/_run_techniques.json (key `transfer`, rendered by inrun.render), written atomically; inrun.build
    carries them over from mechanisms.json when the ladder rebuilds the file."""
    p = Path(root) / inrun.TECH_FILE; tech = inrun.load(root)
    if tech is None and not fb:
        return
    tech = dict(tech or {"built": _now()}); tech["transfer"] = fb
    _atomic(p, tech)


def kill_own() -> int:
    """SIGKILL the compile processes this lane started (they carry LRA_TRANSFER in their environment; memgate runs them in sessions of their own)."""
    mk = os.environ.get("LRA_TRANSFER")
    if not mk:
        return 0
    from harness.hx_heldout import _kill_marked
    return _kill_marked(f"LRA_TRANSFER={mk}")


def kill_until_quiet(limit: float = 5.0, sleep=time.sleep) -> int:
    """kill_own until two rounds in a row find nothing, at most `limit` seconds (review 2026-10-12: a thread whose compile was killed starts the
    next listed toolchain's compile, which would outlive the lane and its memgate grant)."""
    n, quiet, t0 = 0, 0, time.time()
    while quiet < 2 and time.time() - t0 < limit:
        k = kill_own(); n += k; quiet = 0 if k else quiet + 1
        sleep(0.25)
    return n


class LaneBusy(RuntimeError):
    pass


@contextlib.contextmanager
def lane_lock(root: Path):
    """One lane per work root (<root>/_transfer/.lane.lock, non-blocking): a second lane on the same root is refused."""
    xd = Path(root) / XDIR; xd.mkdir(exist_ok=True)
    with open(xd / ".lane.lock", "a") as fh:
        try:
            fcntl.flock(fh, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise LaneBusy("another transfer lane holds this work root") from None
        try:
            yield
        finally:
            fcntl.flock(fh, fcntl.LOCK_UN)


# ---- canary -------------------------------------------------------------------------------------------------------------------------------
def canary(work_root, spec: dict, base_dir: Path | None = None, *, precheck=None, bank=None, jobs: int = 1, slice_s: float = 3600.0,
           deadline_s: float = 7200.0, log=print, stop: threading.Event | None = None) -> dict:
    """A known transfer must be found and banked: the source row's mechanisms only (no operators), scanned on the target row alone, in a temporary
    copy of the two workspaces (the work root and probe/runs are never written; the copies carry no runs[] or review, so the live-row guard
    stays out of it). spec: {"source": problem, "target": problem, "target_best": an optional proof file (relative to base_dir) installed as
    the target's incumbent through one normal check}. Warm-up roots only (a internal or internal pool root is refused). Returns counts and `pass`."""
    if set_tag(work_root):
        return {"pass": False, "why": "the canary runs on warm-up roots only"}
    rows = {w["problem"]: w for w in workspaces(Path(work_root))}
    src, dst = rows.get(spec.get("source")), rows.get(spec.get("target"))
    if not src or not dst:
        return {"pass": False, "why": "source or target row not in the work root"}
    with tempfile.TemporaryDirectory(prefix="lra-transfer-canary-") as td:
        tr = Path(td) / "root"; tr.mkdir()
        for w in {src["dir"], dst["dir"]}:
            shutil.copytree(w, tr / w.name, ignore=shutil.ignore_patterns(".state.lock", ".*.tmp-*", "_*", "review.md"))
            s = _read(tr / w.name / "state.json")
            if s is not None:
                s["runs"] = []; inrun.write_state(tr / w.name / "state.json", s)
        vp = Path(td) / "verified.jsonl"; out = {"pass": False}
        if spec.get("target_best"):
            p = (Path(base_dir or ".") / spec["target_best"]); sp = tr / dst["dir"].name / "state.json"
            s = _read(sp) or {"problem": dst["problem"], "attempts": [], "runs": []}
            s["best"] = {"score": 33.33, "proof": None}; inrun.write_state(sp, s)
            r = inrun.locked_check(sp.parent, dst["problem"], p.read_text(), {"run_id": "transfer-canary", "mode": "transfer-canary"}, None)
            if not r.get("new_best"):
                return {"pass": False, "why": "the target_best proof did not check as the incumbent"}
        lane = Lane(tr, jobs=jobs, slice_s=slice_s, deadline=time.time() + deadline_s, run_id="transfer-canary", rows_filter={dst["problem"]},
                    mine_rows={src["problem"]}, ops=(), precheck=precheck, bank=bank, vpath=vp, log=lambda *a, **k: None, stop=stop)
        c = lane.sweep(); key = src["key"]
        from_src = {m["id"] for m in lane.mechs.values() if key in m["src"]}
        hits = [(mid, d) for mid, hs in lane.hits.items() if mid in from_src for r, d in hs if r == dst["key"]]
        out.update({"pass": bool(hits), "mechanisms": len(from_src), "candidates": c["candidates"], "compiled": c["compiled"], "hits": len(hits),
                    "gain": round(sum(d for _m, d in hits), 2)})
    return out


# ---- CLI ----------------------------------------------------------------------------------------------------------------------------------
def summary(k: int, c: collections.Counter, lane: Lane) -> str:
    kinds = collections.Counter(m["kind"] for m in lane.mechs.values())
    return (f"transfer sweep {k}: {c['rows']} row(s) scanned ({c['not_in_rows'] + c['no_best']} without a row or a best), {len(lane.mechs)} "
            f"mechanism(s) ({', '.join(f'{n} {kd}' for kd, n in sorted(kinds.items()))}); {c['pairs']} (mechanism, best) pair(s) tried, "
            f"{c['candidates']} candidate(s), {c['compiled']} compiled; {c['hits']} hit(s) banked (summed gain {c['gain']:+.2f}); "
            f"{c['cut']} row slice(s) cut by time, {c['live']} left to a live session / unused review, {c['lock_busy']} busy, "
            f"{c['infra']} infrastructure failure(s) (not recorded), {c['errors']} error(s)")


def run_loop(lane: Lane, sweeps: int, follow: bool, poll_s: float, say, sleep=time.sleep) -> int:
    """--sweeps K sweeps, or with --follow one sweep every poll_s seconds until the deadline or a stop (each re-mines the root, so new ledger
    wins and new bests become new (mechanism, best sha) pairs; tried pairs are skipped). Every wait is bounded by the deadline. Returns sweeps."""
    k = 0
    while not lane.halted() and (follow or k < sweeps):
        k += 1; say(summary(k, lane.sweep(), lane))
        t_next = lane.clock() + poll_s
        while follow and not lane.halted() and lane.clock() < t_next:
            sleep(1.0)
    return k


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--work-root", required=True, help="the line's work root (relative to the checkout, or absolute)")
    ap.add_argument("--mine-root", action="append", default=[], help="another work root whose ledger wins and bests are mined (never scanned)")
    ap.add_argument("--jobs", type=int, default=4, help="rows scanned at once (one compile each; the memgate admits every compile)")
    ap.add_argument("--sweeps", type=int, default=1); ap.add_argument("--max-hours", type=float, default=2.0)
    ap.add_argument("--slice-min", type=float, default=15.0, help="per-row time slice of a sweep (a started visit of a pair finishes)")
    ap.add_argument("--rows-file", help="scan only these problems (one name per line; mining still reads every row)")
    ap.add_argument("--run-id", help="the run its banked records go under (default <work-root name, work_ stripped>-xfer, with the internal / "
                                     "internalpool set prefix; on such a set it must start with internal / internalpool)")
    ap.add_argument("--ops", default=",".join(OPS), help="operators run as mechanisms (comma-separated of hb_polish,normalize; '' for none)")
    ap.add_argument("--dry-run", action="store_true", help="mine and match only: no compile, nothing written")
    ap.add_argument("--follow", action="store_true", help="re-sweep every --poll-min minutes until --max-hours (new pairs only)")
    ap.add_argument("--poll-min", type=float, default=10.0)
    ap.add_argument("--canary", help="a JSON spec {source, target[, target_best]} on a warm-up work root: exit 0 when the transfer is banked")
    a = ap.parse_args()
    root = ROOT / a.work_root
    if not root.is_dir():
        ap.error("--work-root is not a directory")
    stop = threading.Event()

    def on_signal(signum, frame):
        stop.set()
    signal.signal(signal.SIGTERM, on_signal); signal.signal(signal.SIGINT, on_signal)
    os.environ.setdefault("LRA_TRANSFER", f"{os.getpid()}-{time.time_ns()}")   # compile processes inherit it (kill_own)
    if a.canary:
        sp = Path(a.canary)
        r = canary(root, json.loads(sp.read_text()), sp.parent, jobs=1, deadline_s=a.max_hours * 3600, stop=stop)
        print(f"transfer canary: {'PASS' if r.get('pass') else 'FAIL'}: " + (r["why"] if r.get("why") else
              f"{r['mechanisms']} mechanism(s) mined from the source row, {r['candidates']} candidate(s) on the target ({r['compiled']} compiled), "
              f"{r['hits']} hit(s) banked (summed gain {r['gain']:+.2f})"))
        return 0 if r.get("pass") else 3
    rows = None
    if a.rows_file:
        rows = {l.strip() for l in Path(a.rows_file).read_text().splitlines() if l.strip() and not l.lstrip().startswith("#")}
    ops = tuple(x.strip() for x in a.ops.split(",") if x.strip())
    if set(ops) - set(OPS):
        ap.error(f"--ops: unknown operator(s) {sorted(set(ops) - set(OPS))}")
    t0 = time.time()
    try:
        lane = Lane(root, mine_roots=[ROOT / r for r in a.mine_root], jobs=a.jobs, slice_s=a.slice_min * 60, deadline=t0 + a.max_hours * 3600,
                    run_id=a.run_id, rows_filter=rows, ops=ops, stop=stop, write=not a.dry_run)
    except ValueError as e:
        ap.error(str(e))
    if a.dry_run:
        c = lane.dry_run(); kinds = collections.Counter(m["kind"] for m in lane.mechs.values())
        print(f"transfer dry run: {c['rows']} row(s) ({c['skipped']} without a row or a best), {len(lane.mechs)} mechanism(s) "
              f"({', '.join(f'{n} {kd}' for kd, n in sorted(kinds.items()))}); {c['pairs_pending']} (mechanism, best) pair(s) pending on "
              f"{c['rows_with_pending']} row(s) ({', '.join(f'{c[k]} {k[8:]}' for k in sorted(c) if k.startswith('pending:'))}), "
              f"{c['candidates']} candidate(s); {c['pairs_done']} pair(s) already tried")
        return 0
    try:
        with lane_lock(root):
            k = run_loop(lane, a.sweeps, a.follow, a.poll_min * 60, lambda line: print(line, flush=True))
    except LaneBusy as e:
        print(f"transfer: refused: {e}"); return 2
    h = sum(len(v) for v in lane.hits.values())
    print(f"transfer done: {k} sweep(s) in {(time.time() - t0) / 60:.1f} min; {h} hit(s) recorded on this root so far; "
          f"{len(lane.feedback()[0])} TRANSFER HITS entr(y/ies) -> {XDIR}/mechanisms.json" + ("; stopped by signal" if stop.is_set() else ""),
          flush=True)
    if stop.is_set() or lane.unjoined:
        kill_until_quiet()   # a compile thread may still sit in the memgate's bounded wait (not joined) or start its next toolchain's compile
        sys.stdout.flush(); os._exit(143 if stop.is_set() else 0)
    return 0


if __name__ == "__main__":
    sys.exit(main())
