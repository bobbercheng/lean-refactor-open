#!/usr/bin/env python3
"""Op `v5_altcases` (open post-step v5, branch open-post-v5-v5altcases, 2026-11-04): Lean-named alternative patterns.

A destructuring step whose pattern is a list of alternatives that are plain names,

    rcases e with n1 | n2 (| ..)        obtain n1 | n2 (| ..) := e        cases' e with n1 n2 (..)

(the pattern optionally in parentheses, `_` allowed for a name; a `· ` bullet before the step and a `<;> ..` tail after it allowed),
loses its pattern: `rcases e` (`cases e` for `cases'`). Lean then names each alternative's hypothesis itself; under the proof's top
`unhygienic` (or `unhygienic rcases e`, the narrow form, when the proof has none) those names are accessible: the constructor's field
name (`h` for Or), as Lean prints them. Every later use of n_i in the step's scope (the rest of its block; the bullet's block for a
bulleted step; the `<;>` tail) is renamed to Lean's name. Names are never guessed: they come from a `trace_state` right after the step,
the incumbent's display aligned with the rewritten step's display position by position, goal by goal (harness/post/v4_unhyg's probe
copies, its compile adapter, scope-aware renaming and capture check, imported read-only).

  sites     single-line steps only (a following line that continues the term is no site); no nested pattern, `rfl`, `-`, `@`, type
            ascription, `h : e` target or several targets. A site whose names are all `_` or never written again in its scope is
            free: converted without a probe (the plain check compile decides). At most MAX_SITES per proof, in line order.
  probe     ONE file per row (chunked only when the row's compile is slow, t4ind.per_file): per non-free site two copies, the
            incumbent and the proof with that one site converted (the top form: one top `unhygienic`, added when missing), plus the
            narrow-form copy when the proof has no top `unhygienic`; each copy with one `trace_state` after the site (t4ind.quiet's
            `stop` after it). A site converts when every displayed goal aligns: each n_i takes ONE accessible name across the goals
            (the same old name in two alternatives must get the same Lean name), every other hypothesis keeps its name (an
            inaccessible `x✝` of the incumbent aligns with anything), the goal and hypothesis counts agree; and the textual capture
            check (v4_unhyg.capture's rule, `λx` read as `λ` + `x`) finds no new name written for something else before an own
            renamed use, except a later BINDER of it (`intro .. x`, `fun .. x`, `λx`, `have x`): that binder and its uses (its line's
            block) are alpha-renamed with the site to a fresh one-token name unused in the proof (`x'`, ..; shared by every site it
            captures; at most MAX_BINDERS per site).
  re-probe  Lean names an alternative with a fresh name (`h_1`, ..) when an earlier converted site's name is in its context, so a chain
            with two probed sites in one scope is probed again in ONE file (per site, the chain's earlier conversions applied in both
            copies); the re-aligned chain joins the chains to check.
  chain     the converted sites joined (with their renamed later binders): the top chain (every site whose top probe aligned, plus the free ones) and, without a top
            `unhygienic`, the narrow chain (each probed site as `unhygienic <step>`, free ones bare); plus each converted site alone;
            all checked in ONE plain compile; a chain with an error keeps the innermost converted site holding its first error and
            is re-checked, at most REPAIRS rounds (v4_unhyg's repair loop; a blamed later binder drops its sites, a dropped site its
            binders). Only error-free forms that save tokens are proposed,
            fewest tokens first; the post-step's unchanged gate (every pin, paired re-reading, audit) decides adoption.

    has_sites(proof, statement) -> bool                                           (pure)
    query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None) -> dict   (probes + checks through `run`; cached)
    candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None) -> [{"op", "decl", "note"}]   (pure)

Generic by construction: Lean syntax only (`rcases`, `obtain`, `cases'`, `cases`, `unhygienic`, `trace_state`); no row name, lemma
name, proof text or table; every name written comes from Lean's trace of the row's own proof on its primary pin (a renamed later
binder takes a fresh spelling of its own name). A budget stop raised
by `run` propagates; any other fault of this op proposes nothing (open_post's per-op isolation)."""
from __future__ import annotations

import hashlib, re, sys, threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness import dialect_unhyg as U  # noqa: E402
from harness.dialect import blank, extent, indent, scope_end  # noqa: E402
from harness.post import d4_kit as K, t4ind as T4I  # noqa: E402
from harness.post import v4_unhyg as V4  # noqa: E402   (read-only: probe copies, compile adapter, scope-aware rename, capture)
from scorer.tokenize import count_tokens  # noqa: E402

FAMILY = "v5_altcases"
OP = "v5_altcases"
MAX_SITES = 12        # alternative sites per proof (line order)
REPAIRS = 3           # check-and-repair rounds of the chains (one plain compile each)
PER_FILE = 16         # copies per probe / check file at most (fewer on a slow row: t4ind.per_file)
MAX_CANDS = 6
CACHE_MAX = 128
TRACE = U.TRACE
_IDC = r"\w'!?₀-₉"
NM = r"(?:[^\W\d][" + _IDC + r"]*|_)"
NAME = re.compile(r"[^\W\d][" + _IDC + r"]*")
LEAD_RE = re.compile(r"^(\s*(?:[·.][ \t]+)?)(\S.*?)\s*$")
ALTS_RE = re.compile(r"^(\()?\s*(" + NM + r"(?:\s*\|\s*" + NM + r")+)\s*(\))?$")
NAMES_RE = re.compile(r"^" + NM + r"(?:\s+" + NM + r")*$")
RCASES_RE = re.compile(r"^rcases\s+(?P<rest>.+)$")
OBTAIN_RE = re.compile(r"^obtain\s+(?P<pat>[^:]+?)\s*:=\s*(?P<e>.+)$")
CASESP_RE = re.compile(r"^cases'\s+(?P<rest>.+)$")
_LOCK = threading.Lock()
_CACHE: dict = {}
_OPEN, _CLOSE = "([{⟨", ")]}⟩"


# ------------------------------------------------------------------------------------------------------------------------------ parsing
def _depths(s: str) -> list[int]:
    """The bracket depth before each character of s (None-free: an unbalanced text gives negative depths)."""
    out, d = [], 0
    for ch in s:
        out.append(d)
        if ch in _OPEN:
            d += 1
        elif ch in _CLOSE:
            d -= 1
    return out


def balanced(s: str) -> bool:
    d = 0
    for ch in s:
        if ch in _OPEN:
            d += 1
        elif ch in _CLOSE:
            d -= 1
            if d < 0:
                return False
    return d == 0


def split_tail(s: str) -> tuple[str, str]:
    """(the step, its ` <;> ..` tail with the leading space) at the first top-level `<;>`."""
    dp = _depths(s)
    for m in re.finditer(r"\s*<;>", s):
        if dp[m.start()] == 0:
            return s[:m.start()].rstrip(), s[m.start():]
    return s, ""


def _top_word(s: str, word: str) -> int:
    """The index of the last top-level ` word ` in s, or -1."""
    dp = _depths(s)
    best = -1
    for m in re.finditer(r"\s" + word + r"\s", s):
        if dp[m.start()] == 0:
            best = m.start()
    return best


def _term_ok(e: str) -> bool:
    """A single target term the step can take without a pattern: balanced, no top-level `,` (several targets) or `:` (a named target),
    no `by` / `fun` block, no `@` pattern marker."""
    e = e.strip()
    if not e or not balanced(e) or e.startswith(("by ", "fun ", "λ", "@", "-")) or e in ("by", "fun"):
        return False
    dp = _depths(e)
    for k, ch in enumerate(e):
        if dp[k] == 0 and (ch == "," or (ch == ":" and e[k + 1:k + 2] not in ("=", ":") and (k == 0 or e[k - 1] != ":"))):
            return False
    return " with " not in f" {e} " and "<;>" not in e


def parse_alts(pat: str) -> list[str] | None:
    """`n1 | n2 ..` (optionally in parentheses) -> [n1, n2, ..], else None."""
    m = ALTS_RE.match(pat.strip())
    if not m or bool(m.group(1)) != bool(m.group(3)):
        return None
    alts = [x.strip() for x in m.group(2).split("|")]
    return alts if len(alts) >= 2 and all(re.fullmatch(NM, a) and a != "rfl" for a in alts) else None


def parse_step(text: str) -> dict | None:
    """A site's step (the line without its lead): {"spell", "e", "alts", "tail"} or None."""
    step, tail = split_tail(text)
    m = RCASES_RE.match(step)
    if m:
        rest = m.group("rest")
        k = _top_word(rest, "with")
        if k < 0:
            return None
        e, alts = rest[:k].strip(), parse_alts(rest[k + len(" with "):])
        if alts is None or not _term_ok(e):
            return None
        return {"spell": "rcases", "e": e, "alts": alts, "tail": tail, "src": "rcases"}
    m = OBTAIN_RE.match(step)
    if m:
        alts, e = parse_alts(m.group("pat")), m.group("e").strip()
        if alts is None or not _term_ok(e):
            return None
        return {"spell": "rcases", "e": e, "alts": alts, "tail": tail, "src": "obtain"}
    m = CASESP_RE.match(step)
    if m:
        rest = m.group("rest")
        k = _top_word(rest, "with")
        if k < 0:
            return None
        e, names = rest[:k].strip(), rest[k + len(" with "):].strip()
        if not NAMES_RE.match(names) or "rfl" in names.split() or not _term_ok(e):
            return None
        return {"spell": "cases", "e": e, "alts": names.split(), "tail": tail, "src": "cases'"}
    return None


class AltSite(V4.Site):
    """A v4_unhyg.Site (kind "alt": binder / rename_line / capture read it) with the step's parts."""
    __slots__ = ("lead", "spell", "e", "alts", "tail", "src", "used")

    def __init__(self, idx, i, lo, hi, p: dict, lead: str, end: int | None = None):
        names = []
        for a in p["alts"]:
            if a != "_" and a not in names:
                names.append(a)
        super().__init__(idx, "alt", i, names, lo, hi, end=end)
        self.lead, self.spell, self.e, self.alts, self.tail, self.src = lead, p["spell"], p["e"], list(p["alts"]), p["tail"], p["src"]
        self.used = True


def find_alt_sites(lines: list[str]) -> list[AltSite]:
    """The alternative sites of a tactic body (line 0 is the `by` line), each with its scope; `free` when no name is written again."""
    out: list[AltSite] = []
    for i, l in enumerate(lines):
        if i == 0 or blank(l) or ("rcases" not in l and "obtain" not in l and "cases'" not in l):
            continue
        m = LEAD_RE.match(l)
        if not m:
            continue
        lead, text = m.group(1), m.group(2)
        if text.startswith("--") or "--" in text or "/-" in text:
            continue
        p = parse_step(text)
        if p is None:
            continue
        col = len(lead)
        nxt = next((k for k in range(i + 1, len(lines)) if not blank(lines[k])), None)
        bullet = lead.strip() in ("·", ".")
        end = i + 1
        if nxt is not None and indent(lines[nxt]) > col:
            if bullet or not (p["tail"] or lines[nxt].lstrip().startswith("<;>")):
                continue    # the term (or the bullet's step) continues on the next line
            end = extent(lines, i)   # the `<;>` tail continues on deeper lines: they belong to the step (a probe copy drops them)
        hi = extent(lines, i) if bullet else alt_scope_end(lines, i)
        s = AltSite(len(out), i, i, hi, p, lead, end=end)
        later = "\n".join([p["tail"]] + lines[i + 1:hi])
        s.used = any(re.search(r"(?<![" + _IDC + r".])" + re.escape(n) + r"(?![" + _IDC + r"])", later) for n in s.names)
        s.free = not s.used
        out.append(s)
        if len(out) >= MAX_SITES:
            break
    return out


CONT_START = ("$", "<|", "|>", "<;>", ")", "]", "}", "⟩", ",")


def alt_scope_end(lines: list[str], i: int) -> int:
    """dialect.scope_end, where a shallower line that continues a term (it starts with `$`, `<|`, `|>`, `<;>` or a closing bracket or
    comma) stays in the block."""
    d = indent(lines[i]); j = i + 1; last = i + 1
    while j < len(lines):
        if blank(lines[j]):
            j += 1; continue
        if indent(lines[j]) >= d or lines[j].lstrip().startswith(CONT_START):
            j += 1; last = j
        else:
            break
    return last


# ------------------------------------------------------------------------------------------------------------------------------ render
def step_text(s: AltSite, *, narrow: bool, e: str | None = None) -> str:
    return s.lead + ("unhygienic " if narrow else "") + s.spell + " " + (s.e if e is None else e)


def render(lines: list[str], sites: list, conv: dict, *, top: bool, trace: AltSite | None = None, probe_conv: bool = False
           ) -> tuple[list[str], list[int], int | None]:
    """The body with the converted alternative sites (conv: site idx -> {"map", "mode": "top" | "narrow" | "bare"}) rewritten and their
    uses renamed (v4_unhyg.rename_line: scope-aware over `sites`, which holds the alternative sites and v4_unhyg's naming sites); the
    top `unhygienic` added when `top`. trace: a probe copy, the site's step without its tail, then `trace_state` at the step's
    column (the copy's later lines as they are). Returns (lines, the orig line of every output line, the trace's output index)."""
    names: set = set()
    for s in sites:
        if s.idx in conv:
            names |= set(conv[s.idx].get("map", {}))
    alt = {s.i: s for s in sites if isinstance(s, AltSite)}
    out: list[str] = []
    src: list[int] = []
    tline = None
    drop = range(0)
    for j, l in enumerate(lines):
        if j in drop:
            continue        # a probe copy: the traced step's `<;>` continuation lines
        if j == 0:
            out.append(l.rstrip() + " unhygienic" if top and not U.has_top_unhyg(lines) else l)
            src.append(0)
            continue
        s = alt.get(j)
        if s is not None and (s.idx in conv or s is trace):
            c = conv.get(s.idx)
            if c is not None:     # the target keeps its own names, except those an earlier converted site renames
                t = step_text(s, narrow=c.get("mode") == "narrow", e=V4.rename_line(s.e, j, sites, conv, names, skip=s))
            else:
                t = LEAD_RE.match(l).group(1) + split_tail(LEAD_RE.match(l).group(2))[0]
            if s is trace:
                out.append(t); src.append(j)
                out.append(" " * len(s.lead) + TRACE); src.append(j)
                tline = len(out) - 1
                drop = range(j + 1, s.end)
                continue
            out.append(t + V4.rename_line(s.tail, j, sites, conv, names)); src.append(j)
            continue
        for b in sites:
            if isinstance(b, _Binder) and b.i == j and b.idx in conv and l[b.col:b.col + len(b.names[0])] == b.names[0]:
                l = l[:b.col] + conv[b.idx]["map"][b.names[0]] + l[b.col + len(b.names[0]):]
        out.append(V4.rename_line(l, j, sites, conv, names) if names else l); src.append(j)
    return out, src, tline


# ------------------------------------------------------------------------------------------------------------------------------ align
def align(tos: list, tvs: list, s: AltSite) -> tuple[dict | None, str]:
    """{old name: Lean's name} for the alternative site s from the incumbent's displays (tos) and the rewritten step's (tvs) at the same
    place, every displayed goal aligned position by position, or (None, why)."""
    tos, tvs = V4.distinct(tos), V4.distinct(tvs)
    if not tos or not tvs:
        return None, f"traces {len(tos)} / {len(tvs)}"
    n = min(len(tos), len(tvs))
    want = s.bound()
    mp: dict = {}
    for to, tv in zip(tos[:n], tvs[:n]):
        if not to or not tv or len(to) != len(tv):
            return None, "goal count"
        for go, gv in zip(to, tv):
            if len(go["hyps"]) != len(gv["hyps"]):
                return None, f"hyps {len(go['hyps'])} / {len(gv['hyps'])}"
            for (on, _), (vn, _) in zip(go["hyps"], gv["hyps"]):
                if on in want:
                    if not NAME.fullmatch(vn) or mp.get(on, vn) != vn:
                        return None, f"site name {on} -> {vn}"
                    mp[on] = vn
                elif "✝" in on:
                    continue
                elif vn != on:
                    return None, f"context {on} -> {vn}"
    if not want <= set(mp):
        return None, f"names not in the context: {sorted(want - set(mp))}"
    return mp, ""


# ------------------------------------------------------------------------------------------------------------------------------ capture
IDENT_L = re.compile(r"(?<![" + _IDC + r".])λ?([^\W\d][" + _IDC + r"]*)")     # `λh` read as `λ` + `h` (Lean's lexer)
BINDER_PRE = re.compile(r"(?:(?:^|[\s(;>])(?:intro|intros|rintro|fun)\s+(?:[^\W\d][" + _IDC + r"]*\s+)*|λ\s*|(?:^|\s)have\s+)$")
BINDER_POST = re.compile(r"^(?:\s*(?:=>|:|$)|\s+[^\W\d][" + _IDC + r"]*(?:\s|$))")
MAX_BINDERS = 2       # later binders alpha-renamed per site


def capture_at(lines: list[str], s, sites: list, mp: dict) -> tuple | None:
    """v4_unhyg.capture's rule with the position: (new name, line, column) of the first occurrence of a new name written in s's scope for
    something else before one of s's own renamed uses, else None (`λx` read as `λ` + `x`)."""
    news = {v: k for k, v in mp.items() if k != v}
    if not news:
        return None
    first: dict = {}
    last_own = None
    for j in range(s.i, s.hi):
        l = lines[j]
        if j == s.i:
            l = getattr(s, "tail", "") or ""
            off = len(lines[j]) - len(l)
        else:
            off = 0
        for m in IDENT_L.finditer(l):
            k = m.group(1)
            at = (j, off + m.start(1))
            if k in mp and k != mp[k] and V4.binder(sites, k, j) is s:
                last_own = at
            if k in news and not (k in mp and V4.binder(sites, k, j) is s) and k not in first:
                bd = V4.binder(sites, k, j)
                if isinstance(bd, _Binder) and s.idx in bd.owners:
                    continue      # a later binder of the new name, renamed away with s
                first[k] = at
    if last_own is None:
        return None
    hits = sorted((at, v) for v, at in first.items() if at < last_own)
    return (hits[0][1], hits[0][0][0], hits[0][0][1]) if hits else None


def is_binder(line: str, col: int, name: str) -> bool:
    """The occurrence of `name` at `col` binds it: after `intro` / `intros` / `rintro` / `fun` (with earlier names), `λ` or `have`,
    followed by `=>`, `:`, another name or the line's end."""
    return bool(BINDER_PRE.search(line[:col])) and bool(BINDER_POST.match(line[col + len(name):]))


def fresh(name: str, used: set) -> str | None:
    for c in (name + "'", name + "''", name + "0", name * 2, name + "x"):
        if c not in used and count_tokens(c) == count_tokens(name):
            return c
    return None


class _Binder(V4.Site):
    """A later binder of a site's new name (alpha-renamed with the site): scope = its line's block; owners: the sites it is renamed for."""
    __slots__ = ("col", "owner", "owners", "fresh")


def accept(lines: list[str], s, sites: list, mp: dict, used: set, pidx: list) -> tuple[dict | None, str, list]:
    """{site idx: entry, binder idx: entry ..} for site s and its aligned map, or (None, why): a capture by a later binder of the new name
    (`intro x`, `fun x`, `λx`, `have x`) alpha-renames that binder and its uses to a fresh name (one token, unused in the proof; at most
    MAX_BINDERS per site); any other capture keeps the site. The check compile judges the result."""
    out: dict = {}
    extra: list = []
    for _ in range(MAX_BINDERS + 1):
        cap = capture_at(lines, s, sites + extra, mp)
        if cap is None:      # (a binder renamed for s earlier, e.g. for its other form, goes with it again)
            for b in sites + extra:
                if isinstance(b, _Binder) and s.idx in b.owners and b.idx not in out:
                    out[b.idx] = {"map": {b.names[0]: b.fresh}, "mode": "binder", "owners": list(b.owners)}
                    if b not in extra:
                        extra.append(b)
            return {**out, s.idx: {"map": {a: b for a, b in mp.items() if a != b}}}, "", extra
        x, j, col = cap
        if len(extra) >= MAX_BINDERS or not is_binder(lines[j], col, x):
            return None, f"{x} (written at line {j}) captured", []
        old = next((b for b in sites if isinstance(b, _Binder) and (b.i, b.col, b.names[0]) == (j, col, x)), None)
        if old is not None:      # the same binder renamed for an earlier site: shared (one fresh name)
            old.owner = s.idx if old.owner is None else old.owner
            old.owners.append(s.idx)
            extra.append(old)
            out[old.idx] = {"map": {x: old.fresh}, "mode": "binder", "owners": list(old.owners)}
            continue
        f = fresh(x, used)
        if f is None:
            return None, f"{x} (written at line {j}) captured; no fresh name", []
        b = _Binder(pidx[0], "binder", j, [x], j, alt_scope_end(lines, j))
        b.col, b.owner, b.owners, b.fresh = col, s.idx, [s.idx], f
        pidx[0] += 1
        used.add(f)
        extra.append(b)
        out[b.idx] = {"map": {x: f}, "mode": "binder", "owners": [s.idx]}
    return None, "binders", []


# ------------------------------------------------------------------------------------------------------------------------------ generate
def generate(proof: str, statement: str, cb, *, log=None, stats: dict | None = None, low=None) -> list[dict]:
    """The op's candidates on `proof` (module docstring): one probe file, then the chains' check-and-repair compiles."""
    st = stats if stats is not None else {}
    say = log or (lambda d: None)
    hb = K.head_body(proof.rstrip(), statement)
    if hb is None:
        return []
    head, body = hb
    lines = body.split("\n")
    asites = find_alt_sites(lines)
    if not asites:
        return []
    has_top = U.has_top_unhyg(lines)
    can_top = has_top or V4.top_ok(lines)
    vsites = []
    try:
        vsites = V4.find_sites(lines)
        for k, v in enumerate(vsites):
            v.idx = 1000 + k          # v4's naming sites: scope only (never converted here)
    except Exception:  # noqa: BLE001  (no v4 sites: the alternative sites' own scopes)
        vsites = []
    sites = list(asites) + vsites
    base = count_tokens(body)
    st["sites"] = len(asites)
    st["free"] = sum(1 for s in asites if s.free)
    # ---- probe: one file, the incumbent and the converted step per probed site (top form; narrow form without a top word)
    texts, plan = [], []
    dl = lambda li: head.count("\n") + li + 1  # noqa: E731
    probed = [s for s in asites if not s.free]
    if probed and not (low is not None and low()):
        for s in probed:
            o, _src, ot = render(lines, sites, {}, top=False, trace=s)
            entry = {"site": s, "orig": (len(texts), ot), "forms": []}
            texts.append(head + "\n".join(o))
            modes = (["top"] if can_top else []) + ([] if has_top else ["narrow"])
            for mode in modes:
                v, _src, vt = render(lines, sites, {s.idx: {"map": {}, "mode": mode}}, top=(mode == "top"), trace=s)
                entry["forms"].append((mode, len(texts), vt))
                texts.append(head + "\n".join(v))
            plan.append(entry)
        got = list(cb(texts) or []) + [None] * len(texts)
        st["probe_copies"] = len(texts)
    else:
        got = []
    conv_top: dict = {}
    conv_nar: dict = {}
    used = set(IDENT_L.findall(body)) | set(V4.IDENT.findall(body))
    pidx = [2000]
    for e in plan:
        s = e["site"]
        oi, ot = e["orig"]
        tos = U.traces_at(got[oi], dl(ot)) if got[oi] is not None else []
        for mode, vi, vt in e["forms"]:
            tvs = U.traces_at(got[vi], dl(vt)) if got[vi] is not None else []
            mp, why = align(tos, tvs, s)
            ent = None
            if mp is not None:
                ent, cwhy, extra = accept(lines, s, sites, mp, used, pidx)
                if ent is None:
                    why = "capture: " + cwhy
                else:
                    sites.extend(b for b in extra if b not in sites)
            if ent is None:
                say({"site": repr(s), "mode": mode, "fail": why})
                continue
            st["verified"] = st.get("verified", 0) + 1
            ent[s.idx]["mode"] = "bare" if has_top else mode
            say({"site": repr(s), "mode": mode, "map": mp, "binders": [ent[k]["map"] for k in ent if k != s.idx]})
            _merge(conv_top if mode == "top" else conv_nar, ent)
    free = {s.idx: {"map": {}, "mode": "bare"} for s in asites if s.free}
    chains = []
    if can_top and (conv_top or (free and has_top)):
        chains.append(("top" if not has_top else "bare", {**free, **conv_top}, not has_top and bool(conv_top)))
    if not has_top:
        if conv_nar or free:
            chains.append(("narrow", {**free, **conv_nar}, False))
    if not (low is not None and low()):
        chains += joint_reprobe(head, lines, sites, asites, chains, cb, log=say, stats=st, used=used, pidx=pidx)
    return check_and_repair(head, lines, sites, asites, chains, cb, base, log=say, stats=st)


def _merge(conv: dict, ent: dict) -> None:
    """ent's entries into conv; a binder shared by several sites keeps the union of its owners."""
    for k, v in ent.items():
        if k in conv and v.get("mode") == "binder":
            conv[k] = dict(v, owners=sorted(set(conv[k].get("owners", [])) | set(v.get("owners", []))))
        else:
            conv[k] = v


def _owner_i(by: dict, v: dict) -> int:
    """A binder entry's position for the re-probe's `before`: its first owner's line."""
    os_ = [by[o].i for o in v.get("owners", []) if o in by]
    return min(os_) if os_ else -1


def _overlap(sa: AltSite, sb: AltSite) -> bool:
    return sa.lo <= sb.i < sa.hi or sb.lo <= sa.i < sb.hi


def joint_reprobe(head: str, lines: list[str], sites: list, asites: list, chains: list, cb, *, log=None,
                  stats: dict | None = None, used: set | None = None, pidx: list | None = None) -> list:
    """(chain re-probe) Lean picks a fresh name (`h_1`, ..) for an alternative when an earlier converted site's name is already in the
    context, so a chain's names can differ from the one-site probes: each chain with two probed sites in one scope is probed again in
    ONE file, per probed site k (line order) the chain's conversions before k applied in both copies (the incumbent's step and the
    nameless one, a trace after k); the re-aligned chain (sites whose re-probe fails dropped) joins the chains to check."""
    st = stats if stats is not None else {}
    say = log or (lambda d: None)
    by = {s.idx: s for s in asites}
    todo, texts = [], []
    dl = lambda li: head.count("\n") + li + 1  # noqa: E731
    used = used if used is not None else set()
    pidx = pidx if pidx is not None else [3000]
    for n, conv, top in chains:
        probed = sorted((by[k] for k in conv if k in by and not by[k].free), key=lambda x: x.i)
        if len(probed) < 2 or not any(_overlap(a, b) for a in probed for b in probed if a is not b):
            continue
        plan = []
        for s in probed:
            before = {k: v for k, v in conv.items() if (by[k].i if k in by else _owner_i(by, v)) < s.i}
            o, _src, ot = render(lines, sites, before, top=top, trace=s)
            v, _src, vt = render(lines, sites, {**before, s.idx: {"map": {}, "mode": conv[s.idx]["mode"]}}, top=top, trace=s)
            plan.append((s, len(texts), ot, len(texts) + 1, vt))
            texts += [head + "\n".join(o), head + "\n".join(v)]
        todo.append((n, conv, top, plan))
    if not todo:
        return []
    got = list(cb(texts) or []) + [None] * len(texts)
    st["reprobe_copies"] = st.get("reprobe_copies", 0) + len(texts)
    out = []
    for n, conv, top, plan in todo:
        new = {k: v for k, v in conv.items() if k in by and by[k].free}
        for s, oi, ot, vi, vt in plan:
            tos = U.traces_at(got[oi], dl(ot)) if got[oi] is not None else []
            tvs = U.traces_at(got[vi], dl(vt)) if got[vi] is not None else []
            mp, why = align(tos, tvs, s)
            ent = None
            if mp is not None:
                ent, cwhy, extra = accept(lines, s, sites, mp, used, pidx)
                if ent is None:
                    why = "capture: " + cwhy
                else:
                    sites.extend(b for b in extra if b not in sites)
            if ent is None:
                say({"reprobe": n, "site": repr(s), "fail": why})
                continue
            ent[s.idx]["mode"] = conv[s.idx]["mode"]
            _merge(new, ent)
        if new != conv and new:
            say({"reprobe": n, "chain": {repr(by.get(k, k)): v["map"] for k, v in new.items()}})
            out.append((n + "J", new, top and any(v["mode"] == "top" for v in new.values())))
    return out


def check_and_repair(head: str, lines: list[str], sites: list, asites: list, chains: list, cb, base: int, *, log=None,
                     stats: dict | None = None) -> list[dict]:
    """Every chain (and, in round 0, every converted site alone) checked in one plain compile per round; a chain with an error keeps
    its innermost converted site holding the first error and is re-checked (REPAIRS rounds); error-free token savers proposed."""
    st = stats if stats is not None else {}
    say = log or (lambda d: None)
    out: list[dict] = []
    seen: set = set()
    live = [(n, dict(c), t) for n, c, t in chains if c]
    singles = []
    for n, c, t in live:
        if len(c) > 1 and not n.endswith("J"):
            for k, v in c.items():
                if v.get("mode") == "binder":
                    continue      # a later binder goes with its site
                one = {k: v, **{q: w for q, w in c.items() if k in w.get("owners", ())}}
                if len(one) < len(c):
                    singles.append((f"{n}1", one, t and v.get("mode") != "bare"))
    for rnd in range(REPAIRS):
        batch = []
        for n, conv, top in live + (singles if rnd == 0 else []):
            key = (top, tuple(sorted((k, tuple(sorted(v["map"].items())), v["mode"]) for k, v in conv.items())))
            if key in seen or not conv:
                continue
            seen.add(key)
            b, src, _t = render(lines, sites, conv, top=top)
            if count_tokens("\n".join(b)) < base:
                batch.append((n, conv, top, b, src))
        if not batch:
            break
        chk = V4.check(head, [x[3] for x in batch], cb)
        st["checks"] = st.get("checks", 0) + 1
        say({"check": rnd, "forms": [f"{n}:{len(c)}" for n, c, _t, _b, _s in batch], "errors": [e if e is None else e[:4] for e in chk]})
        nxt = []
        for (n, conv, top, b, src), e in zip(batch, chk):
            if e is not None and not e:
                nb = sum(1 for v in conv.values() if v.get("mode") == "binder")
                out.append(_cand(head, b, f"{n}: {len(conv) - nb} of {len(asites)} site(s)" + (f", {nb} later binder(s) renamed" if nb else "")
                                 + (" +top unhygienic" if top else "")))
                continue
            if e is None or not any(x[0] == n and x[1] is conv for x in live):
                continue
            bl = V4.blame(e, src, sites, conv)
            if bl is None:
                continue
            say({"repair": f"{n}: {bl!r}"})
            gone = set(conv[bl.idx].get("owners", [])) | {bl.idx}     # a blamed later binder: its sites go too; a site's binders with it
            conv2 = {k: v for k, v in conv.items() if k not in gone and not (set(v.get("owners", ())) & gone)}
            if conv2:
                nxt.append((n, conv2, top and any(v["mode"] == "top" for v in conv2.values())))
        live = nxt
        if not live:
            break
    out.sort(key=lambda c: c["tokens"])
    res, dd = [], set()
    for c in out:
        if c["decl"] not in dd:
            dd.add(c["decl"]); res.append(c)
    return res[:MAX_CANDS]


def _cand(head: str, b: list[str], note: str) -> dict:
    body = "\n".join(b)
    return {"op": OP, "decl": head + body.rstrip() + "\n", "note": note, "tokens": count_tokens(body)}


# ------------------------------------------------------------------------------------------------------------------------------ lane interface
def has_sites(proof: str, statement: str) -> bool:
    try:
        hb = K.head_body(proof.rstrip(), statement)
        if hb is None:
            return False
        return bool(find_alt_sites(hb[1].split("\n")))
    except Exception:  # noqa: BLE001  (a body the parsers cannot read has no site)
        return False


def _key(proof: str, statement: str) -> str:
    return hashlib.sha256((statement + "\0" + proof.strip()).encode()).hexdigest()[:24]


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    """The probe and the checks through `run` (charged; a budget stop propagates); {"v5a_for": key, "v5a": [candidates]}."""
    st = stats if stats is not None else {}
    key = _key(proof, statement)
    with _LOCK:
        if key in _CACHE:
            return dict(_CACHE[key])
    if not has_sites(proof, statement):
        return {}
    say = log or (lambda m: None)
    cs = (ctx or {}).get("compile_s")
    cb = V4.make_compile_batch(statement, run, attached=V4._attached(run), stats=st.setdefault("batch", {}), log=say,
                               per_file=min(PER_FILE, T4I.per_file(cs)))
    bud = getattr(run, "budget", None)
    floor_s = max(V4.LOW_MIN_S, V4.LOW_MULT * float(cs or 0.0))
    low = (lambda: V4._low(bud, floor_s)) if bud is not None and hasattr(bud, "left_s") else None
    try:
        got = generate(proof, statement, cb, log=lambda d: say(f"{FAMILY}: {str(d)[:400]}"), stats=st, low=low)
    except Exception as e:  # noqa: BLE001
        if type(e).__name__ == "_Stop":
            raise
        say(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:300]}")
        got = []
    say(f"{FAMILY}: {len(got)} candidate(s); stats { {k: v for k, v in st.items()} }")
    res = {"v5a_for": key, "v5a": got}
    with _LOCK:
        if len(_CACHE) >= CACHE_MAX:
            _CACHE.clear()
        _CACHE[key] = dict(res)
    return res


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    c = ctx or {}
    if c.get("v5a_for") != _key(proof, statement):
        return []
    return [{"op": OP, "decl": x["decl"], "note": str(x.get("note", ""))[:160]} for x in (c.get("v5a") or [])
            if isinstance(x, dict) and x.get("decl")][:int(max_per_op or MAX_CANDS)]
