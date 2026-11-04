#!/usr/bin/env python3
"""Op `v4_unhyg` (open post-step v4, branch open-post-v4-v4unhyg, 2026-11-04): Lean-named `unhygienic` renames, repaired.

The open package's own dialect family `unhyg` (harness/dialect_unhyg.py, b98; imported, never modified) drops the binder names of a
proof's naming sites under one `unhygienic` and renames every later use to the name Lean gives the hypothesis without them; the names are
never guessed, Lean prints them (`trace_state`). No v1-v3 op runs it (it ran only inside the open package's end stage). This lane op
runs a fork of its generate() (this module) through a compile_batch adapter on the post-step's charged run(text, version), with five
repairs measured on run 3's proofs (scratch census probe, VM1, 2026-11-04):

  copies    (1) every probe / check copy is `[private] theorem <Ns>.lraD4M<i> ...` (harness/post/ctorsearch.renamed: the declaration's
            own namespace prefix, so names the proof resolves through it still resolve; `private` kept, so the module's private names
            stay visible), self-references renamed (ctorsearch.self_renamed), and the `open .. in` / `set_option .. in` combinators the
            row's compile attaches to the declaration (open_post.attached_in(run.meter)) written before every copy (a probe file's first
            command, the anchor, takes the file prefix's own ones). Measured: a dotted name lost its namespace (`Unknown identifier`).
  align     (2) the incumbent's context (traced after the site, original names) and the rewritten proof's (traced at the same place,
            Lean's names) are aligned position by position: the site's own names take Lean's name at their position (an inaccessible
            `✝` name there: the site keeps its names); an inaccessible `x✝` of the incumbent (a `_` binder, never referable) aligns with
            whatever Lean prints; every other hypothesis must carry the name the earlier converted sites give it at that line
            (scope-aware: only sites whose scope contains the line), else the site keeps its names. A site whose new name is written
            in its scope for something else before one of its own renamed uses (a capture) keeps its names.
  chain     (3) the sites (rename_i lines, `· rename_i` and `<;> rename_i`, `case tag xs =>` / `next xs =>` headers, `intro x ..`
            (multi-line too), `by_contra h`, `ext x`, `funext x`; `by_cases h :` measured and left out: Lean keeps `h✝`) are
            converted one after another under ONE top `unhygienic` (each probe sees the earlier conversions); a site that fails is kept
            and the chain continues. The candidates are full chains only (MEASURED: 9 of 15 prefix candidates of the as-is engine
            failed with "too many variable names provided": the top `unhygienic` makes the hypotheses of a not-yet-converted site
            accessible). Each chain is checked in ONE plain compile of all its forms (repair): an error inside a converted site's
            scope keeps that site (innermost first) and the forms are re-checked, at most REPAIRS times; only error-free forms are
            proposed. Chains: A (greedy, line order); B, when a site failed after earlier conversions, without the conversions
            before the first failure (an early `intros` renamed the context so that every later header's hypotheses read `a_2✝`:
            MEASURED); R, chain A plus the sites only the textual capture check kept (a nested block's own name looks like a
            capture; the check compile judges). When no top chain can be made clean, the narrow form is tried: `unhygienic <split>`
            on each split tactic whose naming sites (the `case` / `next` headers after it) are all converted, names probed in that
            same form, and every such split at once. Two Lean behaviours handled in the probes: a linter that re-runs the traced
            tactics prints the trace again later (the first displays are aligned), and a slow row's files hold fewer copies
            (t4ind.per_file); no new probe starts once the row's wall or compile budget left is low (LOW_MIN_S / LOW_MULT /
            LOW_COMPILES: the pass keeps room to read every op's candidates and confirm the best).
  scope     (4) a rename applies to the uses whose innermost binding naming site is the converted one: a nested header or a later
            `rename_i` / `intro` that binds the same name again keeps its own scope (measured: renaming an outer name inside a
            nested `next` that rebinds it broke a proof).
  inner     (5) under the top `unhygienic` every inner `unhygienic tac` loses the word (the same hygiene); a proof with >= 2 inner
            wrappers and no top one gets the hoist even with no naming site.
  forms     `by_contra h` -> `by_contra` (Lean names it `this`), `ext x` / `funext x` -> `ext` / `funext` (probed: the same goals);
            `case tag x _ =>` -> `case tag =>`; `next x y =>` -> `next =>`, and the chain also with each such `next =>` as a `·`
            bullet (the same focus: the main goal, closed); `rename_i x _ y` line deleted; `intro a b c` -> `intros` when Lean's goal
            after it is the same (no binder left; probed in the same file), else `iterate k intro` (k >= 3) or k bare `intro`s.

    has_sites(proof, statement) -> bool                                           (pure)
    query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None) -> dict   (probes + checks through `run`; cached)
    candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None) -> [{"op", "decl", "note"}]   (pure)

Generic by construction: Lean syntax only (`unhygienic`, `trace_state`, `case`, `next`, `intro`, `intros`, `iterate`, `·`, and the
row's own `by_contra` / `ext` / `funext` without their names); no row
name, lemma name, proof text or table; every name written comes from Lean's trace of the row's own proof on its primary pin; the
post-step's gate (every pin, paired re-reading, audit) decides adoption. A budget stop raised by `run` propagates; any other fault of
this op proposes nothing (open_post's per-op isolation)."""
from __future__ import annotations

import hashlib, re, sys, threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness import dialect_unhyg as U  # noqa: E402
from harness.dialect import blank, case_parts, extent, indent, scope_end  # noqa: E402
from harness.post import ctorsearch as CT, d4_kit as K, t4ind as T4I  # noqa: E402
from scorer.tokenize import count_tokens  # noqa: E402

FAMILY = "v4_unhyg"
OP = "v4_unhyg"
MAX_SITES = 16        # naming sites probed per proof (in line order); one probe file each
REPAIRS = 4           # check-and-repair rounds of the top chain (one plain compile each)
NARROW_MAX = 4        # splits tried in the narrow form
MAX_CANDS = 6
PER_FILE = 8          # copies per probe / check file at most (fewer on a slow row: t4ind.per_file)
LOW_MIN_S = 600.0     # no new probe once the row's wall left is below max(LOW_MIN_S, LOW_MULT input compile times), or its compile
LOW_MULT = 25.0       # budget left is below LOW_COMPILES: the chain so far is checked and proposed, and the pass keeps room to read
LOW_COMPILES = 40     # every op's candidates and confirm the best (open_post.reserve_hit needs 3 + 2 x pins compiles at 1.5 x)
CACHE_MAX = 128
TRACE = U.TRACE
_IDC = r"\w'!?₀-₉"
NAMED_ARG_L = re.compile(r"\([ \t]*$")
NAMED_ARG_R = re.compile(r"[ \t]*:=")
IDENT = re.compile(r"(?<![" + _IDC + r".])([^\W\d][" + _IDC + r"]*)")
NAME = re.compile(r"[^\W\d][" + _IDC + r"]*")
INTRO_RE = re.compile(r"^(\s*)intros?((?:[ \t]+(?:[^\W\d][" + _IDC + r"]*|_))+)[ \t]*$")
INNER_RE = re.compile(r"^(\s*(?:·\s+)?)unhygienic[ \t]+(?=\S)")
SPLIT_RE = re.compile(r"^\s*(?:induction|cases|rcases|match)\b")
_LOCK = threading.Lock()
_CACHE: dict = {}


# ------------------------------------------------------------------------------------------------------------------------------ sites
class Site:
    __slots__ = ("idx", "kind", "i", "end", "names", "lo", "hi", "free", "col")

    def __init__(self, idx, kind, i, names, lo, hi, end=None, col=0):
        self.idx, self.kind, self.i, self.names, self.lo, self.hi = idx, kind, i, list(names), lo, hi
        self.end = i + 1 if end is None else end      # the site's own lines: i .. end - 1
        self.col = col                                 # brename: the column of the bullet's tactics
        self.free = all(n == "_" for n in self.names) and kind != "tacnames"   # `ext _` vs `ext`: the depth may differ, probe it

    def bound(self) -> set:
        return {n for n in self.names if n != "_"}

    def __repr__(self):
        return f"Site({self.kind}@{self.i} {self.names})"


TACNAMES_RE = re.compile(r"^(\s*)(by_contra!?|funext|ext)((?:[ \t]+(?:[^\W\d][" + _IDC + r"]*|_))+)[ \t]*$")
BRENAME_RE = re.compile(r"^(\s*)·([ \t]+)rename_i[ \t]+(.+?)\s*$")
INTRO_CONT_RE = re.compile(r"^[ \t]+((?:[^\W\d][" + _IDC + r"]*|_)(?:[ \t]+(?:[^\W\d][" + _IDC + r"]*|_))*)[ \t]*$")


def _names_ok(names) -> bool:
    return bool(names) and all(n == "_" or NAME.fullmatch(n) for n in names)


def find_sites(lines: list[str]) -> list[Site]:
    """The naming sites of a tactic body (its lines; line 0 is the `by` line): `tac <;> rename_i xs`, `intro xs` (names or `_` only,
    continuation lines of names included), `rename_i xs` (also as a bullet's first tactic, `· rename_i xs`), `case tag xs =>` /
    `next xs =>` with at least one binder; each with its scope (lines, the site's own lines included). A header whose tactics follow
    at its own column (no deeper line) scopes the rest of its block."""
    out: list[Site] = []
    for i, l in enumerate(lines):
        if i == 0 or blank(l):
            continue
        m = U.SEQ_RENAME_RE.match(l)
        if m and extent(lines, i) == i + 1:
            if _names_ok(m.group(3).split()):
                out.append(Site(len(out), "seqrename", i, m.group(3).split(), i, scope_end(lines, i)))
            continue
        m = INTRO_RE.match(l)
        if m:
            names, e = m.group(2).split(), extent(lines, i)
            cont = [INTRO_CONT_RE.match(lines[k]) for k in range(i + 1, e) if not blank(lines[k])]
            if all(cont):
                for c in cont:
                    names += c.group(1).split()
                if _names_ok(names):
                    out.append(Site(len(out), "intro", i, names, i, scope_end(lines, i), end=e))
            continue
        m = TACNAMES_RE.match(l)
        if m and extent(lines, i) == i + 1:
            if _names_ok(m.group(3).split()):
                out.append(Site(len(out), "tacnames", i, m.group(3).split(), i, scope_end(lines, i)))
            continue
        m = U.RENAME_RE.match(l)
        if m and extent(lines, i) == i + 1:
            if _names_ok(m.group(2).split()):
                out.append(Site(len(out), "rename", i, m.group(2).split(), i, scope_end(lines, i)))
            continue
        m = BRENAME_RE.match(l)
        if m:
            e = extent(lines, i)
            col = len(m.group(1)) + 1 + len(m.group(2))
            nxt = next((k for k in range(i + 1, e) if not blank(lines[k])), None)
            if _names_ok(m.group(3).split()) and nxt is not None and indent(lines[nxt]) == col:
                out.append(Site(len(out), "brename", i, m.group(3).split(), i, e, col=col))
            continue
        cp = case_parts(lines, i)
        if cp and ((cp[3] and _names_ok(cp[3])) or (cp[1] == "next" and not cp[3])):
            e = cp[5]
            if e == i + 1 and not cp[4].strip():
                e = scope_end(lines, i)
            out.append(Site(len(out), "case", i, cp[3], i, e))   # a nameless `next =>`: free (only its bullet form changes it)
    return out


def needs_top(sites: list[Site], conv: dict, inner: list) -> bool:
    """The top `unhygienic` is needed when a converted site had names (they become Lean's) or an inner wrapper is dropped; free
    conversions (`_`-only binders, a nameless `next`) mean the same under hygiene."""
    return bool(inner) or any(s.idx in conv and not s.free for s in sites)


def inner_lines(lines: list[str]) -> list[int]:
    return [i for i, l in enumerate(lines) if i > 0 and INNER_RE.match(l)]


def top_ok(lines: list[str]) -> bool:
    """The body is a tactic block opened by a bare `by` line (the top `unhygienic` joins it) or already has the top word."""
    return U.with_unhyg(lines) is not None


def binder(sites: list[Site], name: str, j: int, skip=None) -> Site | None:
    """The innermost naming site that binds `name` at line j (its scope contains j; the latest header wins); `skip`: a site not
    counted."""
    best = None
    for s in sites:
        if s is skip:
            continue
        if name in s.names and name != "_" and s.lo <= j < s.hi and (best is None or s.i > best.i):
            best = s
    return best


# ------------------------------------------------------------------------------------------------------------------------------ render
def rename_line(text: str, j: int, sites: list[Site], conv: dict, names: set, skip=None) -> str:
    """`text` (orig line j, or a part of it) with every identifier whose innermost binding site is converted renamed to Lean's name."""
    if not names:
        return text

    def sub(m):
        k = m.group(1)
        if k not in names:
            return k
        if NAMED_ARG_L.search(text, 0, m.start()) and NAMED_ARG_R.match(text, m.end()):
            return k      # the key of a named argument `(k := e)` is the callee's parameter name, not a use of the local
        s = binder(sites, k, j, skip)
        if s is None or s.idx not in conv:
            return k
        return conv[s.idx].get("map", {}).get(k, k)
    return IDENT.sub(sub, text)


def intro_form(lead: str, k: int, form: str) -> list[str]:
    if form == "intros":
        return [lead + "intros"]
    return [lead + f"iterate {k} intro"] if k >= 3 else [lead + "intro"] * k


def render(lines: list[str], sites: list[Site], conv: dict, *, top: bool, drop_inner: bool, bullets: bool = False,
           narrow: tuple = ()) -> tuple[list[str], dict, list[int]]:
    """The body with the converted sites (conv: site idx -> {"map", "form", "bullet"}) rewritten and their uses renamed (scope-aware),
    the top `unhygienic` (top), the inner wrappers dropped (drop_inner), converted `next` headers as `·` bullets (bullets); narrow:
    line indices whose tactic gets the `unhygienic` word. Returns (lines, {site idx: (output index, output line count)}, the orig line
    of every output line)."""
    names = set()
    for s in sites:
        if s.idx in conv:
            names |= set(conv[s.idx].get("map", {}))
    by_line = {s.i: s for s in sites}
    out: list[str] = []
    src: list[int] = []
    pos: dict = {}
    shifts: list = []          # (first line, end line, delta): a bulleted block's lines re-indented

    merge: list = []           # a converted `· rename_i xs` line: its bullet joins the next tactic line written

    def put(text: str, j: int):
        if merge and not blank(text):
            text = merge.pop() + text.lstrip(" ")
        out.append(text); src.append(j)

    def shifted(l: str, j: int) -> str:
        d = sum(x for lo, hi, x in shifts if lo <= j < hi)
        return l if not d or blank(l) else " " * max(0, indent(l) + d) + l.lstrip(" ")
    j = 0
    while j < len(lines):
        if j == 0:
            put(lines[0].rstrip() + " unhygienic" if top and not U.has_top_unhyg(lines) else lines[0], 0)
            j += 1
            continue
        l = shifted(lines[j], j)
        s = by_line.get(j)
        if s is not None and s.idx in conv:
            start = len(out)
            c = conv[s.idx]
            lead = " " * indent(l)
            if s.kind == "seqrename":
                m = U.SEQ_RENAME_RE.match(l)
                put(m.group(1) + rename_line(m.group(2), j, sites, conv, names), j)
            elif s.kind == "tacnames":
                put(lead + TACNAMES_RE.match(l).group(2), j)
            elif s.kind == "intro":
                for x in intro_form(lead, len(s.names), c.get("form") or "iterate"):
                    put(x, j)
                pos[s.idx] = (start, len(out) - start)
                j = s.end
                continue
            elif s.kind == "brename":
                bl = BRENAME_RE.match(l)
                merge.append(bl.group(1) + "·" + bl.group(2))
                pos[s.idx] = (start, 1)
                j += 1
                continue
            elif s.kind == "case":
                cp = case_parts(lines, j)
                kw, tag, inline, e = cp[1], cp[2], cp[4], s.hi
                inl = rename_line(inline, j, sites, conv, names).strip()
                body = [k for k in range(j + 1, e) if not blank(lines[k])]
                if kw == "next" and bullets and c.get("bullet", True) and bool(inl) != bool(body):
                    if inl:
                        put(lead + "· " + inl, j)
                    else:      # the block's first line joins the bullet (written by the loop: it may be a site itself)
                        bi = min(indent(lines[k]) for k in body)
                        shifts.append((body[0], e, indent(lines[j]) + 2 - bi))
                        merge.append(lead + "· ")
                        pos[s.idx] = (start, 1)
                        j += 1
                        continue
                else:
                    put(lead + kw + ((" " + tag) if tag else "") + " =>" + ((" " + inl) if inl else ""), j)
            pos[s.idx] = (start, len(out) - start)
            j += 1
            continue
        if s is not None:
            pos[s.idx] = (len(out), s.end - s.i)
            if s.end > j + 1:      # a kept multi-line intro: its lines as they are
                for k in range(j, s.end):
                    put(shifted(lines[k], k), k)
                j = s.end
                continue
        if drop_inner and INNER_RE.match(l):
            l = INNER_RE.sub(lambda m: m.group(1), l, count=1)
        if j in narrow:
            l = " " * indent(l) + "unhygienic " + l.lstrip(" ")
        if s is not None and s.kind == "case":
            m = re.match(r"^(.*?=>)(.*)$", l)
            l = m.group(1) + rename_line(m.group(2), j, sites, conv, names) if m else l

        elif s is None or s.kind == "seqrename":
            l = rename_line(l, j, sites, conv, names)
        put(l, j)    # (a kept rename_i / intro line: its names are its own binders; a kept `· rename_i` line too)
        j += 1
    return out, pos, src


def with_trace(out: list[str], s: Site, pos: dict) -> tuple[list[str], int] | None:
    """`out` (render's lines) with one `trace_state` right after site s; (lines, the trace's line index) or None."""
    if s.idx not in pos:
        return None
    p, n = pos[s.idx]
    o = list(out)
    if s.kind == "seqrename":
        o[p] = o[p].rstrip() + " <;> " + TRACE
        return o, p
    if s.kind in ("rename", "intro", "tacnames"):
        ref = o[p] if p < len(o) else o[-1]
        col = len(re.match(r"^\s*(?:·[ \t]+)?", ref).group(0))   # a tactic written after a bullet: the bullet's column
        return o[:p + n] + [" " * col + TRACE] + o[p + n:], p + n
    if s.kind == "brename":
        bl = BRENAME_RE.match(o[p])
        if bl:     # kept: the trace after it, at the bullet's column
            return o[:p + 1] + [" " * s.col + TRACE] + o[p + 1:], p + 1
        m = re.match(r"^(\s*·[ \t]+)(.*)$", o[p])
        if not m:
            return None
        return o[:p] + [m.group(1) + TRACE, " " * len(m.group(1)) + m.group(2)] + o[p + 1:], p
    cp = case_parts(o, p)
    if cp is None:
        return None
    if cp[5] == p + 1 and not cp[4].strip():     # tactics at the header's own column follow: the trace at that column
        return o[:p + 1] + [" " * cp[0] + TRACE] + o[p + 1:], p + 1
    blk, e, _n = U.case_block(o, p, True, True)
    return o[:p] + blk + o[e:], p + 1


# ------------------------------------------------------------------------------------------------------------------------------ copies
def build_file(statement: str, texts: list[str], attached: str = "") -> tuple[str, list]:
    """t4ind.build_file with fix (1): each copy `[private] theorem <Ns>.lraD4M<i>` (ctorsearch.renamed), self-references renamed,
    the attached combinators before it. Spans as t4ind.split_messages reads them (the anchor first)."""
    out, spans = [T4I.ANCHOR_TEXT, "\n"], []
    line = T4I.ANCHOR_TEXT.count("\n") + 1
    for i, t in enumerate(texts):
        r = CT.renamed(statement, i)
        if r is None or not t.startswith(statement):
            spans.append(None)
            continue
        body = CT.self_renamed(statement, t[len(statement):], i)
        copy = attached + (r + body).rstrip() + "\n\n"
        a = attached.count("\n")
        n = copy.count("\n")
        spans.append((line + a, line + n, statement.count("\n") - r.count("\n")))
        out.append(copy)
        line += n
    return "".join(out), spans


def make_compile_batch(statement: str, run, *, attached: str = "", stats: dict | None = None, log=None, per_file: int = 8):
    """compile_batch(texts) -> [None | messages with "decl_line"] on the post-step's run(text, version): one plain compile on the primary
    pin per file of at most per_file copies (a one-trace copy gets t4ind.quiet's `stop`)."""
    st = stats if stats is not None else {}
    for c in ("files", "copies", "no_anchor", "timeouts"):
        st.setdefault(c, 0)
    say = log or (lambda m: None)

    def compile_batch(texts: list[str], quiet: bool = True) -> list:
        res: list = [None] * len(texts)
        for a in range(0, len(texts), per_file):
            chunk = list(range(a, min(len(texts), a + per_file)))
            text, spans = build_file(statement, [T4I.quiet(texts[i]) if quiet else texts[i] for i in chunk], attached)
            if all(sp is None for sp in spans):
                continue
            r = run(text, None)
            st["files"] += 1
            st["copies"] += sum(sp is not None for sp in spans)
            if getattr(r, "timed_out", False):
                st["timeouts"] += 1
                say(f"{FAMILY}: a file of {len(chunk)} cop(ies) timed out")
                continue
            got = T4I.split_messages(getattr(r, "messages", None), spans)
            if got is None:
                st["no_anchor"] += 1
                say(f"{FAMILY}: a file printed no anchor: {str((getattr(r, 'errors', None) or ['?'])[0])[:160]}")
                continue
            for i, g in zip(chunk, got):
                res[i] = g
        return res
    return compile_batch


# ------------------------------------------------------------------------------------------------------------------------------ align
def expect_name(sites: list[Site], conv: dict, name: str, j: int) -> str:
    s = binder(sites, name, j)
    if s is None or s.idx not in conv:
        return name
    return conv[s.idx].get("map", {}).get(name, name)


def distinct(traces: list) -> list:
    """The goal displays of one trace line, each distinct one once, in first-print order: a term-mode `by` block that Lean elaborates
    again (error recovery in the rewritten copy, whose later uses still carry the old names) prints the same display twice."""
    out, seen = [], set()
    for t in traces or []:
        key = repr([(g.get("tag"), [tuple(h) for h in g.get("hyps", [])], g.get("target")) for g in (t or [])])
        if key not in seen:
            seen.add(key); out.append(t)
    return out


def align(tos: list, tvs: list, s: Site, sites: list[Site], conv: dict) -> tuple[dict | None, str]:
    """(fix 2) {old name: Lean's name} for site s from the incumbent's traces (tos) and the rewritten proof's (tvs) at the same place,
    or (None, why)."""
    tos, tvs = distinct(tos), distinct(tvs)
    if not tos or not tvs:
        return None, f"traces {len(tos)} / {len(tvs)}"
    n = min(len(tos), len(tvs))      # a linter that re-runs the tactics after the declaration (Mathlib's tactic analysis, e.g. its
    tos, tvs = tos[:n], tvs[:n]      # intro-merge suggestion for `intro` / `intro`) prints the trace again, later and with `✝` names
    want = s.bound()
    mp: dict = {}
    for to, tv in zip(tos, tvs):
        if not to or not tv or len(to) != len(tv):
            return None, "goal count"
        go, gv = to[0], tv[0]
        if len(go["hyps"]) != len(gv["hyps"]):
            return None, f"hyps {len(go['hyps'])} / {len(gv['hyps'])}"
        for (on, _), (vn, _) in zip(go["hyps"], gv["hyps"]):
            if on in want:
                if not NAME.fullmatch(vn) or mp.get(on, vn) != vn:
                    return None, f"site name {on} -> {vn}"
                mp[on] = vn
            elif "✝" in on:
                continue
            elif vn != expect_name(sites, conv, on, s.i):
                return None, f"context {on} -> {vn} (expected {expect_name(sites, conv, on, s.i)})"
    if not want <= set(mp):
        return None, f"names not in the context: {sorted(want - set(mp))}"
    return mp, ""


def capture(lines: list[str], s: Site, sites: list[Site], mp: dict) -> str | None:
    """A new name written in s's scope for something else before one of s's own renamed uses (module docstring, align), else None."""
    news = {v: k for k, v in mp.items() if k != v}
    if not news:
        return None
    first_other: dict = {}
    last_own = None
    for j in range(s.i if s.kind == "case" else s.end, s.hi):
        l = lines[j]
        if j == s.i:
            m = re.match(r"^.*?=>(.*)$", l)
            l = m.group(1) if m else ""
            off = len(lines[j]) - len(l)
        else:
            off = 0
        for m in IDENT.finditer(l):
            k = m.group(1)
            at = (j, off + m.start())
            if k in mp and k != mp[k] and binder(sites, k, j) is s:
                last_own = at
            if k in news and not (k in mp and binder(sites, k, j) is s) and k not in first_other:
                first_other[k] = at
    if last_own is None:
        return None
    for v, at in first_other.items():
        if at < last_own:
            return f"{v} (written at line {at[0]}) captured"
    return None


# ------------------------------------------------------------------------------------------------------------------------------ chain
def _errors(msgs) -> list[int]:
    """decl lines of the error messages of one copy (an unused-variable or linter warning is no error)."""
    out = []
    for m in msgs or []:
        if m.get("severity") == "error":
            ln = m.get("decl_line")
            if isinstance(ln, int):
                out.append(ln)
    return out


def probe_chain(head: str, lines: list[str], sites: list[Site], cb, *, top: bool, narrow: tuple = (), only: set | None = None,
                exclude: set | None = None, failed: list | None = None, risky: dict | None = None, log=None, stats: dict | None = None,
                low=None) -> dict:
    """Sites converted one after another (module docstring, chain): {site idx: {"map", "form"}} for the converted ones. A site that
    fails is kept (its idx appended to `failed`) and the chain goes on (later probes see it kept); `exclude`: sites kept unprobed;
    low(): True when the row's wall left is low (no more probes: the chain so far is checked); `risky`: the sites kept only by the
    capture check, with their maps (the textual check cannot tell a nested block's own name from a real capture: the check compile
    judges a chain with them)."""
    st = stats if stats is not None else {}
    say = log or (lambda d: None)
    fl = failed if failed is not None else []
    conv: dict = {}
    dl = lambda li: head.count("\n") + li + 1  # noqa: E731
    o_out, o_pos, _src = render(lines, sites, {}, top=False, drop_inner=False)
    for s in sites:
        if (only is not None and s.idx not in only) or s.idx >= MAX_SITES or (exclude and s.idx in exclude):
            continue
        if s.free:
            conv[s.idx] = {"map": {}, "form": "iterate"}
            continue
        if low is not None and low():
            say({"site": repr(s), "stop": "row wall low: no more probes"})
            st["low_stops"] = st.get("low_stops", 0) + 1
            break
        ot = with_trace(o_out, s, o_pos)
        vts = []
        for form in (("intros", "iterate") if s.kind == "intro" else ("iterate",)):
            trial = dict(conv)
            trial[s.idx] = {"map": {}, "form": form}
            v_out, v_pos, _src = render(lines, sites, trial, top=top, drop_inner=top, narrow=narrow)
            vts.append((form, with_trace(v_out, s, v_pos)))
        if ot is None or any(v is None for _, v in vts):
            say({"site": repr(s), "fail": "no trace position"})
            fl.append(s.idx)
            continue
        st["sites"] = st.get("sites", 0) + 1
        got = cb([head + "\n".join(ot[0])] + [head + "\n".join(v[0]) for _, v in vts])
        got = list(got or []) + [None] * 3
        tos = U.traces_at(got[0], dl(ot[1])) if got[0] is not None else []
        why = ""
        for k, (form, vt) in enumerate(vts, 1):
            tvs = U.traces_at(got[k], dl(vt[1])) if got[k] is not None else []
            mp, why = align(tos, tvs, s, sites, conv)
            if mp is None:
                continue
            cap = capture(lines, s, sites, mp)
            if cap:
                why = "capture: " + cap
                if risky is not None and s.idx not in risky:
                    risky[s.idx] = {"map": {a: b for a, b in mp.items() if a != b}, "form": form}
                continue
            conv[s.idx] = {"map": {a: b for a, b in mp.items() if a != b}, "form": form}
            st["verified"] = st.get("verified", 0) + 1
            say({"site": repr(s), "form": form, "map": conv[s.idx]["map"]})
            break
        else:
            say({"site": repr(s), "fail": why})
            fl.append(s.idx)
    return conv


def check(head: str, bodies: list[list[str]], cb) -> list:
    """One plain compile of every body (no trace): per body None (no reading) or its error lines (body line indices, 0-based)."""
    got = cb([head + "\n".join(b) for b in bodies], quiet=False)
    off = head.count("\n") + 1
    return [None if g is None else [ln - off for ln in _errors(g)] for g in got]


def blame(err_lines: list[int], src: list[int], sites: list[Site], conv: dict) -> Site | None:
    """The converted site whose scope holds the first error line (innermost), else None."""
    for el in sorted(err_lines):
        if not 0 <= el < len(src):
            continue
        j = src[el]
        best = None
        for s in sites:
            if s.idx in conv and s.lo <= j < s.hi and (best is None or s.i > best.i):
                best = s
        if best is not None:
            return best
    return None


def forms(lines: list[str], sites: list[Site], conv: dict, *, top: bool, narrow: tuple = ()) -> list[tuple[str, list[str], list[int]]]:
    """The chain's candidate bodies: (name, lines, src); with the converted `next` headers as bullets first (when any), then plain."""
    out, _p, src = render(lines, sites, conv, top=top, drop_inner=top, narrow=narrow)
    res = [("chain", out, src)]
    if any(s.kind == "case" and s.idx in conv and case_parts(lines, s.i)[1] == "next" for s in sites):
        b, _p, bsrc = render(lines, sites, conv, top=top, drop_inner=top, bullets=True, narrow=narrow)
        if b != out:
            res.insert(0, ("chain+bullets", b, bsrc))
    return res


def _cand(head: str, b: list[str], note: str) -> dict:
    body = "\n".join(b)
    return {"op": OP, "decl": head + body.rstrip() + "\n", "note": note, "tokens": count_tokens(body)}


def generate(proof: str, statement: str, cb, *, log=None, stats: dict | None = None, low=None) -> list[dict]:
    """The op's candidates on `proof` (module docstring): probe the top chain (and, when a site failed after earlier conversions, a
    second chain without the conversions before the first failure: an early rename can shift Lean's names for every later site),
    check and repair each in shared check compiles, else the narrow forms."""
    st = stats if stats is not None else {}
    say = log or (lambda d: None)
    hb = K.head_body(proof.rstrip(), statement)
    if hb is None:
        return []
    head, body = hb
    lines = body.split("\n")
    base = count_tokens(body)
    sites = find_sites(lines)
    inner = inner_lines(lines)
    out: list[dict] = []
    if top_ok(lines) and (sites or len(inner) >= 2 or (inner and U.has_top_unhyg(lines))):
        failed: list = []
        risky: dict = {}
        conv = probe_chain(head, lines, sites, cb, top=True, failed=failed, risky=risky, log=say, stats=st, low=low)
        chains = [("A", conv)]
        if risky:      # the capture-flagged sites converted too (their probes passed; only the textual capture check stopped them)
            chains.append(("R", {**conv, **risky}))
        if failed:
            first = min(sites[i].i for i in failed)
            pre = {i for i in conv if sites[i].i < first and not sites[i].free}
            if pre:
                say({"chain B": f"without {len(pre)} conversion(s) before line {first}"})
                chains.append(("B", probe_chain(head, lines, sites, cb, top=True, exclude=pre, log=say, stats=st, low=low)))
        out += check_and_repair(head, lines, sites, inner, chains, cb, base, log=say, stats=st)
    if not out and sites and not (low is not None and low()):
        out += narrow_forms(head, lines, sites, cb, base, log=say, stats=st, low=low)
    out.sort(key=lambda c: c["tokens"])
    seen, res = set(), []
    for c in out:
        if c["decl"] not in seen:
            seen.add(c["decl"]); res.append(c)
    return res[:MAX_CANDS]


def check_and_repair(head: str, lines: list[str], sites: list[Site], inner: list, chains: list, cb, base: int, *, log=None,
                     stats: dict | None = None) -> list[dict]:
    """Every chain's forms checked in one plain compile per round; a chain with a clean form is done (its clean forms proposed),
    else its innermost converted site holding the plain form's first error is kept and the chain re-checked (REPAIRS rounds)."""
    st = stats if stats is not None else {}
    say = log or (lambda d: None)
    live = [(n, dict(c)) for n, c in chains]
    out: list[dict] = []
    seen_conv: set = set()
    for rnd in range(REPAIRS):
        batch = []
        for n, conv in live:
            key = tuple(sorted((k, tuple(sorted(v.get("map", {}).items())), v.get("form")) for k, v in conv.items()))
            if key in seen_conv:
                continue
            seen_conv.add(key)
            top = needs_top(sites, conv, inner)
            for f in forms(lines, sites, conv, top=top):
                if count_tokens("\n".join(f[1])) < base:
                    batch.append((n, conv, top, f))
        if not batch:
            break
        chk = check(head, [f[1] for _n, _c, _t, f in batch], cb)
        st["checks"] = st.get("checks", 0) + 1
        say({"check": rnd, "forms": [f"{n}:{f[0]}:{len(c)}" for n, c, _t, f in batch], "errors": [e if e is None else e[:4] for e in chk]})
        nxt = []
        for n, conv in live:
            mine = [(t, f, e) for (n2, c2, t, f), e in zip(batch, chk) if n2 == n and c2 is conv]
            clean = [(t, f) for t, f, e in mine if e is not None and not e]
            for t, (fn, b, _src) in clean:
                out.append(_cand(head, b, f"{'top' if t else 'free'} {n} {fn}: {len(conv)} of {len(sites)} site(s)"
                                 + (f", {len(inner)} inner" if inner else "")))
            if clean or not mine:
                continue
            plain = [(f, e) for t, f, e in mine if f[0] == "chain" and e]
            if not plain:
                continue
            bl = blame(plain[0][1], plain[0][0][2], sites, conv)
            if bl is None:
                continue
            say({"repair": f"{n}: {bl!r}"})
            conv2 = {k: v for k, v in conv.items() if k != bl.idx}
            if conv2 or inner:
                nxt.append((n, conv2))
        live = nxt
        if not live:
            break
    return out


def split_groups(lines: list[str], sites: list[Site]) -> dict:
    """{split line: [case-site idx]}: the `case` / `next` headers that follow a split tactic (`induction` / `cases` / `rcases` /
    `match`) at the same indent, other sibling lines between them allowed (the split's goals are named in order)."""
    groups: dict = {}
    for s in sites:
        if s.kind != "case":
            continue
        d = indent(lines[s.i])
        j = s.i - 1
        while j > 0:
            l = lines[j]
            if blank(l) or indent(l) > d:
                j -= 1; continue
            if indent(l) < d:
                j = 0; break
            if SPLIT_RE.match(l) and not l.rstrip().endswith("with"):
                break
            j -= 1
        if j > 0:
            groups.setdefault(j, []).append(s.idx)
    return groups


def narrow_forms(head: str, lines: list[str], sites: list[Site], cb, base: int, *, log=None, stats=None, low=None) -> list[dict]:
    """(fix 3, narrow) per split: `unhygienic <split>` with its headers converted, names probed in that form; checked in one compile."""
    say = log or (lambda d: None)
    groups = split_groups(lines, sites)
    fs, notes = [], []
    union: dict = {}
    splits: list = []
    for sp, idxs in list(groups.items())[:NARROW_MAX]:
        conv = probe_chain(head, lines, sites, cb, top=False, narrow=(sp,), only=set(idxs), log=say, stats=stats, low=low)
        if set(idxs) - set(conv):
            say({"narrow": sp, "fail": f"{len(set(idxs) - set(conv))} header(s) not converted"})
            continue
        union.update(conv); splits.append(sp)
        for n, b, _src in forms(lines, sites, conv, top=False, narrow=(sp,)):
            if count_tokens("\n".join(b)) < base:
                fs.append(b); notes.append(f"narrow {n}: split line {sp}, {len(conv)} header(s)")
    if len(splits) >= 2:      # every converted split at once (names probed per split; the check compile decides)
        for n, b, _src in forms(lines, sites, union, top=False, narrow=tuple(splits)):
            if count_tokens("\n".join(b)) < base:
                fs.append(b); notes.append(f"narrow union {n}: {len(splits)} splits, {len(union)} header(s)")
    if not fs:
        return []
    chk = check(head, fs, cb)
    out = []
    for b, n, e in zip(fs, notes, chk):
        say({"narrow check": n, "errors": e if e is None else e[:4]})
        if e is not None and not e:
            out.append(_cand(head, b, n))
    return out


# ------------------------------------------------------------------------------------------------------------------------------ lane interface
def has_sites(proof: str, statement: str) -> bool:
    try:
        hb = K.head_body(proof.rstrip(), statement)
        if hb is None:
            return False
        lines = hb[1].split("\n")
        if not top_ok(lines) and not find_sites(lines):
            return False
        return bool(find_sites(lines)) or len(inner_lines(lines)) >= 2 or (bool(inner_lines(lines)) and U.has_top_unhyg(lines))
    except Exception:  # noqa: BLE001  (a body the parsers cannot read has no site)
        return False


def _low(bud, floor_s: float) -> bool:
    """The row's wall or compile budget left is low (query: no new probe)."""
    if bud.left_s() < floor_s:
        return True
    try:
        return int(bud.max) - int(bud.meter.compiles) < LOW_COMPILES
    except Exception:  # noqa: BLE001  (a budget without these fields: the wall alone)
        return False


def _key(proof: str, statement: str) -> str:
    return hashlib.sha256((statement + "\0" + proof.strip()).encode()).hexdigest()[:24]


def _attached(run) -> str:
    try:
        from harness import open_post as OPM
        return OPM.attached_in(getattr(run, "meter", None))
    except Exception:  # noqa: BLE001  (no file context: the copies go without)
        return ""


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    """The chain's probes and checks through `run` (charged; a budget stop propagates); {"v4u_for": key, "v4u": [candidates]}."""
    st = stats if stats is not None else {}
    key = _key(proof, statement)
    with _LOCK:
        if key in _CACHE:
            return dict(_CACHE[key])
    if not has_sites(proof, statement):
        return {}
    say = log or (lambda m: None)
    cs = (ctx or {}).get("compile_s")
    cb = make_compile_batch(statement, run, attached=_attached(run), stats=st.setdefault("batch", {}), log=say,
                            per_file=min(PER_FILE, T4I.per_file(cs)))
    bud = getattr(run, "budget", None)
    floor_s = max(LOW_MIN_S, LOW_MULT * float(cs or 0.0))
    low = (lambda: _low(bud, floor_s)) if bud is not None and hasattr(bud, "left_s") else None
    try:
        got = generate(proof, statement, cb, log=lambda d: say(f"{FAMILY}: {str(d)[:400]}"), stats=st, low=low)
    except Exception as e:  # noqa: BLE001
        if type(e).__name__ == "_Stop":
            raise
        say(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:300]}")
        got = []
    say(f"{FAMILY}: {len(got)} candidate(s); stats { {k: v for k, v in st.items()} }")
    res = {"v4u_for": key, "v4u": got}
    with _LOCK:
        if len(_CACHE) >= CACHE_MAX:
            _CACHE.clear()
        _CACHE[key] = dict(res)
    return res


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    c = ctx or {}
    if c.get("v4u_for") != _key(proof, statement):
        return []
    return [{"op": OP, "decl": x["decl"], "note": str(x.get("note", ""))[:160]} for x in (c.get("v4u") or [])
            if isinstance(x, dict) and x.get("decl")][:int(max_per_op or MAX_CANDS)]
