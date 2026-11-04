#!/usr/bin/env python3
"""t4ind: the open package's T4 `t4:induction` rewrite (harness/tools/t4_nameless.py, written before any final-row data) switched on in
the open post-step (harness/open_post.py, op "t4ind"). A wrapper: the rewrite, the probe and the name alignment are T4's; this module
adapts T4's probe to the post-step's charged compile, lets T4's parser and checks read more real proofs (pure widening and masking,
relaxed alignment and capture checks inside this module's calls only), and adds pure bullet-drop follow-ups so that one adoption can
carry "arms -> bullets -> no bullets".

    sites(proof, statement) -> bool                                            (pure)
    query(proof, statement, run, *, ctx=None, stats=None, log=None) -> dict    (T4's probe through `run`; cached per proof)
    candidates(proof, statement, *, exchange=None, ctx=None) -> [{"op", "decl", "note"}]   (pure)

  rewrite   `induction x ... with` / `cases x ... with` + `| tag names => tactics` alternatives -> the bare `induction x ...` /
            `cases x ...` + one `·` bullet per goal in Lean's goal order (the case tags the probe printed), each holding its
            alternative's tactics; the names the alternatives bound are renamed to the names Lean gave (under `unhygienic`: the narrow
            `unhygienic <tactic>` wrap, or bare inside an `unhygienic` region). T4 ops t4:induction (one site) and t4:all (every verified
            site of the proof under one top `unhygienic` line, T4's round 2). An alternative with no name used later needs no probe (its
            bare form, in the written order, is proposed as is).
  widening  (pure, before T4 reads the proof) a shared alternative `| a xs | b ys => R` is written as one alternative per tag, `| a xs => R`
            and `| b ys => R` (R copied: an inline tactic, or the indented block). Lean elaborates a shared alternative as R on each
            of its goals, so the widened proof is the same proof; T4's parser takes only one tag per alternative. Tokens are always
            counted against the proof as given, never the widened one.
  lifting   (pure, before widening) an inline alternative whose tactic continues on deeper lines is written as a block alternative:
            the head, the tactic on its own line two columns deeper than the `|`, the continuation lines shifted right by one common
            amount until they are deeper than the tactic (the same tactic sequence; T4 reads an inline alternative on one line only).
  masking   (pure, before T4 reads the proof; undone in every text T4 writes: the probe copies before they are compiled, the candidates)
            spellings T4's conservative parser misreads, so that a whole site is skipped, are hidden from it: the term
            `funext` / `ext` applied to an argument (`funext λx => ..`: T4's binder scan takes the tactic `funext x y` and reads the
            rest of the line as binders) and the key of a named argument (`(ih := ih ..)`: the key is the callee's parameter name, not
            a use of the local, so it is never renamed; T4 skips any name that has one). A key or a term head is written with the
            suffix MASK (an identifier T4 never renames) and the suffix is removed again. An explicit alternative `| @tag xs =>` (every
            field named, implicit ones included) is read by T4 as `| tag<ATMASK> xs =>` (its parser takes plain tags only); the case tag
            Lean prints for that goal is written the same way in the probe's goal displays, and the `@` comes back on unmasking.
  alignment T4's alignment of a goal under the original names with the goal after the nameless tactic compares each hypothesis type after
            renaming EVERY occurrence of a renamed name, bound variables included, so a site whose name also appears bound in another
            hypothesis (`k` renamed to `n` while `ha : ∀ (k : ℕ), ..` keeps its bound `k`) never verifies. Inside this module's
            calls (a thread-local switch; every other caller of T4 keeps T4's own check) the types are compared identifier by
            identifier: equal, the original name and the name Lean gave it, or one bound name with Lean's display suffix `_<n>` added
            or dropped (the pretty printer renames a bound `o` to `o_1` once a local `o` exists). T4's capture check (a name Lean gave
            that already occurs in the scope) is narrowed the same way to the occurrences up to the last renamed use (captures_relaxed),
            and a split whose `with` lists only Lean's first goals (the others stay goals for the tactics after it) is checked on
            those goals (site_maps_relaxed). Everything else in T4's checks is unchanged.
  probe     T4.probe (round 1: the proof with `trace_state` inside every alternative, one nameless copy per site; round 2: every verified
            site at once) with T4.PROBE_MAX_SITES raised to PROBE_MAX_SITES (the dialect pass's value), run only when an induction site
            has a name used later. Its compile_batch(texts) is adapted to the post-step's run(text, version): one plain compile on the
            primary pin per file, the file = an anchor theorem (it takes the declaration's modifiers and prints one known goal, which
            locates the file in Lean's line numbers) + one copy per text, the declaration renamed `lraD4M<i>`
            (harness/post/d4_measure.renamed); every message inside a copy's lines comes back with "decl_line" (its line in the text
            as given, 1-based), as T4's own batch compiler returns them. At most per_file(compile_s) copies per file and PROBE_FILES
            files per probe call (both rounds together); copies over the budget, a file that timed out or lost its anchor come back
            None (T4 then verifies nothing for them). In the goal displays every case tag is cut to its last component (a split inside
            the `mpr` case tags its goals `mpr.zero`, `mpr.succ`; T4 matches `zero`, `succ`). A round-1 copy gets Lean core's `stop`
            after its one trace (quiet): the rest of that tactic sequence, where the old names fail by design, is not elaborated, so a
            file stays under the command-line frontend's 100-error exit (maxErrors) that lost every later copy's trace; the copy's
            line numbers up to the trace are unchanged. The answer is cached per (statement, proof).
  probe plan T4's probed sites (its ranking, PROBE_MAX_SITES) with the induction sites first and cut to what fits in ONE probe file
            (probe_plan): round 1 never takes the second file, so round 2 (the union, t4:all) always has it. Sites left out are probed
            in the next pass, on the proof after the adoption. The union is proposed only when it rewrites at least one induction site
            (its other sites are T4's t4:intro / t4:rcases sites verified in the same probe).
  catch-all (pure, no probe; not T4's: T4 skips a split with a `_` alternative) a split whose last alternative is a one-line
            `| _ => R` and whose other alternatives bind no names -> the bare split, one `·` bullet per named alternative in the written
            order, then `all_goals R` (Lean core; R runs on every goal the catch-all took), and the same with those bullets dropped.
            Lean's goal order is not read: when the named goals do not come first in the written order the candidate does not compile
            and the gate rejects it (one reading).
  follow-up (pure) on each T4 output, the bullets T4 wrote (the lines it inserted that start with `·`): all of them dropped (their
            tactics then run unfocused, in goal order: each closes its own goal, so the next goal becomes the main one), and only the
            last of each sibling run dropped (drop_bullet: the bullet's block dedented to the bullet's column). Only follow-ups with fewer tokens
            are kept.
  order     the union (t4:all) first, then single sites (T4's order: fewest tokens first); per T4 output: all bullets dropped, the
            output itself, the last bullet dropped. Every candidate has fewer tokens than the proof given; at most MAX_CANDS.
Generic by construction: no row names, lemma names, proof text or tables; the tags, the goal order and the names come from Lean's own
trace of the row's own proof on its primary pin; the gate (every pin, paired re-reading, audit) decides adoption."""
from __future__ import annotations

import difflib, hashlib, re, sys, threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from harness.tools import t4_nameless as T4  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

OP = "t4ind"
T4_OPS = ("t4:induction", "t4:all")
PROBE_MAX_SITES = 32      # T4's sites per probe (its module default 12; the dialect pass uses 32)
PROBE_FILES = 2           # probe files per query (T4's round 1 and round 2 together)
PROBE_S = 210.0           # seconds of copies per probe file (d4_measure.MEASURE_S: the query's 300 s timeout leaves the imports room)
MAX_K = 24                # copies per probe file at most
DEFAULT_COPY_S = 15.0     # seconds per copy when the input's compile time is unknown
MAX_CANDS = 12
CACHE_MAX = 256
ANCHOR = "lraT4IAnchorHyp"
ANCHOR_TEXT = f"theorem lraT4IAnchor ({ANCHOR} : True) : True := by trace_state; exact {ANCHOR}\n"

_CACHE: dict = {}
_LOCK = threading.Lock()

MASK = "_lraT4m"           # (module docstring, "masking"); never written into a candidate
ATMASK = "_lraT4at"        # an explicit alternative `| @tag ..` read by T4 as `| tag<ATMASK> ..` (module docstring, "masking")
_AT_ALT = re.compile(r"^([ \t]*\|[ \t]*)@(" + T4.NAME + r")(?=[ \t])", re.M)
_AT_BACK = re.compile(r"(?<![\w'!?₀-₉.])([^\W\d][\w'!?₀-₉.]*?)" + ATMASK + r"(?![\w'!?₀-₉])")
_TERM_HEAD = re.compile(r"(?<![\w.'!?])(funext|ext)(?=[ \t]*(?:λ|fun(?![\w'!?])|\(|\$|<\||·))")
_NAMED_KEY = re.compile(r"(\([ \t]*)(" + T4.NAME + r")([ \t]*:=)")
_TLS = threading.local()
_ALT_HEAD = re.compile(r"^(?P<ind>[ \t]*)\|(?P<rest>.*?)=>(?P<rhs>.*)$")
_NAME_FULL = re.compile(T4.NAME)
_BULLET = re.compile(r"^(\s*)·(\s+)(\S.*)$")


# ------------------------------------------------------------------------------------------------------------------------------ widening
def _alt_parts(rest: str) -> list[list[str]] | None:
    """The tags + names of a shared alternative's head (`a xs | b ys`), or None when it is not one (one tag, a `_` tag, anything but
    plain names)."""
    if "|" not in rest or any(c in rest for c in "()[]{}⟨⟩:@.,"):
        return None
    parts = [p.split() for p in rest.split("|")]
    if len(parts) < 2 or any(not p for p in parts):
        return None
    for p in parts:
        if p[0] == "_" or not _NAME_FULL.fullmatch(p[0]) or not all(x == "_" or _NAME_FULL.fullmatch(x) for x in p[1:]):
            return None
    return parts


def widen(body: str) -> str:
    """The body with every shared alternative `| a xs | b ys => R` of an `induction` / `cases ... with` written as one alternative per
    tag (module docstring, "widening"); the body itself when there is none. Only alternatives T4's own parser would read (the head line
    of a `with` block: the line after it, or after a sibling alternative) are touched."""
    lines = body.split("\n")
    out, i, changed = [], 0, False
    in_with, with_col = False, -1
    while i < len(lines):
        ln = lines[i]
        s = ln.strip()
        ind = len(ln) - len(ln.lstrip(" \t"))
        if T4.IND_LINE.match(ln):
            in_with, with_col = True, ind
            out.append(ln); i += 1
            continue
        m = _ALT_HEAD.match(ln)
        if in_with and m and s.startswith("|") and ind >= with_col:
            j = i + 1
            while j < len(lines) and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip(" \t")) > ind):
                j += 1
            while j > i + 1 and not lines[j - 1].strip():
                j -= 1
            block = lines[i + 1:j]
            parts = _alt_parts(m.group("rest"))
            if parts is not None and "|" not in m.group("rhs") and "--" not in m.group("rest"):
                rhs = m.group("rhs")
                for p in parts:
                    out.append(f"{m.group('ind')}| {' '.join(p)} =>{rhs}")
                    out += block
                changed = True
            else:
                out.append(ln)
                out += block
            i = j
            continue
        if s and ind <= with_col:
            in_with = False
        out.append(ln); i += 1
    return "\n".join(out) if changed else body


def lift(body: str) -> str:
    """The body with every inline alternative of an `induction` / `cases ... with` whose tactic continues on deeper lines
    (`| t xs => simp only [a,` + `    b]`) written as a block alternative: the head `| t xs =>`, the tactic on the next line two columns
    deeper than the `|`, its continuation lines shifted right (all by the same amount) until they are deeper than that tactic (module
    docstring, "lifting"); the body itself when there is none. T4's parser takes an inline alternative on one line only."""
    lines = body.split("\n")
    out, i, changed = [], 0, False
    in_with, with_col = False, -1
    while i < len(lines):
        ln = lines[i]
        s = ln.strip()
        ind = len(ln) - len(ln.lstrip(" \t"))
        if T4.IND_LINE.match(ln):
            in_with, with_col = True, ind
            out.append(ln); i += 1
            continue
        m = T4.ALT_LINE.match(ln)
        if in_with and m and ind >= with_col and m.group("rhs") and "--" not in ln and "/-" not in ln:
            j = i + 1
            while j < len(lines) and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip(" \t")) > ind):
                j += 1
            while j > i + 1 and not lines[j - 1].strip():
                j -= 1
            cont = lines[i + 1:j]
            if cont and not any("--" in c or "/-" in c or "\t" in c for c in cont):
                col = ind + 2
                low = min(len(c) - len(c.lstrip(" ")) for c in cont if c.strip())
                d = max(0, col + 1 - low)
                head = ln[:ln.index("=>") + 2].rstrip()
                out += [head, " " * col + m.group("rhs")] + [(" " * d + c) if c.strip() else c for c in cont]
                changed = True
                i = j
                continue
        if s and ind <= with_col and not s.startswith("|"):
            in_with = False
        out.append(ln); i += 1
    return "\n".join(out) if changed else body


def mask(body: str) -> str:
    """(module docstring, "masking") the body with term heads `funext` / `ext` and named-argument keys suffixed MASK; the body itself
    when it already holds MASK (then nothing is masked)."""
    if MASK in body or ATMASK in body:
        return body
    body = _TERM_HEAD.sub(lambda m: m.group(1) + MASK, body)
    body = _AT_ALT.sub(lambda m: m.group(1) + m.group(2) + ATMASK, body)
    return _NAMED_KEY.sub(lambda m: m.group(1) + m.group(2) + MASK + m.group(3), body)


RMARK = "rename_i_lraT4r"   # a leading `rename_i` of an alternative (module docstring, "rename_i"); never written into a candidate
KMARK = "rename_i_lraT4k"   # any other `rename_i` inside an alternative
DMARK = "rename_i_lraT4d"   # a leading `rename_i` resolved by the probe: the line is dropped
_MARKS = (RMARK, KMARK, DMARK)
_RENAME_LINE = re.compile(r"^([ \t]*)rename_i((?:[ \t]+(?:" + T4.NAME + r"|_))+)[ \t]*$")
_NAMED_INTRO = re.compile(r"^[ \t]*intros?(?:[ \t]+" + T4.NAME + r")+[ \t]*$")
_RENAME_WORD = re.compile(r"(?<![\w'!?₀-₉.])rename_i(?![\w'!?₀-₉])")
_DROP_LINE = re.compile(r"^([ \t]*)(·[ \t]+)?" + DMARK + r"(?![\w'!?₀-₉])[^\n]*$")


def _drop_resolved(text: str, probe: bool) -> str:
    """The DMARK lines (module docstring, "rename_i") dropped; one that opens a bullet hands the bullet to the next line of its block.
    probe: each written `skip` instead (`· skip` for a bullet line), so that the copy keeps its line numbers. A bullet line with no
    next line in its block is written back as `rename_i` (the gate then judges the candidate)."""
    lines = text.split("\n")
    out, i = [], 0
    while i < len(lines):
        m = _DROP_LINE.match(lines[i])
        if not m:
            out.append(lines[i]); i += 1
            continue
        if probe:
            out.append(m.group(1) + (m.group(2) or "") + "skip"); i += 1
            continue
        if not m.group(2):
            i += 1
            continue
        j = i + 1
        while j < len(lines) and not lines[j].strip():
            j += 1
        col = len(m.group(1)) + len(m.group(2))
        if j < len(lines) and len(lines[j]) - len(lines[j].lstrip(" ")) == col:
            out.append(m.group(1) + m.group(2) + lines[j].lstrip(" "))
            i = j + 1
            continue
        out.append(lines[i].replace(DMARK, "rename_i")); i += 1
    return "\n".join(out)


def _alternatives(lines: list[str]):
    """[(head line, end line, inline)] of every alternative of every `induction` / `cases ... with` block (T4's line shapes)."""
    out = []
    for i, ln in enumerate(lines):
        if not T4.IND_LINE.match(ln):
            continue
        c = len(ln) - len(ln.lstrip(" \t"))
        j, a = i + 1, None
        while j < len(lines):
            if not lines[j].strip():
                j += 1
                continue
            ind = len(lines[j]) - len(lines[j].lstrip(" \t"))
            m = T4.ALT_LINE.match(lines[j])
            if a is None:
                if not m or ind < c:
                    break
                a = ind
            if ind < a or (ind == a and not m) or ind > a:
                break
            k = j + 1
            while k < len(lines) and (not lines[k].strip() or len(lines[k]) - len(lines[k].lstrip(" \t")) > a):
                k += 1
            out.append((j, k, bool(m.group("rhs"))))
            j = k
    return out


def mark_renames(body: str) -> str:
    """(module docstring, "rename_i") the body with the `rename_i` lines inside alternatives marked: a block alternative's leading one
    (preceded only by `intro` / `intros` lines of plain names) written RMARK, any other KMARK; the body itself when there is none."""
    lines = body.split("\n")
    alts = _alternatives(lines)
    lead = set()
    for h, e, inline in alts:
        if inline:
            continue
        for x in range(h + 1, e):
            if not lines[x].strip():
                continue
            if _NAMED_INTRO.match(lines[x]):
                continue
            if _RENAME_LINE.match(lines[x]):
                lead.add(x)
            break
    inside = {x for h, e, _ in alts for x in range(h + 1, e)}
    changed = False
    for x in sorted(inside):
        if x in lead:
            lines[x] = _RENAME_WORD.sub(RMARK, lines[x], count=1)
            changed = True
        elif _RENAME_WORD.search(lines[x]) and "--" not in lines[x]:
            lines[x] = _RENAME_WORD.sub(KMARK, lines[x])
            changed = True
    return "\n".join(lines) if changed else body


def unmask(text: str, probe: bool = False) -> str:
    """The text with every mask undone: a resolved leading `rename_i` (DMARK) line dropped (probe: written `skip`, so that the copy
    keeps its line numbers), the other marks back to `rename_i`, the `@` of explicit alternatives back, MASK removed."""
    if DMARK in text:
        text = _drop_resolved(text, probe).replace(DMARK, "rename_i")
    text = text.replace(RMARK, "rename_i").replace(KMARK, "rename_i")
    return _AT_BACK.sub(lambda m: "@" + m.group(1), text).replace(MASK, "")


def at_tags(src: str) -> dict:
    """{Lean's case tag: the tag T4 reads} for the explicit alternatives masked in `src`."""
    return {m.group(1): m.group(1) + ATMASK for m in _AT_BACK.finditer(src)}


def _source(proof: str, statement: str) -> str | None:
    """The proof T4 reads: the proof given, lifted, widened and masked (module docstring, "lifting", "widening", "masking"); None when it does not start
    with the statement."""
    body = split_declaration(proof, statement)
    if body is None or MASK in body or ATMASK in body or any(k in body for k in _MARKS):
        return None
    return proof[:len(proof) - len(body)] + mask(mark_renames(widen(lift(body))))


def _ids(s: str) -> list[str]:
    """s split at T4's pretty-printed identifiers: [text, identifier, text, ..., text]."""
    out, p = [], 0
    for m in T4._PPID.finditer(s):
        out += [s[p:m.start(1)], m.group(1)]
        p = m.end(1)
    return out + [s[p:]]


_DISPLAY_SUFFIX = re.compile(r"_\d+$")


def same_upto(old: str, new: str, full: dict) -> bool:
    """(module docstring, "alignment") `new` is `old` with some identifiers renamed by `full` (each occurrence kept or renamed), or
    with a bound variable's display suffix changed (Lean's pretty printer writes a bound `o` as `o_1` while a local `o` is in scope,
    and back)."""
    a, b = _ids(T4._norm(old)), _ids(T4._norm(new))
    if len(a) != len(b):
        return False
    for i, (x, y) in enumerate(zip(a, b)):
        if x == y:
            continue
        if i % 2 == 0:
            return False
        if full.get(x) != y and _DISPLAY_SUFFIX.sub("", x) != _DISPLAY_SUFFIX.sub("", y):
            return False
    return True


def align_relaxed(O: dict, N: dict, names, used):
    """T4.align (harness/tools/t4_nameless.py) with the type comparison of same_upto; everything else as T4's."""
    if len(O["hyps"]) != len(N["hyps"]):
        return None
    names, used = set(names), set(used)
    full, rename, fresh = {}, {}, []
    for (on, _), (nn, _) in zip(O["hyps"], N["hyps"]):
        if on != nn:
            if not T4._inacc(on) and on not in names:
                return None
            if T4._inacc(nn):
                if on in used:
                    return None
            else:
                if not T4._valid(nn):
                    return None
                fresh.append(nn)
            if on in full:
                return None
            full[on] = nn
        if on in used:
            rename[on] = nn
    if not used <= set(rename):
        return None
    if len(set(rename.values())) != len(rename):
        return None
    for (_, ot), (_, nt) in zip(O["hyps"], N["hyps"]):
        if not same_upto(ot, nt, full):
            return None
    if not same_upto(O["target"], N["target"], full):
        return None
    return rename, fresh


def captures_relaxed(P, st, uid: str, rename: dict, fresh: list) -> bool:
    """T4._captures (a new name occurring anywhere in the unit's scope is a capture) narrowed to the occurrences up to the end of the
    line of the last renamed use: a later occurrence names a binding made after the renamed uses (a nameless split or intro inside
    the scope shadows it), which the renaming does not reach. A wrong call costs one failed reading, never the row (the gate compiles
    every candidate)."""
    u = T4._unit(st, uid)
    if u is None:
        return True
    hits = [f for f in fresh if f not in rename and f in T4._words(P.B, u["s"], u["e"])]
    if not hits:
        return False
    uses = [i for old in rename for i in (T4._refs(P.B, P.S, u["s"], u["e"], old) or [])]
    if not uses:
        return True
    eol = P.B.body.find("\n", max(uses))
    eol = len(P.B.body) if eol < 0 else eol
    for f in hits:
        for m in re.finditer(T4._ID_L + re.escape(f) + T4._ID_R, P.B.body[:u["e"]]):
            if m.start() >= u["s"] and not P.B.mask[m.start()] and m.start() <= eol:
                return True
    return False


def _align_switch(O, N, names, used):
    if getattr(_TLS, "relaxed", False):
        return align_relaxed(O, N, names, used)
    return _align_switch.t4(O, N, names, used)


def _captures_switch(P, st, uid, rename, fresh):
    if getattr(_TLS, "relaxed", False):
        return captures_relaxed(P, st, uid, rename, fresh)
    return _captures_switch.t4(P, st, uid, rename, fresh)


def site_maps_relaxed(P, st, orig: dict, goals):
    """T4.site_maps, and for a split whose `with` lists only some alternatives (Lean leaves the others as goals for the tactics after
    it): when the listed tags are exactly Lean's first goals, T4's own check on those goals (their bullets come first, the tactics
    after the split keep the other goals in Lean's order)."""
    t4 = _site_maps_switch.t4
    if st.kind == "induction" and goals and len(goals) > len(st.alts):
        k = len(st.alts)
        if sorted(str(g.get("tag")) for g in goals[:k]) == sorted(a["tag"] for a in st.alts):
            goals = goals[:k]
    r = t4(P, st, orig, goals)
    if r is None or st.kind != "induction":
        return r
    return resolve_renames(P, st, orig, goals, r)


def _lead_rename(P, u) -> tuple[int, list[str]] | None:
    """(offset, names) of the RMARK line in the unit's span, or None."""
    for m in re.finditer(T4._ID_L + re.escape(RMARK) + T4._ID_R, P.B.body[u["s"]:u["e"]]):
        i = u["s"] + m.start()
        if P.B.mask[i]:
            continue
        eol = P.B.body.find("\n", i)
        return i, P.B.body[i + len(RMARK):(len(P.B.body) if eol < 0 else eol)].split()
    return None


def resolve_renames(P, st, orig: dict, goals: list, r):
    """(module docstring, "rename_i") site_maps' answer with every alternative's leading `rename_i x y` resolved: the names it gives are
    the last inaccessible hypotheses of the alternative's goal under the original names (the trace at its first line), which the
    nameless split names (the same positions in its trace); their uses are renamed to those names and the line itself is dropped
    (RMARK -> DMARK). None when a name cannot be resolved (fewer inaccessible hypotheses, an inaccessible or invalid new name, a use
    that is not a plain reference, a clash, a capture)."""
    units, order = r
    out = dict(units)
    for u in st.units:
        lr = _lead_rename(P, u)
        if lr is None:
            continue
        _, names = lr
        tag = u["id"].split(":", 1)[1]
        O = (orig.get(u["id"]) or [None])[0]
        g = next((x for x in goals if str(x.get("tag")) == tag), None)
        if not O or not g or len(O["hyps"]) != len(g["hyps"]):
            return None
        inacc = [i for i, (n, _) in enumerate(O["hyps"]) if T4._inacc(n)]
        if len(inacc) < len(names):
            return None
        mp = dict(out.get(u["id"]) or {})
        fresh = []
        for name, pos in zip(names, inacc[len(inacc) - len(names):]):
            if name == "_":
                continue
            nn = g["hyps"][pos][0]
            if T4._inacc(nn) or not T4._valid(nn) or mp.get(name, nn) != nn or nn in fresh \
                    or T4._refs(P.B, P.S, u["s"], u["e"], name) is None:
                return None
            mp[name] = nn
            fresh.append(nn)
        mp[RMARK] = DMARK
        if _captures_switch(P, st, u["id"], mp, fresh):
            return None
        out[u["id"]] = mp
    return out, order


def _scopes_switch(B, S, site):
    ok = _scopes_switch.t4(B, S, site)
    if not ok or not getattr(_TLS, "relaxed", False):
        return ok
    marked = any(k in T4._words(B, u["s"], u["e"]) for u in site.units for k in (RMARK, KMARK))
    if site.kind != "induction":
        return not marked          # T4's rule (a scope that uses `rename_i`) for every other site
    if any(RMARK in T4._words(B, u["s"], u["e"]) for u in site.units):
        site.used.add(RMARK)       # a leading `rename_i` needs the probe's names: never the bare form
    return True


def _site_maps_switch(P, st, orig, goals):
    if getattr(_TLS, "relaxed", False):
        return site_maps_relaxed(P, st, orig, goals)
    return _site_maps_switch.t4(P, st, orig, goals)


def probe_plan(ranked: list, k: int | None) -> list:
    """(module docstring, "probe plan") T4's probed sites (its ranking: most tokens saved first) with the induction sites first, then
    the others in T4's order, cut so that round 1 fits in ONE probe file of k copies (the original-names copy + one copy per form;
    a site that does not fit is skipped and a later, smaller one may still fit); at least the first site. k None: reordered only."""
    order = [s for s in ranked if s.kind == "induction"] + [s for s in ranked if s.kind != "induction"]
    if not k:
        return order
    out, n = [], 1
    for s in order:
        c = max(1, len(s.forms))
        if out and n + c > k:
            continue
        out.append(s)
        n += c
    return out


def _probe_sites_switch(P):
    if getattr(_TLS, "relaxed", False):
        return probe_plan(_probe_sites_switch.t4(P), getattr(_TLS, "k", None))
    return _probe_sites_switch.t4(P)


if not getattr(T4.align, "_t4ind_switch", False):   # installed once per process; T4's own checks for every other caller
    _align_switch.t4, _captures_switch.t4, _site_maps_switch.t4 = T4.align, T4._captures, T4.site_maps
    _probe_sites_switch.t4, _scopes_switch.t4 = T4._probe_sites, T4._scopes
    _align_switch._t4ind_switch = _captures_switch._t4ind_switch = _site_maps_switch._t4ind_switch = True
    _probe_sites_switch._t4ind_switch = _scopes_switch._t4ind_switch = True
    T4.align, T4._captures, T4.site_maps, T4._probe_sites = _align_switch, _captures_switch, _site_maps_switch, _probe_sites_switch
    T4._scopes = _scopes_switch


class _relaxed:
    def __init__(self, k: int | None = None):
        self.k = k

    def __enter__(self):
        self.prev = getattr(_TLS, "relaxed", False), getattr(_TLS, "k", None)
        _TLS.relaxed, _TLS.k = True, self.k

    def __exit__(self, *exc):
        _TLS.relaxed, _TLS.k = self.prev
        return False


def _ind_sites(src: str, statement: str) -> list:
    with _relaxed(getattr(_TLS, "k", None)):
        P = T4.Prep(src, statement)
    if not P.ok:
        return []
    return [s for s in P.sites if s.kind == "induction"]


_CATCH_ALL = re.compile(r"^(?P<ind>[ \t]*)\|[ \t]*_[ \t]*=>[ \t]*(?P<rhs>\S.*?)[ \t]*$")


def catchall_bodies(body: str) -> list[tuple[str, str]]:
    """(module docstring, "catch-all") [(tag, body)]: per split whose last alternative is a one-line `| _ => R` and whose other
    alternatives bind no names (`| tag =>`, `| tag _ =>`), the bare split, one `·` bullet per named alternative in the written order,
    then `all_goals R`; and the same with those bullets dropped. Pure (no probe): the gate reads Lean's goal order."""
    lines = body.split("\n")
    out = []
    for i, ln in enumerate(lines):
        m = T4.IND_LINE.match(ln)
        if not m or "--" in ln:
            continue
        c = len(ln) - len(ln.lstrip(" \t"))
        col = len(m.group("lead"))
        alts, j, a, catch = [], i + 1, None, None
        while j < len(lines):
            if not lines[j].strip():
                j += 1
                continue
            ind = len(lines[j]) - len(lines[j].lstrip(" \t"))
            if a is None:
                a = ind
            if ind != a or not lines[j].lstrip().startswith("|") or ind < c:
                break
            k = j + 1
            while k < len(lines) and (not lines[k].strip() or len(lines[k]) - len(lines[k].lstrip(" \t")) > a):
                k += 1
            while k > j + 1 and not lines[k - 1].strip():
                k -= 1
            cm = _CATCH_ALL.match(lines[j])
            am = T4.ALT_LINE.match(lines[j])
            if cm and k == j + 1:
                catch, j = cm.group("rhs"), k
                break
            if not am or am.group("tag") == "_" or any(x != "_" for x in am.group("names").split()) or "--" in lines[j]:
                break
            if bool(am.group("rhs")) == (k > j + 1):
                break                     # inline with continuation lines, or an empty block
            alts.append((am.group("rhs"), lines[j + 1:k]))
            j = k
        if catch is None or not alts or "|" in catch or "--" in catch:
            continue
        if j < len(lines) and lines[j].strip() and len(lines[j]) - len(lines[j].lstrip(" \t")) >= a \
                and lines[j].lstrip().startswith("|"):
            continue                       # an alternative after the catch-all
        new, bl = [m.group("lead") + m.group("head") + " " + m.group("rest").strip()], []
        for rhs, blk in alts:
            bl.append(i + len(new))
            if rhs:
                new.append(" " * col + "· " + rhs)
            else:
                blk = T4._dedent_to(blk, col + 2)
                f = next((x for x, y in enumerate(blk) if y.strip()), None)
                if f is None or blk[f].lstrip().startswith("--"):
                    break
                new += blk[:f] + [" " * col + "· " + blk[f].lstrip()] + blk[f + 1:]
        else:
            new.append(" " * col + "all_goals " + catch)
            nl = lines[:i] + new + lines[j:]
            out.append(("", "\n".join(nl)))
            cur = list(nl)
            for x in sorted(bl, reverse=True):
                cur = drop_bullet(cur, x) or cur
            if cur != nl:
                out.append(("bulletdrop", "\n".join(cur)))
    return out


def sites(proof: str, statement: str) -> bool:
    """Does the proof have an `induction` / `cases ... with` site T4 can rewrite, or a catch-all split (pure)?"""
    try:
        src = _source(proof, statement)
        if src is None or not T4.AVAILABLE:
            return False
        body = split_declaration(proof, statement)
        return bool(_ind_sites(src, statement)) or bool(body is not None and catchall_bodies(body))
    except Exception:  # noqa: BLE001  (a proof the parsers cannot read has no site)
        return False


# ------------------------------------------------------------------------------------------------------------------------------ probe
def per_file(compile_s) -> int:
    """Copies per probe file: a copy costs about half a standalone compile (the imports are loaded once; d4_measure.budget)."""
    per = max(1.0, float(compile_s) / 2.0) if isinstance(compile_s, (int, float)) and compile_s > 0 else DEFAULT_COPY_S
    return max(2, min(MAX_K, int(PROBE_S / per)))


def build_file(statement: str, texts: list[str]) -> tuple[str, list]:
    """(the file text, per text (first line, end line, line delta) in the file text, 0-based, or None): the anchor, then one copy per
    text, the statement written as `theorem lraD4M<i> ...` (d4_measure.renamed); delta = the statement's line count minus the renamed
    one's (a docstring or attribute line before the keyword is dropped), so a copy's line + delta is the text's own line."""
    out, spans = [ANCHOR_TEXT, "\n"], []
    line = ANCHOR_TEXT.count("\n") + 1
    for i, t in enumerate(texts):
        r = MS.renamed(statement, i)
        if r is None or not t.startswith(statement):
            spans.append(None)
            continue
        copy = (r + t[len(statement):]).rstrip() + "\n\n"
        n = copy.count("\n")
        spans.append((line, line + n, statement.count("\n") - r.count("\n")))
        out.append(copy)
        line += n
    return "".join(out), spans


def _mline(m) -> int | None:
    v = (m.get("pos") or {}).get("line") if isinstance(m, dict) else None
    return int(v) if isinstance(v, int) else None


_CASE_LINE = re.compile(r"(?m)^case [^\n]*?\.([^.\s]+)[ \t]*$")


_CASE_ANY = re.compile(r"(?m)^case ([^\s.]+)[ \t]*$")


def short_tags(data, tags: dict | None = None) -> str:
    """A goal display with every case tag cut to its last component (`case mpr.succ` -> `case succ`): a goal split inside a case of an
    enclosing split is tagged with that case's tag in front, and T4 matches the alternative's own tag (module docstring, "probe");
    then a tag in `tags` (at_tags) is written as T4 reads it."""
    out = _CASE_LINE.sub(lambda m: "case " + m.group(1), str(data))
    if tags:
        out = _CASE_ANY.sub(lambda m: "case " + tags.get(m.group(1), m.group(1)), out)
    return out


def split_messages(messages, spans: list, tags: dict | None = None) -> list | None:
    """Per span the messages inside its lines with "decl_line" (1-based, the text's own line), from a compile of build_file's text after
    an unknown prefix: the anchor's goal message gives the file line of the text's first line. None when the anchor did not print."""
    msgs = [m for m in (messages or []) if isinstance(m, dict)]
    a = next((_mline(m) for m in msgs if m.get("severity") == "information" and ANCHOR in K.msg_text(m) and _mline(m) is not None), None)
    if a is None:
        return None
    out = []
    for sp in spans:
        if sp is None:
            out.append(None)
            continue
        s, e, delta = sp
        lo, hi = a + s, a + e
        out.append([dict(m, decl_line=_mline(m) - lo + 1 + delta, **({"data": short_tags(m.get("data"), tags)} if m.get("severity") == "information" else {}))
                    for m in msgs if _mline(m) is not None and lo <= _mline(m) < hi])
    return out


_TRACE_LINE = re.compile(r"^([ \t]*)" + re.escape(T4.TRACE) + r"[ \t]*$")


def quiet(text: str) -> str:
    """(module docstring, "probe") a probe text with exactly one `trace_state`, on a line of its own (a round-1 copy: the nameless tactic,
    then its trace) gets Lean core's `stop` on the next line, at the trace's column, when a tactic of the same sequence follows: `stop`
    takes the rest of that sequence unelaborated (its goals closed by `sorry`), so the later uses of the old names, which fail in
    such a copy by design, add no errors; Lean's command-line frontend exits at its 100th error (option maxErrors), which lost the
    traces of every later copy of the file. The trace itself prints before `stop`, on the same line as before. Any other text
    (the original-names copy with several traces, round 2) is returned as is."""
    if len(re.findall(r"(?<![\w'.])" + re.escape(T4.TRACE) + r"(?![\w'!?])", text)) != 1:
        return text      # several traces (inline ones included): a line added after the first would move the others
    lines = text.split("\n")
    hits = [i for i, ln in enumerate(lines) if _TRACE_LINE.match(ln)]
    if len(hits) != 1:
        return text
    i = hits[0]
    col = len(_TRACE_LINE.match(lines[i]).group(1))
    j = i + 1
    while j < len(lines) and not lines[j].strip():
        j += 1
    if j >= len(lines) or len(lines[j]) - len(lines[j].lstrip(" \t")) != col \
            or lines[j].lstrip().startswith(("|", "--", "/-", "<;>", ")", "]", "}", "⟩", ",", ":=", "=>")):
        return text      # not a next tactic of the same sequence (a `·` bullet is one: `stop` takes it, checked on Lean)
    return "\n".join(lines[:i + 1] + [lines[i][:col] + "stop"] + lines[i + 1:])


def make_compile_batch(statement: str, run, *, compile_s=None, files: int = PROBE_FILES, stats: dict | None = None, log=None,
                       tags: dict | None = None):
    """T4's compile_batch(texts) -> [None | messages with "decl_line"] on the post-step's run(text, version) (module docstring, "probe").
    The file budget is shared by every call of the returned function."""
    st = stats if stats is not None else {}
    for c in ("files", "copies", "copies_skipped", "no_anchor", "timeouts"):
        st.setdefault(c, 0)
    left = [int(files)]
    k = per_file(compile_s)
    say = log or (lambda m: None)

    def compile_batch(texts: list[str]) -> list:
        out: list = [None] * len(texts)
        for a in range(0, len(texts), k):
            chunk = list(range(a, min(len(texts), a + k)))
            text, spans = build_file(statement, [quiet(unmask(texts[i], probe=True)) for i in chunk])
            if all(sp is None for sp in spans):
                continue
            if left[0] <= 0:
                st["copies_skipped"] += sum(sp is not None for sp in spans)
                continue
            left[0] -= 1
            r = run(text, None)
            st["files"] += 1
            st["copies"] += sum(sp is not None for sp in spans)
            if getattr(r, "timed_out", False):
                st["timeouts"] += 1
                say(f"t4ind: a probe file of {len(chunk)} cop(ies) timed out")
                continue
            got = split_messages(getattr(r, "messages", None), spans, tags)
            if got is None:
                st["no_anchor"] += 1
                say(f"t4ind: a probe file printed no anchor: {str((getattr(r, 'errors', None) or ['?'])[0])[:160]}")
                continue
            for i, g in zip(chunk, got):
                out[i] = g
        return out
    return compile_batch


def _key(proof: str, statement: str) -> str:
    return hashlib.sha256((statement + "\0" + proof.strip()).encode()).hexdigest()[:24]


def query(proof: str, statement: str, run, *, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict:
    """T4's probe of the (widened) proof through `run` (module docstring, "probe"): {"t4_probe": ..., "t4_probe_for": key of the
    widened proof, "t4ind_src": the widened proof}, or {} (no site, or no induction site with a name used later: nothing to ask).
    Cached per (statement, proof); `run` raises the caller's budget stop, which propagates."""
    ctx = ctx or {}
    st = stats if stats is not None else {}
    key = _key(proof, statement)
    with _LOCK:
        if key in _CACHE:
            st["cached"] = st.get("cached", 0) + 1
            return dict(_CACHE[key])
    src = _source(proof, statement)
    got: dict = {}
    if src is not None and any(s.used for s in _ind_sites(src, statement)):
        T4.PROBE_MAX_SITES = max(int(T4.PROBE_MAX_SITES), PROBE_MAX_SITES)
        cb = make_compile_batch(statement, run, compile_s=ctx.get("compile_s"), stats=st.setdefault("batch", {}), log=log,
                                tags=at_tags(src))
        with _relaxed(per_file(ctx.get("compile_s"))):
            pr = T4.probe(src, statement, cb, stats=st.setdefault("probe", {}), log=log) or {}
        if pr.get("t4_probe"):
            got = dict(pr, t4ind_src=src)
    with _LOCK:
        if len(_CACHE) >= CACHE_MAX:
            _CACHE.clear()
        _CACHE[key] = dict(got)
    return got


# ------------------------------------------------------------------------------------------------------------------------------ candidates
def new_bullets(old_body: str, new_body: str) -> list[int]:
    """Lines of new_body (0-based) that start with `·` and are not lines of old_body kept in place (difflib's inserted / replaced
    lines): the bullets the rewrite wrote."""
    a, b = old_body.split("\n"), new_body.split("\n")
    out = []
    for tag, _i1, _i2, j1, j2 in difflib.SequenceMatcher(None, a, b, autojunk=False).get_opcodes():
        if tag in ("insert", "replace"):
            out += [j for j in range(j1, j2) if _BULLET.match(b[j])]
    return out


def drop_bullet(lines: list[str], i: int) -> list[str] | None:
    """Line i `<d>· <tactic>` written `<d><tactic>`, the lines of its block (deeper than the bullet) dedented by the same amount, so the
    block's tactics stay in one column with the first (Lean reads a tactic sequence by column: a line one column deeper would continue
    the previous tactic). The line count is kept. None when line i is not a bullet."""
    from harness import dialect as D
    m = _BULLET.match(lines[i])
    if not m:
        return None
    d = len(m.group(1))
    delta = 1 + len(m.group(2))
    e = D.extent(lines, i)
    return lines[:i] + [" " * d + m.group(3)] + D.dedent(lines[i + 1:e], delta, d) + lines[e:]


def follow_ups(old_body: str, new_body: str) -> list[tuple[str, str]]:
    """[(tag, body)]: the new bullets all dropped, and the last of each sibling run dropped (module docstring, "follow-up")."""
    from harness import dialect as D
    bl = new_bullets(old_body, new_body)
    if not bl:
        return []
    lines = new_body.split("\n")
    out = []
    cur = list(lines)
    for i in sorted(bl, reverse=True):   # drop_bullet keeps the line count: indices stay valid
        cur = drop_bullet(cur, i) or cur
    if cur != lines:
        out.append(("bulletdrop", "\n".join(cur)))
    groups = D.sibling_groups(lines, sorted(bl))
    cur = list(lines)
    for g in reversed(groups):
        cur = drop_bullet(cur, g[-1]) or cur
    if cur != lines and "\n".join(cur) not in [x for _, x in out]:
        out.append(("bulletdrop-last", "\n".join(cur)))
    return out


def candidates(proof: str, statement: str, *, exchange: float | None = None, ctx: dict | None = None) -> list[dict]:
    """[{"op", "decl", "note"}] (module docstring, "order"); pure. ctx: query()'s answer for this proof (absent: only the bare forms of
    sites whose names are unused)."""
    ctx = ctx or {}
    body0 = split_declaration(proof, statement)
    src = _source(proof, statement)
    if body0 is None or src is None or not T4.AVAILABLE:
        return []
    if ctx.get("t4ind_src") not in (None, src):
        ctx = {}
    head = proof[:len(proof) - len(body0)]
    t0 = count_tokens(body0)
    c4: dict = {"ops": list(T4_OPS)}
    if ctx.get("t4_probe") and ctx.get("t4_probe_for") == T4.proof_key(src):
        c4.update(t4_probe=ctx["t4_probe"], t4_probe_for=ctx["t4_probe_for"])
    with _relaxed():
        base = T4.candidates(src, statement, ctx=c4)
    n_ind = len(_ind_sites(src, statement))
    base = [c for c in base if c["op"] == "t4:all" and len(_ind_sites(c["decl"], statement)) < n_ind] \
        + [c for c in base if c["op"] != "t4:all"]
    src_body = unmask(split_declaration(src, statement))
    out, seen = [], {body0.rstrip()}
    for c in base:
        b = split_declaration(c["decl"], statement)
        if b is None:
            continue
        b = unmask(b)
        fol = follow_ups(src_body, b)
        tagged = fol[:1] + [("", b)] + fol[1:]
        for tag, nb in tagged:
            nb = nb.rstrip()
            if nb in seen or count_tokens(nb) >= t0 or re.match(r"[ \t]*\n", nb):
                continue
            seen.add(nb)
            op = "t4ind:" + c["op"].split(":", 1)[1] + (f"+{tag}" if tag else "")
            widened = " (widened)" if src_body != body0 else ""
            note = re.sub(r"rename_i→rename_i(, )?", "", unmask(c.get("note", "")))
            out.append({"op": op, "decl": head + nb + "\n", "note": (note + widened)[:300]})
            if len(out) >= MAX_CANDS:
                return out
    ca = catchall_bodies(body0)
    for tag, nb in [x for x in ca if x[0]] + [x for x in ca if not x[0]]:
        nb = nb.rstrip()
        if nb in seen or count_tokens(nb) >= t0:
            continue
        seen.add(nb)
        out.append({"op": "t4ind:catchall" + (f"+{tag}" if tag else ""), "decl": head + nb + "\n",
                    "note": "split with a catch-all `| _ =>` -> bare split, named alternatives in the written order, all_goals"})
        if len(out) >= MAX_CANDS:
            return out
    return out
