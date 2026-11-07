#!/usr/bin/env python3
"""Joint edit engine of the open post-step v2 (harness/open_post.py; shared by the jointres, projpath and lexsurf ops, 2026-11-03): many
small, independent token-saving edits of one proof are compiled TOGETHER, and the ones that break it are found from Lean's own error
positions (error-localized rollback) instead of one standalone compile per edit. A 1-3 token edit cannot pay for its own reading in the
post-step's gate; a joint set of them can. Pure Python apart from run_joint's compiles, which go through the caller's charged
`run(text, version)`.

  Edit        (start, end, text, rule, dtok[, hunks, note]): body offsets (the text after the statement's `:=`) of the span replaced by
              `text`, a rule tag and the exact token saving (count_tokens(body) - count_tokens(the body with this edit alone)). A
              multi-hunk edit (from_decl on a candidate that changes several places) keeps its hunks: it is applied atomically (all
              hunks or none), and other edits may sit between its hunks. Its key is its hunks (two generators proposing the same
              rewrite are one edit).
  from_decl   a whole-declaration candidate of an existing generator -> one Edit: a line diff of the two bodies, each changed region
              trimmed to its common character prefix / suffix (one hunk per region; adjacent changed lines are one region); a
              candidate that changes nothing or adds tokens -> None.
  select      the non-conflicting subset (hunks may not overlap or touch; of two conflicting edits the larger dtok stays, then the earlier
              start, then the rule / text order: deterministic).
  apply       select, then every kept hunk applied right to left (apply_map also returns each kept edit's spans in the new body).
  localize    Lean's errors of one compiled copy mapped back to its edits, in two passes: (1) an error position inside an edit's (new)
              span blames that edit; (2) every other error is skipped when its range holds an edit already blamed (a consequence,
              e.g. `unsolved goals` around a failed term), else blames the edits inside its range when at most RANGE_MAX, else every edit
              on its line (the edit's span +- the rest of its lines), else the nearest edit before it in the same indentation block;
              errors that point nowhere (the statement, a block holding many edits) are counted as unlocalized. A copy of more than
              TRUST edits blames by pass (1) only (cascades); a failing copy of ONE edit blames that edit whatever the position.
  run_joint   rounds of ONE plain compile each (the caller's run(text, None): the primary pin, after the row's file prefix), each a
              file of renamed copies `theorem lraJ<k> ...` (the statement with its name replaced; self-references in the body renamed
              too), each under `set_option maxHeartbeats HB in` and followed by an end marker, after a dummy theorem that takes the
              declaration's modifiers and a BASE marker that maps the reported lines back to each copy's body. The first round of a row
              carries the incumbent as copy 0 (the control: if it does not compile clean, the layout does not hold on this row, e.g. an
              `open ... in` modifier, and the row gets no joint run; cached per statement). Per round (plan()): S = the non-conflicting
              selection of the edits not yet failed; its unverified edits are ordered by the caller's prior (ctx "prior": expected
              saving = dtok x prior(rule)) and at most gmax per spare copy are TESTED this round; copies = the joint of the verified
              plus the tested edits, the union of the verified edits alone, then each tested edit alone when they fit, else interleaved
              groups of at most gmax (with every edit verified: the joint and its two halves). A copy that compiles clean verifies its
              edits; the edits its errors blame are dropped (their conflicting alternatives get their turn); an edit verified in a clean
              copy is never dropped by another copy's error (an interaction). Budget: ROUNDS + BISECT compiles, more (up to
              MAX_ROUNDS) while the call is within WALL_S seconds; it stops early when every edit is decided and the union of the
              verified ones compiled clean, or after BISECT rounds in a row that neither dropped nor verified anything.
  candidates  the best clean set (largest token saving; status "joint" when it is the union of every verified edit) first, then its
              per-rule subsets, its two halves, the union of every verified edit (when it differs; not compiled together yet), then
              singles by dtok; each an {"op", "decl", "note"} for the gate, which measures it like any candidate (exact statement,
              forbidden list, every pin, paired re-reading, sorry audit). Nothing here is trusted.
  cache       an edit blamed on its own (an exact hit, or its copy held only it) is remembered by its local key (the text of its lines
              before and after) for the row's statement; jointres leaves such edits out in later passes and calls. An edit verified in
              a clean copy is remembered the same way: later calls test it first (prior KNOWN_OK_PRIOR, so it joins the likely copy).
No row name, table or proof text: the engine reads only the given proof, its statement and the compile messages of its own copies."""
from __future__ import annotations

import difflib, hashlib, re, sys, threading, time
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

ROUNDS = 3             # rounds (compiles) of the base budget
BISECT = 2             # extra rounds, and the rounds without progress (nothing dropped, nothing verified) tolerated in a row
WALL_S = 480.0         # seconds of rounds per call at most (a round never starts after it)
MAX_ROUNDS = 10        # compiles per call at most when the rounds are fast (the base budget is ROUNDS + BISECT; more only within WALL_S)
GMAX = 2               # tested edits per group copy when they do not fit one per copy
LIKELY_MAX = 16        # edits of the "likely" group copy at most (plan; ctx likely_min turns it on)
RANGE_MAX = 3          # an error range blames the edits inside it only when it holds at most this many
TRUST = 3              # a copy of more edits than this blames only by exact hits (an error inside exactly one edit's span)
COPY_S = 180.0         # seconds of copies per file (the post-step's query timeout is 300 s)
COPY_FRAC = 0.6        # one copy's elaboration ~ this share of the incumbent's whole primary compile (imports included)
MAX_COPIES = 24        # copies per file at most (the control included)
MIN_COPIES = 2
MAX_COMPILE_S = 150.0  # an incumbent whose primary compile takes longer gets no joint run (two copies would not fit)
HB = 400000            # maxHeartbeats of every copy (a looping edit ends its own copy)
MAX_POOL = 160         # edits per run at most (largest dtok first)
MAX_OUT = 10           # candidates per call at most
MARK = "LRAJ"
DUMMY = "theorem lraJDummy : True := trivial"
_W = "_'!?₀₁₂₃₄₅₆₇₈₉"


# ------------------------------------------------------------------------------------------------------------------------------ edits
@dataclass(frozen=True)
class Edit:
    start: int
    end: int
    text: str
    rule: str = ""
    dtok: int = 0
    hunks: tuple = ()      # ((s, e, text), ...) ascending and disjoint; () = the one hunk (start, end, text)
    note: str = ""

    def parts(self) -> tuple:
        return self.hunks or ((self.start, self.end, self.text),)

    @property
    def key(self) -> str:
        """The edit's identity: its hunks only (two generators proposing the same rewrite are one edit)."""
        return hashlib.sha256(repr(self.parts()).encode()).hexdigest()[:16]


def _hunks(a: str, b: str) -> list[tuple[int, int, str]]:
    """The changed regions of b against a as (start, end, replacement) in a's offsets: a line diff, each region trimmed to its common
    character prefix and suffix."""
    la, lb = a.splitlines(keepends=True), b.splitlines(keepends=True)
    oa, ob = [0], [0]
    for l in la:
        oa.append(oa[-1] + len(l))
    for l in lb:
        ob.append(ob[-1] + len(l))
    out = []
    for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, la, lb, autojunk=False).get_opcodes():
        if tag == "equal":
            continue
        s, e, t = oa[i1], oa[i2], b[ob[j1]:ob[j2]]
        old = a[s:e]
        p = 0
        while p < len(old) and p < len(t) and old[p] == t[p]:
            p += 1
        q = 0
        while q < len(old) - p and q < len(t) - p and old[len(old) - 1 - q] == t[len(t) - 1 - q]:
            q += 1
        out.append((s + p, e - q, t[p:len(t) - q]))
    return out


def edit_from_bodies(body: str, new_body: str, rule: str, note: str = "", t0: int | None = None) -> Edit | None:
    """One Edit turning `body` into `new_body` (module docstring, from_decl), or None when nothing changes or no token is saved."""
    if new_body == body:
        return None
    hs = _hunks(body, new_body)
    if not hs:
        return None
    t0 = count_tokens(body) if t0 is None else t0
    dtok = t0 - count_tokens(new_body)
    if dtok < 1:
        return None
    s, e = hs[0][0], hs[-1][1]
    text = new_body[s:len(new_body) - (len(body) - e)]
    return Edit(s, e, text, rule, int(dtok), tuple(hs) if len(hs) > 1 else (), note)


def from_decl(incumbent: str, cand_decl: str, rule: str, statement: str | None = None, note: str = "", t0: int | None = None) -> Edit | None:
    """A whole-declaration candidate -> one Edit in the incumbent BODY's offsets (with `statement`: both declarations split after it;
    without: the two texts are the bodies). None: not the same statement, nothing changed, or no token saved."""
    if statement is not None:
        b0, b1 = split_declaration(incumbent, statement), split_declaration(cand_decl, statement)
        if b0 is None or b1 is None:
            return None
    else:
        b0, b1 = incumbent, cand_decl
    return edit_from_bodies(b0.rstrip(), b1.rstrip(), rule, note, t0)


def conflict(a: Edit, b: Edit) -> bool:
    """Hunks overlap or touch (an insertion at the other's boundary included): applying both is not well defined."""
    for s1, e1, _ in a.parts():
        for s2, e2, _ in b.parts():
            if s1 <= e2 and s2 <= e1:
                return True
    return False


def _rank(e: Edit):
    return (-int(e.dtok), e.start, e.rule, e.parts())


def select(edits) -> list[Edit]:
    """The non-conflicting subset, larger dtok first (module docstring), sorted by start."""
    kept: list[Edit] = []
    seen = set()
    for e in sorted(edits, key=_rank):
        if e.key in seen:
            continue
        if any(conflict(e, k) for k in kept):
            continue
        kept.append(e); seen.add(e.key)
    return sorted(kept, key=lambda e: (e.start, e.end))


def apply_map(body: str, edits) -> tuple[str, list[Edit], list[list[tuple[int, int]]]]:
    """(new body, the kept edits by start, per kept edit its hunks' spans in the NEW body)."""
    kept = select(edits)
    hunks = sorted(((s, e, t, i) for i, ed in enumerate(kept) for s, e, t in ed.parts()), key=lambda h: (h[0], h[1]))
    out, pos, shift = [], 0, 0
    spans: list[list[tuple[int, int]]] = [[] for _ in kept]
    for s, e, t, i in hunks:
        out.append(body[pos:s]); out.append(t)
        ns = s + shift
        spans[i].append((ns, ns + len(t)))
        shift += len(t) - (e - s)
        pos = e
    out.append(body[pos:])
    return "".join(out), kept, spans


def apply(body: str, edits) -> str:
    """The body with the non-conflicting edits applied (module docstring)."""
    return apply_map(body, edits)[0]


def local_key(body: str, e: Edit) -> str:
    """The edit's rule plus the text of the lines it touches before and after (stable across incumbents that keep those lines)."""
    ls = body.rfind("\n", 0, e.start) + 1
    le = body.find("\n", e.end)
    le = len(body) if le < 0 else le
    seg = body[ls:le]
    new = apply(seg, [Edit(s - ls, x - ls, t) for s, x, t in e.parts()])
    return hashlib.sha256(repr((seg, new)).encode()).hexdigest()[:16]


# ------------------------------------------------------------------------------------------------------------------------------ localize
def _line_starts(text: str) -> list[int]:
    out = [0]
    for i, ch in enumerate(text):
        if ch == "\n":
            out.append(i + 1)
    return out


def _indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def body_offset(line: int, col: int, line0: int, col0: int, starts: list[int]) -> int | None:
    """The body offset of file position (line, col) when the body starts at file (line0, col0); None before the body or past its end."""
    k = line - line0
    if k < 0 or k >= len(starts):
        return None
    if k == 0:
        return col - col0 if col >= col0 else None
    return starts[k] + col


def localize(errors, spans, body: str) -> tuple[set, int, set]:
    """(blamed edit indices, unlocalized error count, indices blamed ALONE by an exact hit) for one copy: `errors` [(p, q)] body offsets
    of each error's start and end (q None when unknown), `spans` per edit its new-body hunk spans, `body` the copy's (new) body
    (module docstring, localize)."""
    starts = _line_starts(body)
    lines = body.split("\n")

    def line_no(p):
        lo, hi = 0, len(starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if starts[mid] <= p:
                lo = mid
            else:
                hi = mid - 1
        return lo
    ext = []
    for sp in spans:
        if not sp:
            ext.append(None); continue
        a, b = min(s for s, _ in sp), max(e for _, e in sp)
        la, lb = line_no(a), line_no(max(a, b - 1) if b > a else a)
        ext.append((starts[la], starts[lb] + len(lines[lb]), la, lb))
    blamed, exact, unloc = set(), set(), 0
    rest = []
    for p, q in errors:   # pass 1: errors inside an edit's span
        if p is None or p < 0 or p > len(body):
            unloc += 1; continue
        hit = {i for i, sp in enumerate(spans) if any(s <= p <= e for s, e in sp)}
        if hit:
            blamed |= hit
            if len(hit) == 1:
                exact |= hit
        else:
            rest.append((p, q))
    for p, q in rest:     # pass 2: the others, unless their range holds an edit already blamed (a consequence of it)
        if q is not None and q > p:
            inr = {i for i, sp in enumerate(spans) if any(s < q and e > p for s, e in sp)}
            if inr & blamed:
                continue
            if 0 < len(inr) <= RANGE_MAX:
                blamed |= inr; continue
            if len(inr) > RANGE_MAX:
                unloc += 1; continue
        online = {i for i, x in enumerate(ext) if x and x[0] <= p <= x[1]}
        if online:
            if not (online & blamed):
                blamed |= online
            continue
        lp = line_no(p)
        ind = _indent(lines[lp]) if lines[lp].strip() else 0
        k = lp
        while k > 0:   # the block: lines above at the error line's indentation or deeper
            prev = lines[k - 1]
            if prev.strip() and _indent(prev) < ind:
                break
            k -= 1
        lo = starts[k]
        before = [(max(e for _, e in sp), i) for i, sp in enumerate(spans) if sp and lo <= min(s for s, _ in sp) and max(e for _, e in sp) <= p]
        if before:
            blamed.add(max(before)[1])
        else:
            unloc += 1
    return blamed, unloc, exact


# ------------------------------------------------------------------------------------------------------------------------------ files
_DECL_RE = re.compile(r"\A((?:\s+|/--(?:(?!-/).)*-/|@\[[^\]]*\]|(?:private|protected|noncomputable|nonrec)\b)*)(?:theorem|lemma)\s+"
                      r"([^\s(:{\[⦃]+)(?:\{[^}]*\})?", re.S)
_MARK_RE = re.compile(r"^%s (BASE|END (\d+))$" % MARK)


_DOC_RE = re.compile(r"/--(?:(?!-/).)*-/|/-(?:(?!-/).)*-/|--[^\n]*", re.S)
_OPEN_IN_RE = re.compile(r"(?:^|(?<=\s))(open\s+[\w.\s]+?\s+in)(?=\s|\Z)")


def in_mods(core: str, tail: str, attached=None) -> str:
    """The `... in` combinators a row's file prefix attaches to the declaration, one per line, outermost first: the trailing
    `omit` / `include` / `unseal` / `variable` / `set_option ... in` lines of the prefix's core (scorer/compile._ATTACHED_IN, repeated
    for a chain), then the `open ... in` of its modifier tail (docstrings and comments skipped). `core`, `tail`: scorer/compile.
    split_modifiers of the row's file prefix (its own Lean environment; no proof text)."""
    att = []
    if attached is not None:
        rest = core
        for _ in range(8):
            m = attached.search(rest)
            if not m:
                break
            att.insert(0, re.sub(r"\s+", " ", rest[m.start():].strip()))
            rest = rest[:m.start()]
    opens = [re.sub(r"\s+", " ", x) for x in _OPEN_IN_RE.findall(_DOC_RE.sub(" ", tail or ""))]
    return "".join(l + "\n" for l in att + opens)


def renamed(statement: str, k: int, stem: str = "lraJ") -> tuple[str, str] | None:
    """(the copy's header: `theorem <ns>lraJ<k>` + the statement after its name, the original name), else None (not a theorem / lemma;
    universe parameters in the name). The name's namespace prefix `<ns>` stays (a dotted name opens its namespace for the statement and
    the body), and so does a `private` modifier (a private name in the statement is visible only to a private declaration in a module
    file); docstrings and attributes are dropped."""
    m = _DECL_RE.match(statement)
    if not m or ".{" in m.group(0):
        return None
    name = m.group(2)
    ns = name.rsplit(".", 1)[0] + "." if "." in name.strip(".") else ""
    priv = "private " if re.search(r"(?<![\w.])private\b", _DOC_RE.sub(" ", m.group(1))) else ""
    return f"{priv}theorem {ns}{stem}{k}" + statement[m.end():], name


def _rename_body(body: str, name: str, k: int, stem: str = "lraJ") -> str:
    """Whole-identifier occurrences of the declaration's own name (a recursive call: the full dotted name, then its last component) ->
    the copy's name."""
    if not name:
        return body
    short = name.split(".")[-1]
    if "." in name.strip("."):
        ns = name.rsplit(".", 1)[0]
        body = re.sub(r"(?<![\w.%s])%s(?![\w%s])" % (re.escape(_W), re.escape(name), re.escape(_W)), f"{ns}.{stem}{k}", body)
    if not short or short not in body:
        return body
    return re.sub(r"(?<![\w.%s])%s(?![\w%s])" % (re.escape(_W), re.escape(short), re.escape(_W)), f"{stem}{k}", body)


@dataclass
class Layout:
    text: str
    base_line: int                     # 1-based line of the BASE marker in `text`
    copies: list = field(default_factory=list)   # per copy: (first line, body line, body column, body, END marker line); lines 1-based in `text`


def build(statement: str, bodies: list[str], hb: int = HB, mods: str = "") -> Layout | None:
    """The file: a dummy theorem (it takes the declaration's modifiers and any `... in` line of the prefix), the BASE marker, then per
    body the row's own `... in` combinators (`mods`: in_mods() of its file prefix, e.g. `omit [inst] in` / `open X in`, one per line;
    the dummy took the originals, so each copy repeats them) + `set_option maxHeartbeats hb in` + `theorem lraJ<k> ... :=` + body + its
    END marker. None: the statement cannot be renamed."""
    parts = [DUMMY + "\n", f'#print "{MARK} BASE"\n']
    line = 3
    copies = []
    mods = "".join(l.strip() + "\n" for l in (mods or "").split("\n") if l.strip())
    for k, b in enumerate(bodies):
        rn = renamed(statement, k)
        if rn is None:
            return None
        head, name = rn
        b = _rename_body(b.rstrip(), name, k)
        pre = mods + f"set_option maxHeartbeats {int(hb)} in\n" + head.rstrip() + " :="
        l0 = line + pre.count("\n")
        c0 = len(pre) - (pre.rfind("\n") + 1)
        chunk = pre + b + "\n" + f'#print "{MARK} END {k}"\n'
        end_line = line + chunk.count("\n") - 1
        copies.append((line, l0, c0, b, end_line))
        parts.append(chunk)
        line += chunk.count("\n")
    return Layout("".join(parts), 2, copies)


def _is_sorry(m: dict) -> bool:
    d = str(m.get("data", ""))
    return "declaration uses 'sorry'" in d or "declaration uses `sorry`" in d


def read(res, L: Layout) -> dict:
    """{"status": ok | none (no usable answer), "why", "copies": [{"clean", "ended", "errors": [(p, q)], "sorry", "msgs"}]} from one compile
    of L.text: positions mapped to each copy's body through the BASE marker's reported line."""
    if res is None or getattr(res, "timed_out", False):
        return {"status": "none", "why": "timeout"}
    msgs = getattr(res, "messages", None) or []
    base, ends = None, set()
    for m in msgs:
        if m.get("severity") == "information":
            mm = _MARK_RE.match(str(m.get("data", "")).strip())
            if mm:
                line = (m.get("pos") or {}).get("line")
                if mm.group(1) == "BASE" and isinstance(line, int):
                    base = line
                elif mm.group(2) is not None:
                    ends.add(int(mm.group(2)))
    if base is None:
        errs = [str(m.get("data", ""))[:160] for m in msgs if m.get("severity") == "error"]
        return {"status": "none", "why": "no base marker" + (f": {errs[0]}" if errs else "")}
    off = base - L.base_line
    out = []
    for k, (first, l0, c0, b, endl) in enumerate(L.copies):
        starts = _line_starts(b)
        errs, sorry, texts = [], False, []
        for m in msgs:
            pos = m.get("pos") or {}
            line = pos.get("line")
            if not isinstance(line, int) or not (first + off <= line <= endl + off):
                continue
            sev = m.get("severity")
            if sev == "error":
                p = body_offset(line, int(pos.get("column") or 0), l0 + off, c0, starts)
                ep = m.get("endPos")
                q = None
                if isinstance(ep, dict) and isinstance(ep.get("line"), int):
                    q = body_offset(int(ep["line"]), int(ep.get("column") or 0), l0 + off, c0, starts)
                errs.append((p, q))
                texts.append(str(m.get("data", ""))[:200])
            elif _is_sorry(m):
                sorry = True
        ended = k in ends
        out.append({"clean": ended and not errs and not sorry, "ended": ended, "errors": errs, "sorry": sorry, "msgs": texts})
    return {"status": "ok", "copies": out}


# ------------------------------------------------------------------------------------------------------------------------------ cache
_LOCK = threading.Lock()
_FAILED: dict = {}     # (statement sha, local key) -> reason
_LAYOUT: dict = {}     # statement sha -> True (the control compiled clean) / False (it did not: no joint run on this row)
_OK: dict = {}         # (statement sha, local key) -> True: verified in a clean copy of an earlier call (tested first, likely group)
KNOWN_OK_PRIOR = 0.95
_ROW_OBS: dict = {}    # statement sha -> {rule: (verified, dropped)}: the row's own test outcomes (the test order adapts to the row)
ROW_PSEUDO = 6.0       # the caller's prior counts as this many observations against the row's own


def _ssha(statement: str) -> str:
    return hashlib.sha256(statement.encode()).hexdigest()[:16]


def known_failed(statement: str, body: str, e: Edit) -> bool:
    with _LOCK:
        return (_ssha(statement), local_key(body, e)) in _FAILED


def remember_failed(statement: str, body: str, e: Edit, why: str) -> None:
    with _LOCK:
        _FAILED[(_ssha(statement), local_key(body, e))] = why[:120]


def known_ok(statement: str, body: str, e: Edit) -> bool:
    with _LOCK:
        return (_ssha(statement), local_key(body, e)) in _OK


def remember_ok(statement: str, body: str, e: Edit) -> None:
    with _LOCK:
        if len(_OK) < 200000:
            _OK[(_ssha(statement), local_key(body, e))] = True


def reset_cache() -> None:
    with _LOCK:
        _FAILED.clear(); _LAYOUT.clear(); _OK.clear(); _ROW_OBS.clear()


# ------------------------------------------------------------------------------------------------------------------------------ engine
def copies_per_file(compile_s: float | None, max_copies: int = MAX_COPIES) -> int:
    per = max(1.0, float(compile_s) * COPY_FRAC) if isinstance(compile_s, (int, float)) and compile_s > 0 else 10.0
    return max(MIN_COPIES, min(int(max_copies), int(COPY_S / per)))


def _interleave(items: list, g: int) -> list[list]:
    g = max(1, min(g, len(items)))
    return [items[i::g] for i in range(g)]


def plan(S: list, ok_keys: set, room: int, gmax: int = 2, rank=None, extra=(), likely=None, base=None, base_plus=()) -> list[tuple[str, list]]:
    """The copies of one round (after the control; `room` copies at most): with every edit of S verified, the joint of S and its two
    halves (an interaction between verified edits), or, given `base` (the best clean set, a strict subset of S, after S's joint
    failed), the joint, `base` plus every edit of `base_plus` (those whose extension compiled clean last round) and `base` plus each
    other edit of S alone (greedy extension: which verified edits still combine); else the joint of the verified edits plus this round's TESTED edits (the unverified
    ones of S, best rank first, at most `gmax` per remaining copy), the union of the verified edits alone (two or more), with `likely`
    (edit -> bool: its rule's success rate is high) the verified edits plus the tested LIKELY ones in one copy (two or more of them;
    they then get no copy of their own: a clean copy verifies them all), and the other tested edits each alone when they fit, else in
    interleaved groups of at most `gmax`; copies still free then test `extra` edits (alternatives that conflict with S, untested) one per
    copy."""
    ver = [e for e in S if e.key in ok_keys]
    unv = sorted((e for e in S if e.key not in ok_keys), key=rank or _rank)
    if not unv:
        out = [("joint", list(S))]
        bk = {e.key for e in base or ()}
        if base and bk < {e.key for e in S}:
            plus = [e for e in base_plus if e.key not in bk]
            if len(plus) >= 2 and room > 1:
                out.append(("extall", sorted(list(base) + plus, key=lambda x: (x.start, x.end))))
            pk = {e.key for e in plus} if len(plus) >= 2 else set()
            add = sorted((e for e in S if e.key not in bk and e.key not in pk), key=rank or _rank)[:max(0, room - len(out))]
            out += [(f"ext{i}", sorted(list(base) + [e], key=lambda x: (x.start, x.end))) for i, e in enumerate(add)]
            return out
        if len(S) >= 2 and room >= 3:
            h = (len(S) + 1) // 2
            out += [("half1", S[:h]), ("half2", S[h:])]
        free = room - len(out)
        out += [(f"alt{i}", [e]) for i, e in enumerate(list(extra)[:max(0, free)])]
        return out
    room -= 1
    out = []
    if len(ver) >= 2 and room > 1:
        out.append(("verified", ver)); room -= 1
    lik = [e for e in unv if likely(e)][:LIKELY_MAX] if likely is not None else []
    if len(lik) >= 2 and room > 1:
        out.append(("likely", sorted(ver + lik, key=lambda e: (e.start, e.end)))); room -= 1
        lk = {e.key for e in lik}
        rest = [e for e in unv if e.key not in lk]
        tested = lik + rest[:max(1, room * gmax)] if rest else lik
        own = rest[:max(1, room * gmax)] if rest else []
    else:
        tested = unv[:max(1, room * gmax)]
        own = tested
    joint = sorted(ver + tested, key=lambda e: (e.start, e.end))
    out.insert(0, ("joint", joint))
    if room <= 0 or (len(own) == 1 and not ver and not lik):
        return out
    if not own:
        return out + [(f"alt{i}", [e]) for i, e in enumerate(list(extra)[:max(0, room)])]
    if len(own) <= room:
        out += [(f"single{i}", [e]) for i, e in enumerate(own)]
        free = room - len(own)
        out += [(f"alt{i}", [e]) for i, e in enumerate(list(extra)[:max(0, free)])]
    else:
        out += [(f"group{i}", sorted(g, key=lambda e: (e.start, e.end))) for i, g in enumerate(_interleave(own, room))]
    return out


def run_joint(proof: str, statement: str, edits, run, rounds: int = ROUNDS, ctx: dict | None = None, log=None, now=time.time) -> dict:
    """The joint search (module docstring, run_joint). run(text, version) -> CompileResult-like (messages, timed_out). At most
    rounds + BISECT compiles: it stops when the joint copy compiles clean, when every edit is decided and their union compiled clean,
    when a round can tell nothing (no usable answer), or after BISECT rounds without progress. Returns {"status": joint | partial | none |
    abort, "final": [Edit] (the best clean set), "verified": [Edit] (every edit of some clean copy), "sets": [[Edit]] (the clean copies'
    edit sets), "failed": {key: why}, "compiles", "rounds": [...], "why"}."""
    ctx = ctx or {}
    say = log or (lambda *a: None)
    body0 = split_declaration(proof, statement)
    res = {"status": "none", "final": [], "verified": [], "sets": [], "failed": {}, "compiles": 0, "rounds": [], "why": None}
    if body0 is None:
        res["why"] = "the proof does not start with the statement"; return res
    body0 = body0.rstrip()
    if renamed(statement, 0) is None:
        res["why"] = "not a theorem / lemma statement"; return res
    cs = ctx.get("compile_s")
    if isinstance(cs, (int, float)) and cs > float(ctx.get("max_compile_s", MAX_COMPILE_S)):
        res["why"] = f"the incumbent compiles in {cs:.0f} s"; return res
    ss = _ssha(statement)
    with _LOCK:
        lay = _LAYOUT.get(ss)
    if lay is False:
        res["status"] = "abort"; res["why"] = "the control copy did not compile on this row"; return res
    prior = ctx.get("prior") or (lambda rule: 1.0)

    _known: dict = {}
    with _LOCK:   # the row's own test outcomes by rule (this statement's earlier calls), updated after every round
        obs = {r: list(v) for r, v in _ROW_OBS.get(ss, {}).items()}

    def eprior(e):  # an edit verified on this statement in an earlier call (same lines before and after): KNOWN_OK_PRIOR; else the
        k = _known.get(e.key)   # caller's prior for the rule, updated by the row's own outcomes (ROW_PSEUDO pseudo-observations)
        if k is None:
            k = _known[e.key] = known_ok(statement, body0, e)
        if k:
            return KNOWN_OK_PRIOR
        p = float(prior(e.rule))
        o = obs.get(e.rule)
        return p if not o else (p * ROW_PSEUDO + o[0]) / (ROW_PSEUDO + o[0] + o[1])

    def prank(e):   # the order edits are tested in: expected saving = dtok x the caller's prior for the edit's rule
        return (-float(e.dtok) * eprior(e),) + _rank(e)
    lmin = ctx.get("likely_min")   # a prior at least this high: the edit joins the round's "likely" group copy (plan)
    likely = (lambda e: eprior(e) >= float(lmin)) if isinstance(lmin, (int, float)) else None
    pool = sorted({e.key: e for e in edits if e.dtok >= 1}.values(), key=prank)[:int(ctx.get("max_pool", MAX_POOL))]
    if not pool:
        res["why"] = "no edit"; return res
    ncop = copies_per_file(cs, int(ctx.get("max_copies", MAX_COPIES)))
    max_compiles = max(int(rounds) + int(ctx.get("bisect", BISECT)), int(ctx.get("max_rounds", MAX_ROUNDS)))
    base = int(rounds) + int(ctx.get("bisect", BISECT))
    failed: dict = {}
    ok_keys: set = set()
    sets: list = []
    need_control = lay is not True
    stale = 0
    prev_sig = None
    best_dtok = 0         # the largest saving of a clean copy so far (a round that raises it made progress)
    counted_ok: set = set()
    bad_sets: list = []   # key sets of failing copies whose edits were all verified (interactions): candidates() skips their supersets
    ext_ok: list = []     # edits whose extension copy (best clean set + it) compiled clean in the last round
    joint_failed = None   # the key set of S when its joint copy (every edit verified) failed: the next round extends the best clean set
    done = None
    t_start = now()
    wall = float(ctx.get("wall_s", WALL_S))
    while (res["compiles"] < base or (res["compiles"] < max_compiles and now() - t_start < wall)) and stale <= int(ctx.get("bisect", BISECT)):
        S = select([e for e in pool if e.key not in failed])
        if not S:
            break
        inS = {e.key for e in S}
        extra = [e for e in pool if e.key not in failed and e.key not in ok_keys and e.key not in inS]
        ext_base = None
        if joint_failed is not None and joint_failed == {e.key for e in S} and sets:
            best_set = max(sets, key=lambda st: (sum(e.dtok for e in st), len(st)))
            if {e.key for e in best_set} < joint_failed:
                ext_base = best_set
        variants = ([("control", [])] if need_control else []) + plan(S, ok_keys, ncop - (1 if need_control else 0), int(ctx.get("gmax", GMAX)),
                                                                       prank, extra, likely, ext_base, ext_ok if ext_base else ())
        S = next(es for lab, es in variants if lab == "joint")
        sig = tuple(sorted(tuple(sorted(e.key for e in es)) for lab, es in variants if lab != "control"))
        if sig == prev_sig:
            break   # the same file as the last round: a deterministic compile can tell nothing new
        prev_sig = sig
        bodies, maps = [], []
        for lab, es in variants:
            nb, kept, spans = apply_map(body0, es)
            bodies.append(nb); maps.append((lab, kept, spans))
        L = build(statement, bodies, int(ctx.get("hb", HB)), str(ctx.get("in_mods") or ""))
        if L is None:
            res["why"] = "the statement cannot be renamed"; break
        r = run(L.text, None)
        res["compiles"] += 1
        rd = read(r, L)
        sec = getattr(r, "seconds", None)
        if ctx.get("adapt", True) and isinstance(sec, (int, float)) and sec > 0 and rd.get("status") == "ok":
            # the next file's copies from this round's own wall time (imports included, so per copy is over-estimated): a row whose
            # first compile read slow on a loaded machine is not held to a few copies per round for the whole call
            per = max(0.25, float(sec) / max(1, len(variants)))
            ncop = max(MIN_COPIES, min(int(ctx.get("max_copies", MAX_COPIES)), int(COPY_S / per)))
        info = {"copies": len(variants), "edits": len(S), "unverified": sum(1 for e in S if e.key not in ok_keys),
                "s": round(float(sec), 1) if isinstance(sec, (int, float)) else None}
        if rd["status"] != "ok":
            info["none"] = rd.get("why"); res["rounds"].append(info)
            if need_control:
                with _LOCK:
                    _LAYOUT[ss] = False
            res["why"] = f"no usable answer: {rd.get('why')}"; break
        cps = rd["copies"]
        if need_control:
            c0 = cps[0]
            with _LOCK:
                _LAYOUT[ss] = bool(c0["clean"])
            if not c0["clean"]:
                info["control"] = (c0["msgs"] or ["no end marker" if not c0["ended"] else "sorry"])[0][:160]
                res["rounds"].append(info)
                res["status"] = "abort"; res["why"] = "the control copy did not compile clean: " + info["control"]
                say(f"jointres: control copy failed ({info['control'][:100]})")
                return res
            need_control = False
        new_bad: dict = {}
        clean_labels, new_ok = [], 0
        for (lab, kept, spans), cp, nb in zip(maps, cps, bodies):
            if lab == "control":
                continue
            if cp["clean"]:
                clean_labels.append(lab)
                if kept:
                    sets.append(list(kept))
                    for e in kept:
                        if e.key not in ok_keys:
                            ok_keys.add(e.key); new_ok += 1
                continue
            if not cp["ended"] and not cp["errors"]:
                continue   # no answer for this copy
            if len(kept) >= 2 and all(e.key in ok_keys for e in kept):
                bad_sets.append(frozenset(e.key for e in kept))   # verified edits that do not combine (an interaction)
            blamed, unloc, exact = localize(cp["errors"], spans, nb)
            if lab == "likely" and not exact:
                likely = None   # the likely group failed and Lean pointed at none of its edits: singles from here on
            if len(kept) > TRUST:
                blamed = exact   # cascades in a large copy: only an error inside exactly one edit's span blames it
            elif len(kept) == 1:
                blamed, exact = {0}, {0}   # the control compiled clean: a failing copy of one edit is that edit's failure
            for i in blamed:
                e = kept[i]
                if e.key in failed or e.key in new_bad:
                    continue
                new_bad[e.key] = (e, (cp["msgs"] or ["error"])[0], len(kept) == 1 or i in exact)
        for k in [k for k in new_bad if k in ok_keys]:
            new_bad.pop(k)   # verified in a clean copy: its failure here is an interaction, not the edit itself
        info.update(clean=clean_labels, dropped=len(new_bad), verified=new_ok)
        res["rounds"].append(info)
        for k, (e, why, alone) in new_bad.items():
            failed[k] = why
            obs.setdefault(e.rule, [0, 0])[1] += 1
            if alone:
                remember_failed(statement, body0, e, why)
        for e in pool:
            if e.key in ok_keys and e.key not in counted_ok:
                counted_ok.add(e.key)
                obs.setdefault(e.rule, [0, 0])[0] += 1
        ext_ok = []
        for (lab, kept, _sp), cp in zip(maps, cps):
            if lab.startswith("ext") and lab != "extall" and cp["clean"] and ext_base is not None:
                bk = {e.key for e in ext_base}
                ext_ok += [e for e in kept if e.key not in bk]
        if all(e.key in ok_keys for e in S) and "joint" not in clean_labels and len(S) >= 2:
            joint_failed = {e.key for e in S}
        else:
            joint_failed = None
        if "joint" in clean_labels:
            done = ("joint", S)
        elif "verified" in clean_labels:
            done = ("joint", [e for e in S if e.key in ok_keys])
        left = [e for e in select([e for e in pool if e.key not in failed]) if e.key not in ok_keys]
        if not left and done is not None and {e.key for e in done[1]} >= {e.key for e in select([e for e in pool if e.key in ok_keys])}:
            break   # every edit decided and the union of the verified ones compiled clean
        bd = max((sum(e.dtok for e in st) for st in sets), default=0)
        stale = 0 if (new_bad or new_ok or bd > best_dtok) else stale + 1
        best_dtok = max(best_dtok, bd)
    verified = [e for e in pool if e.key in ok_keys]
    for e in verified:
        remember_ok(statement, body0, e)
    with _LOCK:
        _ROW_OBS[ss] = {r: tuple(v) for r, v in obs.items()}
    res["verified"] = sorted(verified, key=lambda e: (e.start, e.end))
    res["failed"] = failed
    res["sets"] = sets
    res["bad_sets"] = [s_ for s_ in dict.fromkeys(bad_sets)]
    if sets:
        best = max(sets, key=lambda s: (sum(e.dtok for e in s), len(s), -min(e.start for e in s)))
        if done is not None and sum(e.dtok for e in done[1]) >= sum(e.dtok for e in best):
            best = done[1]
        whole = {e.key for e in select(verified)}
        res["status"] = "joint" if {e.key for e in best} == whole else "partial"
        res["final"] = sorted(best, key=lambda e: (e.start, e.end))
    res["seconds"] = round(now() - t_start, 1)
    return res


def _decl(proof: str, statement: str, edits) -> str | None:
    body = split_declaration(proof, statement)
    if body is None:
        return None
    head = proof[:len(proof) - len(body)]
    return head + apply(body.rstrip(), edits)


def candidates(proof: str, statement: str, res: dict, op: str = "jointres", max_out: int = MAX_OUT) -> list[dict]:
    """The gate's candidates from a run_joint result (module docstring, candidates): {"op": f"{op}:<form>", "decl", "note"}."""
    final = list(res.get("final") or [])
    verified = list(res.get("verified") or [])
    if not final and not verified:
        return []
    body = split_declaration(proof, statement)
    if body is None:
        return []
    t0 = count_tokens(body.rstrip())
    newline0 = bool(re.match(r"[ \t]*\n", body))
    forms: list[tuple[str, list]] = []
    if final:
        forms.append(("joint" if res.get("status") == "joint" else "set", final))
        rules = sorted({e.rule for e in final})
        if len(rules) > 1:
            per = sorted(((r, [e for e in final if e.rule == r]) for r in rules), key=lambda x: -sum(e.dtok for e in x[1]))
            forms += [(f"rule[{r}]", es) for r, es in per]
        if len(final) >= 2:
            h = (len(final) + 1) // 2
            forms += [("half1", final[:h]), ("half2", final[h:])]
    union = select(verified)
    if union and {e.key for e in union} != {e.key for e in final}:
        forms.insert(1 if final else 0, ("union", union))
    singles = sorted({e.key: e for e in final + verified}.values(), key=_rank)
    forms += [("single", [e]) for e in singles]
    bad = [b for b in res.get("bad_sets") or ()]
    out, seen = [], {proof.rstrip()}
    for form, es in forms:
        if len(out) >= max_out:
            break
        ks = {e.key for e in es}
        if any(b <= ks for b in bad):
            continue   # holds verified edits that failed together: a gate reading would only fail
        decl = _decl(proof, statement, es)
        if decl is None or decl.rstrip() in seen:
            continue
        nb = split_declaration(decl, statement)
        if nb is None or (not newline0 and re.match(r"[ \t]*\n", nb)):
            continue
        dt = t0 - count_tokens(nb.rstrip())
        if dt < 1:
            continue
        seen.add(decl.rstrip())
        rules = sorted({e.rule for e in es})
        out.append({"op": f"{op}:{form.split('[')[0]}", "decl": decl.rstrip(),
                    "note": f"{form} {len(es)} edit(s) -{dt} tok [{', '.join(rules)[:120]}]", "edit_keys": [e.key for e in es]})
    return out


def combine(proof: str, statement: str, ranked: list, edits_by_key: dict, op: str = "jointres", bad_sets=()) -> dict | None:
    """One candidate joining the edit sets of `ranked` candidates (best first: each a candidate of candidates() with "edit_keys"), greedily:
    a candidate's edits join only when none of them conflicts with those already chosen. None when it adds nothing to the first one."""
    chosen: list = []
    used = 0
    for c in ranked:
        es = [edits_by_key[k] for k in c.get("edit_keys") or () if k in edits_by_key]
        if not es:
            continue
        new = [e for e in es if e.key not in {x.key for x in chosen}]
        if any(conflict(e, x) for e in new for x in chosen) or any(conflict(a, b) for i, a in enumerate(new) for b in new[i + 1:]):
            continue
        ks = {x.key for x in chosen} | {e.key for e in new}
        if any(b <= ks for b in bad_sets or ()):
            continue
        chosen += new
        used += 1
    if used < 2:
        return None
    decl = _decl(proof, statement, chosen)
    body = split_declaration(proof, statement)
    if decl is None or body is None:
        return None
    dt = count_tokens(body.rstrip()) - count_tokens((split_declaration(decl, statement) or "").rstrip())
    if dt < 1:
        return None
    rules = sorted({e.rule for e in chosen})
    return {"op": f"{op}:combo", "decl": decl.rstrip(), "note": f"combo {len(chosen)} edit(s) of {used} candidate(s) -{dt} tok "
            f"[{', '.join(rules)[:120]}]", "edit_keys": [e.key for e in chosen]}
