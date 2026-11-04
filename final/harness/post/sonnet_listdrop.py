#!/usr/bin/env python3
"""Op `sonnet_listdrop` (gap lane sonnet, surface / lexer): verified DELETION of syntactic units that Lean does not need.

Every token of an open proof costs; a deleted unit saves its tokens exactly (scorer/tokenize.count_tokens), and Lean itself says whether
it was needed. Units (all found from the proof text alone, comments and strings masked):
  item   one item of a tactic's bracket list: `simp [a, b, c]`, `simp only [..]`, `simp_all`, `simpa`, `dsimp`, `norm_num`,
         `field_simp`, `nlinarith`, `linarith`, `positivity`, `rw`, `rwa`, `simp_rw`, `grind`, `aesop`, `push_cast`, ... : the item and its
         comma go (-2 tokens for an atom); the only item of a simp-family list takes its brackets with it (`simp only [a]` -> `simp only`)
  only   `simp only [..]` -> `simp [..]`, `dsimp only` -> `dsimp` (-1 token; the gate decides whether the heartbeats rise)
  line   a leaf tactic line (no nested block below it, balanced, not a continuation, not a bullet / arm / case header) is removed
Nothing here is trusted: query() compiles the proof's own variants in one-file measured batches (harness/post/d4_measure.py: one theorem
copy per variant, its heartbeat reading), keeps the units whose copy compiles with no error and no sorry and whose predicted score (the
scorer's own linear L and H through the row's exchange rate) rises, then tries the cumulative union of the kept units (best first) in
one more file, and proposes the best predicted variants. The caller's gate (harness/open_post.py) still reads each on every pin.
Pure text + env queries; no table, no row name, no proof text."""
from __future__ import annotations

# provenance: research lane gaplane-sonnet (worktree lra-gl-sonnet), commit 0024646, ported unchanged into open-post-v3 (2026-11-04)

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from scorer.tokenize import count_tokens  # noqa: E402

FAMILY = "sonnet_listdrop"
LIST_HEADS = ("simp_all", "simp_arith", "simp_rw", "simpa", "simp", "dsimp", "norm_num", "field_simp", "nlinarith", "linarith", "positivity",
              "rwa", "rw", "rewrite", "nth_rewrite", "nth_rw", "grind", "aesop", "push_cast", "norm_cast", "ring_nf", "unfold", "gcongr",
              "bound", "fun_prop", "decide", "omega", "polyrith", "tauto", "itauto", "cc")
SIMP_FAMILY = frozenset({"simp_all", "simp_arith", "simpa", "simp", "dsimp", "norm_num", "field_simp", "push_cast", "norm_cast", "ring_nf",
                         "grind", "aesop", "nlinarith", "linarith", "positivity", "gcongr", "bound", "fun_prop"})
HEAD_RE = re.compile(r"(?:^|[\s(;·]|<;>|=>)(%s)(?=[\s+!?(\[\-]|$)[^\[\]\n]*$" % "|".join(LIST_HEADS))
ONLY_RE = re.compile(r"(?<![\w.'])(simp_all|simp|dsimp|simpa|norm_num|field_simp|simp_arith)(!?\??) only(?![\w'])")
MAX_UNITS = 45
MAX_VARIANT_BODIES = 64


_FAILED: set = set()   # (statement, kind, context, text): units whose copy did not compile; later passes on the same row skip them


def _ukey(statement: str, body: str, u) -> tuple:
    return (statement.strip(), u.kind, body[max(0, u.start - 40):u.start], body[u.start:u.end], u.text)


class Unit:
    __slots__ = ("start", "end", "text", "kind", "dtok", "note")

    def __init__(self, start, end, text, kind, note):
        self.start, self.end, self.text, self.kind, self.note, self.dtok = start, end, text, kind, note, 0


def _split_items(body: str, mask, lo: int, hi: int):
    """Depth-0 comma-separated items of body[lo:hi] as (start, end) with surrounding blanks trimmed."""
    items, depth, s = [], 0, lo
    for i in range(lo, hi):
        if mask[i]:
            continue
        ch = body[i]
        if ch in "([{⟨⦃":
            depth += 1
        elif ch in ")]}⟩⦄":
            depth -= 1
        elif ch == "," and depth == 0:
            items.append((s, i)); s = i + 1
    items.append((s, hi))
    out = []
    for a, b in items:
        while a < b and body[a] in " \t\n":
            a += 1
        while b > a and body[b - 1] in " \t\n":
            b -= 1
        out.append((a, b))
    return out


_STATEMENT_HINT = [""]   # the statement's own text (binder names), set by the entry points


_IDENT = re.compile(r"[^\W\d][\w']*")
_BIND_AFTER = re.compile(r"^\s*(?:·\s*)?(rcases|cases|cases'|induction|induction')\b[^\n]*?\bwith\b(.*)$")
_BIND_BEFORE = re.compile(r"^\s*(?:·\s*)?(have|obtain|set|let|choose|generalize|suffices)\b([^\n]*)$")
_BIND_ALL = re.compile(r"^\s*(?:·\s*)?(intro|intros|rintro|rename_i|by_cases|by_contra|by_contra!|next|case|case'|specialize|peel|ext)\b(.*)$")


def _bound_names(text: str, statement: str) -> set:
    """Over-approximation of the local names bound before `text` ends: binder lists of the statement, intro / obtain / have / rcases
    patterns, `fun` binders and `| ctor a b =>` arms (lemma names are not looked for: only binding positions)."""
    names: set = set()
    for m in re.finditer(r"[({\[⦃]([^(){}\[\]:]+?) :", statement):
        names.update(_IDENT.findall(m.group(1)))
    for ln in text.split("\n"):
        for rx in (_BIND_AFTER, _BIND_BEFORE, _BIND_ALL):
            m = rx.match(ln)
            if not m:
                continue
            part = m.group(2)
            if rx is _BIND_BEFORE:
                part = re.split(r":=|\s:\s|\busing\b", part)[0]
            names.update(_IDENT.findall(part))
        for m in re.finditer(r"(?:fun|λ)\s+([^=↦]*?)\s*(?:=>|↦)", ln):
            names.update(_IDENT.findall(m.group(1)))
        m = re.match(r"^\s*\|\s*([^=]*)=>", ln)
        if m:
            names.update(_IDENT.findall(m.group(1)))
    names -= {"only", "at", "using", "with", "fun", "have", "obtain", "from", "by", "show", "this_"}
    return {n for n in names if n[0].islower() or n[0] == "_" and len(n) > 1 or n == "this"}


def _units(body: str, statement: str = "") -> list[Unit]:
    _STATEMENT_HINT[0] = statement
    mask = _mask(body)
    pairs = _pairs(body, mask)
    units: list[Unit] = []
    # -- list items
    for o, c in sorted(pairs.items()):
        if body[o] != "[" or mask[o]:
            continue
        ls = body.rfind("\n", 0, o) + 1
        m = HEAD_RE.search(body[ls:o])
        if not m:
            continue
        head = m.group(1)
        items = _split_items(body, mask, o + 1, c)
        if len(items) == 1 and items[0][0] == items[0][1]:
            continue
        n = len(items)
        if head in ("simp", "simp_all", "simpa", "dsimp", "simp_arith", "norm_num", "field_simp") and n >= 2:
            names = _bound_names(body[:o], _STATEMENT_HINT[0])
            loc = [k for k, (a, b) in enumerate(items) if body[a:b] in names]
            if len(loc) >= 2 and "*" not in [body[a:b] for a, b in items]:
                rest = [body[a:b] for k, (a, b) in enumerate(items) if k not in loc]
                units.append(Unit(o + 1, c, ", ".join(["*"] + rest), "star", f"{head} list: {len(loc)} local items -> *"))
        for k, (a, b) in enumerate(items):
            if a == b:
                continue
            if n == 1:
                if head not in SIMP_FAMILY:
                    continue
                s = o
                while s > ls and body[s - 1] in " \t":
                    s -= 1
                units.append(Unit(s, c + 1, "", "item", f"{head} list: the only item {body[a:b][:30]!r} with its brackets"))
            elif k < n - 1:
                units.append(Unit(a, items[k + 1][0], "", "item", f"{head} list: item {body[a:b][:30]!r}"))
            else:
                units.append(Unit(items[k - 1][1], b, "", "item", f"{head} list: last item {body[a:b][:30]!r}"))
    # -- block units on long lists: first half / second half (n >= 6), the whole list (`wipe`), the whole list and `only` (`bare`)
    for o, c in sorted(pairs.items()):
        if body[o] != "[" or mask[o]:
            continue
        ls = body.rfind("\n", 0, o) + 1
        m = HEAD_RE.search(body[ls:o])
        if not m or m.group(1) not in SIMP_FAMILY:
            continue
        items = [t for t in _split_items(body, mask, o + 1, c) if t[0] < t[1]]
        n = len(items)
        if n < 3:
            continue
        h = m.group(1)
        if n >= 6:
            k = (n + 1) // 2
            units.append(Unit(items[0][0], items[k][0], "", "block", f"{h} list: first {k} of {n} items"))
            units.append(Unit(items[k - 1][1], items[-1][1], "", "block", f"{h} list: last {n - k} of {n} items"))
        s0 = o
        while s0 > ls and body[s0 - 1] in " \t":
            s0 -= 1
        mo = re.search(r"(?<![\w.'])%s(!?\??) only\s*$" % re.escape(h), body[ls:s0])
        if mo:   # `simp only [long list]` -> `simp`: the default simp set may do it all (the gate prices the heartbeats)
            units.append(Unit(ls + mo.start() + len(h) + len(mo.group(1)), c + 1, "", "bare", f"{h} only list: all {n} items and `only`"))
        else:
            units.append(Unit(s0, c + 1, "", "wipe", f"{h} list: all {n} items"))
    # -- only
    for m in ONLY_RE.finditer(body):
        if mask[m.start()]:
            continue
        units.append(Unit(m.start(1) + len(m.group(1)) + len(m.group(2)), m.end(), "", "only", f"{m.group(1)} only -> {m.group(1)}"))
    # -- redundant parentheses / casts / succ
    TERM_START = re.compile(r"(?:^|[\s;(<>|])(exact|apply|refine|use|simpa|have|obtain|rcases|show|calc|exists|constructor|from)\b|:=|\$|<\|")
    for o, c in sorted(pairs.items()):
        if body[o] != "(" or mask[o] or mask[c]:
            continue
        inner = body[o + 1:c]
        ls = body.rfind("\n", 0, o) + 1
        le = body.find("\n", c); le = len(body) if le < 0 else le
        before, after = body[ls:o], body[c + 1:le]
        # cast (x : T) -> ↑x
        mc = re.fullmatch(r"([^\W\d][\w'.]*) : (ℝ≥0|ℝ|ℕ|ℤ|ℚ|ℂ|NNReal|Real|Nat|Int|Rat|Complex|ℝ≥0∞|ENNReal|ENat|ℕ∞)", inner)
        if mc and not before.endswith(("↑", "(", "⟨")) and not after.startswith(".") and not re.match(r"[\w'.]", after[:1]) and not after.lstrip().startswith(":"):
            units.append(Unit(o, c + 1, "↑" + mc.group(1), "cast", f"cast ({inner}) -> ↑{mc.group(1)}"))
        # (x + 1) -> x.succ ; (x - 1) -> x.pred
        ms = re.fullmatch(r"([^\W\d][\w'.]*) ([+-]) 1", inner)
        if ms and not after.startswith(".") and not re.match(r"[\w'.]", after[:1]) and not before.endswith(("↑", ".")):
            units.append(Unit(o, c + 1, ms.group(1) + (".succ" if ms.group(2) == "+" else ".pred"), "succ", f"({inner}) -> {ms.group(1)}.succ/pred"))
        # tail group: `exact (E)` -> `exact E`; `f a (g b)` -> `f a $ g b`
        if after.strip() == "" or re.match(r"\s*(<;>|;|\)|\])", after):
            depth0 = [i for i in range(o + 1, c) if not mask[i] and body[i] in ":,|" and all(not (o2 < i < c2) for o2, c2 in pairs.items() if o < o2 and c2 < c)]
            if depth0 or not inner.strip():
                continue
            if re.search(r"(?:^|\s)(exact|apply|refine|use|simpa|rwa|exists|from|:=|\$|<\||using|then|else)\s*$", before):
                units.append(Unit(o, c + 1, inner, "paren", f"redundant parens after {before.split()[-1] if before.split() else ''}"))
            elif " " in inner.strip() and re.search(r"[\w'.)\]⟩]\s+$", before) and TERM_START.search(before) and not inner.lstrip().startswith(("fun", "λ", "by")):
                units.append(Unit(o, c + 1, "$ " + inner if before.endswith(" ") else " $ " + inner, "dollar", "tail parens -> $"))
    # -- leaf lines
    lines = body.split("\n")
    offs, p = [], 0
    for ln in lines:
        offs.append(p); p += len(ln) + 1
    ind = [len(l) - len(l.lstrip()) if l.strip() else None for l in lines]

    def crosses(a, b):   # does a bracket pair cross the boundary of [a, b)?
        return any((o < a <= cc < b + 1) or (a <= o < b < cc) for o, cc in pairs.items())

    nz = [i for i, v in enumerate(ind) if v is not None]
    for pos, i in enumerate(nz):
        if pos == 0:
            continue
        a, b = offs[i], offs[i] + len(lines[i])
        if any(mask[a:b]) or i == len(lines):
            continue
        t = lines[i].strip()
        prev = lines[nz[pos - 1]].rstrip()
        nxt = ind[nz[pos + 1]] if pos + 1 < len(nz) else -1
        if nxt is not None and nxt > ind[i]:
            continue
        if not re.match(r"[A-Za-z_]", t) or t.startswith(("case", "next", "termination_by", "decreasing_by", "where", "else", "then", "with",
                                                            "at ", "using", "from")):
            continue
        if re.search(r"(by|=>|:=|,|\(|\[|⟨|<;>|\$|<\||fun|then|else|with|∘|→|↔|∧|∨|\+|-|\*|/|=|<|>|≤|≥|≠|∈|\\|\|)$", t):
            continue
        if re.search(r"(,|\(|\[|⟨|<;>|\$|<\||then|else|with|∘|\|)$", prev):
            continue
        if re.search(r"(by|=>|:=)$", prev) and nxt < ind[i]:
            continue   # the only line of its block
        if crosses(a, b + 1):
            continue
        units.append(Unit(a, min(len(body), b + 1), "", "line", f"line {t[:36]!r}"))
    # tokens saved (exact, in context)
    t0 = count_tokens(body)
    seen, out = set(), []
    for u in units:
        nb = body[:u.start] + u.text + body[u.end:]
        u.dtok = t0 - count_tokens(nb)
        key = (u.start, u.end, u.text)
        if u.dtok <= 0 or key in seen:
            continue
        seen.add(key); out.append(u)
    return out


def _apply(body: str, us) -> str | None:
    us = sorted(us, key=lambda u: u.start)
    for x, y in zip(us, us[1:]):
        if y.start < x.end:
            return None
    out, last = [], 0
    for u in us:
        out.append(body[last:u.start]); out.append(u.text); last = u.end
    out.append(body[last:])
    return "".join(out)


def _ranked(units):
    return sorted(units, key=lambda u: (-u.dtok, u.start))


def has_sites(proof: str, statement: str) -> bool:
    hb = K.head_body(proof, statement)
    if hb is None or MS.renamed(statement, 0) is None:
        return False
    try:
        return bool(_units(hb[1], statement))
    except Exception:  # noqa: BLE001
        return False


def _selfref(statement: str, bodies: list[str]) -> list[str]:
    """Bodies whose references to the theorem being proved (a recursive proof) point at the renamed copy `lraD4M<i>` instead."""
    m = re.match(r"\s*(?:(?:private|protected|noncomputable|nonrec)\s+)*(?:theorem|lemma)\s+([^\s(:{\[⦃]+)", statement)
    if not m:
        return bodies
    nm = re.escape(m.group(1).split(".")[-1])
    pat = re.compile(r"(?<![\w.'])(?:[\w']+\.)*" + nm + r"(?![\w'])")
    return [pat.sub(f"lraD4M{i}", b) for i, b in enumerate(bodies)]


def plain_text(statement: str, bodies: list[str]) -> str | None:
    """The fallback measuring file for rows whose file prefix lacks `Lean` (the #eval of d4_measure cannot read there): one plain theorem
    copy per body, each preceded by a `#print "<marker>"` that tells the copy's first line (messages carry pos.line)."""
    out = []
    for i, b in enumerate(bodies):
        r = MS.renamed(statement, i)
        if r is None:
            return None
        out.append(f'#print "LRASL {i}"\n' + r.rstrip() + " :=" + b.rstrip("\n") + "\n")
    out.append('#print "LRASL end"\n')
    return "".join(out)


def plain_parse(messages, n: int) -> dict:
    """{i: {"ok": bool, "hb": None}}: a copy is ok when its marker is seen and no error message lies between its marker and the next one
    (None for all when a marker is missing: nothing to trust)."""
    marks, errs = {}, []
    for m in messages or []:
        d = K.msg_text(m)
        pos = (m.get("pos") or {}) if isinstance(m, dict) else {}
        ln = pos.get("line")
        if ln is None:
            continue
        mm = re.search(r"LRASL (\d+|end)", d)
        if mm and (m.get("severity") == "information"):
            marks[n if mm.group(1) == "end" else int(mm.group(1))] = ln
        elif m.get("severity") == "error":
            errs.append(ln)
    if len(marks) < n + 1:
        return {}
    out = {}
    for i in range(n):
        lo, hi = marks[i], marks[i + 1]
        out[i] = {"ok": not any(lo <= e < hi for e in errs), "hb": None}
    return out


def _fmt(us):
    kinds = {}
    for u in us:
        kinds[u.kind] = kinds.get(u.kind, 0) + 1
    return ",".join(f"{k}x{v}" for k, v in sorted(kinds.items()))


def _read(statement, bodies, run, mode):
    """({i: {"ok", "hb"}}, mode): the d4_measure #eval file first (heartbeats); when its control does not read, the plain marker file
    (ok only), and that mode sticks for the row."""
    bodies = _selfref(statement, bodies)
    if mode == "eval":
        text = MS.text(statement, bodies)
        if text is not None:
            rd = MS.parse(getattr(run(text, None), "messages", None), len(bodies))
            if (rd.get(0) or {}).get("ok"):
                return rd, "eval"
    text = plain_text(statement, bodies)
    if text is None:
        return {}, "plain"
    return plain_parse(getattr(run(text, None), "messages", None), len(bodies)), "plain"


def _pred(ctl, body0, body, reading, exchange):
    """MS.predicted when both readings carry heartbeats; in plain mode (no heartbeats) the token saving alone (the gate prices H)."""
    if ctl.get("hb") is None or reading.get("hb") is None:
        return float(count_tokens(body0) - count_tokens(body)) if ctl.get("ok") and reading.get("ok") else None
    return MS.predicted(ctl, body0, body, reading, exchange)


def query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None):
    """Screen the units, then their cumulative union (module docstring). Returns {"variants": [{"body", "pred", "note"}]} or None."""
    try:
        hb = K.head_body(proof, statement)
        if hb is None or MS.renamed(statement, 0) is None:
            return None
        head, body = hb
        exchange = (ctx or {}).get("exchange")
        n = MS.budget(ctx)
        if n < 3:
            return None
        units = [u for u in _ranked(_units(body, statement)) if _ukey(statement, body, u) not in _FAILED]
        if not units:
            return {"variants": []}
        units = units[:max(1, min(MAX_UNITS, (n - 1) * 3))]
        good = []   # (pred, unit)
        mode = "eval"
        for i in range(0, len(units), n - 1):
            chunk = units[i:i + n - 1]
            bodies = [_apply(body, [u]) for u in chunk]
            rd, mode = _read(statement, [body] + bodies, run, mode)
            ctl = rd.get(0) or {"ok": False}
            if not ctl.get("ok"):
                if log:
                    log(f"{FAMILY}: control did not read ({mode})")
                return {"variants": []}
            for k, (u, b) in enumerate(zip(chunk, bodies), 1):
                if not (rd.get(k) or {}).get("ok") and k in rd:
                    _FAILED.add(_ukey(statement, body, u))
                pr = _pred(ctl, body, b, rd.get(k) or {"ok": False}, exchange)
                if pr is not None and pr > 0:
                    good.append((pr, u))
        if stats is not None:
            stats[FAMILY] = {"units": len(units), "ok": len(good)}
        if not good:
            return {"variants": []}
        good.sort(key=lambda x: (-x[0], x[1].start))
        variants = [{"body": _apply(body, [u]), "pred": pr, "note": f"single {u.kind}: {u.note}"} for pr, u in good[:3]]
        if len(good) >= 2:
            # cumulative union, best first, skipping overlaps
            chosen, bodies, notes = [], [], []
            for pr, u in good:
                if _apply(body, chosen + [u]) is None:
                    continue
                chosen = chosen + [u]
                if len(chosen) >= 2:
                    bodies.append(_apply(body, chosen)); notes.append(f"union of {len(chosen)} ({_fmt(chosen)})")
            if len(bodies) > n - 1:   # keep the largest unions and a spread of smaller ones
                keep = sorted(set(list(range(len(bodies)))[-(n - 1) // 2:] + list(range(0, len(bodies), max(1, len(bodies) // ((n - 1) // 2 or 1))))))
                keep = keep[:n - 1]
                bodies = [bodies[j] for j in keep]; notes = [notes[j] for j in keep]
            if bodies:
                rd, mode = _read(statement, [body] + bodies, run, mode)
                ctl = rd.get(0) or {"ok": False}
                if ctl.get("ok"):
                    for k, (b, nt) in enumerate(zip(bodies, notes), 1):
                        pr = _pred(ctl, body, b, rd.get(k) or {"ok": False}, exchange)
                        if pr is not None and pr > 0:
                            variants.append({"body": b, "pred": pr, "note": nt})
        variants.sort(key=lambda v: -v["pred"])
        return {"variants": variants}
    except Exception as e:  # noqa: BLE001
        if e.__class__.__name__ == "_Stop":
            raise
        if log:
            log(f"{FAMILY}.query error {type(e).__name__}: {str(e)[:160]}")
        return None


def candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None):
    try:
        hb = K.head_body(proof, statement)
        if hb is None:
            return []
        head, body = hb
        em = K.Emitter(proof, statement, head, body, int(max_per_op or 8))
        var = (ctx or {}).get("variants")
        if var is not None:
            for v in var:
                em.add(f"{FAMILY}:verified", v["body"], v["note"], extra={"pred": v["pred"]})
            return em.out
        # no env answer (pure preview): the top units alone
        for u in _ranked(_units(body, statement))[:em.cap]:
            b = _apply(body, [u])
            if b is not None:
                em.add(f"{FAMILY}:raw", b, u.note)
        return em.out
    except Exception:  # noqa: BLE001
        return []
