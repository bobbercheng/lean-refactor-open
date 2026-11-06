#!/usr/bin/env python3
# Vendored, unchanged except for this comment and the `harness.post` imports, from the closed line's bet D4 code (branch closed-bets-d4 402c44d2, harness/tools/d4_closerprep.py) for the open post-step harness/open_post.py (2026-11-03).
"""Bet D4C, "closerprep" (docs/closed_run2.md, closed-bets-d4 2026-11-02: a research move distilled into a generic rule): an end-stage
family ("closerprep", registered only by harness/end_d4.register() with the sub-switch D4C, never by default) with the
harness/sweep.candidates contract and an ENV QUERY (harness/endstage.py QUERY_FAMILIES; without an answer the family proposes nothing).
Every token of a candidate comes from the proof being edited or is Lean tactic syntax (INSERTS); no table, no row knowledge.

The rule: a decide-family closer C (`decide` with `+flag` / `-flag` options, never `+native`) decides the goal it is given; when one side
of that goal is a closed term, `conv_rhs => reduce` (or `conv_lhs`, or `conv => reduce`) on the line before C reduces it in the
elaborator, and the simp-family call earlier in the proof may then need fewer lemmas (what they computed, reduce computes). The insertion
alone usually costs tokens (3) and the list minimisation alone usually fails or costs heartbeats: the pair is the move.

  sites     a closer C alone on its line (outside comments and strings; a trailing comment allowed) at the end of its tactic block (the
            next code line is less indented, or there is none); at most MAX_SITES, the last ones first. A site is PREPARED when the code
            line before C, at C's indentation, is one of INSERTS.
  lists     the simp-family lemma lists (`simp` / `simp only` / `simp_all` / `simpa` / `dsimp` / `norm_num` / `field_simp`, options and
            configuration allowed before the `[`; never a search variant `simp?`) whose `[` lies before the site's line, at tactic
            position; the MAX_LISTS nearest to the site, 2 to MAX_ITEMS items each.
  drops     the complement half of ddmin's test sequence (harness/tools/d3_grind.ddmin_lists is the whole sequence): at granularity
            g = 2, 4, 8, ... up to the list's length n, each of the g chunks LEFT OUT, coarse to fine, then by position; distinct; the
            lists round robin.
  space     (unprepared site)
    closerprep:insert  each of INSERTS on the line before C, at C's indentation
    closerprep:joint   one insertion AND one drop of one list
            (prepared site: the insertion is already there, banked by an earlier greedy pass)
    closerprep:ddmin   one drop of one list (the end stage's greedy passes re-run it on the reduced list: ddmin's restart)
  query     the space is too large to screen and measure one candidate at a time on a row whose compile takes tens of seconds, so the
            query reads it in one-file batches (harness/tools/d4_measure.py: every variant elaborated in one `#eval` between two heartbeat
            readings, ok = no sorryAx; the incumbent first as the control; at most d4_measure.budget(ctx) variants per file): file 1
            the insertions of the unprepared sites and the drops of the prepared ones; file 2 (an unprepared site whose insertions read)
            the joint variants with the insertion that read the fewest heartbeats. Two compiles at most, charged to the tool phase and the
            family's cap.
  generate  the measured variants predicted to read higher than the control (d4_measure.predicted: heartbeats saved minus tokens added
            times the row's exchange rate), best first, at most PROPOSE. Insertions add tokens: the prediction prices them.
The caller measures every proposal back to back with its incumbent (batch screen with the heartbeat bound, paired decide, all-pin
confirmation): the query's readings only choose what is proposed. No harm: no site, no answer, a failed variant or a budget stop proposes
or banks nothing; the final is a floor. Generic by construction: no row names, lemma names, proof fragments or tables.
    python3 harness/tools/d4_closerprep.py --file proof.lean --statement-file stmt.txt     sites and the query's space as JSON lines"""
from __future__ import annotations

import argparse, json, re, sys, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs  # noqa: E402
from harness.lint_delete import _list_items  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from scorer.tokenize import split_declaration  # noqa: E402

FAMILY = "closerprep"
OPS = ("closerprep:insert", "closerprep:joint", "closerprep:ddmin")
ALL_OPS = OPS
OPT_IN_OPS: tuple = ()
DEFAULT_OPS = OPS
QUERY_OPS = OPS
TABLES: dict = {}
INSERTS = ("conv_rhs => reduce", "conv_lhs => reduce", "conv => reduce")
MAX_PER_OP = 8
PROPOSE = 3            # proposals per incumbent (the best predicted)
QUERY_TIMEOUT = 300
MAX_SITES = 2
MAX_LISTS = 2
MAX_ITEMS = 40

CLOSER_RE = re.compile(r"^decide(?:[ \t]+[+-][A-Za-z][\w.]*)*$")
HEAD_RE = re.compile(r"(?<![\w.'?!])(simp_all|simpa|simp|dsimp|norm_num|field_simp)(!?)(?![\w'?!])")
TACPOS_RE = re.compile(r"(?:^[ \t]*(?:·[ \t]*)?|(?:;|<;>|(?<![\w.'])by|=>)[ \t]*)$")
FLAG_RE = re.compile(r"[+-][^\W\d][\w'.]*")


def _code(line: str, mask_line) -> str:
    """The line's code: comment / string characters blanked."""
    return "".join(" " if mask_line[i] else ch for i, ch in enumerate(line))


def _lines(body: str):
    """[(start offset, line text, code text)] of the body's lines."""
    mask = _mask(body)
    out, pos = [], 0
    for ln in body.split("\n"):
        out.append((pos, ln, _code(ln, mask[pos:pos + len(ln)])))
        pos += len(ln) + 1
    return out


def _indent(s: str) -> int:
    return len(s) - len(s.lstrip(" \t"))


def closer_sites(body: str) -> list[dict]:
    """[{"lo", "hi": the closer's span, "closer", "indent", "line_start", "prepared": the INSERTS line before it or None}] (module
    docstring, "sites"), the last ones first."""
    ls = _lines(body)
    out = []
    for i, (start, ln, code) in enumerate(ls):
        c = code.strip()
        if i == 0 or not c or not CLOSER_RE.match(re.sub(r"[ \t]+", " ", c)) or "native" in c:
            continue   # (line 0 is the `:=` line: a closer there is not alone on its line)
        ind = _indent(code)
        nxt = next((x for x in ls[i + 1:] if x[2].strip()), None)
        if nxt is not None and _indent(nxt[2]) >= ind:
            continue   # not the end of its tactic block
        prv = next((x for x in reversed(ls[:i]) if x[2].strip()), None)
        prep = None
        if prv is not None and _indent(prv[2]) == ind and re.sub(r"[ \t]+", " ", prv[2].strip()) in INSERTS:
            prep = {"lo": prv[0], "hi": prv[0] + len(prv[1]), "ins": re.sub(r"[ \t]+", " ", prv[2].strip())}
        lo = start + ind
        out.append({"lo": lo, "hi": lo + len(c), "closer": re.sub(r"[ \t]+", " ", c), "indent": code[:ind], "line_start": start,
                    "prepared": prep})
    out.reverse()
    return out[:MAX_SITES]


def _tacpos(body: str, i: int) -> bool:
    ls = body.rfind("\n", 0, i) + 1
    return TACPOS_RE.search(body[ls:i]) is not None


def simp_lists(body: str, before: int | None = None, max_lists: int = MAX_LISTS, min_items: int = 2,
               max_items: int = MAX_ITEMS) -> list[dict]:
    """The simp-family lemma lists of the body (module docstring, "lists") whose `[` lies before offset `before` (None: anywhere) and that
    hold min_items to max_items items, the max_lists nearest first: [{"h0", "h1": the head's span, "head", "bang", "lb", "rb": the
    brackets, "items": [(a, b)]}]."""
    mask = _mask(body)
    pairs = _pairs(body, mask)
    out = []
    for m in HEAD_RE.finditer(body):
        h0 = m.start()
        if mask[h0] or not _tacpos(body, h0):
            continue
        p = m.end()
        while True:   # options before the list on the head's line: blanks, `only`, `(...)` groups, `+flag` / `-flag`
            q = p
            while q < len(body) and body[q] in " \t":
                q += 1
            if q >= len(body) or mask[q]:
                p = q
                break
            if body.startswith("only", q) and not re.match(r"[\w'.]", body[q + 4:q + 5] or " "):
                p = q + 4; continue
            if body[q] == "(" and q in pairs:
                p = pairs[q] + 1; continue
            fm = FLAG_RE.match(body, q)
            if fm and not body.startswith("--", q):
                p = fm.end(); continue
            p = q
            break
        if p >= len(body) or body[p] != "[" or mask[p] or p not in pairs:
            continue
        if before is not None and p >= before:
            continue
        items = _list_items(body, mask, pairs, p) or []
        if not min_items <= len(items) <= max_items:
            continue
        out.append({"h0": h0, "h1": m.end(), "head": m.group(1), "bang": m.group(2), "lb": p, "rb": pairs[p], "items": list(items)})
    out.sort(key=lambda L: -L["lb"])
    return out[:max_lists]


def drops(n: int) -> list[list[int]]:
    """The complement half of ddmin's sequence on n items (module docstring, "drops"): index lists to leave out, coarse to fine."""
    out, seen = [], set()
    if n < 2:
        return out
    g = 2
    while True:
        g = min(g, n)
        size = n / g
        for j in range(g):
            ch = list(range(int(round(j * size)), int(round((j + 1) * size))))
            if ch and len(ch) < n and tuple(ch) not in seen:
                seen.add(tuple(ch)); out.append(ch)
        if g >= n:
            break
        g *= 2
    return out


def with_drop(body: str, L: dict, drop: list[int]) -> str:
    keep = [body[a:b] for j, (a, b) in enumerate(L["items"]) if j not in set(drop)]
    return body[:L["lb"] + 1] + ", ".join(keep) + body[L["rb"]:]


def with_insert(body: str, s: dict, ins: str) -> str:
    return body[:s["line_start"]] + s["indent"] + ins + "\n" + body[s["line_start"]:]


def _at(body: str, s: dict) -> str:
    return f"`{s['closer']}` @L{K.line_of(body, s['lo'])}"


def _drop_note(body: str, L: dict, d: list[int]) -> str:
    return f"items {d[0] + 1}-{d[-1] + 1} of {len(L['items'])} left out of `{L['head']}` @L{K.line_of(body, L['h0'])}"


def _round_robin(lists: list[dict]):
    per = [(L, drops(len(L["items"]))) for L in lists]
    for k in range(max([len(ds) for _, ds in per] or [0])):
        for L, ds in per:
            if k < len(ds):
                yield L, ds[k]


def insert_space(body: str, s: dict) -> list[tuple[str, str, str]]:
    return [("closerprep:insert", with_insert(body, s, ins), f"`{ins}` before {_at(body, s)}") for ins in INSERTS]


def joint_space(body: str, s: dict, ins: str) -> list[tuple[str, str, str]]:
    """The insertion `ins` with each drop (the list lies before the closer's line: the insertion moves none of its offsets)."""
    return [("closerprep:joint", with_drop(with_insert(body, s, ins), L, d), f"`{ins}` before {_at(body, s)} and {_drop_note(body, L, d)}")
            for L, d in _round_robin(simp_lists(body, before=s["line_start"]))]


def drop_space(body: str, s: dict) -> list[tuple[str, str, str]]:
    return [("closerprep:ddmin", with_drop(body, L, d), f"{_drop_note(body, L, d)} (`{s['prepared']['ins']}` before {_at(body, s)})")
            for L, d in _round_robin(simp_lists(body, before=s["line_start"]))]


def query(proof: str, statement: str, run, *, versions=None, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict | None:
    """The measured space (module docstring, "query"). Always returns {"closerprep_query": {...}, "closerprep_query_for": key}; no site:
    no compile. "variants": [{"op", "body", "note", "file", "ok", "hb"}], "controls": {file: reading of the incumbent}."""
    st = stats if stats is not None else {}
    log = log or (lambda *a: None)
    ctx = ctx or {}
    t0 = time.time()
    key = K.proof_key(proof)
    body = split_declaration(proof, statement)
    ops = K.ops_for(FAMILY, OPS, DEFAULT_OPS, OPT_IN_OPS, ctx)
    ss = closer_sites(body) if body is not None else []
    q = {"answered": False, "variants": [], "controls": {}}
    if not ss or MS.renamed(statement, 0) is None:
        q["skip"] = "no decide-family closer alone on its line at the end of a block of a theorem's tactic proof"
        st["query"] = {"ids": 0, "used": 0, "vars": 0, "class_vars": 0, "skip": q["skip"]}
        return {"closerprep_query": q, "closerprep_query_for": key}
    n = MS.budget(ctx)
    vs = list(versions or [None])

    def measure(space, f):
        space = [x for x in space if x[0] in ops][:n - 1]
        if not space:
            return {}
        mt = MS.text(statement, [body] + [x[1] for x in space])
        if mt is None:
            return {}
        rd = MS.parse(getattr(run(mt, vs[0]), "messages", None), len(space) + 1)
        q["controls"][str(f)] = rd.get(0) or {"ok": False}
        for i, (op, nb, note) in enumerate(space, 1):
            q["variants"].append({"op": op, "body": nb, "note": note, "file": f, **(rd.get(i) or {"ok": False, "hb": None})})
        return rd
    first = []
    for s in ss:
        first += insert_space(body, s) if s["prepared"] is None else drop_space(body, s)
    measure(first, 1)
    un = [s for s in ss if s["prepared"] is None]
    if un and (q["controls"].get("1") or {}).get("ok") and "closerprep:joint" in ops:
        s = un[0]
        read = [v for v in q["variants"] if v["op"] == "closerprep:insert" and v.get("ok") and v["note"].endswith(_at(body, s))]
        if read:
            ins = v_ins(min(read, key=lambda v: v["hb"])["note"])
            if ins in INSERTS:
                measure(joint_space(body, s, ins), 2)
    q["answered"] = any((c or {}).get("ok") for c in q["controls"].values())
    if not q["answered"]:
        q["skip"] = "the control did not read in the measuring file"
    q["seconds"] = round(time.time() - t0, 2)
    nread = sum(1 for v in q["variants"] if v.get("ok"))
    st["query"] = {"ids": len(ss), "used": len(q["controls"]), "vars": nread, "class_vars": 0, "seconds": q["seconds"],
                   **({"skip": q["skip"]} if q.get("skip") else {})}
    log(f"closerprep: {len(ss)} site(s), {len(q['variants'])} variant(s) measured in {len(q['controls'])} file(s), {nread} read; "
        f"control {[c.get('hb') for c in q['controls'].values()]} in {q['seconds']} s" + (f" ({q['skip']})" if q.get("skip") else ""))
    return {"closerprep_query": q, "closerprep_query_for": key}


def v_ins(note: str) -> str | None:
    """The insertion named first in a variant's note."""
    m = re.match(r"^`([^`]+)`", note)
    return m.group(1) if m else None


def proposals(q: dict, body: str, exchange: float | None, family_ops) -> list[tuple[float, dict]]:
    """[(predicted, variant)] of the measured variants predicted to read higher than their file's control, best first."""
    out = []
    for v in q.get("variants") or []:
        if v.get("op") not in family_ops:
            continue
        pr = MS.predicted((q.get("controls") or {}).get(str(v.get("file"))) or {}, body, v.get("body") or "", v, exchange)
        if pr is not None and pr > 0:
            out.append((pr, v))
    out.sort(key=lambda x: -x[0])
    return out


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int | None = None,
               ctx: dict | None = None) -> list[dict]:
    ctx = ctx or {}
    ops = K.ops_for(FAMILY, OPS, DEFAULT_OPS, OPT_IN_OPS, ctx)
    hb = K.head_body(proof, statement)
    if hb is None or not ops:
        return []
    head, body = hb
    q = ctx.get("closerprep_query")
    if not (q and ctx.get("closerprep_query_for") == K.proof_key(proof) and q.get("answered")):
        return []
    em = K.Emitter(proof, statement, head, body, int(max_per_op) if max_per_op else MAX_PER_OP)
    n = 0
    for pr, v in proposals(q, body, exchange if exchange is not None else ctx.get("exchange"), ops):
        if n >= PROPOSE:
            break
        if em.add(v["op"], v["body"], f"{v['note']} (query: {v['hb']} hb, predicted +{pr:.0f})", save=False):
            n += 1
    return em.out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description="closerprep sites and the query's space of one declaration (no compile)")
    ap.add_argument("--file", required=True); ap.add_argument("--statement-file", required=True)
    a = ap.parse_args(argv)
    proof = Path(a.file).read_text(); stmt = Path(a.statement_file).read_text().rstrip("\n")
    body = split_declaration(proof, stmt) or ""
    for s in closer_sites(body):
        print(json.dumps({"site": s["closer"], "line": K.line_of(body, s["lo"]), "prepared": bool(s["prepared"]),
                          "lists": [len(L["items"]) for L in simp_lists(body, before=s["line_start"])]}, ensure_ascii=False))
        sp = insert_space(body, s) + joint_space(body, s, INSERTS[0]) if s["prepared"] is None else drop_space(body, s)
        for op, _, note in sp:
            print(json.dumps({"op": op, "note": note}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
