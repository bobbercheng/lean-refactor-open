#!/usr/bin/env python3
"""Shared one-file screen of the opus lane ops (harness/post/opus_*.py).

  measured  harness/post/d4_measure.py: one `#eval` per variant that elaborates it and reads its heartbeats (needs the `Lean`
            package in the row's imports); a variant is proposed when d4_measure.predicted() > 0 against the incumbent (control).
            measured_parse (pass 3): d4_measure's own ok (theorem in the environment, no sorryAx) MISSES failures: a tactic error
            followed by "(kernel) declaration has metavariables" still logs ok 1 (MEASURED: 21 of 26 screen-OK rundrop runs then failed
            in the gate). So an error message (or a sorry warning) emitted after variant n-1's reading line and before variant n's
            fails variant n (the messages come in emission order; their positions are string-relative and useless here).
  plain     fallback when the measured file's control does not read (files that do not import `Lean`, e.g. core-only projects):
            the variants as plain renamed theorems in ONE file, each preceded by a `#check "LRAOPUSn"` marker; an error (or a
            sorry warning) located between marker n and marker n+1 fails variant n. No heartbeat reading: a variant that compiles
            is proposed when it is shorter (the gate then measures it). The control (the incumbent, variant 0) must compile clean.
Pure text building and parsing around the caller's run(text, version) (one charged compile per file)."""
from __future__ import annotations

# provenance: research lane gaplane-opus (worktree lra-gl-opus), commit ef7dde5, ported unchanged into open-post-v3 (2026-11-04)

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from scorer.tokenize import count_tokens  # noqa: E402

MARK = "LRAOPUS"
UNCHECKED = "skipKernelTC"   # a kernel-unchecked closer (the kskip op's): edits before it are not judged by Lean; no site


def selfref(statement: str, body: str, i: int) -> str:
    """The body with the theorem's own (short) name renamed to copy i's name (`lraD4M<i>`, the name MS.renamed gives): a
    recursive theorem (a `match` / induction proof that calls itself) otherwise refers to a name that does not exist yet in the
    screen file, and every copy (the control too) fails. Whole identifiers only, never after a `.` (a qualified reference)."""
    m = MS.DECL_RE.match(statement)
    if not m:
        return body
    name = re.split(r"\s+", m.group(0).strip())[-1].split(".{")[0]
    short = name.split(".")[-1]
    if not short or short not in body:
        return body
    return re.sub(r"(?<![\w'.!?])" + re.escape(short) + r"(?![\w'!?])", f"lraD4M{i}", body)


def unchecked(body: str) -> bool:
    return UNCHECKED in body


def plain_text(statement: str, bodies: list[str]) -> str | None:
    out = []
    for i, b in enumerate(bodies):
        r = MS.renamed(statement, i)
        if r is None:
            return None
        out.append(f'#check "{MARK}{i}"\n' + r.rstrip() + " :=" + selfref(statement, b, i).rstrip() + "\n")
    out.append(f'#check "{MARK}{len(bodies)}"\n')
    return "\n".join(out)


def _line(m) -> int | None:
    try:
        p = m.get("pos") or {}
        return int(p.get("line"))
    except Exception:
        return None


def plain_parse(messages, n: int) -> dict | None:
    """{i: ok} for i < n, or None when the markers were not all found."""
    marks: dict = {}
    bad_lines = []
    for m in messages or []:
        if not isinstance(m, dict):
            continue
        txt = K.msg_text(m)
        ln = _line(m)
        if ln is None:
            continue
        if f'"{MARK}' in txt and m.get("severity") == "information":
            try:
                k = int(txt.split(f'"{MARK}', 1)[1].split('"', 1)[0])
                marks[k] = ln
            except Exception:
                pass
            continue
        sev = m.get("severity")
        if sev == "error" or (sev == "warning" and "sorry" in txt):
            bad_lines.append(ln)
    if any(k not in marks for k in range(n + 1)):
        return None
    out = {}
    for i in range(n):
        a, b = marks[i], marks[i + 1]
        out[i] = not any(a < x < b for x in bad_lines)
    return out


def measured_parse(messages, n: int) -> dict:
    """d4_measure.parse plus the error rule above: {i: {"ok", "hb"}}."""
    rd = MS.parse(messages, n)
    bad, last = set(), None
    for m in messages if isinstance(messages, list) else []:
        if not isinstance(m, dict):
            continue
        txt = K.msg_text(m)
        tag = None
        for ln in txt.split("\n"):
            p = ln.strip().split("\t")
            if len(p) >= 3 and p[0] == "LRAD4M" and p[1].isdigit():
                tag = int(p[1])
        if tag is not None:
            if last == "err":
                bad.add(tag)
            last = None
            continue
        sev = m.get("severity")
        if sev == "error" or (sev == "warning" and "sorry" in txt):
            last = "err"
    for i in bad:
        if i in rd:
            rd[i] = dict(rd[i], ok=False)
    return rd


_PLAIN_ONLY: set = set()   # statements whose measured control did not read once (this process): later screens go plain directly


def screen(statement: str, body0: str, bodies: list[str], run, ctx: dict | None, log=None, tag: str = "opus",
           max_files: int = 1) -> dict | None:
    """{"up": [(body, predicted)], "unscreened": [bodies not read], "mode": "measured" | "plain"}, or None (nothing read)."""
    if MS.renamed(statement, 0) is None or not bodies:
        return None
    n = MS.budget(ctx or {})
    exch = (ctx or {}).get("exchange")
    up, read, mode = [], 0, ("plain" if statement in _PLAIN_ONLY else None)
    size, retried, files = n - 1, False, 0
    while files < max_files and read < len(bodies):
        files += 1
        chunk = bodies[read:read + size]
        if mode in (None, "measured"):
            text = MS.text(statement, [selfref(statement, b, i) for i, b in enumerate([body0] + chunk)])
            if text is None:
                return None
            r = run(text, None)
            rd = measured_parse(getattr(r, "messages", None), len(chunk) + 1)
            ctl = rd.get(0) or {"ok": False}
            if ctl.get("ok"):
                mode = "measured"
                for k, b in enumerate(chunk, 1):
                    pr = MS.predicted(ctl, body0, b, rd.get(k) or {"ok": False}, exch)
                    if pr is not None and pr > 0:
                        up.append((b, pr))
                read += len(chunk)
                continue
            if mode == "measured":
                # a later file's control did not read (MEASURED under load: the file ran past the query timeout): retry ONCE
                # with half the chunk, then stop
                if not retried and size >= 4:
                    retried, size = True, size // 2
                    files -= 1   # the retry does not count as a file
                    if log:
                        log(f"{tag}: measured screen file {files} did not read; retry with {size} variants")
                    continue
                break
            _PLAIN_ONLY.add(statement)
            if log:
                log(f"{tag}: measured screen control did not read; plain screen")
        mode = "plain"
        text = plain_text(statement, [body0] + chunk)
        if text is None:
            return None
        r = run(text, None)
        ok = plain_parse(getattr(r, "messages", None), len(chunk) + 1)
        if ok is None or not ok.get(0):
            if log:
                log(f"{tag}: plain screen unreadable (markers {'missing' if ok is None else 'ok, control failed'})")
            return None if read == 0 else {"up": up, "unscreened": bodies[read:], "mode": mode}
        t0 = count_tokens(body0)
        for k, b in enumerate(chunk, 1):
            if ok.get(k):
                up.append((b, float(t0 - count_tokens(b))))
        read += len(chunk)
    if log:
        log(f"{tag}: {mode} screen read {read} of {len(bodies)}; predicted up {len(up)}")
    return {"up": up, "unscreened": bodies[read:], "mode": mode}
