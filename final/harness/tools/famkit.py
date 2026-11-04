#!/usr/bin/env python3
"""Shared pieces of the compiled-fact families t8 (instance pin) and t11 (relation template), b63 (docs/adaptive_plan_93.md §4.1 items












"""
from __future__ import annotations

import json, re, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TABLE_DIRS = (ROOT / "harness/tools/tables", ROOT / "probe/b63/dxr")

OPEN = {"(": ")", "[": "]", "{": "}", "⦃": "⦄", "⟨": "⟩"}
CLOSE = {v: k for k, v in OPEN.items()}
_IDC = r"\w'!?₀-₉"
IDENT = re.compile(r"(?<![" + _IDC + r".])[^\W\d][" + _IDC + r"]*(?:\.[^\W\d][" + _IDC + r"]*)*")
DECL_HEAD = re.compile(r"(?:^|\n)\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*"
                       r"(theorem|lemma|def|instance|example|abbrev)\s+([^\s:({\[⦃]+)?", re.S)
_MEMO: dict = {}


def load_table(name: str) -> dict:
    if name in _MEMO:
        return _MEMO[name]
    for d in TABLE_DIRS:
        p = d / f"{name}.json"
        if p.is_file():
            try:
                _MEMO[name] = json.loads(p.read_text())
                return _MEMO[name]
            except (OSError, ValueError):
                pass
    _MEMO[name] = {}
    return {}


def depth0_positions(text: str, seps) -> list[tuple[int, str]]:
    """(position, separator) for every occurrence of a separator at bracket depth 0, longest separators matched first."""
    seps = sorted(seps, key=len, reverse=True)
    out, depth, i, n = [], 0, 0, len(text)
    while i < n:
        c = text[i]
        if c in OPEN:
            depth += 1
        elif c in CLOSE:
            depth -= 1
        elif depth == 0:
            for s in seps:
                if text.startswith(s, i):
                    out.append((i, s))
                    i += len(s) - 1
                    break
        i += 1
    return out


def depth0_split(text: str, seps) -> list[str]:
    parts, last = [], 0
    for p, s in depth0_positions(text, seps):
        parts.append(text[last:p])
        last = p + len(s)
    parts.append(text[last:])
    return parts


def _groups(text: str) -> list[tuple[int, int]]:
    """Top-level bracket groups (start, end exclusive) of `text`."""
    out, depth, start = [], 0, None
    for i, c in enumerate(text):
        if c in OPEN:
            if depth == 0:
                start = i
            depth += 1
        elif c in CLOSE:
            depth -= 1
            if depth == 0 and start is not None:
                out.append((start, i + 1))
                start = None
    return out


def statement_parts(statement: str) -> dict:
    st = statement.rstrip()
    m = None
    for m_ in DECL_HEAD.finditer(st):
        m = m_
    if m is None:
        return {"ok": False}
    name = (m.group(2) or "").strip()
    rest = st[m.end():]
    colon = next((p for p, _ in depth0_positions(rest, [":"]) if not rest.startswith(":=", p)), None)
    header = rest if colon is None else rest[:colon]
    typ = "" if colon is None else rest[colon + 1:].strip()
    binders = []
    for a, b in _groups(header):
        g = header[a:b]
        kind = {"[": "inst", "(": "explicit", "{": "implicit", "⦃": "strict"}.get(g[0])
        if kind is None:
            continue
        inner = g[1:-1].strip()
        bn, bt = None, inner
        cp = [p for p, _ in depth0_positions(inner, [":"]) if not inner.startswith(":=", p)]
        if cp:
            bn, bt = inner[:cp[0]].strip(), inner[cp[0] + 1:].strip()
        if kind == "inst" and bn is not None and not re.fullmatch(r"[\w'!?₀-₉\s]+", bn):                                        
            bn, bt = None, inner
        binders.append({"kind": kind, "text": g, "name": bn, "type": bt})
                                                                       
    t = typ
    hyps = 0
    while True:
        t2 = t.lstrip()
        if t2.startswith(("∀", "Π")):
            cm = next((p for p, _ in depth0_positions(t2, [","])), None)
            if cm is None:
                break
            seg = t2[:cm]
            hyps += max(1, len(_groups(seg)) or len(seg.split()) - 1)
            t = t2[cm + 1:]
            continue
        arrows = depth0_positions(t2, ["→"])
        if arrows:
            hyps += 1
            t = t2[arrows[0][0] + 1:]
            continue
        break
    return {"ok": True, "name": name, "binders": binders, "type": typ, "hyps": hyps, "concl": t.strip()}


def body_of(decl: str, statement: str):
    from scorer.tokenize import split_declaration
    return split_declaration(decl, statement)


def first_tactic_insert(decl: str, statement: str, line: str) -> str | None:
    body = body_of(decl, statement)
    if body is None:
        return None
    head = decl[:len(decl) - len(body)]
    b = body.lstrip()
    if b.startswith(":="):                                                                                  
        b = b[2:]
    elif head.rstrip().endswith(":="):
        head = head.rstrip()[:-2].rstrip()
    else:
        return None
    s = b.lstrip()
    if s.startswith("by") and (len(s) == 2 or s[2].isspace()):
        rest = s[2:]
        lines = rest.split("\n")
        if lines[0].strip():                                                                                             
            inline = lines[0].strip()
            tail = lines[1:]
            ind = min((len(l) - len(l.lstrip()) for l in tail if l.strip()), default=2)
            ind = max(ind, 1)
            return _join(head) + ":= by\n" + " " * ind + line + "\n" + " " * ind + inline + ("\n" + "\n".join(tail) if tail else "")
        tail = lines[1:]
        ind = min((len(l) - len(l.lstrip()) for l in tail if l.strip()), default=2)
        return _join(head) + ":= by\n" + " " * ind + line + "\n" + "\n".join(tail)
    term = s.strip()
    if not term:
        return None
    return _join(head) + ":= by\n  " + line + "\n  exact (" + term + ")"


def _join(head: str) -> str:
    """The header with exactly one space before the `:=` that follows (b63 t8: a stripped `:=` glued `T:= by`, measured on T10's banks)."""
    return head if head.endswith((" ", "\n")) else head + " "


class Screen:
    """Paired readings on the workbench with the contract's counters. read(decls) -> list of readings (each with "d_score" when ok)."""

    def __init__(self, wb, incumbent: str, *, meter_reading: dict | None = None, deadline: float | None = None, max_checks: int = 400,
                 timeout: float = 30.0, chunk: int = 16, log=None):
        self.wb, self.inc = wb, incumbent
        self.meter_hb = (meter_reading or {}).get("heartbeats")
        self.inc_score = (meter_reading or {}).get("score_exact")
        self.deadline, self.max_checks, self.timeout, self.chunk = deadline, max_checks, timeout, chunk
        self.log = log or (lambda *a: None)
        self.stats = {"readings": 0, "compiled": 0, "timeouts": 0, "calls": 0, "seconds": 0.0, "errors": {}, "budget_out": False}
        self._inc_est = None

    def left(self) -> bool:
        if self.deadline is not None and time.time() >= self.deadline:
            self.stats["budget_out"] = True
            return False
        if self.stats["readings"] >= self.max_checks:
            self.stats["budget_out"] = True
            return False
        return True

    def read(self, decls: list[str]) -> list[dict]:
        out: list = []
        for i in range(0, len(decls), self.chunk):
            if not self.left():
                break
            batch = decls[i:i + self.chunk]
            t0 = time.time()
            try:
                p = self.wb.paired(self.inc, batch, meter_hb=self.meter_hb, timeout=self.timeout)
            except Exception as e:                
                cls = type(e).__name__
                self.stats["errors"][cls] = self.stats["errors"].get(cls, 0) + 1
                self.log(f"famkit screen: workbench call failed ({cls}: {str(e)[:120]})")
                break
            self.stats["calls"] += 1
            self.stats["seconds"] += time.time() - t0
            inc = p.get("incumbent") or {}
            if self._inc_est is None and inc.get("status") == "ok":
                hb0 = self.meter_hb if self.meter_hb is not None else inc.get("heartbeats")
                m = self.wb.metrics(inc["tokens"], hb0)
                self._inc_est = m["score_exact"] if self.inc_score is None else self.inc_score
            for d, r in zip(batch, p.get("readings") or []):
                self.stats["readings"] += 1
                r = dict(r, decl=d)
                if r.get("status") == "ok":
                    self.stats["compiled"] += 1
                    if self._inc_est is not None and r.get("score_exact") is not None:
                        r["d_score"] = round(r["score_exact"] - self._inc_est, 6)
                else:
                    if r.get("status") == "timeout":
                        self.stats["timeouts"] += 1
                    cls = _err_class(r)
                    self.stats["errors"][cls] = self.stats["errors"].get(cls, 0) + 1
                out.append(r)
        return out


def _err_class(r: dict) -> str:
    e = str(r.get("error") or (r.get("errors") or [""])[0] or r.get("status") or "")
    e = e.lower()
    for k, lab in (("unknown identifier", "unknown_ident"), ("unknown constant", "unknown_ident"), ("unsolved goals", "unsolved"),
                   ("type mismatch", "type_mismatch"), ("failed to unify", "unify"), ("could not unify", "unify"),
                   ("timeout", "timeout"), ("heartbeats", "heartbeats"), ("fun_induction", "fun_induction"),
                   ("unexpected token", "syntax"), ("expected", "syntax"), ("statement differs", "statement"),
                   ("not a structural", "fun_induction"), ("failed to synthesize", "synth"), ("apply", "apply"),
                   ("linarith", "closer"), ("simp", "closer"), ("sorry", "sorry")):
        if k in e:
            return lab
    return (r.get("status") or "other")[:20]
