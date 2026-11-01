"""Goal map of a tactic proof: the goal state before each top-level step (and, with depth 2, before each step one level down).

2026-10-07: the hard-tail problems (the same ones are worst for every model: SKI diamond, WickAlgebra, Fsub progress, ...)
need a different strategy (full restructure, lemma search) rather than more passes. The agent only ever sees compiler ERRORS, never the
goals its proof walks through, so it can neither tell which steps are routine nor ask the library for a lemma that closes a goal.
This inserts Lean's `trace_state` before the chosen steps, compiles once in the problem's real environment, and returns
[{line, tactic, goals, n_goals}] keyed by the candidate file's own line numbers.

    python3 harness/goals.py <problem> <candidate.lean> [--depth 2]
"""
from __future__ import annotations

import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "harness")]

_SKIP = re.compile(r"^(\||<;>|\)|\]|,|_\s*[=<≤>≥]|\.\.|--|/-|calc\b)")
_OPENS = re.compile(r"(=>|\bby|\bwith|\bdo|·.*|\bthen|\belse)\s*$")


def _indent(s: str) -> int:
    return len(s) - len(s.lstrip(" "))


def instrument(decl: str, statement: str, depth: int = 1) -> tuple[str, list[dict]] | None:
    """Return (instrumented declaration, probes) or None for a term-mode proof. Each probe: {"line": candidate line (1-based),
    "tactic": text, "at": line of its trace_state in the instrumented text (1-based)}."""
    start = decl.find(statement)
    if start < 0:
        return None
    head_end = start + len(statement)
    m = re.match(r"\s*:=\s*by\b[ \t]*", decl[head_end:])
    if not m:
        return None
    head = decl[:head_end + m.end()]
    rest = decl[head_end + m.end():]
    head_lines = head.count("\n")
    lines = rest.split("\n")
    first_line_no = head_lines + 1              # candidate line of lines[0] (same line as `by` when it holds a tactic)
    body = [(i, l) for i, l in enumerate(lines) if l.strip() and not l.strip().startswith("--")]
    if not body:
        return None
    inline = lines[0].strip() != ""
    if inline:                                   # `:= by tac` on one line: move the tactic to its own line
        ind = min([_indent(l) for i, l in body if i > 0] or [2])
        lines[0] = " " * ind + lines[0].strip()
        body = [(i, l) for i, l in enumerate(lines) if l.strip() and not l.strip().startswith("--")]
    levels = sorted({_indent(l) for _, l in body})
    allowed = set(levels[:max(1, depth)])
    probes, out = [], [head.rstrip(" \t") + ("\n" if not head.endswith("\n") else "")]
    if not inline and lines and lines[0] == "":
        lines = lines[1:]; first_line_no += 1
    cur = head.count("\n") + (0 if head.endswith("\n") else 1)
    prev_nonblank = ""
    for k, l in enumerate(lines):
        s = l.strip(); ind = _indent(l)
        ok = bool(s) and not s.startswith("--") and ind in allowed and not _SKIP.match(s)
        if ok and ind != levels[0]:              # nested level: only directly inside a block opener (bullet, `=>`, `by`, ...)
            ok = bool(_OPENS.search(prev_nonblank.rstrip())) or prev_nonblank.lstrip().startswith("·") or _indent(prev_nonblank) == ind
        if ok and prev_nonblank.rstrip().endswith((",", "(", "[", "⟨", "<;>", "|", ":=", "←")):
            ok = False                           # continuation of the previous tactic
        if ok:
            cur += 1
            out.append(" " * ind + "trace_state\n")
            probes.append({"line": first_line_no + k, "tactic": s[:90], "at": cur})
        cur += 1
        out.append(l + ("\n" if k < len(lines) - 1 else ""))
        if s and not s.startswith("--"):
            prev_nonblank = l
    return "".join(out), probes


def _goal_digest(state: str, limit: int) -> str:
    """First goal with its hypotheses (hypotheses elided if long); every further goal as one line `case <name>: ⊢ <target>`, so the
    model sees the whole case split (which cases exist, which are alike) without the repeated contexts."""
    goals = [g.strip() for g in re.split(r"\n\s*\n", state.strip()) if g.strip()]
    if not goals:
        return ""
    def one_line(g):
        case = re.match(r"case (\S+)", g)
        tgt = g.rsplit("⊢", 1)[1].strip() if "⊢" in g else g.splitlines()[-1]
        return f"case {case.group(1) if case else '?'}: ⊢ " + re.sub(r"\s+", " ", tgt)[:160]
    first = goals[0]
    if len(first) > limit:
        tgt = "⊢" + first.rsplit("⊢", 1)[1] if "⊢" in first else first[-limit // 2:]
        first = first[: max(0, limit - len(tgt) - 30)].rstrip() + "\n  … [hypotheses omitted]\n" + tgt
    rest = [one_line(g) for g in goals[1:]]
    if len(rest) > 12:
        rest = rest[:12] + [f"… and {len(rest) - 12} more goals"]
    return first + ("\n" + "\n".join(rest) if rest else "")


def goal_map(name: str, decl: str, depth: int = 1, per_goal: int = 700, total: int = 9000, from_line: int = 0) -> dict:
    from mine import ROWS, lean_run
    row = ROWS[name]
    inst = instrument(decl, row["statement"], depth)
    if inst is None:
        return {"ok": False, "note": "term-mode proof (no `:= by` tactic block): no steps to trace. Use lean_run `example ... := by exact?` on the statement instead."}
    code, probes = inst
    msgs = lean_run(name, code, timeout=600)
    by_line = {}
    for m in msgs:
        if m["severity"] == "information" and m["line"] in {p["at"] for p in probes}:
            by_line.setdefault(m["line"], []).append(m["data"])
    errs = [m for m in msgs if m["severity"] == "error"]
    steps = []
    for p in probes:
        if p["line"] < from_line:
            continue
        st = "\n".join(by_line.get(p["at"], []))
        if not st:
            continue
        n = st.count("⊢")
        steps.append({"line": p["line"], "tactic": p["tactic"], "n_goals": n, "goals": "no goals" if "no goals" in st[:40] else _goal_digest(st, per_goal)})
    out = {"ok": not errs, "steps": steps}
    if errs:
        out["note"] = (f"{len(errs)} error(s) while tracing (first: line {errs[0]['line']}: {errs[0]['data'][:160]}); goals listed are those reached before it. "
                       + ("Retry with depth 1." if depth > 1 else ""))
    s = json.dumps(out, ensure_ascii=False)
    while len(s) > total and per_goal > 150:     # shrink each goal until the map fits
        per_goal = int(per_goal * 0.7)
        for st_, p in zip(out["steps"], steps):
            st_["goals"] = _goal_digest(by_line.get(next(q["at"] for q in probes if q["line"] == st_["line"]), [""])[0], per_goal) if st_["goals"] != "no goals" else "no goals"
        s = json.dumps(out, ensure_ascii=False)
    if len(s) > total:                           # still too long: keep the first steps, say how to see the rest
        keep = list(out["steps"])
        while keep and len(json.dumps({**out, "steps": keep}, ensure_ascii=False)) > total - 200:
            keep.pop()
        out["note"] = (out.get("note", "") + f" Showing steps 1-{len(keep)} of {len(out['steps'])}; pass from_line={out['steps'][len(keep)]['line']} for the rest.").strip()
        out["steps"] = keep
    return out


_TACTIC_CTX = re.compile(r"(^|\bby|=>|·|<;>|;|\bthen|\belse|\bdo)\s*$")


def skeleton_check(name: str, draft: str, per_goal: int = 700, total: int = 9000) -> dict:
    """Top-down development (Tier 1, panel R1): check a draft whose unfinished parts are `sorry` holes and return each hole's goal, plus the
    real errors (anything except the 'declaration uses sorry' warning). Scratch compile only: a draft with holes can never be banked."""
    from mine import lean_run
    lines = draft.split("\n"); holes = []
    for li, line in enumerate(lines):
        out, pos = [], 0
        for m in re.finditer(r"\bsorry\b", line):
            before = line[:m.start()]
            tactic = bool(_TACTIC_CTX.search(before.rstrip()) or not before.strip())
            out.append(line[pos:m.start()] + ("(trace_state; sorry)" if tactic else "(by trace_state; exact sorry)"))
            pos = m.end(); holes.append({"hole": len(holes) + 1, "line": li + 1, "position": "tactic" if tactic else "term"})
        if out:
            lines[li] = "".join(out) + line[pos:]
    if not holes:
        return {"ok": False, "note": "no `sorry` holes in the draft; use lean_check for a complete candidate."}
    msgs = lean_run(name, "\n".join(lines), timeout=600)
    infos = {}
    for m in msgs:
        if m["severity"] == "information":
            infos.setdefault(m["line"], []).append(m["data"])
    used = {}
    for h in holes:
        k = used.get(h["line"], 0); states = infos.get(h["line"], [])
        h["goal"] = _goal_digest(states[k], per_goal) if k < len(states) else "(not reached: an error before this hole stops elaboration)"
        used[h["line"]] = k + 1
    errs = [f"line {m['line']}: {m['data'][:300]}" for m in msgs if m["severity"] == "error"]
    out = {"ok": not errs, "holes": holes, "errors": errs[:6],
           "note": "fill one hole at a time and re-run lean_skeleton; lean_check the full candidate only when no sorry remains (sorry is forbidden in candidates)."}
    s = json.dumps(out, ensure_ascii=False)
    while len(s) > total and per_goal > 150:
        per_goal = int(per_goal * 0.7)
        for h in holes:
            if not h["goal"].startswith("(not reached"):
                h["goal"] = h["goal"][:per_goal]
        s = json.dumps(out, ensure_ascii=False)
    return out


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(); ap.add_argument("problem"); ap.add_argument("file"); ap.add_argument("--depth", type=int, default=1); ap.add_argument("--from-line", type=int, default=0)
    a = ap.parse_args()
    print(json.dumps(goal_map(a.problem, Path(a.file).read_text(), a.depth, from_line=a.from_line), ensure_ascii=False, indent=1))
