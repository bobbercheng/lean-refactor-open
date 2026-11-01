"""Heartbeat profile of a tactic proof: where the heartbeats go, block by block, and the floor (Tier 1, panel proposal R1).

Four panel analysts built the same tool by hand (variational, interleaved, fiberwise, substOldPostSubset): cut the proof after each top-level step,
close the rest with `all_goals sorry`, measure the declaration's heartbeats, and take differences. The floor is the statement with a `sorry` body:
H can never pass (1 - floor / reference) on that problem, so it tells the agent how many heartbeat points are really left.

    python3 harness/profile.py <problem> <candidate.lean> [--max-cuts 10]
"""
from __future__ import annotations

import json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT), str(ROOT / "harness")]


def _measure(row: dict, decl: str, version: str) -> int | None:
    from scorer.compile import compile_putnam, compile_project
    r = (compile_putnam(row["header"], decl, version, count=True, timeout=600) if row["source"] == "putnambench"
         else compile_project(row, decl, version, count=True, timeout=600))
    return r.heartbeats if r.ok else None


def _sequences(lines: list[str], first: int) -> list[dict]:
    """Tactic sequences: runs of step-start lines at one indentation inside the same parent block. A step owns the following lines that are
    indented deeper; `|` arm lines at the same indentation belong to the step that opened them (`induction … with`); bullets and `case` are
    sibling steps. A suffix cut closes everything that remains with `all_goals sorry`."""
    def ind(l): return len(l) - len(l.lstrip(" "))
    body = [k for k in range(first, len(lines)) if lines[k].strip() and not lines[k].strip().startswith("--")]
    seqs, used = [], set()
    for k in body:
        if k in used:
            continue
        s = lines[k].strip()
        if s.startswith(("|", "<;>", ")", "]", ",")):
            continue
        d = ind(lines[k]); steps = [k]; used.add(k); m = k + 1
        while m < len(lines):
            if not lines[m].strip() or lines[m].strip().startswith("--"):
                m += 1; continue
            dm = ind(lines[m])
            if dm < d:
                break
            if dm == d:
                if lines[m].strip().startswith(("|", "<;>")):   # arms of `induction/cases/match … with` belong to the step that opened them
                    used.add(m); m += 1; continue
                steps.append(m); used.add(m)                    # bullets / `case` / `next` are sibling steps
            m += 1
        seqs.append({"indent": d, "steps": steps, "end": m})
    return seqs


def profile(name: str, decl: str, max_cuts: int = 12) -> dict:
    from mine import ROWS
    from probe.verify_candidates import newest_first
    from goals import instrument
    from scorer.score import local_reference_heartbeats
    row = ROWS[name]; primary = newest_first(row["version_info"])[0]
    stmt = row["statement"]
    if instrument(decl, stmt, 1) is None:
        return {"ok": False, "note": "term-mode proof (no `:= by` block): only the total and the floor are measured.",
                "total": _measure(row, decl, primary), "floor": _measure(row, stmt.rstrip() + " := by\n  sorry", primary)}
    lines = decl.split("\n")
    head_end = next(k for k, l in enumerate(lines) if re.search(r":=\s*by\s*$", l) or re.search(r":=\s*by\b", l))
    first = head_end + 1
    seqs = _sequences(lines, first)
    total = _measure(row, decl, primary)
    floor = _measure(row, stmt.rstrip() + " := by\n  sorry", primary)
    budget = max_cuts; costs = []
    def suffix_cost(seq, k_idx):
        k = seq["steps"][k_idx]
        cut = lines[:k] + [" " * seq["indent"] + "all_goals sorry"] + lines[seq["end"]:]
        return _measure(row, "\n".join(cut), primary)
    todo = [min(seqs, key=lambda s: (s["indent"], s["steps"][0]))] if seqs else []
    while todo and budget > 0:
        seq = todo.pop(0)
        hs = []
        for k_idx in range(len(seq["steps"])):
            if budget <= 0:
                break
            hs.append(suffix_cost(seq, k_idx)); budget -= 1
        hs.append(total if seq is not None else None)
        for k_idx in range(len(hs) - 1):
            a, b = hs[k_idx], hs[k_idx + 1]
            k = seq["steps"][k_idx]; nxt = seq["steps"][k_idx + 1] if k_idx + 1 < len(seq["steps"]) else seq["end"]
            costs.append({"lines": f"{k + 1}-{nxt}", "depth_indent": seq["indent"],
                          "text": " ".join(l.strip() for l in lines[k:nxt] if l.strip())[:100],
                          "heartbeats": (b - a) if (a is not None and b is not None) else None})
        # descend into the costliest step of this sequence if it has nested sequences
        mine = [c for c in costs if c["depth_indent"] == seq["indent"] and c["heartbeats"] is not None]
        if mine:
            top = max(mine, key=lambda c: c["heartbeats"]); a, b = (int(x) for x in top["lines"].split("-"))
            inner = [s for s in seqs if s["indent"] > seq["indent"] and a <= s["steps"][0] < b and len(s["steps"]) >= 1]
            if inner:
                todo.append(max(inner, key=lambda s: len(s["steps"])))
    ref = local_reference_heartbeats(name)
    out = {"ok": total is not None, "total": total, "floor": floor, "reference": ref,
           "max_heartbeat_score": round((1 - floor / ref) * 100 / 3, 2) if (floor and ref) else None,
           "blocks": sorted(costs, key=lambda c: -(c["heartbeats"] or 0))[:15]}
    if total is not None and floor is not None and ref:
        out["points_left_heartbeats"] = round((total - floor) / ref * 100 / 3, 2)
    out["note"] = ("each block's cost = heartbeats saved if it and its later siblings were `sorry` minus the same for the next sibling; nested blocks "
                   "are profiled under the costliest step. Costs include elaborating terms (notation, instance search). Odd values mean a cut changed elaboration.")
    return out


if __name__ == "__main__":
    import argparse
    ap = argparse.ArgumentParser(); ap.add_argument("problem"); ap.add_argument("file"); ap.add_argument("--max-cuts", type=int, default=10)
    a = ap.parse_args()
    print(json.dumps(profile(a.problem, Path(a.file).read_text(), a.max_cuts), ensure_ascii=False, indent=1))
