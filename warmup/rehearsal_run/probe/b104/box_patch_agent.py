#!/usr/bin/env python3
"""b104: apply the --late-turn-cap / --late-turn-from / --no-trunc-escalation change to an agent.py whose comments the release export
blanked (the A100 box's /workspace/lra/harness/agent.py = export of 528c9694 + the p85c --open-card patch). Code-only anchors, each must
match exactly once; refuses (rc 1, nothing written) otherwise. Writes OUT, never the input.
    python3 box_patch_agent.py IN OUT
Check (GB10): applied to a100-rehearsal's full-source agent.py, the AST equals branch b104-turncap's agent.py (docstrings blanked)."""
import ast, re, sys
from pathlib import Path

src, out = Path(sys.argv[1]), Path(sys.argv[2])
L = src.read_text().split("\n")


def find(pred, what):
    hits = [i for i, l in enumerate(L) if pred(l)]
    if len(hits) != 1:
        sys.exit(f"anchor {what!r}: {len(hits)} matches (need 1); nothing written")
    return hits[0]


def code(l):   # the line without a trailing comment (string-safe enough for these anchors: none holds a '#')
    return l.split("  #")[0].rstrip()


FUNC = '''def turn_output_cap(max_tokens: int, trunc_count: int, turn: int, late_cap: int = 0, late_from: int = 4, escalate: bool = True,
                    relief: bool = False) -> int:
    """b104: per-turn output cap before the preset rules; default = max_tokens x min(4, 3 + truncations) (see the branch's docstring)."""
    base = int(max_tokens) * (min(4, 3 + int(trunc_count)) if escalate else 3)
    if late_cap and late_cap > 0 and turn >= late_from:
        return int(max_tokens) * 3 if relief else int(late_cap)
    return base


'''.split("\n")[:-1]

i = find(lambda l: l.startswith("def fit_output_cap("), "def fit_output_cap"); L[i:i] = FUNC
i = find(lambda l: code(l) == "    trunc_count = 0", "trunc_count = 0"); L.insert(i + 1, "    late_relief = False")
i = find(lambda l: l.startswith('    traj_f.write(json.dumps({"type": "header",'), "header write")
L[i:i] = ['    _tc = dict(late_cap=int(getattr(args, "late_turn_cap", 0) or 0), late_from=int(getattr(args, "late_turn_from", 4)),',
          '               escalate=bool(getattr(args, "trunc_escalation", True)))']
i = find(lambda l: code(l).strip() == '"tools": [t["name"] for t in TOOLS], "best_at_start": ws.state["best"].get("score"),', "header tools")
L.insert(i + 1, ' ' * (len(L[i]) - len(L[i].lstrip())) + '**({"turn_cap": _tc} if (_tc["late_cap"] or not _tc["escalate"]) else {}),')
i = find(lambda l: code(l).strip() == '_cap_next = max(args.max_tokens * min(4, 3 + trunc_count), MODEL_PRESETS[args.model_preset].get("min_cap", 0))', "_cap_next")
ind = L[i][:len(L[i]) - len(L[i].lstrip())]
L[i:i + 1] = [ind + "_cap_next = max(turn_output_cap(args.max_tokens, trunc_count, turn + 1, relief=late_relief, **_tc),",
              ind + '                MODEL_PRESETS[args.model_preset].get("min_cap", 0))']
i = find(lambda l: code(l) == "        cap = args.max_tokens * min(4, 3 + trunc_count)", "cap =")
L[i:i + 1] = ["        cap = turn_output_cap(args.max_tokens, trunc_count, turn, relief=late_relief, **_tc)",
              '        if late_relief and _tc["late_cap"] and turn >= _tc["late_from"]:',
              '            flush_traj({"type": "late_cap_relief", "turn": turn, "max_tokens": cap})',
              "        late_relief = False",
              "        _bf_turn = False"]
hits = [i for i, l in enumerate(L) if code(l).strip() == "m = _m2; forced_turns_bf += 1"]
if len(hits) != 2:
    sys.exit(f"anchor 'm = _m2; forced_turns_bf += 1': {len(hits)} matches (need 2); nothing written")
for i in hits:
    L[i] = code(L[i]) + "; _bf_turn = True"
i = find(lambda l: code(l).strip() == "trunc_count += 1 if last_truncated and not runaway_junk else 0", "trunc_count +=")
L[i + 1:i + 1] = ['        if _tc["late_cap"] and turn >= _tc["late_from"] and last_truncated and not runaway_junk and not _bf_turn:',
                  '            late_relief = bool(uses) or any(b.type == "text" and (b.text or "").strip() for b in m.content)']
i = find(lambda l: l.startswith('    ap.add_argument("--no-budget-forcing"'), "--no-budget-forcing")
L[i + 1:i + 1] = ['    ap.add_argument("--late-turn-cap", type=int, default=0, help="b104 (2026-11-01, default 0 = off): output cap (tokens) of every turn from "', '                    "--late-turn-from on, never escalated after a truncation; the opening turns keep --max-tokens x 3 (x 4 after a truncation "', '                    "unless --no-trunc-escalation). A late turn cut while answering (tool call or text at the cap) gives the next turn the "', '                    "opening cap once. Budget forcing is unchanged (its continuation keeps --max-tokens)")', '    ap.add_argument("--late-turn-from", type=int, default=4, help="b104: first turn index (0-based, as in the trajectory\'s turn events) under "', '                    "--late-turn-cap (default 4)")', '    ap.add_argument("--no-trunc-escalation", dest="trunc_escalation", action="store_false", default=True,', '                    help="b104 (default off): a truncated turn no longer raises the output cap for the rest of the session "', '                         "(the cap stays --max-tokens x 3)")']
i = find(lambda l: code(l) == "        args.lean_io = False", "args.lean_io = False")
L[i + 1:i + 1] = ["    if args.late_turn_cap and not (1000 <= args.late_turn_cap <= 64000):",
                  '        raise SystemExit("--late-turn-cap must be 0 (off) or between 1000 and 64000")',
                  "    if args.late_turn_from < 0:",
                  '        raise SystemExit("--late-turn-from must be >= 0")']
s = "\n".join(L)
ast.parse(s)
out.write_text(s)
print(f"b104 patch applied: {src} -> {out}")
