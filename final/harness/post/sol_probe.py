"""Sandbox tactic queries at existing proof positions and parse tagged messages.

Query-only Lean code: each trial restores the proof state and message log before
the original tactic resumes. Failed trials emit nothing. No query code is ever
spliced into a candidate declaration.
"""
from __future__ import annotations

# provenance: research lane gaplane2-sol (worktree lra-gl2-sol), commit 6cee22b, ported unchanged into open-post-v3 (2026-11-04)

import re

from harness.post.d4_kit import lean_str, msg_text

PREFIX = "theorem solProbeDummy : True := trivial\n\n"

TRIAL = '''(run_tac do
  let state ← Lean.Elab.Tactic.saveState;
  let messages ← Lean.Core.getMessageLog;
  Lean.Core.setMessageLog {};
  let expected ← Lean.withCurrHeartbeats <| Lean.tryCatchRuntimeEx
    (Lean.withOptions (fun o => o.set `maxHeartbeats (30000 : Nat)) (do
      match Lean.Parser.runParserCategory (← Lean.getEnv) `tactic SOL_ORIGINAL with
      | .error _ => pure (none : Option Nat)
      | .ok stx => (do
        Lean.Elab.Tactic.evalTactic stx;
        pure (some (← Lean.Elab.Tactic.getUnsolvedGoals).length)))) (fun _ => pure none);
  state.restore;
  Lean.Core.setMessageLog {};
  let (ok, found) ← Lean.withCurrHeartbeats <| Lean.tryCatchRuntimeEx
    (Lean.withOptions (fun o => o.set `maxHeartbeats (30000 : Nat)) (do
      match Lean.Parser.runParserCategory (← Lean.getEnv) `tactic SOL_SOURCE with
      | .error _ => pure (false, ([] : List String))
      | .ok stx => (do
        Lean.Elab.Tactic.evalTactic stx;
        let ms ← Lean.Core.getMessageLog;
        let found ← (ms.toList.filter (fun m => m.severity == .information)).mapM (fun m => m.data.toString);
        let count := (← Lean.Elab.Tactic.getUnsolvedGoals).length;
        pure (!ms.hasErrors && expected == some count, found)))) (fun _ => pure (false, []));
  state.restore;
  Lean.Core.setMessageLog messages;
  if ok then for s in found do
    Lean.logInfo (Lean.toMessageData (SOL_BEGIN ++ s ++ "\\nSOLPROBE_END")))'''


def call(i: int, tactic: str, original: str | None = None) -> str:
    text = TRIAL.replace("SOL_SOURCE", lean_str(tactic)).replace("SOL_ORIGINAL", lean_str(original or tactic))
    text = text.replace("SOL_BEGIN", lean_str(f"SOLPROBE_BEGIN {i}\n"))
    # Flat do terms avoid imposing a new indentation scheme on an inline site.
    return " ".join(ln.strip() for ln in text.splitlines())


def equivalent_call(i: int, tactic: str, original: str) -> str:
    """Stronger query screen: printed remaining goals and contexts must match.

    Pretty printing can hide implementation details, so this is only a cheap
    rejection screen. The full accept gate remains the proof validation step.
    Legacy call() output is unchanged for reproducible earlier measurements.
    """
    text = call(i, tactic, original)
    snapshot = '(← Lean.Elab.Tactic.getUnsolvedGoals).mapM (fun g => do pure (← Lean.Meta.ppGoal g).pretty)'
    text = text.replace('Option Nat', 'Option (List String)')
    text = text.replace('pure (some (← Lean.Elab.Tactic.getUnsolvedGoals).length)',
                        'pure (some (← ' + snapshot + '))')
    text = text.replace('let count := (← Lean.Elab.Tactic.getUnsolvedGoals).length;',
                        'let count ← ' + snapshot + ';')
    return text


def parse(messages) -> dict[int, list[str]]:
    out = {}
    for m in messages or []:
        text = msg_text(m)
        match = re.fullmatch(r"SOLPROBE_BEGIN (\d+)\n([\s\S]*?)\nSOLPROBE_END", text.strip())
        if match:
            i = int(match[1])
            val = match[2].strip()
            if val not in out.setdefault(i, []):
                out[i].append(val)
    return out
