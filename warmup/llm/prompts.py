"""Prompts for the refactoring task. Generic by design (transfer > tuning)."""
from __future__ import annotations

SYSTEM = (
    "You are an expert Lean 4 and Mathlib proof engineer. You rewrite existing, "
    "working proofs to be shorter and cheaper to elaborate while keeping the theorem "
    "statement byte-for-byte identical."
)

TASK = """\
Refactor the proof body of the Lean 4 theorem below. It is scored on three axes, each a percentage improvement over the reference proof, averaged with equal weight:

1. LENGTH: token count of the proof body (the text after `:=`). The tokenizer splits on spaces, treats every bracket, comma, operator and symbol as its own token, and treats a dotted name like `h.1` or `Nat.succ_le` as ONE token. Comments and blank lines are not counted, but do not add any. Fewer tokens is better.
2. HEARTBEATS: Lean elaboration cost measured with `count_heartbeats` on the whole declaration. Expensive tactics (`simp` with a big simp set, `aesop`, `omega`/`nlinarith`/`polyrith` on big goals, `decide`, heavy typeclass search, `norm_num` on large expressions) cost a lot; targeted `simp only [...]`, direct term proofs, `exact` with the right lemma, and `rw` are cheap. Fewer heartbeats is better.
3. COMPATIBILITY: the proof must compile UNCHANGED on every listed toolchain. A proof that fails on any of them loses a third of that axis. Prefer stable, long-standing Mathlib lemma names and tactics over recent additions.

Hard rules (violations score zero):
- Output the FULL declaration: the statement must be reproduced EXACTLY as given (same characters, same line breaks), followed by `:=` and your new proof.
- No `sorry`, `admit`, `axiom`, `native_decide`, `decide := by native_decide`, `#eval`, `#reduce`, `IO.*`, `unsafe`, `extern`, `initialize`, `run_cmd`, `run_elab`, `#exit`, `#count_heartbeats`.
- No auxiliary top-level declarations of any kind (`def`, `lemma`, `theorem`, `instance`, `abbrev`, `structure`, `macro`, `notation`, `syntax`, `attribute`, `open`, `set_option` outside the proof). Everything must live inside the single proof body. `set_option ... in` inside tactic blocks is allowed but discouraged.
- Do not change imports or options; the header shown is what will be used.

{context_block}

Toolchains it must compile on: {toolchains}
Reference proof body: {ref_tokens} tokens, {ref_heartbeats} heartbeats.

```lean
{declaration}
```

Think carefully about which parts of the reference proof are redundant, which `have`s can be inlined or dropped, where term-mode proofs replace tactic blocks, and where `simp only` with explicit lemmas replaces broad automation. Then output exactly one ```lean code block containing the complete refactored declaration and nothing else after it.
"""


def build_prompt(row: dict, ref_heartbeats: int | None) -> str:
    toolchains = ", ".join(v for pair in row["version_info"] for v in pair)
    if row.get("header"):
        ctx = "Header (imports and options, fixed):\n```lean\n" + row["header"].rstrip() + "\n```"
    else:
        ctx = (f"This declaration lives inside the {row['source']} repository at `{row['file_path']}` "
               f"(lines {row.get('start_line')}-{row.get('end_line')}); the surrounding file's imports, "
               "`open`s, `variable`s and sibling lemmas are available exactly as in the repository.")
    return TASK.format(context_block=ctx, toolchains=toolchains, ref_tokens=row["proof_length"],
                       ref_heartbeats=ref_heartbeats if ref_heartbeats is not None else "unknown",
                       declaration=row["src"].rstrip())


# Lighter variant: targeted edits to the existing proof rather than a fresh
# derivation. Bounds deliberation; intended for cheap first-pass samples and
# for the refine loop.
TASK_EDIT = """\
You will shorten and cheapen an existing, working Lean 4 proof by making targeted edits. Do NOT re-derive the mathematics or restructure the argument; keep the proof's skeleton and make local improvements such as:
- delete `have`s, hypotheses and intermediate steps that are never used;
- inline a `have` that is used once;
- replace broad automation (`simp_all`, `aesop`, `norm_num [...]`, `nlinarith`, `omega` on tiny goals) with the cheapest tactic that closes the goal (`exact`, `rfl`, `simp only [...]`, `rw`, `linarith`, `omega`), and conversely merge several short steps into one tactic when that removes tokens;
- replace tactic blocks that build a term with the term itself (`exact ⟨_, _⟩`, `fun h => ...`);
- drop redundant type ascriptions, parentheses, `show`, `clear`, `classical`, and `try` wrappers that do nothing;
- use `<;>` or `all_goals` to merge identical case bodies.

Scoring: mean of (token reduction %, heartbeat reduction %, compatibility %) versus the reference. Tokens: each bracket/operator/symbol is one token, a dotted name is one token, comments and blank lines do not count. Heartbeats: elaboration cost; broad automation is expensive. Compatibility: must compile UNCHANGED on every listed toolchain, so prefer long-standing lemma names.

Hard rules (violations score zero): reproduce the statement EXACTLY as given (same characters and line breaks) followed by `:=` and your proof; no `sorry`/`admit`/`axiom`/`native_decide`/`#eval`/`IO`/`unsafe`/`run_cmd`/`run_elab`/`#count_heartbeats`; no auxiliary top-level declarations, `open`, `set_option`, `attribute`, `macro`, `notation`; do not change imports.

{context_block}

Toolchains it must compile on: {toolchains}
Reference proof body: {ref_tokens} tokens, {ref_heartbeats} heartbeats.

```lean
{declaration}
```

Be decisive: identify the 5–15 highest-value edits, apply them, and output exactly one ```lean code block containing the complete edited declaration and nothing else after it. Keep your deliberation short.
"""


def build_prompt_edit(row: dict, ref_heartbeats: int | None) -> str:
    toolchains = ", ".join(v for pair in row["version_info"] for v in pair)
    if row.get("header"):
        ctx = "Header (imports and options, fixed):\n```lean\n" + row["header"].rstrip() + "\n```"
    else:
        ctx = (f"This declaration lives inside the {row['source']} repository at `{row['file_path']}`; the surrounding "
               "file's imports, `open`s, `variable`s and sibling lemmas are available exactly as in the repository.")
    return TASK_EDIT.format(context_block=ctx, toolchains=toolchains, ref_tokens=row["proof_length"],
                            ref_heartbeats=ref_heartbeats if ref_heartbeats is not None else "unknown",
                            declaration=row["src"].rstrip())
