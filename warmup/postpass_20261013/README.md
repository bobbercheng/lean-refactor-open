# CPU post-passes of 2026-10-13: 82.29 -> 82.49 with no model calls

Three deterministic, model-free passes were applied on 2026-10-13 to a copy of the A100 line's work root, starting from each problem's
best after the lexer normalizer (the 82.29 line). No model was called. Every improved proof was then re-checked with the standard checker
(byte-identical statement, forbidden constructs, primary compile, every listed toolchain with Z unchanged, strictly better) under the A100
line's own provenance (`glm-5.3-flash-vllm-a100-awq-w4a16@openai`, mode `agent`, run id `fresh-a100-postpass1`, field `postpass` naming
the passes that produced it). Those records are in `../probe/runs/fresh-a100-postpass1/verified.jsonl`, so the assembly command of
README.md section 4 (`--only-run-prefix fresh-a100-`) now prints **82.49**. The line's own work root was not modified. These results were
never submitted; the public open entry is still the older pass-1 result.

| Pass | Command (from a checkout of `code/`, run in a memory-capped process) | Banked on the copy | Summed gain |
|---|---|---|---|
| Transfer lane: rules, spans, closers and deletions mined from this line's own bests (no other line's proofs), compiled on every row | `harness/transfer.py --work-root harness/hwork/a100-postpass --run-id a100-postpass-xfer1 --ops normalize --jobs 2 --max-hours 3` | 14 hits | see below |
| Heartbeat polish: `?`-certificates to `only` lists, unused lemmas pruned | `harness/hb_polish.py --work-root harness/hwork/a100-postpass --run-id a100-postpass-polish1` | 2 rows | +0.44 |
| Heartbeat micro-normalizer: `rw` -> `rewrite`, `simp only` -> `dsimp only`, `simp_rw` / `repeat rw` -> `simp only`, `use` / `exists` -> `refine` / `exact`, `with_reducible` inside `first` | `harness/hb_rewrite.py --work-root harness/hwork/a100-postpass --run-id a100-postpass-hbrewrite1 --kind api-dev-only --deadline-s 7200 --max-compiles 24` | 2 rows | +0.35 |
| Re-check and record under the line's provenance | `probe/postpass/a100_postpass.py prepare` (before the passes) and `record` (after) | **8 rows recorded** | **+3.08 summed = +0.21 mean** |

## The eight recorded rows

| Problem | Tokens | Heartbeats | Score | Produced by |
|---|---|---|---|---|
| `Binius.BinaryBasefold.fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius` | 614 | 4,528 | 76.58 | transfer, hb_rewrite |
| `Binius.BinaryBasefold.fold_advances_evaluation_poly` | 351 | 7,333 | 88.56 | transfer |
| `CallElimCorrect.extractedOldExprInVars` | 101 | 520 | 78.41 | transfer |
| `Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress` | 133 | 6,977 | 85.25 | transfer |
| `Electromagnetism.ElectromagneticPotential.time_deriv_time_deriv_electricField_of_isExtrema` | 646 | 10,826 | 70.99 | transfer, hb_polish, hb_rewrite |
| `FieldSpecification.WickAlgebra.ι_timeOrderF_superCommuteF_eq_time` | 675 | 14,353 | 70.15 | transfer, hb_polish |
| `interleaved_affine_gaps_imply_tensor_gaps` | 346 | 3,765 | 78.10 | transfer |
| `putnam_1995_a3` | 307 | 1,628 | 93.69 | transfer |

All eight records have Z = 100 and compile on every listed toolchain. A sorry/axiom audit of the line (all 15 bests) found no sorry and no
axiom outside {propext, Classical.choice, Quot.sound}.

## Files

| Path | Content |
|---|---|
| `code/` | the code that ran (import closure of `transfer.py`, `hb_polish.py`, `hb_rewrite.py`, `lint_delete.py`, `a100_postpass.py`) at project commit `2756a954` |
| `runs_intermediate/` | the passes' own records on the copy (labelled `transfer@cpu`, `hb-polish@cpu`, `hb-rewrite@cpu`); never assembled or banked |
| `logs/a100-postpass.log` | the chain's log: sweep counts, per-row lines, the recorded rows |
| `transfer/` | the transfer lane's mined mechanisms, hits and dispositions |
| `states_after/` | each problem's state and best proof on the copy after the passes |

**Code version.** The chain ran from the project's main checkout between 19:21 and about 20:40 UTC on 2026-10-13, while harness changes
later committed as `2756a954` were being written (a sorry gate in the scorer, new opt-in prompt flags and a lint-deletion tool, none used by
these passes except the scorer gate). The final re-check that recorded the eight rows ran under `2756a954`, so every recorded proof was
validated by that commit's checker. `code/` is that commit. Staging edits, as for the earlier uploads: comments, docstrings and help text
that named internal evaluation work were generalized; the transfer lane's and discover's guard strings for internal evaluation sets use
neutral prefixes; `harness/hx_heldout.py` is an extract of the one function the transfer lane calls; the Claude Code and Codex drivers,
`prompt_v2.py`, `exemplars.py` and `cc_meter.py` are not included (not needed; `transfer.py` imports `prompt_v2` inside a `try`).
