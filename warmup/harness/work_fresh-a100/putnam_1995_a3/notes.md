# putnam_1995_a3 notes

## Status (run 7)
- BEST candidate.lean: score **93.6** (tokens 317/4085, hb 1629/14130, compat 3/3). Unchanged from run 6.

## Tested this run (all lean_check_variants, no improvement over incumbent)
- `fun i => exact ...` as final closer (no `intro i`) → FAIL: `fun` is not a tactic; unsolved goal.
- hstep inlined into final goal, dropping the `∀`-statement (`no-hstep-inline`) → FAIL: after dropping hstep, `hstep i` referenced in final exact disappears; assumption fails.
- `hstep := fun i => by ...` term form → compiles, 318 tok/1670 hb: WORSE than tactic form.
- `Finset.mem_univ _` and `Finset.mem_univ i (by simp)` for the sum_eq_single_of_mem arg → compiles, hb equal/worse (1633/1647) — no win.
- h6 rewrite chain `[add_sub_cancel_left, mul_neg, neg_sub, dvd_neg]` (instead of `[← dvd_neg, ← neg_mul, neg_sub]`) → FAIL: after `add_sub_cancel_left` the term is `(f i - d i) * 10^↑i` (already sign-folded), no `?a * -?b` pattern.
- `obtain ⟨h2, h4⟩ := ⟨.., ..⟩` → FAIL: anonymous-constructor type can't be inferred.

## Reconfirmed facts
- `Int.isCoprime_iff_gcd_eq_one.mpr rfl |>.pow_right (n := i.1)` — pow_right's exponent is IMPLICIT, needs `(n := i.1)`.
- Lean 4 `obtain` needs `rcases`-patterns over existing terms, not anonymous constructor on the RHS for pairs of hypotheses with unrelated types.

## Structural facts (stable across runs)
- Proof shape: `key` (digit-replacement identity, ~340 hb), `hce : 7 ∣ dtd + dte` via `hE` simp-only+ring block (~478 hb, biggest), `hstep` (~451 hb), final coprime closer.
- hce genuinely needs the summed relation (dte - dtd = ∑(e i - d i)·10^i, and 7 ∣ ∑(e i - d i)·10^i + 9·dtd); no shortcut found avoiding the hE block.
- Prior runs: omega/linarith/norm_num closers for hE all fail or cost more; nsmul_eq_mul variant worse (1649 hb).
- Estimated remaining headroom < 0.5 score (hb points left ≈ 3.3 of floor 202 hb, tokens 317).
