# Notes — `fundamental_theorem_of_variational_calculus'` (physlib v4.32.0)

## Status end of run 9 (2026-10-08)
Best banked: **score 87.02** (202 tok / 1817 hb) — candidate.lean. Reference: 851 tok / 11947 hb.
Axis: 0.0392 pts/token, 2.788 pts/1k hb; work_on = tokens (1 token ≈ 14 hb).
Floor (`by trivial` body) = 536 hb; points left: length 7.91, heartbeats 3.57.

## NEW WIN this run
`hcs.mul_right` — `HasCompactSupport.mul_right : HasCompactSupport f → HasCompactSupport (f * f')`
(NO continuity hypothesis on f', no mono needed!) replaces the 13-token
`(hcs.mono fun _ hx => (mul_ne_zero_iff.mp hx).1)` block. −11 tok, −72 hb, +0.63 score.

## Tested this run (all in [brackets] are verified results)
- [tested: drop `(x := x₀)` pin -> FAIL: nonzero goal becomes `¬φ ?m ∧ ¬⟪f ?m, f x₀⟫ = 0`; pin is load-bearing]
- [tested: `.ne key_integral` with no `simp only [inner_smul_right']` -> FAIL: integrands are NOT defeq
  (`⟪f x, φ x • f x₀⟫_ℝ` vs `(φ * fun x => ⟪f x, f x₀⟫_ℝ) x`; inner_smul_right' goes via WithLp).
  Note: removing the simp line alone dropped hb 1889→1781, so the `simp only … at key_integral`
  line is NOT the hb cost it seemed.]
- [tested: nonzero as term `mul_ne_zero (ne_of_eq_of_ne hφx₀ one_ne_zero) hself.ne'` -> compiles but
  LOSES (86.93 vs 87.02): term elaboration more expensive than `by simp [hφx₀, hself.ne']`]
- [tested: `.ne (by simpa [inner_smul_right'] using key_integral.symm)` -> 86.75, loses]
- [tested: `real_inner_self_pos.mpr` for hself -> FAIL: needs `InnerProductSpace ℝ`, V has
  `InnerProductSpace' ℝ V`; `exact?` finds NO closer for `0 < ⟪v, v⟫_ℝ` from `v ≠ 0`]
- grep of physlib InnerProductSpace/Basic.lean: NO positivity lemma there; only
  `inner_self_eq_zero'` (simp) and `real_inner_self_nonneg'` exist — keep the
  `lt_of_le_of_ne` construction for hself.
- [tested: `pos_of_gt.mp`, `inner_self_pos_of_ne`, `HasCompactSupport.mul` -> do NOT exist.
  `HasCompactSupport.mul_right`/`mul_left` DO exist (no continuity hypothesis).]

## Structure of the winning proof (see candidate.lean, all steps verified by compile)
1. `by_contra h₀; obtain ⟨x₀, hx0⟩ := Function.ne_iff.mp h₀`
2. `hinner := Continuous.inner' f (fun _ => f x₀) hf continuous_const` (ascription + args as shown;
   `Continuous.inner` and `hf.inner` do NOT apply — InnerProductSpace' world).
3. `hself : 0 < ⟪f x₀, f x₀⟫_ℝ := lt_of_le_of_ne (real_inner_self_nonneg') fun h => hx0 (inner_self_eq_zero'.mp h.symm)` — ascription required.
4. `obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp ((hinner.continuousAt).preimage_mem_nhds (Ioi_mem_nhds hself))`.
5. `obtain ⟨φ, hts, hcs, hc, hr, hφx₀⟩ := exists_contDiff_tsupport_subset (Metric.ball_mem_nhds x₀ hδpos)`
   (hr : Set.range φ ⊆ Icc 0 1; hφx₀ : φ x₀ = 1; hts : tsupport φ ⊆ ball).
6. `key_integral := hg (fun x => φ x • f x₀) (IsTestFunction.smul_right ⟨hc, hcs⟩ contDiff_const)`
   then `simp only [inner_smul_right'] at key_integral`.
7. One `exact`:
   - Continuous: `(hc.continuous.mul hinner)`
   - HasCompactSupport: `hcs.mul_right`
   - nonneg: `fun x => if h : φ x = 0 then by simp [h] else mul_nonneg (hr (Set.mem_range_self x)).1 (hδ (hts (subset_closure h))).le`
     (if-split needed: inner can be negative where φ x = 0; note `hr` gives φ x ≥ 0 everywhere,
     so only the second factor is the problem)
   - nonzero: `(by simp [hφx₀, hself.ne'])` — cheapest tested form; goal is
     `(φ * fun x => ⟪f x, f x₀⟫_ℝ) x₀ ≠ 0`.
   - pin `(x := x₀)` on the lemma; close with `.ne key_integral.symm`.

## Costliest remaining lines (token axis) — where to attack next
1. nonneg if-split line, 21 tok. Ideas not yet tried:
   - a tactic `by intro x; split <;> ...` form (probably longer);
   - `mul_nonneg` with the if moved inside the second argument (fails: goal `0 ≤ inner` false when φ x = 0
     — unless phrased `by split_ifs` … untested).
2. hinner line, 18 tok — likely minimal.
3. hself line, 14 tok — no library pos lemma exists (see above); maybe
   `inner_self_eq_zero'.not.mpr hx0` combined with `real_inner_self_nonneg'` via
   `lt_of_le_of_ne` is already minimal; try `(real_inner_self_nonneg'.lt_of_ne ?)` untested.
4. hb axis: biggest block is the final `exact` (~526 hb); `simp only [inner_smul_right']` only 33 hb.
   Floor 536 → max 3.57 pts from hb, so prefer token cuts even at hb cost (1 tok = 14 hb).

## Dead ends (from earlier runs, see git notes) — do not retry
- `simp at hx0` instead of `Function.ne_iff.mp`; `not_forall.1`; `Continuous.inner`;
  `(hr ⟨x, rfl⟩).1` variants (equal cost); ContDiffBump-based φ construction (longer than
  `exists_contDiff_tsupport_subset`); `simp only [inner_smul_right']` inside `hg` application.
