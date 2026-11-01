# Notes: interleaved_affine_gaps_imply_tensor_gaps (DG25/MainResults.lean)

## BEST: 369 tok / 3820 hb → score 77.34 (candidate.lean = Vb3, checked fresh-a100-p5)
Reference: 1353 tok / 9198 hb. Score = mean(len_red 72.7%, hb_red 58.5%, compat 100%).

## ARCHITECTURE (Vb3, full text in candidate.lean)
1. `intro ϑ; induction ϑ; | zero => intro u; contradiction`.
2. Zero case: `intro _ u hprob_gt`, one `simp only [multilinearCombine₁_eq_affineLineEvaluation,
   zero_add, prob_uniform_singleton_finFun_eq (F := F) (P := fun r => Δ₀(affineLineEvaluation
   (u 0) (u 1) r, MC) ≤ e), Nat.cast_one, ENNReal.coe_one, one_mul] at hprob_gt`,
   then `rw [show u = finMapTwoWords (u 0) (u 1) from funext fun rowIdx => by
   fin_cases rowIdx <;> rfl]` and `exact hC_proximityGapAffineLines (u 0) (u 1) hprob_gt`.
   (cost ≈1175 hb; the P explicit arg is needed: prob_uniform_singleton_finFun_eq's P : F → Prop
   is explicit, statement `Pr_{let r ← $ᵖ (Fin 1 → F)}[P (r 0)] = Pr_{let r ← $ᵖ F}[P r]`.)
3. Succ case: `let n := ϑ_sub_2 + 1`, `let U₀/.2, U₁`, `let W₀ := ⋈|(show WordStack A (Fin (2^n)) ι from U₀)` (W₁), `let Rs := R_star_tensor MC (e:=e) (ε:=ε) U₀ U₁`.
   **[tested: dropping (e:=e) or (ε:=ε) from R_star_tensor → fails, ε/e NOT inferable from U₀ U₁ (fresh-a100-p5, two checks)]**
4. `have lem (r : Fin (n+1) → F) : multilinearCombine u r = multilinearCombine
   (affineLineEvaluation U₀ U₁ (r (Fin.last n))) (fun i => r i.castSucc) :=
   multilinearCombine_recursive_form u r` — LOCAL have essential.
5. `have hP_split := prob_split_last_uniform_sampling_of_finFun (ϑ := n) (F := F)
   (P := multilinearCombine_affineComb_split_last_close MC u e)` — the def P (3 tokens,
   322 hb) replaced the old inline lambda (611 hb). MC is EXPLICIT in that def:
   `multilinearCombine_affineComb_split_last_close {ϑ} (u) (e) (r_last) (r_init)`? NO —
   signature is `{ϑ} (MC?) ...` — applied as `... MC u e` works (tested Vb3).
   Positional `... u e` w/o MC fails (fresh-a100-p5); `(u := u) (e := e)` w/o MC fails.
6. `simp only [lem] at hP_multilinearCombine_close_gt` (1313 hb — the biggest single cost),
   then `have hPM2 := hP_split ▸ hP_multilinearCombine_close_gt`,
   `have h_prob_Rstar := prob_R_star_gt_threshold MC u e hPM2` (ALL positional).
7. `have h_prob_line_gt_eps_div_q := lt_of_lt_of_le h_prob_Rstar (Pr_le_Pr_of_implies ($ᵖ F)
   (fun r => r ∈ Rs) (fun r => Δ₀(affineLineEvaluation W₀ W₁ r, MC ^⋈ (Fin (2^n))) ≤ e)
   (fun r hr => (correlatedAgreement_of_mem_R_star_tensor MC (ih (Nat.succ_pos _)) u) ⟨r, hr⟩))`
   — INLINING h_line_close_to_C_m saved 29 tok + 146 hb (V1, 75.93).
8. `apply CA_split_rowwise_implies_CA; exact h_interleaved_gaps (2^n) (Nat.one_le_two_pow) W₀ W₁ h_prob_line_gt_eps_div_q`.

## FAILURES (all fresh-a100-p5 unless noted)
- [tested: Rs with only (ε:=ε) / only (e:=e) / neither → all fail: other implicit not inferable]
- [tested: drop (F := F) from prob_split_last_uniform_sampling_of_finFun → typeclass stuck
  Module ?m (ι → A); keep it]
- [tested: `rw [lem] at hP` → fails, harness auto-repairs to simp_rw; simp_rw ≈ same cost as simp only]
- [tested: `simp only [← lem] at hP_split` → "simp made no progress": hP_split's LHS is
  `P (r (Fin.last n)) (...)` with P = the def, NOT unfolded, so lem's RHS pattern absent;
  would need `simp only [multilinearCombine_affineComb_split_last_close, ← lem] at hP_split` (untested)]
- [tested: `simp only [multilinearCombine_recursive_form] at hP` (global lemma) → fires but
  cascades into nested splitHalfRowWise... rewrites, 9377 hb, ▸ fails]
- [tested: Pr_congr route (replace simp only by explicit Pr_congr with congrArg
  (fun t => distFromCode t MC ≤ e) (lem r)) → compiles but 502 tok / 4926 hb, worse.
  NOTE: `Δ₀(t, MC)` is AMBIGUOUS inside congrArg (ℕ∞ vs ℕ interpretations) — must write
  `distFromCode t MC ≤ e` instead (three checks)]
- [tested: typed h_line_close + `jointProximityNat.mp` → unknown constant; jointProximityNat
  is a def, not an And-structured one accessible via .mp]
- [tested: `multilinearCombine_affineComb_split_last_close u e` (positional, no MC) → arg-order
  mismatch; `...(u := u) (e := e)` (no MC) → MC becomes a lambda arg; `... MC u e` OK]

## COST PROFILE of Vb3 (lean_profile)
floor 694. simp only [lem] at hP: 1313. zero case: ~1175. hP_split: 322. lem: 205.
lets: Rs 47, W₀ 32, W₁ 25, n 15. The 1313 seems irreducible: every alternative route to
convert hP (single-let u-form) → two-let affine form needs that rewrite somewhere.

## NEXT IDEAS (untested)
1. Zero case: try `Fin.cases rfl rfl rowIdx` instead of `fin_cases <;> rfl` (token cut).
   Try shrinking the simp list (e.g. drop zero_add? it was needed in old variants).
2. Try `simp only [multilinearCombine_affineComb_split_last_close, ← lem] at hP_split` +
   `hPM2 := hP_split ▸ hP` — maybe cheaper rewriting the small hP_split than hP? (both
   single-occurrence; likely similar).
3. conv-targeted rewrite inside hP to cut simp's traversal cost.
4. Token axis: 369 tok; biggest lines are the zero-case simp list (~25) and the
   Pr_le_Pr_of_implies lambdas (~26). Points-left on hb axis ≈ 11.1 (per lean_profile).
