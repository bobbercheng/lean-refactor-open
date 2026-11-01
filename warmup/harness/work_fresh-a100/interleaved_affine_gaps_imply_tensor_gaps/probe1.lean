theorem interleaved_affine_gaps_imply_tensor_gaps
    (hC_proximityGapAffineLines : e_ε_correlatedAgreementAffineLinesNat
      (F := F) (A := A) (ι := ι) (C := MC) (e := e) (ε := ε))
    (h_interleaved_gaps : ∀ m : ℕ, m ≥ 1 →
      e_ε_correlatedAgreementAffineLinesNat (F := F)
        (A := InterleavedSymbol A (Fin m)) (ι := ι) (C := MC ^⋈ (Fin m)) e ε) :
    ∀ (ϑ : ℕ), (hϑ_gt_0 : ϑ > 0) → δ_ε_multilinearCorrelatedAgreement_Nat (F := F) (A := A)
      (ι := ι) (C := MC) (ϑ := ϑ) (e := e) (ε := ε) := by
    classical
    intro ϑ
    induction ϑ with
    | zero =>
      intro u
      contradiction
    | succ ϑ_sub_1 ih =>
      cases ϑ_sub_1 with
      | zero =>
        -- `ϑ = 1`
        simp only [zero_add, gt_iff_lt, zero_lt_one, ModuleCode, forall_const]
        intro u
        let toAffineLineEval := multilinearCombine₁_eq_affineLineEvaluation (F := F) (u := u)
        intro hprob_gt
        simp_rw [toAffineLineEval] at hprob_gt
        let prob_eq := prob_uniform_singleton_finFun_eq (F := F)
          (P := fun r => Δ₀(affineLineEvaluation (u 0) (u 1) r, MC) ≤ e)
        -- Convert sampling (r ← (Fin 1 → F)) into sampling (r ← F)
        simp_rw [prob_eq, Nat.cast_one, ENNReal.coe_one, one_mul] at hprob_gt
        have h_correlated_agreement := hC_proximityGapAffineLines (u 0) (u 1) hprob_gt
        simp only [jointProximityNat₂, Fin.isValue] at h_correlated_agreement
        have h_u_eq: u = finMapTwoWords (u 0) (u 1) := by
          funext rowIdx
          match rowIdx with
          | 0 => rfl
          | 1 => rfl
        rw [h_u_eq.symm] at h_correlated_agreement
        exact h_correlated_agreement
      | succ ϑ_sub_2 =>
        sorry
