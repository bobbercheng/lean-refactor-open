theorem interleaved_affine_gaps_imply_tensor_gaps
    (hC_proximityGapAffineLines : e_ε_correlatedAgreementAffineLinesNat
      (F := F) (A := A) (ι := ι) (C := MC) (e := e) (ε := ε))
    (h_interleaved_gaps : ∀ m : ℕ, m ≥ 1 →
      e_ε_correlatedAgreementAffineLinesNat (F := F)
        (A := InterleavedSymbol A (Fin m)) (ι := ι) (C := MC ^⋈ (Fin m)) e ε) :
    ∀ (ϑ : ℕ), (hϑ_gt_0 : ϑ > 0) → δ_ε_multilinearCorrelatedAgreement_Nat (F := F) (A := A)
      (ι := ι) (C := MC) (ϑ := ϑ) (e := e) (ε := ε) := by
    intro ϑ
    induction ϑ with
    | zero =>
      intro u
      contradiction
    | succ ϑ_sub_1 ih =>
      cases ϑ_sub_1 with
      | zero =>
        intro _ u hprob_gt
        simp only [multilinearCombine₁_eq_affineLineEvaluation, zero_add,
          prob_uniform_singleton_finFun_eq (F := F)
            (P := fun r => Δ₀(affineLineEvaluation (u 0) (u 1) r, MC) ≤ e),
          Nat.cast_one, ENNReal.coe_one, one_mul] at hprob_gt
        rw [show u = finMapTwoWords (u 0) (u 1) from
          funext fun rowIdx => by fin_cases rowIdx <;> rfl]
        exact hC_proximityGapAffineLines (u 0) (u 1) hprob_gt
      | succ ϑ_sub_2 =>
        intro _ u hP_multilinearCombine_close_gt
        let n := ϑ_sub_2 + 1
        let U₀ := (splitHalfRowWiseInterleavedWords u).1
        let U₁ := (splitHalfRowWiseInterleavedWords u).2
        let W₀ := ⋈|(show WordStack A (Fin (2 ^ n)) ι from U₀)
        let W₁ := ⋈|(show WordStack A (Fin (2 ^ n)) ι from U₁)
        let Rs := R_star_tensor MC (e:=e) (ε:=ε) U₀ U₁
        have lem (r : Fin (n + 1) → F) : multilinearCombine u r =
            multilinearCombine (affineLineEvaluation U₀ U₁ (r (Fin.last n)))
              (Fin.init r) :=
          multilinearCombine_recursive_form u r
        have hP_split := prob_split_last_uniform_sampling_of_finFun (ϑ := n) (F := F)
          (P := multilinearCombine_affineComb_split_last_close MC u e)
        simp only [lem] at hP_multilinearCombine_close_gt
        have hPM2 := hP_split ▸ hP_multilinearCombine_close_gt
        have h_prob_Rstar := prob_R_star_gt_threshold MC u e hPM2
        have h_prob_line_gt_eps_div_q :=
          lt_of_lt_of_le h_prob_Rstar (Pr_le_Pr_of_implies ($ᵖ F)
            (fun r => r ∈ Rs)
            (fun r => Δ₀(affineLineEvaluation W₀ W₁ r, MC ^⋈ (Fin (2 ^ n))) ≤ e)
            (fun r hr_in_Rstar => (correlatedAgreement_of_mem_R_star_tensor MC
              (ih (Nat.succ_pos _)) u) ⟨r, hr_in_Rstar⟩))
        apply CA_split_rowwise_implies_CA
        exact h_interleaved_gaps (2^n) (Nat.one_le_two_pow) W₀ W₁
          h_prob_line_gt_eps_div_q
