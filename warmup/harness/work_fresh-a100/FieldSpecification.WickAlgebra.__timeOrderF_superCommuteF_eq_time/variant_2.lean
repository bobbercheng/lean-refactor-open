lemma ι_timeOrderF_superCommuteF_eq_time {φ ψ : 𝓕.CrAnFieldOp}
    (hφψ : crAnTimeOrderRel φ ψ) (hψφ : crAnTimeOrderRel ψ φ) (a b : 𝓕.FieldOpFreeAlgebra) :
    ι 𝓣ᶠ(a * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * b) =
    ι ([ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * 𝓣ᶠ(a * b)) := by
  induction (Basis.mem_span ofCrAnListFBasis b) using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φs, rfl⟩ := hx
    simp only [ofListBasis_eq_ofList]
    induction (Basis.mem_span ofCrAnListFBasis a) using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨φs', rfl⟩ := hy
      simp only [ofListBasis_eq_ofList]
      have hmid : ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF =
          ι (ofCrAnListF [φ, ψ]) -
          𝓢(𝓕.crAnStatistics φ, 𝓕.crAnStatistics ψ) • ι (ofCrAnListF [ψ, φ]) := by
        rw [superCommuteF_ofCrAnOpF_ofCrAnOpF]
        simp [← ofCrAnListF_singleton, ← ofCrAnListF_append]
      let l := List.takeWhile (fun c => ¬crAnTimeOrderRel φ c)
        (List.insertionSort crAnTimeOrderRel (φs' ++ φs))
      let l' := List.filter (fun c =>
        crAnTimeOrderRel φ c ∧ crAnTimeOrderRel c φ) φs'
      let r := List.filter (fun c => (crAnTimeOrderRel φ c ∧ ¬crAnTimeOrderRel c φ))
        (List.insertionSort crAnTimeOrderRel (φs' ++ φs))
      let r' := List.filter (fun c => crAnTimeOrderRel φ c ∧ crAnTimeOrderRel c φ) φs
      have h1 := insertionSort_of_eq_list crAnTimeOrderRel φ φs' [φ, ψ] φs (by simp_all)
      have h2 := insertionSort_of_eq_list crAnTimeOrderRel φ φs' [ψ, φ] φs (by simp_all)
      have h3 : crAnTimeOrderList (φs' ++ φs) = l ++ (l' ++ (r' ++ r)) := by
        rw [crAnTimeOrderList, insertionSort_of_takeWhile_filter crAnTimeOrderRel φ φs' φs]
        simp only [l, l', r, r', List.append_assoc]
      have e : ∀ χ η, φs' ++ χ :: η :: φs = φs' ++ [χ, η] ++ φs := fun _ _ => by simp
      calc ι 𝓣ᶠ(ofCrAnListF φs' * [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * ofCrAnListF φs)
        _ = crAnTimeOrderSign (φs' ++ φ :: ψ :: φs) •
          (ι (ofCrAnListF l) * ι (ofCrAnListF l') * ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF *
            ι (ofCrAnListF r') * ι (ofCrAnListF r)) := by
          conv_lhs =>
            simp only [← ofCrAnListF_singleton, ← ofCrAnListF_singleton,
              superCommuteF_ofCrAnListF_ofCrAnListF, mul_sub, sub_mul, smul_mul_assoc,
              mul_smul_comm, ← ofCrAnListF_append, List.append_assoc, List.cons_append,
              List.nil_append, ofList_singleton, map_sub, map_smul, timeOrderF_ofCrAnListF,
              sub_right_inj]
          rw [smul_comm, ← crAnTimeOrderSign_swap_eq_time hφψ hψφ]
          simp only [crAnTimeOrderList, e, h1, h2, map_mul, mul_assoc, ofCrAnListF_append,
            l, l', r, r', hmid, mul_sub, sub_mul, smul_sub, mul_smul_comm,
            smul_mul_assoc]
        _ = ι [ofCrAnOpF φ, ofCrAnOpF ψ]ₛF * ι 𝓣ᶠ(ofCrAnListF φs' * ofCrAnListF φs) := by
          by_cases hq : (𝓕 |>ₛ φ) = (𝓕 |>ₛ ψ)
          · rw [Subalgebra.mem_center_iff.mp (ι_superCommuteF_ofCrAnOpF_ofCrAnOpF_mem_center φ ψ),
              mul_assoc, mul_assoc, mul_assoc, ← map_mul, ← map_mul, ← map_mul,
              ← ofCrAnListF_append, ← ofCrAnListF_append, ← ofCrAnListF_append, ← h3,
              crAnTimeOrderSign, Wick.koszulSign_eq_rel_eq_stat _ _ hφψ hψφ hq.symm,
              ← crAnTimeOrderSign, ← ofCrAnListF_append, timeOrderF_ofCrAnListF]
            simp only [map_smul, mul_smul_comm]
          · simp only [ι_superCommuteF_of_diff_statistic hq, zero_mul, mul_zero, smul_zero]
    | zero => simp only [zero_mul, map_zero, mul_zero]
    | add x y _ _ hpx hpy => simp only [mul_add, add_mul, map_add, hpx, hpy]
    | smul x hx _ h => simp only [smul_mul_assoc, mul_smul_comm, map_smul, h]
  | zero => simp only [mul_zero, map_zero]
  | add x y _ _ hpx hpy => simp only [mul_add, map_add, hpx, hpy]
  | smul x hx _ h => simp only [mul_smul_comm, map_smul, h]
