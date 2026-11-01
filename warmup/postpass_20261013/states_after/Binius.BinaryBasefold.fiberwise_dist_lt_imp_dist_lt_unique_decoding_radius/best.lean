theorem fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius (i : Fin ℓ) (steps : ℕ)
    [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps) (f := f)) :
  hammingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ f := by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 ⟨i, by omega⟩
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i.val + steps, by omega⟩
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').ncard := by
    obtain ⟨g_subtype, _, h_eq⟩ := (Set.mem_image _ _ _).mp
      (Nat.sInf_mem ⟨_, Set.mem_image_of_mem _ $ Set.mem_univ (0 : C_i)⟩)
    exact ⟨g_subtype.val, g_subtype.property, h_eq.symm⟩
  let ΔH := Finset.filter (λx => f x ≠ g' x) Finset.univ
  let Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g'
  have hFinType_Y_bad : Fintype Y_bad := Fintype.ofFinite ↑Y_bad
  let Fib := fun (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩) =>
    Finset.image (qMap_total_fiber 𝔽q β ⟨i, by omega⟩ steps
      (fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y)
      (Finset.univ : Finset $ Fin $ 2 ^ steps)
  have h_ΔH_subset_bad_fiber_points : ΔH ⊆ Y_bad.toFinset.biUnion Fib := by
    intro x hx_in_ΔH
    let y_of_x := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x
    refine Finset.mem_biUnion.mpr ⟨y_of_x,
      Set.mem_toFinset.mpr ⟨x, rfl, (Finset.mem_filter.mp hx_in_ΔH).2⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨pointToIterateQuotientIndex (i := ⟨i, by omega⟩)
      (h_i_add_steps := by omega) (x := x), mem_univ _,
      is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y_of_x).mp rfl⟩
  have h_nat : hammingDist f g' ≤ d_fw * 2 ^ steps := by
    rewrite [h_g'_min_card]
    exact (Finset.card_le_card h_ΔH_subset_bad_fiber_points).trans
      ((Finset.card_biUnion_le_card_mul Y_bad.toFinset Fib _
        (λy _ => Finset.card_image_le.trans
          (le_of_eq $ Finset.card_univ.trans $ Fintype.card_fin _))).trans
        (Nat.mul_le_mul_right _ $ le_of_eq (Set.ncard_eq_toFinset_card' Y_bad).symm))
  have h_bridge : d_H ≤ d_fw * 2 ^ steps :=
    le_trans (Code.distFromCode_le_dist_to_mem f g' h_g'_mem) $ ENat.coe_le_coe.mpr h_nat
  have h_cast : d_H.toNat ≤ d_fw * 2 ^ steps := by
    exact_mod_cast ENat.toNat_le_toNat h_bridge $ ENat.coe_ne_top $ d_fw * 2 ^ steps
  have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 :=
    Nat.le_of_lt_succ $ ENat.coe_lt_coe.mp h_fw_dist_lt
  have h_algebraic_identity : (d_i_plus_steps - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_i_plus_steps, BBF_CodeDistance]
    rewrite [Nat.sub_mul, ←Nat.pow_add, ←Nat.pow_add]
    have h1 : ℓ + 𝓡 - (↑i + steps) + steps = ℓ + 𝓡 - i := by
      rw [← Nat.sub_sub, Nat.sub_add_cancel
        (Nat.le_sub_of_add_le' $ h_i_add_steps.trans $ Nat.le_add_right ℓ 𝓡)]
    have h2 : ℓ - (↑i + steps) + steps = ℓ - i := by
      rw [← Nat.sub_sub, Nat.sub_add_cancel $ Nat.le_sub_of_add_le' h_i_add_steps]
    rw [h1, h2]
  have h_final_inequality : 2 * d_H.toNat ≤ d_i - 1 := by
    rewrite [← h_algebraic_identity]
    exact le_trans (Nat.mul_le_mul_left 2 h_cast)
      (by rewrite [←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h_fw_bound)
  change (2 : ℕ∞) * d_H < d_i
  rewrite [←ENat.coe_toNat $ ne_of_lt $ lt_of_le_of_lt h_bridge $ ENat.coe_lt_top _]
  exact_mod_cast Nat.lt_of_le_pred (Nat.succ_pos _) h_final_inequality
