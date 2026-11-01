theorem fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius (i : Fin ℓ) (steps : ℕ)
    [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps) (f := f)) :
  hammingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ f := by
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  -- 2 * Δ₀(f, ↑(BBF_Code 𝔽q β ⟨↑i, ⋯⟩)) < ↑(BBF_CodeDistance ℓ 𝓡 ⟨↑i, ⋯⟩)
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 (⟨i, by omega⟩)
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i.val + steps, by omega⟩
  have h_d_i_gt_0 : d_i > 0 := Nat.succ_pos _
  -- 1. Relate Hamming distance `d_H` to fiber-wise distance `d_fw`.
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').ncard := by
    -- Let `S` be the set of all possible fiber-wise disagreement sizes.
    let S := (fun (g : C_i) => (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps
      f g).ncard) '' Set.univ
    obtain ⟨g_subtype, _, h_eq⟩ := (Set.mem_image _ _ _).mp
      (Nat.sInf_mem ⟨_, Set.mem_image_of_mem _ (Set.mem_univ (0 : C_i))⟩)
    exact ⟨g_subtype.val, g_subtype.property, h_eq.symm⟩
  -- The Hamming distance to any codeword `g'` is bounded by `d_fw * 2 ^ steps`.
  have h_dist_le_fw_dist_times_fiber_size : (hammingDist f g' : ℕ∞) ≤ d_fw * 2 ^ steps := by
    change (Δ₀(f, g') : ℕ∞) ≤ ↑d_fw * ((2 ^ steps : ℕ) : ℕ∞)
    rw [←ENat.coe_mul, ENat.coe_le_coe, h_g'_min_card]
    -- Let ΔH be the finset of actually bad x points where f and g' disagree.
    let ΔH := Finset.filter (fun x => f x ≠ g' x) Finset.univ
    -- Y_bad is the set of quotient points y that THERE EXISTS a bad fiber point x
    let Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g'
    have hFinType_Y_bad : Fintype Y_bad := Fintype.ofFinite ↑Y_bad
    let Fib := fun (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩) =>
      ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)) ''
      (Finset.univ : Finset (Fin (2 ^ steps)))).toFinset
    -- Every point of disagreement `x` must belong to a fiber over some `y` in `Y_bad`.
    have h_ΔH_subset_bad_fiber_points : ΔH ⊆ Y_bad.toFinset.biUnion Fib := by
      intro x hx_in_ΔH
      let y_of_x := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i steps h_i_add_steps x
      refine Finset.mem_biUnion.mpr ⟨y_of_x,
        Set.mem_toFinset.mpr ⟨x, rfl, (Finset.mem_filter.mp hx_in_ΔH).2⟩, ?_⟩
      simp only [Fib, coe_univ, Set.image_univ, Set.toFinset_range, mem_image, mem_univ, true_and]
      exact ⟨pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (x := x),
        is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
          (x := x) (y := y_of_x).mp rfl⟩
    have h_card_fiber_of_each_y : ∀ _y ∈ Y_bad.toFinset, (Fib _y).card ≤ 2 ^ steps := by
      intro y _
      have hy := card_qMap_total_fiber 𝔽q β i steps h_i_add_steps y
      simp only [Set.image_univ, Fintype.card_ofFinset] at hy
      simp only [Fib, Set.toFinset_card, coe_univ, Set.image_univ, Fintype.card_ofFinset,
        le_refl, hy]
    have h_Y_ncard : Y_bad.toFinset.card = Y_bad.ncard := by
      rw [Set.toFinset_card, ←_root_.Nat.card_coe_set_eq, card_eq_fintype_card]
    refine (Finset.card_le_card h_ΔH_subset_bad_fiber_points).trans ?_
    refine (Finset.card_biUnion_le_card_mul Y_bad.toFinset Fib _ h_card_fiber_of_each_y).trans ?_
    rw [h_Y_ncard]
  -- The minimum distance `d_H` is bounded by the distance to this specific `g'`.
  have h_dist_bridge : d_H ≤ d_fw * 2 ^ steps := by
    refine le_trans (sInf_le ⟨g', h_g'_mem, le_refl _⟩) h_dist_le_fw_dist_times_fiber_size
  have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 :=
    Nat.le_of_lt_succ (WithTop.coe_lt_coe.1 h_fw_dist_lt)
  -- `(d_{i+steps} - 1) * 2 ^ steps = d_i - 1`.
  have h_algebraic_identity : (d_i_plus_steps - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_i_plus_steps, BBF_CodeDistance]
    rw [Nat.sub_mul, ←Nat.pow_add, ←Nat.pow_add];
    have h1 : ℓ + 𝓡 - (↑i + steps) + steps = ℓ + 𝓡 - i := by
      rw [← Nat.sub_sub, Nat.sub_add_cancel
        (Nat.le_sub_of_add_le' (h_i_add_steps.trans (Nat.le_add_right ℓ 𝓡)))]
    have h2 : (ℓ - (↑i + steps) + steps) = ℓ - i := by
      rw [← Nat.sub_sub, Nat.sub_add_cancel (Nat.le_sub_of_add_le' h_i_add_steps)]
    rw [h1, h2]
  -- `d_H` is finite since it is bounded by `d_fw * 2 ^ steps`.
  have h_dH_ne_top : d_H ≠ ⊤ := ne_of_lt (lt_of_le_of_lt h_dist_bridge (ENat.coe_lt_top _))
  let d_H_nat := ENat.toNat d_H
  have h_dH_eq : d_H = d_H_nat := (ENat.coe_toNat h_dH_ne_top).symm
  have h_bridge_nat : d_H_nat ≤ d_fw * 2 ^ steps := by
    rw [←ENat.coe_le_coe]
    exact le_of_eq_of_le h_dH_eq.symm h_dist_bridge
  have h_final_inequality : 2 * d_H_nat ≤ d_i - 1 := by
    rw [← h_algebraic_identity]
    exact le_trans (Nat.mul_le_mul_left 2 h_bridge_nat)
      (by rw [←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ h_fw_bound)
  change (2 : ℕ∞) * d_H < d_i
  rw [h_dH_eq]
  exact_mod_cast Nat.lt_of_le_pred h_d_i_gt_0 h_final_inequality
