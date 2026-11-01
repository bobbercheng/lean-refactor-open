theorem putnam_1964_b2
(S : Type*) [Fintype S] [Nonempty S]
(P : Finset (Set S))
(hPP : ∀ T ∈ P, ∀ U ∈ P, T ∩ U ≠ ∅)
(hPS : ¬∃ T : Set S, T ∉ P ∧ (∀ U ∈ P, T ∩ U ≠ ∅))
: (P.card = 2 ^ (Fintype.card S - 1)) := by
  classical
  have key : ∀ A ∉ P, ∃ U ∈ P, ∀ x ∈ A, x ∉ U := λA hA => by
    by_contra! h
    exact hPS ⟨A, hA, λU hU => nonempty_iff_ne_empty.mp $ h U hU⟩
  have dich : ∀ A, A ∈ P ∨ Aᶜ ∈ P := λA => by
    by_contra! h
    obtain ⟨U, hU, hAU⟩ := key A h.1
    obtain ⟨V, hV, hVc⟩ := key Aᶜ h.2
    exact hPP U hU V hV $ Set.eq_empty_of_forall_notMem λx hx =>
      hVc x (hAU x · hx.1) hx.2
  have h2 : P.card * 2 = 2 ^ (Fintype.card S - 1) * 2 := by
    rw [← pow_succ, Nat.sub_add_cancel Fintype.card_pos,
      ← Finset.card_univ.trans Fintype.card_set,
      ← Finset.eq_univ_of_forall λA =>
        (dich A).elim (Finset.mem_union_left $ P.image compl)
          λhA => Finset.mem_union_right P $ Finset.mem_image.mpr ⟨Aᶜ, hA, compl_compl A⟩,
      Finset.card_union_of_disjoint $ Finset.disjoint_left.mpr
        λA hA hA' => by
          obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA'
          exact hPP B hB Bᶜ hA $ inter_compl_self B,
      Finset.card_image_of_injective P compl_injective, Nat.mul_two]
  exact Nat.eq_of_mul_eq_mul_right Nat.zero_lt_two h2
