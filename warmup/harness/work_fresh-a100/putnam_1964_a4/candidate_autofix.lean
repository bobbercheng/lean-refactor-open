theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  obtain ⟨B, T, hB⟩ := boundedu
  have h_main : ∃ i j : ℕ, i < j ∧ ∀ t < 4, u (i + t) = u (j + t) := by
    have s := Set.finite_Icc B T
    have hfin : (Set.range fun (n : ℕ) (k : Fin 4) => u (n + k)).Finite :=
      (Set.Finite.pi fun _ => s).subset
        (Set.range_subset_iff.mpr fun n k _ => hB (n + k))
    obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp
      fun hinj => hfin.not_infinite (Set.infinite_range_of_injective hinj)
    rcases lt_or_gt_of_ne hne with hij | hij
    · exact ⟨i, j, hij, fun t ht => congrFun heq ⟨t, ht⟩⟩
    · exact ⟨j, i, hij, fun t ht => (congrFun heq ⟨t, ht⟩).symm⟩
  obtain ⟨i, j, hij, heq4⟩ := h_main
  have hrec : ∀ n : ℕ, u (n + 4) = ((u (n + 3) + u (n + 2) + u (n + 1) * u (n + 0)) : ℝ) /
      ((u (n + 3) * u (n + 2) + u (n + 1) + u (n + 0)) : ℝ) :=
    fun n => (hu (n + 4) (Nat.le_add_left 4 n)).1
  have hstep : ∀ a b c : ℕ, (∀ t < 4, u (a + (c + t)) = u (b + (c + t))) →
      u (a + (c + 4)) = u (b + (c + 4)) := by
    intro a b c h
    simp only [← Nat.add_assoc, ← Nat.add_assoc] at h
    show u (a + c + 4) = u (b + c + 4)
    exact Int.cast_injective
      (by rw [hrec (a + c), hrec (b + c), h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)])
  have key : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      rcases Nat.lt_or_ge m 4 with hm | hm
      · exact heq4 m hm
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 4 := ⟨m - 4, (Nat.sub_add_cancel hm).symm⟩
        exact hstep i j k fun t ht => ih (k + t) (Nat.add_lt_add_left ht k)
  refine ⟨i, j - i, Nat.sub_pos_of_lt hij, fun n hn => ?_⟩
  have h9 := key (n - i)
  rw [Nat.add_sub_cancel' hn, show j + (n - i) = n + (j - i) from by omega] at h9
  exact h9.symm
