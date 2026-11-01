theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  obtain ⟨B, T, hB⟩ := boundedu
  obtain ⟨i, j, hij, heq4⟩ : ∃ i j : ℕ, i < j ∧ ∀ t : Fin 4, u (i + t) = u (j + t) := by
    obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp
      (((Set.Finite.pi fun _ => Set.finite_Icc B T).subset
        (Set.range_subset_iff.mpr fun n k _ => hB (n + k)) :
        (Set.range fun (n : ℕ) (k : Fin 4) => u (n + k)).Finite).not_infinite ∘
        Set.infinite_range_of_injective)
    rcases lt_or_gt_of_ne hne with hij | hij
    · exact ⟨i, j, hij, congrFun heq⟩
    · exact ⟨j, i, hij, congrFun heq.symm⟩
  have hrec : ∀ n : ℕ, (u (n + 4) : ℝ) = (u (n + 3) + u (n + 2) + u (n + 1) * u (n + 0)) /
      (u (n + 3) * u (n + 2) + u (n + 1) + u (n + 0)) :=
    fun n => (hu (n + 4) (Nat.le_add_left _ n)).1
  have hstep : ∀ a b : ℕ, (∀ t < 4, u (a + t) = u (b + t)) → u (a + 4) = u (b + 4) := fun a b h =>
    Int.cast_injective
      (by rw [hrec a, hrec b, h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)])
  have key : ∀ m : ℕ, u (i + m) = u (j + m) := fun m =>
    Nat.strongRecOn m fun m ih => by
      rcases Nat.lt_or_ge m 4 with hm | hm
      · exact heq4 ⟨m, hm⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hm
        exact hstep (i + k) (j + k) fun t ht => by
          simp only [Nat.add_assoc]
          exact ih (k + t) (Nat.add_lt_add_left ht k)
  refine ⟨i, j - i, Nat.sub_pos_of_lt hij, fun n hn => ?_⟩
  nth_rewrite 1 [← Nat.add_sub_cancel' hn]
  rw [show i + (n - i) + (j - i) = j + (n - i) from by omega]
  exact (key _).symm
