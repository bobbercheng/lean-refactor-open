theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  obtain ⟨B, T, hB⟩ := boundedu
  obtain ⟨i, j, hij, heq4⟩ : ∃ i j : ℕ, i < j ∧ ∀ t : Fin 4, u (i + t) = u (j + t) := by
    have hfin : (Set.range fun (n : ℕ) (k : Fin 4) => u (n + k)).Finite :=
      (Set.Finite.pi fun _ => Set.finite_Icc B T).subset
        (Set.range_subset_iff.mpr fun n k _ => hB (n + k))
    obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp
      (hfin.not_infinite ∘ Set.infinite_range_of_injective)
    rcases lt_or_gt_of_ne hne with hij | hij
    · exact ⟨i, j, hij, congrFun heq⟩
    · exact ⟨j, i, hij, congrFun heq.symm⟩
  have hrec : ∀ n : ℕ, (u (n + 4) : ℝ) = (u (n + 3) + u (n + 2) + u (n + 1) * u (n + 0)) /
      (u (n + 3) * u (n + 2) + u (n + 1) + u (n + 0)) :=
    fun n => (hu (n + 4) (Nat.le_add_left _ n)).1
  have hstep : ∀ a b : ℕ, (∀ t < 4, u (a + t) = u (b + t)) → u (a + 4) = u (b + 4) := fun a b h =>
    Int.cast_injective
      (by rw [hrec a, hrec b, h _ (by decide), h _ (by decide), h _ (by decide), h _ (by decide)])
  have key : ∀ m : ℕ, u (i + m) = u (j + m) := fun m =>
    Nat.strongRecOn m fun m ih => by
      obtain hm | ⟨k, rfl⟩ := Nat.lt_or_ge m 4
      · exact heq4 ⟨m, hm⟩
      · exact hstep (i + k) (j + k) fun t ht => by
          simp only [Nat.add_assoc]
          exact ih (k + t) (by omega)
  refine ⟨i, j - i, Nat.sub_pos_of_lt hij, fun n hn => ?_⟩
  have h9 := key (n - i)
  rw [Nat.add_sub_cancel' hn, show j + (n - i) = n + (j - i) from by omega] at h9
  exact h9.symm
