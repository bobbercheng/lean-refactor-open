theorem putnam_1964_a4
(u : ℕ → ℤ)
(boundedu : ∃ B T : ℤ, ∀ n : ℕ, B ≤ u n ∧ u n ≤ T)
(hu : ∀ n ≥ 4, u n = ((u (n - 1) + u (n - 2) + u (n - 3) * u (n - 4)) : ℝ) / (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ∧ (u (n - 1) * u (n - 2) + u (n - 3) + u (n - 4)) ≠ 0)
: (∃ N c : ℕ, c > 0 ∧ ∀ n ≥ N, u (n + c) = u n) := by
  obtain ⟨B, T, hB⟩ := boundedu
  have hf : Set.Finite (Set.range fun n => (u n, u (n+1), u (n+2), u (n+3))) :=
    Set.Finite.subset (Set.Finite.prod (Set.finite_Icc B T)
      (Set.Finite.prod (Set.finite_Icc B T)
        (Set.Finite.prod (Set.finite_Icc B T) (Set.finite_Icc B T)))) (by
      rintro _ ⟨n, rfl⟩
      exact Set.mk_mem_prod (hB n) (Set.mk_mem_prod (hB (n+1))
        (Set.mk_mem_prod (hB (n+2)) (hB (n+3)))))
  obtain ⟨i, j, hij, heq⟩ : ∃ i j : ℕ, i < j ∧ (u i, u (i+1), u (i+2), u (i+3)) = (u j, u (j+1), u (j+2), u (j+3)) := by
    by_contra hcon
    have hinj : Function.Injective fun n => (u n, u (n+1), u (n+2), u (n+3)) := by
      intro a b hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact hcon ⟨a, b, h, hab⟩
      · exact hcon ⟨b, a, h, hab.symm⟩
    exact (Set.infinite_range_of_injective hinj).not_finite hf
  have hstep : ∀ m : ℕ, u (i + m) = u (j + m) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      match m with
      | 0 => exact congrArg (fun t => t.1) heq
      | 1 => exact congrArg (fun t => t.2.1) heq
      | 2 => exact congrArg (fun t => t.2.2.1) heq
      | 3 => exact congrArg (fun t => t.2.2.2) heq
      | m + 4 =>
        obtain ⟨hi, -⟩ := hu (i + (m+4)) (by omega)
        obtain ⟨hj, -⟩ := hu (j + (m+4)) (by omega)
        have e₁ : i + (m+4) - 1 = i + (m+3) := by omega
        have e₂ : i + (m+4) - 2 = i + (m+2) := by omega
        have e₃ : i + (m+4) - 3 = i + (m+1) := by omega
        have e₄ : i + (m+4) - 4 = i + m := by omega
        have e₅ : j + (m+4) - 1 = j + (m+3) := by omega
        have e₆ : j + (m+4) - 2 = j + (m+2) := by omega
        have e₇ : j + (m+4) - 3 = j + (m+1) := by omega
        have e₈ : j + (m+4) - 4 = j + m := by omega
        have t₁ : u (i + m) = u (j + m) := ih m (by omega)
        have t₂ : u (i + (m+1)) = u (j + (m+1)) := ih (m+1) (by omega)
        have t₃ : u (i + (m+2)) = u (j + (m+2)) := ih (m+2) (by omega)
        have t₄ : u (i + (m+3)) = u (j + (m+3)) := ih (m+3) (by omega)
        have key : (u (i + (m+4)) : ℝ) = u (j + (m+4)) := by
          rw [hi, e₁, e₂, e₃, e₄, hj, e₅, e₆, e₇, e₈, t₁, t₂, t₃, t₄]
        exact_mod_cast key
  exact ⟨i, j - i, by omega, by
    intro n hn
    have h₅ := hstep (n - i)
    rw [show i + (n - i) = n by omega, show j + (n - i) = n + (j - i) by omega] at h₅
    exact h₅.symm⟩
