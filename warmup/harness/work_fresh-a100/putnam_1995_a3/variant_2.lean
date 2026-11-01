theorem putnam_1995_a3
(relation : (Fin 9 → ℤ) → (Fin 9 → ℤ) → Prop)
(digits_to_num : (Fin 9 → ℤ) → ℤ)
(hdigits_to_num : digits_to_num = fun dig => ∑ i : Fin 9, (dig i) * 10^i.1)
(hrelation : ∀ d e : (Fin 9 → ℤ), relation d e ↔ (∀ i : Fin 9, d i < 10 ∧ d i ≥ 0 ∧ e i < 10 ∧ e i ≥ 0) ∧ (∀ i : Fin 9, 7 ∣ (digits_to_num (fun j : Fin 9 => if j = i then e j else d j))))
: ∀ d e f : (Fin 9 → ℤ), ((relation d e) ∧ (relation e f)) → (∀ i : Fin 9, 7 ∣ d i - f i) := by
  intro d e f h
  have h2 := ((hrelation d e).mp h.1).2
  have h4 := ((hrelation e f).mp h.2).2
  have key : ∀ (x y : Fin 9 → ℤ) (i : Fin 9),
      digits_to_num (fun j => if j = i then y j else x j)
        = digits_to_num x + (y i - x i) * 10 ^ i.1 := by
    intro x y i
    simp only [hdigits_to_num]
    rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib,
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i)
        (fun b _ hb => by simp [hb]), if_pos rfl, ← sub_mul]
  have hce : 7 ∣ digits_to_num d + digits_to_num e := by
    have hE : ∑ i : Fin 9, (digits_to_num d + (e i - d i) * 10 ^ i.1)
        - 7 * digits_to_num d = digits_to_num d + digits_to_num e := by
      simp only [Finset.sum_add_distrib, hdigits_to_num, sub_mul, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_fin]; ring
    exact hE ▸ dvd_sub (Finset.dvd_sum fun i _ => key d e i ▸ h2 i) ⟨digits_to_num d, rfl⟩
  have hstep : ∀ i : Fin 9, 7 ∣ (d i - f i) * 10 ^ i.1 := by
    intro i
    have h5 := dvd_add (key d e i ▸ h2 i) (key e f i ▸ h4 i)
    rw [add_add_add_comm, ← add_mul, sub_add_sub_cancel'] at h5
    have h6 := dvd_sub h5 hce
    rwa [add_sub_cancel_left, mul_neg, neg_sub, dvd_neg] at h6
  intro i
  exact (Int.isCoprime_iff_gcd_eq_one.mpr rfl |>.pow_right (n := i.1)).dvd_of_dvd_mul_right (hstep i)
