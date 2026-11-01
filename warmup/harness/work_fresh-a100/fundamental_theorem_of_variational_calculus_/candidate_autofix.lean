lemma fundamental_theorem_of_variational_calculus' {f : Y → V}
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [OpensMeasurableSpace Y]
    (hf : Continuous f) (hg : ∀ g, IsTestFunction g → ∫ x, ⟪f x, g x⟫_ℝ ∂μ = 0) :
    f = 0 := by
    by_contra h₀
    obtain ⟨x₀, hx0⟩ := Function.ne_iff.mp h₀
    have hinner : Continuous (fun x => ⟪f x, f x₀⟫_ℝ) :=
      Continuous.inner' f (fun _ => f x₀) hf continuous_const
    have hself : 0 < ⟪f x₀, f x₀⟫_ℝ :=
      lt_of_le_of_ne (real_inner_self_nonneg') fun h => hx0 (inner_self_eq_zero'.mp h.symm)
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp
      ((hinner.continuousAt).preimage_mem_nhds (Ioi_mem_nhds hself))
    have bump_exists : ∃ φ : Y → ℝ, IsTestFunction φ ∧ φ x₀ > 0 ∧
        (∀ x ∈ Function.support φ, 0 ≤ φ x) ∧
        Function.support φ ⊆ Metric.ball x₀ δ ∧
        (∀ x ∈ Metric.closedBall x₀ (δ/2), 0 < φ x) := by
          haveI : HasContDiffBump Y := hasContDiffBump_of_innerProductSpace Y
          let φ1 : ContDiffBump x₀ :=
            ⟨δ / 2, δ, div_pos hδpos two_pos, half_lt_self hδpos⟩
          exact ⟨φ1.toFun, ⟨φ1.contDiff, φ1.hasCompactSupport⟩,
            φ1.pos_of_mem_ball (Metric.mem_ball_self φ1.rOut_pos), fun x _ => φ1.nonneg,
            (ContDiffBump.support_eq φ1).subset, fun x hx => φ1.pos_of_mem_ball
              (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hx)
                (half_lt_self hδpos)))⟩
    obtain ⟨φ, hφ_testfun, hφ_pos_x₀, hφ_non_neg, hφ_support_subset, hφ_pos_inner⟩ :=
      bump_exists
    have key_integral := hg (fun x => φ x • f x₀)
      (IsTestFunction.smul_right hφ_testfun contDiff_const)
    simp only [inner_smul_right'] at key_integral
    have supp_subset2 : Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) ⊆ Function.support φ :=
      fun x hx => (mul_ne_zero_iff.mp hx).1
    have integrable_prod :
      Integrable (fun x => φ x * ⟪f x, f x₀⟫_ℝ) μ :=
      (Continuous.mul hφ_testfun.smooth.continuous hinner).integrable_of_hasCompactSupport
        (hφ_testfun.supp.mono supp_subset2)
    have h_nonneg : ∀ x, 0 ≤ φ x * ⟪f x, f x₀⟫_ℝ := fun x =>
      (eq_or_ne (φ x) 0).elim (fun h => le_of_eq (mul_eq_zero.mpr (Or.inl h)).symm)
        fun h => mul_nonneg (hφ_non_neg x h) (hδ (hφ_support_subset h)).le
    have hμ : 0 < μ (Metric.closedBall x₀ (δ/2)) :=
      lt_of_lt_of_le (Metric.isOpen_ball.measure_pos μ
        (Metric.nonempty_ball.mpr (div_pos hδpos two_pos)))
        (measure_mono Metric.ball_subset_closedBall)
    have closedBall_subset_support :
        Metric.closedBall x₀ (δ/2)
          ⊆ Function.support (fun x => φ x * ⟪f x, f x₀⟫_ℝ) := fun x hx =>
        mul_ne_zero (ne_of_gt (hφ_pos_inner x hx)) (ne_of_gt (hδ
          (Metric.closedBall_subset_ball (half_lt_self hδpos) hx)))
    have integral_pos : 0 < ∫ x, φ x * ⟪f x, f x₀⟫_ℝ ∂μ :=
      (integral_pos_iff_support_of_nonneg h_nonneg integrable_prod).mpr
        (lt_of_lt_of_le hμ (measure_mono closedBall_subset_support))
    exact integral_pos.ne key_integral.symm
