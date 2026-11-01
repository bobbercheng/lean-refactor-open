lemma fundamental_theorem_of_variational_calculus' {f : Y → V}
    (μ : Measure Y) [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    [OpensMeasurableSpace Y]
    (hf : Continuous f) (hg : ∀ g, IsTestFunction g → ∫ x, ⟪f x, g x⟫_ℝ ∂μ = 0) :
    f = 0 := by
    by_contra h₀
    obtain ⟨x₀, hx0⟩ := Function.ne_iff.mp h₀
    have hinner : Continuous (λx => ⟪f x, f x₀⟫_ℝ) :=
      Continuous.inner' f (λ_ => f x₀) hf continuous_const
    have hself : 0 < ⟪f x₀, f x₀⟫_ℝ :=
      lt_of_le_of_ne (real_inner_self_nonneg') λh => hx0 $ inner_self_eq_zero'.mp h.symm
    obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp
      ((hinner.continuousAt).preimage_mem_nhds $ Ioi_mem_nhds hself)
    obtain ⟨φ, hts, hcs, hc, hr, hφx₀⟩ := exists_contDiff_tsupport_subset
      (Metric.ball_mem_nhds x₀ hδpos)
    have key_integral := hg (λx => φ x • f x₀)
      (IsTestFunction.smul_right ⟨hc, hcs⟩ contDiff_const)
    simp only [inner_smul_right'] at key_integral
    exact (Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
        (x := x₀) (hc.continuous.mul hinner) hcs.mul_right
        (λx => if h : φ x = 0 then by simp [h] else
          mul_nonneg (hr $ Set.mem_range_self x).1 (hδ $ hts $ subset_closure h).le)
        (by simp [hφx₀, hself.ne'])).ne key_integral.symm
