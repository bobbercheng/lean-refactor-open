lemma time_deriv_time_deriv_electricField_of_isExtrema {A : ElectromagneticPotential d}
    {𝓕 : FreeSpace}
    (hA : ContDiff ℝ ∞ A) (J : LorentzCurrentDensity d)
    (hJ : ContDiff ℝ ∞ J) (h : IsExtrema 𝓕 A J)
    (t : Time) (x : Space d) (i : Fin d) :
    ∂ₜ (∂ₜ (A.electricField 𝓕.c · x i)) t =
      𝓕.c ^ 2 * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
      𝓕.c ^ 2 / 𝓕.ε₀ * ∂[i] (J.chargeDensity 𝓕.c t ·) x -
      𝓕.c ^ 2 * 𝓕.μ₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
  have hEs : ∀ j, ContDiff ℝ 2 (A.electricField 𝓕.c t · j) :=
    λj => electricField_apply_contDiff_space (hA.of_le $ right_eq_inf.mp rfl) t
  have hEd : ∀ j k, Differentiable ℝ (∂[k] (A.electricField 𝓕.c t · j)) :=
    λj k => Space.deriv_differentiable (hEs j) k
  have hBt : ∀ j, Differentiable ℝ
      (λs => ∂[j] (A.magneticFieldMatrix 𝓕.c s · (j, i)) x) :=
    λj => Space.space_deriv_differentiable_time
      (magneticFieldMatrix_contDiff _ (hA.of_le $ right_eq_inf.mp rfl) (j, i)) x
  have hJd : Differentiable ℝ J := hJ.differentiable $ by simp
  have hJt : Differentiable ℝ (λs => J.currentDensity 𝓕.c s x i) :=
    LorentzCurrentDensity.currentDensity_apply_differentiable_time hJd x i
  have hswap : ∑ j, (∂[j] (∂[i] (A.electricField 𝓕.c t · j)) x) =
      ∂[i] (λy => (∇ ⬝ (A.electricField 𝓕.c t)) y) x := by
    erw [Space.deriv_eq_fderiv_basis i _ x, fderiv_fun_sum]
    simp only [FunLike.coe_sum, Finset.sum_apply]
    congr
    funext j
    rewrite [← Space.deriv_eq_fderiv_basis i _ x]
    exact congrArg (· x)
      (Space.deriv_commute (A.electricField 𝓕.c t · j) $ hEs j)
    intro j _
    exact (hEd j j).differentiableAt
  calc _
    _= 1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
        1 / (𝓕.μ₀ * 𝓕.ε₀) * ∑ j, (∂[j] (∂[i] (A.electricField 𝓕.c t · j)) x) -
        1 / 𝓕.ε₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        conv_lhs =>
          enter [1]
          change λt => ∂ₜ (A.electricField 𝓕.c · x i) t
          enter [t]
          rw [Time.deriv_euclid $ electricField_differentiable_time
            (hA.of_le $ right_eq_inf.mp rfl) _,
            time_deriv_electricField_of_isExtrema hA J hJ h]
        rewrite [Time.deriv_eq, fderiv_fun_sub]
        simp only [one_div, FunLike.coe_sub, Pi.sub_apply,
          fderiv_const_mul (Differentiable.fun_sum λj _ => hBt j).differentiableAt,
          fderiv_const_mul hJt.differentiableAt,
          fderiv_fun_sum λi _ => (hBt i).differentiableAt,
          Time.deriv_eq, _root_.smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply]
        simp only [← mul_sub, ← Finset.sum_sub_distrib]
        congr
        funext k
        rewrite [← Time.deriv_eq]
        rewrite [Space.time_deriv_comm_space_deriv]
        simp only [time_deriv_magneticFieldMatrix _ $ hA.of_le $ ENat.LEInfty.out]
        rewrite [Space.deriv_eq_fderiv_basis, fderiv_fun_sub (hEd _ _).differentiableAt
          (hEd _ _).differentiableAt]
        simp only [_root_.sub_apply, ← deriv_eq_fderiv_basis]
        apply magneticFieldMatrix_contDiff
        apply hA.of_le $ right_eq_inf.mp rfl
        · exact ((Differentiable.fun_sum λj _ => hBt j).const_mul _).differentiableAt
        · apply hJt.differentiableAt.const_mul
    _ = 𝓕.c ^ 2 * ∑ j, (∂[j] (∂[j] (A.electricField 𝓕.c t · i)) x) -
        𝓕.c ^ 2 / 𝓕.ε₀ * ∂[i] (J.chargeDensity 𝓕.c t ·) x -
        𝓕.c ^ 2 * 𝓕.μ₀ * ∂ₜ (J.currentDensity 𝓕.c · x i) t := by
        rewrite [isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ] at h
        rewrite [hswap,
          show (λy => (∇ ⬝ (A.electricField 𝓕.c t)) y) =
            λy => (1 / 𝓕.ε₀) * J.chargeDensity 𝓕.c t y from
          funext λy => (h t y).1.trans $ by ring]
        rewrite [Space.deriv_eq_fderiv_basis i _ x,
          fderiv_const_mul $ Differentiable.differentiableAt
            (LorentzCurrentDensity.chargeDensity_differentiable_space hJd t)]
        simp [← Space.deriv_eq_fderiv_basis, 𝓕.c_sq, mul_comm]
        ring
