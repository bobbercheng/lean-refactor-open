# Notes: `time_deriv_time_deriv_electricField_of_isExtrema` (physlib, IsExtrema.lean)

## Status (run 6)
- BEST COMPILING: score 63.65 (tokens 870, hb 12375; ref 1372/26970). candidate.lean unchanged.
- Structure: 4 calc steps (see prior notes below — still accurate).

## Tested this run (do NOT retry)
- `have hAi := hA.of_le (right_eq_inf.mp rfl)`: FAILS standalone — expected type needed to
  pick the ContDiff level. With `ContDiff ℝ 1 A` annotation: electricField_apply_contDiff_space
  wants ContDiff ℝ (2+1) i.e. 3 of A.val. With `ContDiff ℝ 3 A`: works at
  electricField_apply_contDiff_space + magneticFieldMatrix_contDiff sites, but
  electricField_differentiable_time wants ContDiff ℝ 2 — must stay inline. Net: hBsum
  abbreviation saved only ~90 hb for +30 tokens → net score LOSS. Not worth it.
- Final block golf (replacing `simp [← Space.deriv_eq_fderiv_basis, 𝓕.c_sq, mul_comm]; ring`):
  * `rw [𝓕.c_sq]; ring` → stuck on `𝓕.μ₀ * 𝓕.μ₀⁻¹` (ring treats μ₀⁻¹ as unrelated atom).
  * `rw [𝓕.c_sq, Space.deriv_eq_fderiv_basis i ρ x]; simp only [ContinuousLinearMap.smul_apply,
    smul_eq_mul]; ring` → got within one fact: only `μ₀ * μ₀⁻¹ = 1` missing. A closer adding
    `mul_inv_cancel₀` (needs `𝓕.μ₀ ≠ 0`, maybe simp-provable from FreeSpace field instances)
    might work: `simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, mul_inv_cancel₀]` then
    `ring`. UNTESTED with mul_inv_cancel₀ included — try it if resuming (add `𝓕.μ₀ ≠ 0` side
    goal risk; could also try `inv_mul_cancel₀` / `field_simp` with the CLM smul lemma).
  * `field_simp` alone → 12053 hb but stuck on same smul-vs-deriv term;
    `field_simp; simp [← Space.deriv_eq_fderiv_basis, 𝓕.c_sq]` untested.
- `simp only [← Space.deriv_eq_fderiv_basis]` in step 2 FAILS: full `simp` needed there
  (closes the fderiv-sub pointwise goal).
- `congr 2` for step 2 opener: compiles, hb-neutral.

## Prior facts (still valid)
- `rw [isExtrema_iff_gauss_ampere_magneticFieldMatrix hA J hJ] at h` (no side goals).
- `Time.deriv_fun_sum` exists; `Time.deriv_fun_sub`/`Time.deriv_const_mul` DO NOT.
- `Space.deriv_fun_sum` does NOT exist. Function-level rfl:
  `(∇⬝E) = fun x => ∑ j, Space.deriv j (fun x => E x j) x` is TRUE by rfl.
- `Space.deriv_commute (f) (hf) : deriv u (deriv v f) = deriv v (deriv u f)` —
  u/v implicit, need `(u := j) (v := i)` when goal is eta-expanded.
- c_sq: `𝓕.c_sq : 𝓕.c ^ 2 = 1 / (𝓕.ε₀ * 𝓕.μ₀)`.
- Profile: step1+2 block ≈ 10.9k hb of 12.4k; `funext k` alone 1358 hb; floor 663.
- Upstream HEAD has no simplification of this proof.
