# fold_advances_evaluation_poly — notes (run 9, supersedes earlier notes)

## Status / BEST
Banked best: **score 88.5** (tokens 353, hb 7369), candidate.lean holds it (re-profiled this run: ok, total 7369, floor 2536, reference 46076).
Toolchains: all 3 compatible (v4.31/4.30/4.29).

## Profile (this run, current best, total 7369, floor 2536)
- line 39 `let P₀ := evenRefinement …` block: 2696 hb (this is the diff-cut attribution — it covers everything after it: h_P_i_eval + h_equation_39 + calc + tail; nested blocks profiled under the costliest step)
- h_fiber_diff: 1233; h_eval_qMap: 659; h_one 117; fiberMap 94
- points_left_heartbeats = 3.5; axis earlier: 0.0175 pts/token, 0.723 pts/1k hb → at most ~6 length-pts + ~3.5 hb-pts theoretically left. We are near the practical floor of this architecture.

## Tested THIS run (all verified)
- [tested: tail simp list minus `Polynomial.eval_finset_sum` → FAIL 880:47 `ring_nf`/`ring` made no progress on per-j goal; eval_finset_sum is load-bearing]
- [tested: tail simp list minus `Finset.sum_mul` → FAIL same 880:47; load-bearing]
- [tested: tail closer `simp` (full) after the simp-only list → FAIL 876:33 unsolved sum goal (simp leaves ∑ (c*eval*(1-r)+c*eval*r) vs ∑ ((1-r)*c+r*c)*eval)]
- [tested: tail closer `grind` → FAIL, 31879 hb and fails (huge goal diagnostics)]
- [tested: tail closer `congr 1` + per-j `simp only [Finset.mul_sum, …]` → FAIL 881:47 `simp` made no progress]
- [tested: middle step via `linear_combination (P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal) * h_fiber_diff` (re-measured on current structure) → compiles but 367 tok / 7758 hb, WORSE than `rw [h_equation_39 0, h_equation_39 1, eq_add_of_sub_eq h_fiber_diff]; ring` (353/7369)]
- [tested: h_eval_qMap witness `by simp [pointToIterateQuotientIndex_qMap_total_fiber_eq_self]` → FAIL 856:10 simp made no progress; keep `by rw […eq_self]`]
- [tested: h_eval_qMap as a term `(is_fiber_iff…).mpr (…) |>.trans (iteratedQuotientMap_k_eq_1_is_qMap …)` → FAIL: type mismatch; `iteratedQuotientMap_k_eq_1_is_qMap` is a ∀ over x (needs `(fiberMap k)` application and produces a Subtype-valued eq `= ⟨eval x (qMap …), ⋯⟩`), not a plain Eq that trans can consume directly. The rw-based proof exploits the trailing rfl; a term form would need the Subtype coercion — not worth it]
- Linter on current candidate is CLEAN except unused section variables (in the statement, cannot change): [CharP L 2] [NeZero ℓ] c. Every simp-list entry is used; no free deletions left.

## NEW WIN from run 8 (already in candidate.lean)
`h_eval_qMap` as ONE rw (−15 tok, −47 hb):
```lean
  have h_eval_qMap (k : Fin 2) :
      (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval (fiberMap k).val = y := by
    rw [is_fiber_iff_generates_quotient_point 𝔽q β i 1 (by omega) (fiberMap k) y |>.mpr
      (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self]),
      iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i (by omega)]
```
Key: `iteratedQuotientMap_k_eq_1_is_qMap` works as a rewrite rule; rw's trailing rfl closes `↑⟨v,_⟩ = v`. Note its real signature (verified via the term-form failure): `∀ (x : ↥(sDomain …)), iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate i 1 h x = ⟨Polynomial.eval x (qMap 𝔽q β ⟨i⟩), ⋯⟩`.

## Durable facts (verified in earlier runs)
- Signature order: qMap_total_fiber (𝔽q β i:Fin r steps h y); is_fiber_iff…(𝔽q β i steps h x y);
  `pointToIterateQuotientIndex_qMap_total_fiber_eq_self 𝔽q β … i steps h y k` (needs the by-rw form).
- `qMap_total_fiber_one_level_eq` as simp rule fails (let-chain LHS); must use `show x₀ = _ from h_one 0` inside the simp list with expected type.
- Do NOT merge the middle calc `ring` into the tail; `eq_add_of_sub_eq h_fiber_diff` + `ring` beats `linear_combination` (measured twice: run 8 and this run).
- Names that do NOT exist: `Polynomial.mul_add`, `Polynomial.C_smul`, `qMap_eval_fiber_eq_self`.
- Deprecation warnings (`Subtype.eq_iff`, `Polynomial.eval_finsetSum`) harmless.

## Most promising next ideas (if resuming)
1. Length: h_fiber_diff (1233 hb) and h_eval_qMap (659) are the two cheapest targets for hb; but every simp entry is needed. Only a *different* proof of `x₁.val - x₀.val = 1` could cut hb (e.g. via `qMap_total_fiber_basis_sum_repr` directly, as the reference did — likely worse).
2. Token micro: the calc step 2 RHS `P₀.eval y.val * (1 - r_chal) + P₁.eval y.val * r_chal` is restated; a `calc … := rfl; … := by …` with `_` cannot skip it since step 3 needs a concrete LHS for the tail simp. Tried tail-on-full-goal in run 8 → FAIL.
3. Accept 88.5; theoretical max on this architecture ≈ 95.
