# Notes: `ι_timeOrderF_superCommuteF_eq_time` (physlib v4.32.0)

## Status (run 6 FINAL): BEST = 67.58 (727 tok / 15805 hb); candidate.lean holds it.
Run-6 progression: 60.92 → 60.95 (short binders `fun x (_ : x ∈ ...)` in p) → 63.10 (merged calc
steps 1+2, deleting the ~115-token two-term intermediate RHS) → 63.71 (plain smul_mul_assoc /
mul_smul_comm instead of Algebra.*, −780 hb) → 67.18 (`induction (Basis.mem_span ofCrAnListFBasis b)
using Submodule.span_induction`) → 67.58 (smul closers: `simp only [..., map_smul, h]` with the IH
h as a rewrite rule, replacing `exact congrArg (x • ·) h`).

## KEY discoveries (durable)
- OLD claim "induction ... using Submodule.span_induction FAILS" was WRONG. It works, but:
  (1) the major premise must be the MEMBERSHIP PROOF: `induction (Basis.mem_span ofCrAnListFBasis b)
      using Submodule.span_induction with | mem x hx => ...` (Mathlib idiom, Span/Defs.lean:164);
  (2) write the basis EXPLICITLY — `Basis.mem_span _ b` sticks on `Module ?m` typeclass;
  (3) case names mem/zero/add/smul; mem binds (x, h : x ∈ Set.range); add binds x y hx hy IHx IHy.
  Deletes both `p := fun x (_ : ...) => ...` motive blocks (~70 tokens, Lean builds the motive).
- Merging calc steps 1+2 (two-term sign expression never written down) is safe: the post-conv
  rw chain `rw [smul_comm, ← crAnTimeOrderSign_swap_eq_time hφψ hψφ, crAnTimeOrderList, e.1, h1,
  crAnTimeOrderList, e.2, h2]` only matches ψφ-sign / crAnTimeOrderList / insertionSort patterns,
  none of which occur in the 5-factor RHS.
- `module` tactic CANNOT close the merged step-1 equation (products of ι-atoms are not module
  terms; it fails with "ring expressions not equal ⊢ 1 = 0"), though it showed the conv simp-tail
  [smul_mul_assoc, mul_smul_comm, map_sub, map_smul, sub_right_inj] costs ~2.4k hb.
- hmid minimal form (simp?-derived, compiles, break-even 740/15646):
  `rw [superCommuteF_ofCrAnOpF_ofCrAnOpF, ← ofCrAnListF_singleton ×2];
   simp only [Algebra.smul_mul_assoc, map_sub, map_mul, map_smul, ← ofCrAnListF_append,
   List.cons_append, List.nil_append]`. Notes: plain `mul_smul_comm` does NOT fire (need
  Algebra.smul_mul_assoc for (𝓢 • x) * y); without cons/nil_append the final rfl fails on
  [φ]++[ψ] vs [φ,ψ] (rw-fl = instances transparency). Full `simp [← ofCrAnListF_append]` is equal.
- h1/h2 region ≈7k hb is INTRINSIC (using big insertionSort equations in rw): explicit membership
  rcases-terms, shared hgen, short stated types — all neutral or worse. LEAVE.
- Step 3 MUST stay rw-based (not simp only): simp zeta-expands the let-bound l/l'/r/r', breaking
  ← h3. `have e ... := by simp` full-simp is fine (~100s hb); its simp only replacement leaves
  `True ∧ True` (needs `; trivial`) — net loss. anon rcases pattern `| mem _ ⟨φs, rfl⟩` FAILS
  ("Alternative zero has not been provided") — keep obtain ⟨φs, rfl⟩ := hx.
- conv-one-simp (folding the conv rw-prelude into one simp only with ← ofCrAnListF_singleton +
  superCommuteF_ofCrAnListF_ofCrAnListF first) compiles: 734/15810 ≈ break-even.

## Architecture of candidate.lean (727 tok)
induction (Basis.mem_span ofCrAnListFBasis b) using span_induction; mem: obtain ⟨φs, rfl⟩;
inner induction on a; mem: obtain ⟨φs', rfl⟩; hmid; lets l/l'/r/r'; h1/h2 := insertionSort_of_eq_list
... (by simp [hφψ, hψφ]); h3 (regrouped); e; calc 2 steps: step1 via conv_lhs + rw chain + simp only
with hmid.symm; step2 via center rw-chain + rcases eq_or_ne (𝓕 |>ₛ φ) (𝓕 |>ₛ ψ) (koszulSign vs
ι_superCommuteF_of_diff_statistic). Closers: zero/add/smul via simp only with IH-rewrites.
Axis: tokens 727/1217 (40.3% red), hb 15805/42111 (62.5% red) → 67.58.

## Run 7 (2026-10-08): 67.58 → 69.47 (696 tok / 14488 hb), FINAL
Progression: 68.47 (merged e1+e2 into one `have e : ∀ χ η, ...`) → 68.53 (drop binder types
`∀ χ η,`) → 68.65 (fold conv's `rw [← ofCrAnListF_singleton ×2, superCommuteF_...]` prelude INTO
the conv `simp only`) → 68.75 (state h3 with `crAnTimeOrderList (φs' ++ φs)` LHS; then step-2
needs NO `← crAnTimeOrderList` fold) → 69.05 (replace interleaved rw
`[crAnTimeOrderList, e φ ψ, h1, crAnTimeOrderList, e ψ φ, h2]` by ONE
`simp only [crAnTimeOrderList, e, h1, h2]` — simp rewrites all instantiations at once,
rw only the first) → 69.23 (merge the two consecutive step-1 `simp only`s) → 69.37
(`e := fun χ η => by simp` term; full simp closes cons/append goal) → 69.47
(`by_cases hq : (𝓕 |>ₛ φ) = (𝓕 |>ₛ ψ)` instead of `rcases eq_or_ne ... with hq | hq`).

## Run-7 tested FAILURES (do not retry)
- `List.append_cons` (core: `as ++ b :: bs = as ++ [b] ++ bs`) used forward in the step-1 big
  simp only: MAX RECURSION loop (with h1/ofCrAnListF_append). Used backward (←): wrong direction
  for e's use. `have e ... := fun χ η => by simp` stays.
- h3 as ONE `simp only [crAnTimeOrderList, insertionSort_of_takeWhile_filter ..., l, l', r, r',
  List.append_assoc]`: MAX RECURSION (filter lemma re-fires on inner `φs' ++ φs`; rw applies
  once). Keep rw + simp only split.
- Folding `simp only [map_smul, mul_smul_comm]` after `timeOrderF_ofCrAnListF` into the rw list
  of step-2 branch 1: +263 hb for −3 tokens (rw with extra map lemmas is expensive). Net loss.
- hmid via single `simp only [superCommuteF..., ofCrAnListF_cons, ofCrAnListF_nil, map_sub,
  map_smul, map_mul, map_one, mul_one, smul_mul_assoc]`: compiles, 1416 hb vs 1450, but +6
  tokens → net loss. `simp [superCommuteF_ofCrAnOpF_ofCrAnOpF, ← ofCrAnListF_append]` (no
  singleton rws) FAILS: residual `ι (ofCrAnListF [φ,ψ]) - 𝓢 • ι (ofCrAnListF [ψ,φ]) =
  ι (ofCrAnOpF φ) * ι (ofCrAnOpF ψ) - ...` — full simp alone does NOT normalize
  `ofCrAnListF [a, b]` to `ofCrAnOpF a * ofCrAnOpF b` (needs the two `← ofCrAnListF_singleton`
  rws first, which is why current hmid works). Adding ofCrAnListF_cons hint: 14831 hb, worse.
- smul_comm inside the big step-1 simp only (with smul_mul_assoc/mul_smul_comm): MAX RECURSION.
  Keep `rw [smul_comm, ← crAnTimeOrderSign_swap_eq_time hφψ hψφ]` separate.
- `rfl` does NOT prove `φs' ++ φ :: ψ :: φs = φs' ++ [φ,ψ] ++ φs` (List.append not reducible
  here); `simp only [List.append_assoc, List.cons_append, List.nil_append]` does.

## Profile shape at 69.47
~1450 hmid (full simp), ~540 h1/h2 (`by simp [hφψ, hψφ]`), ~110 h3, step-1 conv+simp ~6.5k,
step-2 rw chain ~5k. Profile tool MIS-ATTRIBUTES the step-1 chain cost to the neighbouring
`have e` block (rw elaborates lazily; sorry-ing e truncates the chain). Don't trust its
block attribution when a later block uses the earlier one.
