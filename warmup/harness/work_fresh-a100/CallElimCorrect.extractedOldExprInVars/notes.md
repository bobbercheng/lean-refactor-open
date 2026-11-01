# Notes (yours to keep; persisted across runs)

## Problem: CallElimCorrect.extractedOldExprInVars (strata, v4.26.0)
BEST (score 78.19, 106 tok / 477 hb vs ref 222 / 2696) — in candidate.lean:
- intro Hnorm; induction Hnorm
- app case: `unfold extractOldExprVars; split` (unfold REQUIRED for split to see the match;
  `simp only [extractOldExprVars]` does NOT unfold, split then fails), 3 bullets:
  `. apply List.Subset.refl` (then-goal [v].Subset [v] DEFEQ; apply beats exact _ : 477 vs 484 hb)
  `. rename_i Hfalse; cases h3 IsOldPred.oldPred; cases Hfalse _ _ _ rfl`
  `. exact List.append_subset.mpr ⟨left ih1, right ih2⟩` (mpr form; app form fails to parse
   in a `. ` bullet, see trap below)
- `case quant _ _ ih1 ih2 | eq _ _ ih1 ih2 => exact List.Subset.app
  (List.subset_append_of_subset_left _ ih1) (List.subset_append_of_subset_right _ ih2)`
  (file-local List.Subset.app a⊆c→b⊆c→(a++b)⊆c with c := whole RHS; hb-cheaper than mpr ⟨⟩, +1 tok)
- ite: nested append_subset.mpr (app form = -0.1 net)
- closer: `all_goals first | apply List.nil_subset | assumption`

## [tested this run — do not retry]
- CORRECT SIMP NAMES: `Lambda.LExpr.LExpr.getVars` (double LExpr!) and
  `Imperative.HasVarsPure.getVars` DO unfold under simp/simp_all. But simp_all still can't
  finish: after `simp only [List.Subset, List.mem_append] at ih1 ih2 ⊢` goal becomes
  `∀ ⦃a⦄, a ∈ A ∨ a ∈ B → a ∈ C ∨ a ∈ D` and simp_all won't apply Or.imp ih1 ih2; explicit
  `fun _ h => h.imp ih1 ih2` works but costs more tokens than Subset.app term. Dead end.
- simp_all with subset_append_of_subset_{left,right} as simp lemmas: fails (no rewrite).
- Merged `case quant|eq|ite` tag + `first` of the two terms: 542 hb (failed-branch elaboration
  on ite) → 77.09. Worse.
- `have app := @List.Subset.app` alias: worse (76.82). app2/mono helper: worse (re-measured).
- grind everywhere: getVars projection unfolds to trivial eq under grind hints; fails.
- `exact absurd (Hfalse ...) (by simp)` in h_2: worse.
- ite full Subset.app form: 461 hb but +2 tok → 78.09.
- Folded closer (append terms inside all_goals `first`): IH names not accessible. Fails.
- PARSE TRAP: inside a `. ` bullet, a continuation line starting with `(` → "unknown tactic".
  Under `case ... =>` blocks it's fine. Workaround: single line or mpr ⟨⟩ form.

## [older runs] FAILED — do not retry
- next Hfalse vs rename_i: no gain. `exact (Hfalse _ _ _ rfl).elim`: worse.
- `exact fun x hx => hx` in then-branch: worse than intro/exact-hx (refl now best).
- No 4-arg append-mono lemma in core v4.26; List.append_subset iff has SAME l on both sides,
  so subset_append_of_subset_{left,right} wrappers are forced.
- IsOldPred: single-constructor (oldPred : IsOldPred (.op m (unres "old") ty)).
- extractOldExprVars def (OldExpressions.lean:164): leaves → [], abs → rec, quant/eq → rec ++,
  app → match e1,e2: old/fvar → [v], old/_ → panic!, else rec ++ rec; ite → 3-way ++.
- Axis at 78.19: tokens 106/222 (52% red), hb 477/2696 (82% red). 1 tok ≈ 12 hb.
  Profile (477hb): app case 202 (split 81, mpr-bullet 37, h_2 34, unfold 19, refl 14),
  quant/eq 102, ite 99, closer 35, induction 24. points_left_hb 5.7.
