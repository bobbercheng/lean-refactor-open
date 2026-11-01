open OldExpressions in
theorem extractedOldExprInVars :
  NormalizedOldExpr post →
  (extractOldExprVars post).Subset
  (Imperative.HasVarsPure.getVars post) := by
  intro Hnorm
  induction Hnorm
  case app _ _ h3 ih1 ih2 =>
    unfold extractOldExprVars
    split
    . apply List.Subset.refl
    . rename_i Hfalse
      cases h3 IsOldPred.oldPred
      cases Hfalse _ _ _ rfl
    . exact List.append_subset.mpr ⟨List.subset_append_of_subset_left _ ih1,
      List.subset_append_of_subset_right _ ih2⟩
  case quant _ _ ih1 ih2 | eq _ _ ih1 ih2 | ite _ _ _ ih1 ih2 ih3 =>
    simp_all [extractOldExprVars, Imperative.HasVarsPure.getVars,
      Lambda.LExpr.LExpr.getVars, List.subset_append_of_subset_left,
      List.subset_append_of_subset_right]
