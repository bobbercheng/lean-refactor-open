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
    . intro x hx
      exact hx
    . rename_i Hfalse
      cases h3 IsOldPred.oldPred
      cases Hfalse _ _ _ rfl
    . exact List.append_subset.mpr ⟨List.subset_append_of_subset_left _ ih1,
      List.subset_append_of_subset_right _ ih2⟩
  case quant _ _ ih1 ih2 | eq _ _ ih1 ih2 | ite _ _ _ ih1 ih2 ih3 =>
    intro x hx
    obtain h | h := List.mem_append.mp hx
    · exact List.mem_append.mpr (Or.inl (ih1 h))
    · exact List.mem_append.mpr (Or.inr (ih2 h))
