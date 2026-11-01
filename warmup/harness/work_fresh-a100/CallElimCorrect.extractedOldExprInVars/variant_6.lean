open OldExpressions in
theorem extractedOldExprInVars :
  NormalizedOldExpr post →
  (extractOldExprVars post).Subset
  (Imperative.HasVarsPure.getVars post) := by
  intro Hnorm
  have app2 {a b c d : List Expression.Ident} (h1 : a ⊆ c) (h2 : b ⊆ d) : a ++ b ⊆ c ++ d :=
    List.Subset.app (List.subset_append_of_subset_left _ h1)
      (List.subset_append_of_subset_right _ h2)
  induction Hnorm with
  | const | bvar | op | fvar => exact List.nil_subset _
  | abs _ ih => assumption
  | quant _ _ ih1 ih2 | eq _ _ ih1 ih2 | ite _ _ _ ih1 ih2 ih3 =>
    first | exact app2 ih1 ih2 | exact app2 (app2 ih1 ih2) ih3
  | app _ _ h3 ih1 ih2 =>
    unfold extractOldExprVars
    split
    . intro x hx
      exact hx
    . next Hfalse =>
      exfalso
      cases h3 IsOldPred.oldPred
      exact Hfalse _ _ _ rfl
    . exact app2 ih1 ih2
