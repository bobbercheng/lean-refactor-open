open OldExpressions in
example :
  NormalizedOldExpr post →
  (extractOldExprVars post).Subset
  (Imperative.HasVarsPure.getVars post) := by
  intros Hnorm
  induction Hnorm with
  | const | bvar | op | fvar => intro x hx; cases hx
  | abs _ ih => exact ih
  | quant _ _ ih1 ih2 => exact List.Subset.app ih1 ih2
  | ite _ _ _ ih1 ih2 ih3 => exact List.Subset.app (List.Subset.app ih1 ih2) ih3
  | eq _ _ ih1 ih2 => exact List.Subset.app ih1 ih2
  | app _ _ h3 ih1 ih2 =>
    unfold extractOldExprVars
    split
    . intro x hx; exact hx
    . next Hfalse =>
      exfalso
      cases h3 IsOldPred.oldPred
      exact Hfalse _ _ _ rfl
    . exact List.Subset.app ih1 ih2
