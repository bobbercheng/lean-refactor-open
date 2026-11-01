open OldExpressions in
theorem substOldPostSubset:
  (Imperative.HasVarsPure.getVars (P:=Expression)
    (substOld h2 (Lambda.LExpr.fvar m h1 ty) post)).Subset
    (Imperative.HasVarsPure.getVars (P:=Expression) post ++ [h1]) := by
  intro x
  simp only [Imperative.HasVarsPure.getVars, List.mem_append]
  induction post
  all_goals dsimp only [substOld, Lambda.LExpr.LExpr.getVars]
  all_goals repeat' split
  all_goals (first | dsimp only [Lambda.LExpr.LExpr.getVars] | skip)
  all_goals (first | simp only [List.mem_append] | skip)
  all_goals grind only
