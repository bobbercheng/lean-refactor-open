open OldExpressions in
theorem substOldPostSubset:
  (Imperative.HasVarsPure.getVars (P:=Expression)
    (substOld h2 (Lambda.LExpr.fvar m h1 ty) post)).Subset
    (Imperative.HasVarsPure.getVars (P:=Expression) post ++ [h1]) := by
  intro x
  simp only [Imperative.HasVarsPure.getVars]
  induction post
  all_goals dsimp only [substOld]
  all_goals repeat' split
  all_goals simp only [Lambda.LExpr.LExpr.getVars, List.mem_append]
  all_goals grind only [List.mem_append]
