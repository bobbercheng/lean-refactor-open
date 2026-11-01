# CallElimCorrect.substOldPastSubset — notes

## Problem
`getVars (substOld h2 (fvar m h1 ty) post) ⊆ getVars post ++ [h1]`, `P:=Expression`.
Reference: 313 tokens, 5175 hb. Toolchain: v4.26.0 only.

## SCORE MODEL (confirmed this run by matching reported scores)
score = mean(length_reduction%, heartbeat_reduction%, compatibility%).
Each token ≈ 0.32 pts; each 100 hb ≈ 0.64 pts. So hb cuts pay ~2× tokens.

## BEST (score 85.91 — 32 tokens, 1658 hb) — in candidate.lean
```lean
  intro x
  simp only [Imperative.HasVarsPure.getVars, List.mem_append]
  induction post
  all_goals dsimp only [substOld]
  all_goals repeat' split
  all_goals simp only [Lambda.LExpr.LExpr.getVars, List.mem_append]
  all_goals grind only
```

## This run's results (all lean_check_variants, single checks)
- merge-1 (`all_goals (dsimp only [substOld]; repeat' split)`): 34 tok / 1658 hb, score 85.7 (−0.21). Merging all_goals lines saves hb not at all.
- closer-append (`grind only [List.mem_append]` replacing final simp+grind): 33 tok / **3268 hb** — mem_append as a grind hint is very expensive. FAIL direction.
- dsimp-skip-2nd (2nd pass = `first | dsimp only [LExpr.getVars] | skip`): 976 hb before failing `simp only [LExpr.getVars, mem_append]` made no progress (line 12).
- skip2-skip3 (both later passes wrapped in first|…|skip): OK 50 tok / 1786 hb, 83.17.
- dsimp1-both (first dsimp unfolds BOTH substOld AND LExpr.getVars: `all_goals dsimp only [substOld, Lambda.LExpr.LExpr.getVars]`, then split, then 2nd dsimp+skip): **918 hb** before failing `simp only [List.mem_append]` no-progress. THE most promising structure.
- Variant A (dsimp1-both + `(first | simp only [List.mem_append] | skip)` + grind only): OK 50 tok / 1819 hb, 82.96.
- Variant B (… + `grind only [List.mem_append]` instead of the simp): 41 tok / 3019 hb, 76.18. mem_append in grind = expensive, confirmed twice.
- Variant C (`simp only [← List.mem_append, List.mem_append]`): FAIL no-progress (3rd identical failure — stop retrying simp variants at line 12).
- first-dsimp-or-simp (`first | dsimp | simp only [getVars, mem_append]` as 2nd pass): FAIL grind on quant case — hypotheses show `x ∈ getVars trigger ++ getVars e` unsplit; needs mem_append simp fired there.

## KEY UNRESOLVED BLOCKER
dsimp1-both reaches ~918 hb but the final `simp only [List.mem_append]` makes no
progress in SOME goal while being needed in OTHERS (quant case shows unsplit
`x ∈ getVars trigger ++ getVars e`). A uniform closer that (a) fires mem_append
where needed, (b) doesn't fail elsewhere, (c) doesn't cost 1000+ hb — that is the
win. With hb≈950 and ≤40 tok the score would be ≈90.
Next ideas:
1. Find WHICH goal gives no-progress: run the dsimp1-both prefix with
   `all_goals (first | simp only [List.mem_append] | trace "NOPROG"; trace_state; skip)`
   in lean_run (example must use the real section vars; a hand-rolled example with
   `(Expression : Imperative.PureExpr)` mistyped fails — copy statement from
   original.lean verbatim or use `theorem` in scratch). Then target that goal only,
   e.g. `case`-free: swap order — do mem_append simp BEFORE the 2nd dsimp.
2. Try `all_goals (simp only [List.mem_append] <;> all_goals grind only)` — no.
3. Try `all_goals (first | simp only [List.mem_append] | grind only)` — closer per goal, no separate grind line; may cut tokens (drop `all_goals grind only` line) AND hb.
4. Order swap: `all_goals (dsimp only [substOld, LExpr.getVars]; repeat' split; first | dsimp only [LExpr.getVars] | skip; first | simp only [List.mem_append] | skip)` all in ONE all_goals line → fewer tokens (drop 4 `all_goals` ≈ 8 tok? each `all_goals` is 1 tok + `;`...). Test.

## DURABLE TACTIC INSIGHTS
- `intro x` (NOT hx) BEFORE induction; fixed-x IH implications used cheaply by `grind only`.
- hx-fixed-before-induction architecture FAILS systematically (8 variants, notes from earlier runs).
- `dsimp only [substOld]` beats `simp only [substOld]` (228 vs 471 hb).
- Only `split` can case the app `match … if x = h2 …`; needs a getVars-unfolding pass AFTER split.
- `grind only` (bare) as closer is the cheap winner; `grind only [List.mem_append]` is 2× hb (3268/3019 measured twice this run).
- Case tags `case app` NOT available after this induction shape (earlier run).
- `repeat'` swallows the rest of a `<;>` chain; parenthesize `(repeat' split)`.
- `repeat split` ≈ same hb as `repeat' split` (1661 vs 1658) — no gain.

## Verified existing lemmas (used/available)
`Imperative.HasVarsPure.getVars`, `Lambda.LExpr.LExpr.getVars`, `List.mem_append`, `List.Subset.app`, `List.Subset.trans` (same file), `substOld` (OldExpressions.lean:179).
