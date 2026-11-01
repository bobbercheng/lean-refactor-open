# Cslib.CCS.bisimilarity_congr_choice — notes

## BEST: 110 tok / 387 hb / score 82.07 — restored in candidate.lean (term-header). Do not lean_check unchanged.
```
theorem ... := fun hpq => ⟨ChoiceBisim, .choice hpq, by
  rintro s1 s2 (h | h) μ
  · constructor <;> intro s htr <;>
      cases htr with
      | choiceL htr => first | exact h.follow_fst htr |>.imp fun a => And.imp Tr.choiceL ChoiceBisim.bisim | exact h.follow_snd htr |>.imp fun a => And.imp Tr.choiceL ChoiceBisim.bisim
      | choiceR htr => exact ⟨s, .choiceR htr, .bisim (.refl s)⟩
  · constructor
    · intro _ htr
      exact h.follow_fst htr |>.imp fun a => And.imp_right ChoiceBisim.bisim
    · intro _ htr
      exact h.follow_snd htr |>.imp fun a => And.imp_right ChoiceBisim.bisim⟩
```

## Tested THIS run (cycle 38)
- `[tested: all-first merge (all_goals constructor <;> intro s htr <;> first |cases htr...|fst|snd) -> 104 tok / 628 hb, compiles: net LOSE (~80.8). The extra `cases`+`follow_fst` type-mismatch failures in case2 cost ~240 hb. Note: after `rintro ... (h|h)` producing 2 goals, a plain un-bulleted tactic only hits the FIRST goal — needed `all_goals`.]`
- `[tested: case2 closed by raw anonymous-constructor term ⟨fun _ htr => ..., fun _ htr => ...⟩ -> 111 tok / 391 hb: LOSE by 1 tok/4 hb.]`
- `[tested: dropping `fun a =>` around `And.imp_right ChoiceBisim.bisim` in case2 (no `first` there) -> FAILS: Exists.imp needs ∀ a, p a → q a; the lambda is load-bearing everywhere (again).]`
- `[tested: `rintro (h|h) μ` (dropping s1 s2) -> MISBINDS: pattern applies to s1, μ becomes a Process. rintro patterns alternate; must keep `rintro s1 s2 (h|h) μ`.]`
- `[tested: witness HomBisimilarity/Bisimilarity instead of ChoiceBisim + `Bisimilarity.isBisimulation lts lts` -> membership goal `(choice p r) ~ (choice q r)` from hpq is NOT free (it is the theorem's content); dead end.]`
- `[checked: NO Tr inversion lemmas (`*_inv`) anywhere in Cslib/Languages/CCS; grind cannot invert `lts.Tr (choice ..) μ ..` (tested grind with [Tr.choiceL, Tr.choiceR, follow_fst, follow_snd, ChoiceBisim.*] and forward hints -> fails, hb 900-1900).]`
- `[found: `Bisimilarity.isBisimulation (lts₁) (lts₂) : IsBisimulation lts₁ lts₂ (Bisimilarity lts₁ lts₂)` EXISTS in Foundations/Semantics/LTS/Bisimulation.lean; also IsBisimulation.follow_fst/snd, IsBisimulationUpTo.isBisimulation, Bisimilarity.symm. None shorten this proof.]`
- Process-level `Tr` (Semantics.lean:37) has 9 constructors (pre parL parR com choiceL choiceR res const); `cases htr` in a choice-goal inverts to choiceL/choiceR only, so term-level `htr.elim` impossible; in the `.bisim` case the goal's Tr is `lts.Tr` on raw processes (different type — that's why `cases htr` there errors with pre/parL/... alternatives).

## Established facts (verified earlier)
- h : Bisimilarity has .follow_fst/.follow_snd returning ∃ s', Tr … ∧ Bisimilarity.
- And.imp_right : (a→b) → c∧a → c∧b; exists. Exists.imp_right does NOT exist (v4.31-4.33).
- ChoiceBisim private inductive: .choice (p~q → ChoiceBisim (choice p r) (choice q r)), .bisim (p~q → ChoiceBisim p q).
- No Tr choice-inversion lemma; grind closers dead end (confirmed twice).
- Axes: points_per_token 0.1328, per-1k-hb 8.593, 1 tok ≈ 15.5 hb. At 110/387: ~14.6 pts left on tokens, ~3.0 on hb.
- `cases ... with` alternative bodies must be TACTICS (`exact` needed), not bare terms.

## Verdict
Base is at a strong local optimum. All restructuring families tested (merge-all with all_goals, term-closers, eta-removal, witness swap, grind, rintro-shortening) lose or fail. Remaining ideas: none obvious; a real win likely needs a new library lemma or an IsBisimulationUpTo route (measured shape: witness `fun a b => (∃ p q r0, a = choice p r0 ∧ b = choice q r0 ∧ p ~ q) ∨ a ~ b` — membership cheap but the up-to proof is not shorter).
