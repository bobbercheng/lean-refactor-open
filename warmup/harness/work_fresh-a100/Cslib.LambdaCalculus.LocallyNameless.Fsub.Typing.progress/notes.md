# notes.md — Cslib.LambdaCalculus.LocallyNameless.Fsub.Typing.progress

## Problem
`lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t'` (Fsub/Safety.lean).
Reference: 408 tok / 59830 hb. Toolchains v4.33.0-rc2, v4.32.0, v4.31.0. No upstream simplification (git verified).
Score = mean(tok_red%, hb_red%, compat%). Exchange rates: 1 token ≈ 0.082 pts; 1000 hb ≈ 0.56 pts.

## CURRENT BEST (in candidate.lean): 85.07 — 136 tokens, 6860 hb  (prior 85.05 = 135/7046)

## Current best proof, verbatim
```lean
lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  generalize eq : [] = Γ at der
  have der' := der
  induction der <;> subst eq
  case app l r ih_l ih_r =>
    obtain val_l | ⟨_, h⟩ := ih_l rfl l
    · grind only [→ canonical_form_abs, → Red.abs, → Red.appᵣ]
    · grind [→ Red.appₗ]
  case let' => grind only [→ Red.let_bind, → Red.let_body, body_let.mp der'.wf.2.1]
  case case der _ _ ih _ _ =>
    obtain val | ⟨_, h⟩ := ih rfl der
    · grind only [→ canonical_form_sum, → Red.case_inl, → Red.case_inr, body_case.mp der'.wf.2.1]
    · grind [→ Red.case, body_case.mp der'.wf.2.1]
  all_goals grind [→ Red.inl, → Red.inr, → Red.tabs, → Red.tapp, → canonical_form_tabs]
```
(Win this run: in `case case`, dropped `have hb := body_case.mp der'.wf.2.1` and passed the term
`body_case.mp der'.wf.2.1` inline as a grind hint in BOTH branches: 135/7046 → 136/6860, +0.02.)

## Confirmed signatures (lean_run #check, this run)
- `Red.abs : (Term.abs σ t₁).LC → t₂.Value → (Term.abs σ t₁).app t₂ ⭢βᵛ t₁ ^ᵗᵗ t₂` — NOTE: 2nd arg is the ARGUMENT's Value (val_r), not the lambda's!
- `Red.appₗ : t₂.LC → t₁ ⭢βᵛ t₁' → t₁.app t₂ ⭢βᵛ t₁'.app t₂` (t₂ = right arg; needs r.LC = r.wf.2.1? actually r.wf.2.1 worked)
- `Red.appᵣ : t₁.Value → t₂ ⭢βᵛ t₂' → t₁.app t₂ ⭢βᵛ t₁.app t₂'`
- `Red.case_inl : t₁.Value → t₂.body → t₃.body → t₁.inl.case t₂ t₃ ⭢βᵛ t₂ ^ᵗᵗ t1`; case_inr symmetric
- `Red.let_body : t₁.Value → t₂.body → t₁.let' t₂ ⭢βᵛ t₂ ^ᵗᵗ t₁`; `Red.let_bind : t₁ ⭢ t₁' → t₂.body → ...`
- `Red.inl/inr : t₁ ⭢ t₁' → t₁.inl/inr ⭢ t₁'.inl/inr`
- `Red.tabs : (tabs σ t₁).LC → τ.LC → (tabs σ t₁).tapp τ ⭢βᵛ t₁ ^ᵗᵞ τ`; `Red.tapp : σ.LC → t₁ ⭢ t₁' → ...`
- `canonical_form_abs : t.Value → Typing [] t (σ.arrow τ) → ∃ δ t', t = abs δ t'` — dot notation `der.canonical_form_tabs val` = `canonical_form_tabs val der` (der goes into the Typing slot via head matching). Argument order: Value first, Typing second.
- For `case tapp σ' der sub ih`: der : Typing [] t₁ (all…), sub : Sub [] σ' σ; `canonical_form_tabs val der`, then `Red.tabs der.wf.2.1 sub.wf.2.1.lc` [tested: tapp-explicit8 → compiles, 217 tok / 4540 hb]
- For `case app t₁ σ _ t₂ l r ih_l ih_r`: l : Typing [] t₁ (arrow…), r : Typing [] t₂ σ [tested: tapp-explicit8 app block compiles]

## Negative results (all tested this run unless noted)
- [tested: case-one-grind `grind [→ canonical_form_sum, → Red.case_inl, → Red.case_inr, → Red.case]` without pre-splitting the IH → FAIL, 21297 hb; grind cannot case IHs internally — must `obtain val | ⟨_,h⟩ := ih rfl der` first. Confirms prior V3 note.]
- [tested: app-one-grind `case app => grind [→ canonical_form_abs, → Red.abs, → Red.appᵣ, → Red.appₗ]` without obtains → FAIL 40051 hb (same reason).]
- [tested: `case tapp => grind` (default, no hints) → FAIL; tapp needs Red.tabs/Red.tapp/canonical_form_tabs hints.]
- [tested: explicit tapp + explicit app cases, all_goals `grind [→ Red.inl, → Red.inr]` → compiles 217 tok / 4540 hb but score 79.74: explicit terms cost far more tokens than hb saved. Not worth.]
- [tested: `case var | sub => grind` + `all_goals grind only [→ wf, cases Value, → Red.inl, → Red.inr, → Red.tabs, → Red.tapp, → canonical_form_tabs]` (and without cases Value) → FAIL ×4 at abs case: only-mode gets `wf` as a raw conjunction fact `(Typing … → Env.Wf) ∧ (→ t.LC) ∧ (→ Wf τ)` but never projects `(abs σ t₁).LC` from it, so it can't build `Value.abs`. Does NOT respond to adding `→ wf`. Possible fix: add a hint that IS the projection, e.g. a hint term like `fun h => (wf h).2.1`? or `Term.wf` differently shaped, or handle `case abs | tabs` reference-style (`left; constructor; grind only [→ wf, cases Term.LC]; grind only [→ wf]` — the reference proves this exact subgoal, so it works) and leave var|sub|tapp|inl|inr in a only-mode all_goals. This is THE most promising next idea: only-mode measured ~3100 hb total vs 4748 for the default all_goals grind.]
- [tested: `case var => grind` prefix before only-mode all_goals → same abs failure (not a var problem).]
- Explicit `Red.appₗ r.wf.2.1 h` term for app red branch: compiles [tested: app+case-red-explicit → 144/6145, score 84.81 < best: token cost not worth it]. Explicit `Red.case h hb.2.1 hb.2.2` for case red: compiles but 140/6397, no gain.
- let' explicit branch terms (`Red.let_body val hb.2` etc.) with full tag `case let' t₁ σ t₂ τ L der _ ih _`: compiles [tested: let'+case-red-explicit → 174/6229, 82.32]. Not worth.

## Older still-valid notes
- `cases Term.LC` as a grind hint is INVALID in most spots ("failed to find a usable pattern") but the reference uses it successfully in `case abs`/`case tabs` after `left; constructor; apply LC.abs L`.
- `case abs | tabs` closed with only-mode `grind only [→ wf, cases Term.LC]` alone FAILED before (V4) — abs/tabs need the default pool there; reference-style `left; constructor` + two grind only calls is the known-good shape.
- Hint terms (`body_let.mp der'.wf.2.1`) are cheaper than letting default-pool grind derive things (measured: dropping the hint in let' cost +1273 hb for -4 tok).
- Red constructors are not auto-found by default grind; `→ Red.inl, → Red.inr` hints ARE needed in the final all_goals (bare `all_goals grind` fails at case red — old note F).
- Floor hb ≈ 50. Profile of 135/7046 version: all_goals 4748, case 1244, app 598, let' 224, induction 173, generalize 7, have 2.

## Next ideas (ranked)
1. Split final closer: `case abs | tabs => left; constructor; <reference-style grind only>` then `all_goals grind only [→ Red.inl, → Red.inr, → Red.tabs, → Red.tapp, → canonical_form_tabs, cases Value]` for var|sub|inl|inr|tapp (var needs default pool? [tested: only-mode with var included FAILS on var — var needs dlookup facts from the default pool; so keep `case var | sub => grind` or var+sub default]). Token cost ~+8, hb save potentially ~1500 → worth ~+0.7 pts.
2. Shave the `case case der _ _ ih _ _` tag or other binder lists (untested whether fewer `_` bind correctly).
3. Try `Term.wf`/`wf` projection hint term inside only-mode all_goals for abs/tabs instead of splitting cases.
