# Notes: Cslib.SKI.parallelReduction_diamond

## RESULT: best candidate score 68.70 (ref 33.33)
- 270 tokens (−33.7%), 392 heartbeats (−71.7%), compat 4/4.
- candidate.lean holds it (byte-identical, re-verified run 9).

## Architecture (stable, ~90 attempts)
intro a a₁ a₂ h₁ h₂; `have : Std.Refl _ := ⟨ParallelReduction.refl⟩`;
`induction h₁ generalizing a₂`; 5 nested blocks × `cases h₂`; cells use `‹_›`,
`rename_i`, `obtain … rfl`, `use` with explicit witnesses, apply-chains with
`<;> assumption`.

## NEW TESTED FACTS (run 9)
- [tested: drop `have : Std.Refl` -> FAILS exactly as notes said: "failed to
  synthesize Std.Refl (Join ParallelReduction)". The instance goal is
  Std.Refl (Join PR), derived from local Std.Refl PR via a Join-instance.]
- [tested: `have : Std.Refl _ := ⟨.refl⟩` -> FAILS: dotted `.refl` needs a
  constant-headed expected type; must write ParallelReduction.refl.]
- [tested: `exact this.refl _` instead of `apply Std.Refl.refl` -> FAILS: the
  have's type is Std.Refl ParallelReduction, its .refl : PR x x ≠ goal
  Join PR x x. `apply Std.Refl.refl` works only through instance synthesis of
  Std.Refl (Join PR). this.refl is unusable.]
- [tested: `exact Std.Refl.refl _` (3×) -> 273/395: WORSE than apply (more hb!).]
- [tested: par·par cell via `obtain ⟨_,hc⟩ := iha ha''; obtain ⟨_,hd⟩ := ihb hb''
  + .par hc.1 hd.1 ...` -> 275/386: −6 hb but +5 tokens; net −0.27. Token cost:
  `J.choose_spec.1` is ONE token, `⟨c, hc⟩` is 3 — projections win on tokens.]
- [tested: Ka cell `obtain ⟨a₂',h1,h2⟩ := ...; cases h2; use a₂',...` -> 272/398:
  worse than rfl-in-obtain (38 hb).]
- [tested: Sab cells `refine ⟨_, .par (.par h1 _) (.par h2 _), .red_S ..⟩` ->
  FAILS: `_` placeholders elaborated before `.red_S ..` fixes the target type
  ("don't know how to synthesize placeholder"); must use `?_`/apply-chain. With
  `?_` + `<;> assumption`: 283/394 — worse (tokens). Failed run still showed
  hb≈366, so a working term version would save ~26 hb but cost ≥6 tokens: net
  negative at current exchange rate.]
- [tested: `constructor <;> constructor <;> assumption` for Sab cells -> 408 hb:
  constructor on PR goals is expensive.]
- Heartbeat profile (392 total): par block 136 (cases h₂ 66, Ka cell 38,
  cases ha' 23), Sab block 92, red_I block 68, red_K block 66, induction 12,
  have 7. Floor estimate stands ~385.

## STANDING FACTS (earlier runs)
- `use _, ...` placeholder witness FAILS (not synthesizable).
- `induction` CONSUMES h₁ → `.par ha' hb'` reconstruction required in (par,refl).
- Generalized IHs are IMPLICIT: `iha : ∀ {a₂}, PR a a₂ → Join a₁ a₂`.
- Flattened `induction … <;> cases h₂` (15 flat cells) analyzed: per-cell
  rename_i overhead → nested wins. match h₁,h₂ double match: source equality not
  propagated → dead. Structural induction on SKI term: 25-cell cross-product.
- [UNVERIFIED per panel: "both axes at floor 268–270/385–392". Each of the 8
  micro-variants tried in run 9 lost; treat floor as likely but not proven.]
