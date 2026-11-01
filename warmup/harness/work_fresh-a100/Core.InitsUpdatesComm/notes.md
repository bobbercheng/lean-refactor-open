# Problem Core.InitsUpdatesComm (Strata/Languages/Core/StatementSemanticsProps.lean)

## FINAL RESULT (this run)
- ref: 224 tokens / 4251 hb → 33.33
- **best: 99 tokens / 208 hb → 83.66**, banked in candidate.lean
  (gain over previous best 104/213/82.87 came from replacing
  `absurd h (by simp [g])` with `Bool.noConfusion (g ▸ h)`: −5 tok, −5 hb)
- Marginal rates: 1 token ≈ +0.15 pts; 1 hb ≈ +0.008 pts (19 hb ≈ 1 token).
- hb floor (sorry body) = 33 hb. Profile of best: outer `simp only` w/ inlined
  comm = 103 hb, refine w/ updatedStatesInit = 66 hb, final exact = 5 hb.
  Length headroom dominant; est. remaining potential ≈ 2–3 pts (floor ~88 tok / 33 hb).

## CURRENT BEST PROOF (VERIFIED 83.66, banked in candidate.lean)
```
  intro Hup Hinit
  refine ⟨_, rfl, updatedStatesInit (InitStatesLength Hinit)
    (UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup)
    (InitStatesNodup Hinit), ?_⟩
  simp only [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, updatedStates,
    updatedStatesComm (kvs := ks.zip vs) (kvs' := ks'.zip vs') (by
      simp [List.unzip_zip, UpdateStatesLength Hup, InitStatesLength Hinit]
      exact fun a Ha Hb =>
        Bool.noConfusion (InitStatesNotDefined Hinit a Hb ▸
          UpdateStatesDefined Hup a Ha))]
  exact updatedStatesUpdate (UpdateStatesLength Hup)
    (updatedStatesDefMonotone (UpdateStatesDefined' Hup))
```

## KEY TYPES (read from source, verified)
- `UpdateStatesDefined Hup a Ha : (σ' a).isSome = true` (result store!).
- `UpdateStatesDefined' Hup a Ha : isDefined σ a` (source store).
- `InitStatesNotDefined Hinit a Hb : σ' a = none`.
- `UpdateStatesLength Hup : ks.length = vs.length` (an EQUALITY, not ≤).
- `List.unzip_zip : l₁.length = l₂.length → (l₁.zip l₂).unzip = (l₁, l₂)`.
- `InitStatesNotDefined Hinit : isNotDefined σ' ks'` where σ' is the SOURCE of
  the InitStates (i.e. the RESULT of Hup's updates); contradiction with
  UpdateStatesDefined is direct, no store rewriting needed.
- `updatedStatesComm` is stated at `updatedStates'` level:
  `kvs.unzip.1.Disjoint kvs'.unzip.1 → updatedStates' (updatedStates' σ kvs) kvs' = …`.
  `updatedStates σ ks vs` DEFEQ-unfolds to `updatedStates' σ (ks.zip vs)` — that's
  why the final `exact` works but simp patterns (keyed on head `updatedStates'`)
  can't use `updatedStatesUpdate` as a simp lemma.

## NAMES CONFIRMED EXIST (this run, lean_run #check)
- `Nat.le_of_eq : n = m → n ≤ m`.  NOTE: bare `le_of_eq` does NOT exist;
  `h.le` (Eq.le projection) does NOT exist [tested: #check → unknown/invalid field].

## MEASURED THIS RUN [tested: lean_check_variants]
- `Bool.noConfusion (g ▸ h)` closure: 99 tok / 208 hb → 83.66 NEW BEST (banked).
- `nomatch (g ▸ h)` closure: 99 tok / 214 hb → 83.61 (nomatch elaborates dearer).
- inner `simp only [...]` instead of `simp [...]`: 100 tok / 207 hb → 83.51
  (−1 hb, +1 tok: net loss; token axis dominates).
- pure-term transport instead of inner simp (both ▸-casts of the lambda):
  105 tok / **194 hb** → 82.87. Works! (−14 hb, +6 tok, net −0.8). If a shorter
  transport exists (< 3 extra tokens) it would WIN. Transport used:
  `(List.unzip_zip (UpdateStatesLength Hup)).symm ▸ (List.unzip_zip
  (InitStatesLength Hinit)).symm ▸ fun a Ha Hb => …` (pair projections are
  defeq to ks/ks', so the lambda's memberships typecheck after the cast).
- single `.trans` of the two symm casts: FAILS — Eq.trans arg order mismatch
  [tested: pure-term-transport-trans → type mismatch at col 60].
- inner closure by `rw [List.unzip_zip (UpdateStatesLength Hup), …]` (both named
  args): compiles, 103 tok / 234 hb → 82.86. Worse.
- `updatedStatesComm` with ONLY `(kvs := ks.zip vs)` (no kvs'): FAILS — the
  ?kvs' mvar unifies with `(ks, vs)`-garbage; rw then can't find pattern
  [tested: single-named-rw → rewrite failed, goal (ks,vs).fst.Disjoint (ks,vs).fst].
  BOTH named args `(kvs := …) (kvs' := …)` are REQUIRED.
- direct contradiction applications FAIL: `InitStatesNotDefined Hinit a Hb` is
  `σ' a = none` (not a function), and `UpdateStatesDefined Hup a Ha` is
  `(σ' a).isSome = true` (not a function) [tested: direct-app, neg-app → error].
- absurd with swapped/negated sides: FAILS [tested: absurd-swapped → simp made
  no progress; absurd-rw → unsolved ¬none.isSome = true (rw alone doesn't close;
  would need Option.isSome_none then false_ne_true)].

## DEAD ENDS (from this + earlier runs)
- Absorbing the final `exact updatedStatesUpdate …` into the simp only: IMPOSSIBLE —
  after `updatedStates` unfolding the goal's store heads are `updatedStates'`, while
  `updatedStatesUpdate`'s RHS pattern has head `updatedStates`; simp matching is
  syntactic, the exact exploits defeq [analysis of StatementSemantics.lean defs].
- Full absorption of the InitStates conjunct into simp: blocked by the same
  unfold/no-unfold conflict (InitStates goal needs `updatedStates` UNfolded to
  match `updatedStatesInit`; UpdateStates goal needs it FOLDED for comm).
- Names that do NOT exist: `le_of_eq`, `List.unzip_left`, `List.mem_unzip_left`,
  `List.mem_zip_left`, `List.mem_of_mem_unzip_left`, `List.mem_unzip`, `List.mem_zip`.
- Upstream has NO simplification of this proof (checked git history).

## NEXT IDEAS (most promising first)
1. Shorter ▸-transport for the disjoint term (the 194-hb variant is proven to
   compile; it only needs ~3 fewer tokens to win). Look for a lemma
   `(l₁.zip l₂).unzip.fst = l₁` with a cheaper side condition than the two
   `List.unzip_zip` casts — e.g. `List.unzip_zip_left` exists (takes ≤; combine
   with `Nat.le_of_eq`, likely same length) or some `List.fst_zip`/subset lemma;
   also try a single `congrArg`/`Prod.fst`-based cast.
2. Shave the refine block (66 hb, 23 tok): try explicit witness
   `refine ⟨updatedStates σ ks' vs', rfl, …⟩` (+2 tok, maybe −10 hb — likely net
   loss, only if combined with idea 1).
3. The exact line (13 tok): nothing found; `updatedStatesDefMonotone
   (updatedStatesDefined (UpdateStatesLength Hup))` alternative is longer.
4. Outer simp list seems minimal (3 lemma names + comm, all needed).
