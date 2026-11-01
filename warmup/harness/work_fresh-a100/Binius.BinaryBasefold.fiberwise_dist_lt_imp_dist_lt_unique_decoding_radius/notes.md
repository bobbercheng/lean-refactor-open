# Problem: fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius (Binius.BinaryBasefold.Prelude)

## Current best (candidate.lean): score 74.76, tokens 657 (ref 1463), heartbeats 4934 (ref 15645), compiles 4/4.

## Big wins this run
- **Fib as plain Finset.image**: `qMap_total_fiber 𝔽q β ⟨i, by omega⟩ steps (fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y` is itself a function `Fin (2^steps) → sDomain`, so the fiber = `Finset.image f (Finset.univ : Finset (Fin (2^steps)))` — NO Set.toFinset layer. Killed the whole card_qMap_total_fiber block: per-fiber bound is just `Finset.card_image_le.trans (le_of_eq (Finset.card_univ.trans (Fintype.card_fin _)))` (note: card_univ takes NO argument; card_fin needs `.le` under rw, or le_of_eq chain).
- `Finset.card_image_le` unifies against `(Fib y).card` (let-fvar zeta unfolds under `exact`), but NOT under `simp only [Fib]` (stuck DecidableEq metas) and NOT when RHS is `2^steps` (needs the card_univ/card_fin chain — Fintype.card (Fin n) is NOT defeq to n).
- `(0 : C_i)` replaces the long BBF_Code ascription in the sInf block (`Set.mem_univ (0 : C_i)`) — works, ~-25 tokens.
- `Nat.succ_pos _` inlined into final `Nat.lt_of_le_pred` (h_d_i_gt_0 was used once).
- qMap_total_fiber 4th positional arg is `i.val + steps < ℓ + 𝓡` (NOT ≤ ℓ); `fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps` fits directly (also cheaper than `by apply Nat.lt_add_of_pos_right_of_le; omega`).
- pointToIterateQuotientIndex CANNOT take positional/semi-positional args (section vars become 6 leading @-slots; `(i := ⟨i, by omega⟩) steps h x` fails). is_fiber_iff also keeps `(by omega)` form. [tested twice]
- `exact_mod_cast h_fw_dist_lt` fails for h_fw_bound (mod_cast doesn't bridge `2*d < BBF_CodeDistance` to `2*d_fw ≤ d-1`); keep `Nat.le_of_lt_succ (ENat.coe_lt_coe.mp h_fw_dist_lt)`.
- Yfin let (hoisting Y_bad.toFinset) : no hb gain. h_fin restructure (have + exact instead of change+rw): -96 hb but +11 tokens, net negative.
- lean_profile can't profile files with sorry; blocks after the first expensive one get nested under it (hFinType_Y_bad swallows the whole tail ~3600 hb) — hb localization is hard here; remaining hb is mostly statement-driven (fw_bound ~1159, algebraic, lets).
- omega for h1/h2 would save ~28 tokens but ~+1600 hb → net negative (exchange 1 token ≈ 11 hb).
