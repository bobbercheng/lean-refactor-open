# putnam_1964_b2 notes

## Status (run fresh-a100-p6)
- Best score **95.52** (tokens 224, heartbeats 918, image-multwo) — candidate.lean holds it.
- This run's wins:
  - `Finset.card_map _, Nat.mul_comm, Nat.two_mul` → `Finset.card_map _, Nat.mul_two`
    (`Nat.mul_two : n * 2 = n + n`, goal after card_map is `P.card * 2 = P.card + P.card`,
    one rw closes it) — −2 tokens, ~−20 hb. [tested: multwo variant -> ok, 95.33]
  - map→image: `P.image compl` + `Finset.mem_image.mpr ⟨Aᶜ, hA, compl_compl A⟩` +
    `Finset.card_image_of_injective P compl_injective` — −11 tokens but +99 hb
    (image elaboration costlier than embedding map). Net score win on token axis.
    [tested: image-multwo -> ok 95.52; map-multwo -> ok 95.33]
- NOTE: first batch's "baseline" copy failed with `Finset.mem_image_of_mem compl hA`
  giving `Aᶜᶜ ∈ image` — with image, the member is `Aᶜᶜ`, so the witness must be the
  `mem_image.mpr ⟨Aᶜ, hA, compl_compl A⟩` form (rfl does NOT work; compl_compl is needed).

## Architecture (current best)
classical → key (∀ A ∉ P, ∃ U ∈ P, ∀ x ∈ A, x ∉ U; by_contra! + hPS +
nonempty_iff_ne_empty.mp) → dich (A ∈ P ∨ Aᶜ ∈ P; two key applications +
`Set.eq_empty_of_forall_notMem fun x hx => hVc x (hAU x · hx.1) hx.2`)
→ h2 : P.card * 2 = 2 ^ (Fintype.card S - 1) * 2, rw chain:
`[← pow_succ, Nat.sub_add_cancel Fintype.card_pos,
  ← Finset.card_univ.trans Fintype.card_set,
  ← Finset.eq_univ_of_forall fun A => (dich A).elim (Finset.mem_union_left (P.image compl))
    fun hA => Finset.mem_union_right P (Finset.mem_image.mpr ⟨Aᶜ, hA, compl_compl A⟩),
  Finset.card_union_of_disjoint (Finset.disjoint_left.mpr fun A hA hA' => by
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.mp hA';
    exact hPP B hB Bᶜ hA (inter_compl_self B)),
  Finset.card_image_of_injective P compl_injective, Nat.mul_two]`
closer `Nat.eq_of_mul_eq_mul_right Nat.zero_lt_two h2`.

## Next ideas (untested, most promising first)
1. Map variant with `Finset.mem_union_left _` (dash instead of explicit
   `P.map (⟨compl, compl_injective⟩ : Set S ↪ Set S)`) — FAILED: Lean picked the wrong
   instantiation of the `_` and `compl_compl A` type-mismatched.
   [tested: map-multwo-dash -> fail 38:64 ?m.241 Aᶜ = A]. With image the dash version
   compiles (img-dash == current best, byte-identical, not re-scored). Try hybrid:
   map version where the union arg is spelled but the `← Finset.card_univ...` etc. kept,
   or image version where mem_union_left's arg is `_` — that's what img-dash does.
2. Term-mode `match hA' with | ⟨B, hB, rfl⟩ => ...` instead of `by obtain` inside
   disjoint — FAILED for Finset: `⟨...⟩` anonymous-constructor doesn't work on
   `Finset.val` (Quot.lift, not an inductive). [tested: img-match -> fail 41:12]
   An `Obtain`-free term needs `Finset.mem_image.mp hA'` destructuring another way
   (e.g. `.choose`/`.choose_spec` on the And after Exists — likely not cheaper).
3. Two-in-one: with image, hb 918 vs map 819; if hb axis ever dominates, revert to map
   version with Nat.mul_two ending (multwo variant, 95.33, tokens 235/hb 819).

## Tested negatives (do not retry)
- `Set.not_nonempty_iff` DOES NOT EXIST (v4.26 Mathlib); `Set.not_nonempty_iff.mp` unknown.
  [tested: lean_run #check -> Unknown constant]. So dich must keep
  `Set.eq_empty_of_forall_notMem`.
- `mul_right_cancel₀ Nat.zero_lt_two h2` closer: signature wants `?m ≠ 0`, not `0 < 2`.
  [tested: closer-cancel -> fail 44:26]
- `Nat.two_mul` after `Finset.card_map _` in this chain: no `2 * ?n` occurrence
  (goal is P.card*2 = P.card+P.card); must use Nat.mul_two. [tested: mulswap -> fail 43:25]
- rcases-dich (`by rcases dich A with hA | hA` + bullets instead of `.elim` term):
  compiles but 240 tok / 883 hb, loses. [tested: rcases-dich -> ok 883 hb]
- From earlier runs: `have ⟨…⟩ :=` destructure loses to `obtain` (912 vs 821 hb);
  `Nat.eq_of_mul_eq_mul_left`/linarith/nlinarith closers worse; `hPP`'s `≠ ∅` is literally
  ¬(=∅), `Set.eq_empty_of_forall_notMem` wrapper is load-bearing; `set Q := …` costs ~165 hb
  for nothing; key in `A ∩ U = ∅` form no shorter.

## Nonexistent names (confirmed)
`Set.not_nonempty_iff`, `Set.ne_empty_of_mem`, `Set.ne_empty_of_nonempty`,
`Nat.sub_one_add_cancel`, `Function.mpr`, `Finset.card_union_disjoint`.
Exist: `Nat.mul_two`, `Finset.card_image_of_injective`, `Finset.mem_image.mp/mpr`,
`Finset.card_union_of_disjoint`, `Nat.eq_of_mul_eq_mul_right`, `compl_injective`.
