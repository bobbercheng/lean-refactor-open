# putnam_1964_a4 notes (v4.27.0 primary; v4.26.0, v4.25.0 compat)

## BEST: score 90.16 (candidate.lean): 483 tok, 2480 hb, compat 3/3
Structure: typed obtain pigeonhole via Set.Finite.pi + Function.not_injective_iff + ∘ Set.infinite_range_of_injective;
hrec single-cast; hstep with `h 0 (by decide)..h 3 (by decide)`; key = term Nat.strongRecOn;
final: `have h9 := key (n - i); rw [Nat.add_sub_cancel' hn, show j + (n - i) = n + (j - i) from by omega] at h9; exact h9.symm`.

## This run (3-check polish run)
- `[tested: h _ (by decide) x4, hfin-as-separate-have, ih (k+t) (by omega), congrArg-trans closer -> all compile but NOT better than 483/2480 (482/2578, 489/2484)]`
- `[tested: obtain hm | ⟨k, rfl⟩ := Nat.lt_or_ge m 4 -> FAILS: Nat.lt_or_ge's second arm is 4 ≤ m (a Le, not an ∃), so ⟨k, rfl⟩ cannot destruct it; error 'Unknown identifier k']`
- **PROMISING (unfinished, next run's first idea): the goal-side rewrite closer.**
  ```
  refine ⟨i, j - i, Nat.sub_pos_of_lt hij, fun n hn => ?_⟩
  nth_rewrite 1 [← Nat.add_sub_cancel' hn]   -- rewrites only FIRST n: goal u (i+(n-i)+(j-i)) = u n
  rw [show i + (n - i) + (j - i) = j + (n - i) from by omega]   -- goal u (j+(n-i)) = u n
  exact ((key _).symm.trans (congrArg u (Nat.add_sub_cancel' hn)))   -- UNTESTED closer
  ```
  Measured on the near-misses: nth_rewrite route hits **hb ≈ 2009-2274 (vs 2480 floor of best)** and tokens 465-486.
  `[tested: nth_rewrite 1 [← Nat.add_sub_cancel' hn]; rw [Nat.add_right_comm, Nat.add_sub_cancel' hij] -> FAILS: with hij : i < j the add_sub_cancel' instance unifies to i.succ + (j - i.succ) pattern, not found; use `show i + (j - i) = j from by omega` instead]`
  `[tested: closing with exact (key _).symm directly -> type mismatch: goal RHS is u n but key gives u (i+(n-i)); the fix above threads congrArg u (Nat.add_sub_cancel' hn) after .symm.trans]`
  Beware: plain `rw [← Nat.add_sub_cancel' hn]` (no nth_rewrite) rewrites ALL n's incl. inside (n-i) — chaos. `[tested]`

## Durable facts (re-confirmed in earlier runs)
- `Nat.add_sub_cancel' (h : m ≤ n) : m + (n - m) = n`; `Nat.sub_add_cancel (h : m ≤ n) : n - m + m = n`.
- No library lemma for `j + (n - i) = n + (j - i)` (exact?/simp? both fail). `[tested this run: lean_run exact? and simp? on that goal -> no proof found / no progress]`
- `Finite.exists_ne_map_eq_of_infinite` useless (ℤ⁴ not Finite). Pigeonhole MUST go through
  Set.Finite.pi (or .prod) on the window map + not_injective contrapositive.
- `Set.Infinite.exists_ne_map_eq_of_finite`, `Ne.lt_or_lt` do NOT exist.
- `Nat.add_right_comm : a + b + c = a + c + b` exists and fired fine.
- hb profile of best: final rw 457, pigeonhole 494, hrec 435, hstep 305, key 200; floor (sorry body) 558.

## Dead ends (earlier runs, all measured worse or failing)
- `(key (n - i)).symm` upfront + rwa: 484 tok. simpa only [Nat.add_assoc] in key step: +6 hb.
- rwa anywhere in final block; rcases-based obtain of k combined with Nat.lt_or_ge (see above).
