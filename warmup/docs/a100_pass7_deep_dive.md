# Why the A100 line stopped short of 82 (deep dive, 2026-10-09)

We asked why the last A100 pass barely improved and the line could not pass 82. The line ended at **81.72** after pass 7: 81.46 → 81.72,
+0.26. Reaching 82 needed +0.28 more, i.e. **+4.2 points summed over the 15 problems**. Sources: the run's verified records, its trajectories
(`probe/pass_dive.py`, per-turn tools, checks, errors and session ends), the knowledge-graph comparison (`docs/kg_diff_zai_a100.md`) and
the babysit log.

## Answer in one paragraph
Passes 6 and 7 were **fragmented by four vast stops** (outbids at 04:42, 05:40 and 13:09, and the credit running out at 13:46). Those passes did
336 and 211 turns where passes 3–5 did 380–470. The lost turns landed on exactly the problems that still had headroom, because long, hard
sessions are the ones a stop interrupts. The resume tooling then re-ran only problems that had **never taken a turn**, so a hard problem
cut after 2–18 turns got no second chance in that pass. With full sessions, the cut problems' own recent gain rates put the line at about
82.2–82.7. A second, independent limit sits under that: the biggest remaining gaps (EM, interleaved) need a **different proof
architecture**, which z.ai found and incremental editing does not reach.

## 1. The last two passes did half the work

| pass | turns | problems DONE | summed gain | line |
|---|---|---|---|---|
| 3 | 381 | 15/15 | +20.50 | 76.83 |
| 4 | 466 | 15/15 | +26.55 | 78.60 |
| 5 | 421 | 15/15 | +32.29 | 80.76 |
| 6 | 336 | 10/15 | +10.57 | 81.46 |
| 7 | **211** | **9/15** | +3.90 | 81.72 |

## 2. The lost turns hit the problems with headroom
Turns per session in passes 6 and 7 (the turn budget is 40–50 for these problems), and the gain each problem made in its last full session:

| problem | score | pass 6 | pass 7 | last full session | state at the end of it |
|---|---|---|---|---|---|
| interleaved | 77.34 | **2** (cut) | **5** (cut) | p5: +2.72 in 40 turns | 3 new bests; it gained +1.98 to +8.90 in every pass 2–5 |
| fiberwise | 75.85 | 15 (cut) | 18 (cut) | p5: +2.86 in 36 turns | still improving: its last new best came on its final turn |
| Wick ι_timeOrderF | 69.47 | 45: +1.89 | 19 (cut) | p6: +1.89 | 9 new bests in p6 |
| EM time_deriv | 66.49 | 50: +0 | 24 (cut): **+2.84** | p7, cut: 3 new bests in 24 turns | the fresh session was finding gains when cut |
| SKI parallelReduction | 68.70 | 29 (cut) | 11 (cut) | p5: +1.29 in 42 turns | |

The stops took the hard sessions because those run longest. At 04:42 fiberwise, SKI and interleaved were in flight. At 13:09 EM, Wick, SKI,
fiberwise and interleaved were. The resume rule ("finish the pass for problems that never took a turn") treats a session cut after 2 turns
as done for that pass.

## 3. What full sessions would likely have given
Each cut problem's gain per turn in its last full session (a recent, conservative rate), times the turns it lost in passes 6–7:

| problem | rate per turn | turns lost | linear | halved |
|---|---|---|---|---|
| interleaved | 0.068 | 73 | +5.0 | +2.5 |
| fiberwise | 0.079 | 39 | +3.1 | +1.5 |
| EM | 0.118 (p7) | 26 | +3.1 | +1.5 |
| SKI | 0.031 | 44 | +1.4 | +0.7 |
| Wick | 0.042 | 26 | +1.1 | +0.5 |
| others (CCS, the Putnam pair) | | | +0.5 | +0.3 |
| **summed** | | | **+14.2 → line 82.66** | **+7.0 → line 82.19** |

Both columns pass 82, which needed +4.2. This is an estimate, but the direction is robust: the problems that were cut were the ones still moving.

## 4. The rest of the field had plateaued
The problems that got full sessions in passes 6–7 mostly made nothing:
- **substOld** (85.91): 0 in two full 20-turn sessions; 24 of 32 checks failed in pass 7. At 32 tokens it is far shorter than z.ai's 105.
- **fundamental theorem** (86.39): 0 in pass 7 (finished early after 15 turns; 12 of 15 checks failed). z.ai's proof is shorter (152 vs 213 tokens).
- **putnam a4 / b2 / 1995_a3 and fold** (88.5–95.5): small gains, agents finishing after 4–6 turns.

These sessions are still cheap insurance, but each 20-turn plateau session is turns the hard tail did not get (the cycle-64 finding).

## 5. The biggest gaps are architectural
- **EM (z.ai 81.81 vs 66.49):** the A100 proof keeps one `calc` block that costs 10,927 of its 12,375 heartbeats (88%; profile in pass 6).
  z.ai's proof states a `key` identity and rewrites with it, with no `calc` at all: 469 tokens and 5.5k heartbeats against 783 and 11.8k. In
  pass 6 the A100 agent spent 50 turns, including 6 `lean_skeleton` rewrite attempts, and 23 of 34 checks failed (type mismatch 9, unsolved
  goals 8). The rewrites never compiled.
- **interleaved (z.ai 89.48 vs 77.34):** z.ai uses `refine Nat.le_induction ?base ?step ϑ …`, an induction that starts at 1, in 141 tokens. The
  A100 proof inducts from 0 with a `contradiction` base case and a chain of `have`s, in 369 tokens. No amount of golfing turns one into the
  other.

These two problems alone hold 27 of the 49 points by which z.ai leads. Incremental editing converges to a local optimum. A restructure
needs a different plan, which the harness asks for ("start a NEW rewrite with a different architecture") but the model at low effort rarely
lands.

## 6. Smaller factors
- Pass 6 ran **without ripgrep**: all 16 opening lemma searches failed and 12 of the model's `rg` calls returned not-found. There is no
  visible spike in unknown names (0.086 per turn vs 0.06–0.08 before), but the model got no library leads in pass 6.
- Pass 7 lost one lemma search to the **index race** (now fixed: a lock per index, unique temp names; 4/4 threads pass, selftest 13/13).
- Error profile of the stuck sessions: type mismatch and unsolved goals dominate. These are failed restructures, not wrong names.

## 7. What to change
1. **(Done, cycle 79: `infra/vast/resume_pass_instance.sh`; dry run on pass 6 selects exactly its 5 cut sessions.) Resume a cut session, not just a never-started one:** a resumed pass should re-run every problem without an `end` record, with the
   turns it has left. A stop then costs time, not a problem's pass.
2. **Gain-weighted turn budgets:** move turns from plateaued problems (two full sessions with no gain) to problems still finding new bests.
3. **Architecture search for the hard tail:** for problems where one block dominates the profile (EM's `calc`, 88%) or where the other line's
   proof is far shorter, run the hard-tail strategy: a goal map, then 3–5 alternative plans under a token target, as general practice and
   never the other line's proof. Higher effort for those sessions only.
4. **No interruptible hardware for runs that matter:** the official run is on the organizers' server. For our rehearsals, use on-demand
   instances for the last passes, or accept the cost of stops, now made cheaper by fix 1.

## 8. How z.ai solved the two big gaps
Not by higher effort. The z.ai records, in time order:
- **EM, through a second, independent line plus migration.** The z.ai main line kept a `calc` proof for passes 2–9 and crawled to 57.38
  (1,170 tokens). The calc-free architecture first appeared in **`fresh-zai-p1`**: the first pass of an independent, fresh-state z.ai
  replication, at 61.55 (1,002 tokens). At pass 10 the main line **adopted it through bank sync** ("Electromagnetism starts from the
  control's 61.6"). From that new start it gained +13 in one run (74.84, structural mode at LOW effort), then polished it to 79.46 by pass 16
  and 81.81 in the tier-1/2 measurement run. The A100 line was a single line with no bank sync (replication roots never sync), so it kept
  its pass-1 `calc` to the end.
- **interleaved, by acting on a library lead.** The lemma search put `Nat.le_induction` in the prompt as a LIBRARY LEAD in z.ai's tier-1/2
  runs, and the model used it (138 mentions in the top-up run): 286 → 146 tokens. The A100 prompts carried the same lead in passes 4, 5
  and 7, three mentions each. The A100 model never acted on it and stayed with induction from 0 at 369 tokens (pass 6 had no leads:
  ripgrep was missing).
- **More runs, too.** z.ai had about 25 runs touching each of these problems: the main line, a replication, POC 2, measurements and
  top-ups. The A100 line had 7. The official run has room for about 5 passes over 50 problems, so more passes are not available.

**The mechanisms that worked were diversity with migration, and library leads turned into restructures.** Neither needs higher effort.
