# Late-turn output cap for GLM-5.3-Flash on the A100: NO-GO (b104, 2026-11-01)

Operator 2026-11-01 ~04:05 UTC, "immediate actions" from the open-model gap (docs/open_vs_closed_agent_gap.md: GLM emits ~8k output tokens
per turn, 80-85% thinking). Hypothesis: capping later turns gives more turns per GPU-minute and a better score per GPU-minute. Workflow
wf_8abf312a-ca2; branch b104-turncap (lra-a100) at 160f4500, pushed, NOT merged; design and full result in that branch's
docs/b104_turncap.md (sections 1-7); raw readout probe/b104/p85e_ab/ab_final.json there.

## Verdict
**NO-GO.** The recipe stays: `--max-tokens 6000`, cap 18000 per turn and 24000 for the rest of a session after the first truncated or
rescued turn, budget forcing on. The new flags (`--late-turn-cap N`, `--late-turn-from K`, `--no-trunc-escalation`) stay opt-in, default
off. No package change; nothing from b104 goes into rc2/rc3 or the official run.

## What was tested
- A = the package recipe. B = A + `--late-turn-cap 6000 --late-turn-from 4 --no-trunc-escalation` (18000 on turns 0-3, 6000 from turn 4,
  never 24000; one relief turn at 18000 after a cut answer).
- Box test (the Mississippi box, 04:39-06:34 UTC, $0): pairs A/B started together from byte-identical snapshots of the main row dir, 2400 s
  of wall time per row and arm, up to 4 pairs, through an opt-in mode of the p85e side scheduler (v3.2-ab); rows = the warm-up rows below
  94, lowest first. Pre-registered clear win: paired mean B-A >= +0.50, bootstrap 90% lower bound > 0, rows won >= lost + 2, no row
  worse than -5, B's gain per Mtok >= 1.2x A's; adoption needed a win in BOTH this test and an OpenRouter stand-in.
- OpenRouter stand-in: not launched ($0). Its gate (balance >= the closed final's $180 reserve + $15) failed at 04:30 ($119.37), and it was
  a weak proxy anyway (GLM on Wafer ~3.3k output tokens per turn vs 10.6k on the A100). After the box result the operator skipped it
  (06:20, decision 6).

## Result (9 pairs finished, 0 dropped)
| arm | sessions | turns | out tokens | model-min | out/turn | budget-forced | truncated | compile ok | gain (9 rows) |
|---|---|---|---|---|---|---|---|---|---|
| A (recipe) | 12 | 88 | 666,117 | 307.3 | 7,570 | 10 | 12 (13.6%) | 17/79 (21.5%) | 0.00 |
| B (+cap) | 11 | 71 | 689,850 | 318.7 | 9,716 | 27 | 31 (43.7%) | 31/77 (40.3%) | +0.05 (row 04, EM) |

- Paired mean B-A **+0.006** (90% lower bound 0.00); won 1, lost 0, worst 0.00: only "no row worse than -5" held.
- Row 00's pair (substOld) was cut at 34 min by the operator-requested stop of all warm-up agents at 06:34 (equally for both arms).
- Load was clean: vLLM KV mean 0.42, max 0.71, no preemptions.

## Why it did not work
- GLM's late turns are already short on the median: from turn 4, A's turns had a median of 2.3k tokens (mean 5.4k). A 6000 cap sits at
  B's median (6.0k) and turns the long tail into cut + budget-forced rescue (a second call of up to 6000 tokens): 13 of 31 late B turns were
  forced vs 2 of 50 for A. So B got rescues, not extra turns: turns per million output tokens A 132 vs B 103.
- 40-minute blocks on these plateaued rows gain too rarely to separate arms (1 improvement in 18 arm blocks).

## Lessons
1. Capping GLM's thinking does not make it act sooner; it truncates. The excess is in a long tail of turns, not in every turn.
2. Any retry needs a cap well above the late-turn median (e.g. 12000), more time per row (>= 60 min) and its own pre-registered A/B.
3. Contrast (gap6 step test, running since 06:06, docs/open_gap6_prompt.md): a ONE-move, line-specific instruction made GLM take ~1.7x
   more turns in the same time in its first sessions (18 vs 10, 13 vs 8). Steering what to try seems to help where limiting how long to
   think did not; the step test's scores decide.
