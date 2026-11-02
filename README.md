# Lean Refactor Arena: open-weight track (team Vexorium)

This repository holds our entry (username `Vexorium`) for the open-source LLM track of the Lean Refactor Arena (NeurIPS 2026 VERICODEGEN
workshop competition). Every proof in our line is written by one open-weight model, GLM-5.3-Flash (AWQ W4A16), served with vLLM on
4 x A100 80 GB. No hosted model is called during a run, and no model was trained or fine-tuned.

## Contents

| Folder | What it is |
|---|---|
| [`final/`](final/README.md) | **The official run (released benchmark, 60 problems).** The package we submit: the release export of package commit `2dcf255f`, which is our run's code `748d964c` with only switched-off code removed (see [`final/CODE_VERSION.md`](final/CODE_VERSION.md); the exact export is the tag `open-run2-exact-748d964c`) (`setup.sh`, `run.sh`, harness, scorer, model-free end stage), the 60 released rows in `final/data/official/rows.jsonl`, our own run orchestration on a rented vast.ai box in [`final/official_run/`](final/official_run/README.md), and the environment fixes we applied on that box in [`final/official_run/env_fixes/`](final/official_run/env_fixes/NOTES.md). |
| [`warmup/`](warmup/README.md) | **The last warm-up rehearsal** (15 warm-up problems, p85 / p85b, Oct 30 to Nov 1): the package export that ran, the scripts that rented, ran, watched and stopped the boxes, and the environment setup. Scripts and configs only, no run outputs. |

The earlier warm-up material (the Oct 6-13 A100 line: run data, trajectories and per-problem state; 82.03, 82.29 with the normalizer
post-pass) is in this repository's git history, up to commit `b244fbd`.

## Status of the official run

Our official open-track run is **run 2**: package commit `748d964c` (the package in `final/` is the same code with switched-off code removed, with its defaults: 11 concurrent sessions,
at most 12 sessions per row, a per-session context cap of 200,000 tokens, a staggered first wave, pipelined end stage on, 2-hour end
stage at the deadline), started from the seed proofs on 2026-11-01 at 11:55:21 UTC on an on-demand 4 x A100 80 GB SXM4 box, for 48
hours (until 2026-11-03 11:55:21 UTC). Its exported proofs are what we upload; they will be added here after the run, with the run's
summary. To rerun the package on your own 4 x A100 server, start with [`final/README.md`](final/README.md): `bash setup.sh`, then the
required environment step `python3 official_run/env_fixes/envfix_auto.py --rows data/official/rows.jsonl` (our box had this edit; see
the next section), then `bash run.sh`.

Operational notes (recorded in `final/official_run/`; no code was changed during either run):

- Environment fixes on our box before the first clock started, including an env-side workaround for 5 released rows whose reference
  proof failed in our measured compile (`final/official_run/env_fixes/NOTES.md`). The package fix is pending: a rerun without the same
  environment edit (`envfix.py`) has the same failure on these 5 rows.
- **Run 1** (package `1d1a31d4`, 14 concurrent sessions) started at 07:56:49 UTC. Its 14 first sessions started together and reached long
  contexts at the same time, which saturated the vLLM KV cache and cut the server's output to about a third. We stopped five long
  sessions between 09:36 and 10:59 UTC (three by hand, two by an automatic shedder; their rows kept their best proofs) and relaunched run 1 with
  11 sessions at 11:00 UTC. At 11:48 UTC we stopped run 1 (its export, 60 rows, stored mean 44.79, is kept as a record, not uploaded),
  installed package `748d964c`, restarted vLLM and started run 2 from the seed proofs with a new 48-hour clock
  (`final/official_run/README.md`, "Run 1 and run 2"). In run 2 the KV cache has stayed below 75% (no saturation).

## Warm-up results on the public board

| Submission | When | Official score | What |
|---|---|---|---|
| sub19 | 2026-10-31 22:06 UTC | **86.66** (L 74.66, H 85.33, Z 100) | p85 / p85b rehearsal, 23 h from the seed proofs |
| sub18 | 2026-10-31 17:26 UTC | 85.13 | the same rehearsal, earlier |
| sub13 | 2026-10-27 02:53 UTC | 83.31 | the Oct 6-13 A100 line after a model-free end stage (history at `606142e`) |

## Provenance and disclosures

- **The harness** (prompts, technique cards, turn rules, tools, the model-free end stage) was developed on the 15 warm-up problems and
  on internal development sets, with our own analyses and development tools, including Claude Code, which wrote the harness code. The
  prompts carry general practices (proof patterns, a rewrite-first workflow, a token and heartbeat cost table).
- **No stored proofs in the official run:** every row starts from the seed proof in the rows file; no proof from an earlier run is
  reused.
- **Closed-model example pairs:** the opt-in style step and its 9 encoded closed-model example pairs (two from our internal development
  sets) were removed from `final/` on 2026-11-02 together with the other switched-off options; the step was off in our official run, and
  the example file was never in this repository or its history. `warmup/package/` leaves it out too.
- **Closed-line prompt texts:** `final/harness/agent.py` also holds prompt texts mined from our closed-model lines (`--closed-lessons`
  and a review lever). `--open-package` forces them off, but the model's shell tool can read the file.
- **Shared end stage:** the model-free end stage (the r10 rounds, on by default) is shared with our closed-track final. It holds
  mechanical rewrite families and contains no model output.
- **Isolation:** each row's sessions learn only from that row's own history (its best proof, attempts, notes and winning edits). The
  model's shell tool runs on the host, so isolation between rows is by convention, not enforced.
- **Run operations** (rentals, environment setup, monitoring, the interventions above) were supervised by Claude Code; it wrote no
  proofs and changed no prompt or harness code during the run.

**Removed for public release.** Credentials and private values (the vLLM bearer key, TLS pairs, the bucket key, the Kaggle key, the
vast.ai CLI configuration, the private push-notification topic) are not in this repository; the scripts read them from
`~/.config/vexorium/` and from files you create (see `final/official_run/README.md`). A since-rotated push topic remains in commit
`eee8f07`. Our operation diaries (rentals, bids, credit and host details) stay in our private development repository.
[`NOTICE.md`](NOTICE.md) lists every edit made for public release and what was kept.

## License

Our code, notes and run records are licensed under the [PolyForm Noncommercial License 1.0.0](LICENSE): free for study, research and
other noncommercial use. **Commercial use needs a separate license**: contact b.cheng@vexorium.net. Third-party material (upstream
Lean library sources, competition data, model outputs, the model checkpoint) keeps its own terms; see [`NOTICE.md`](NOTICE.md).
