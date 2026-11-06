# Lean Refactor Arena: open-weight track (team Vexorium)

**This branch (`release/open-run3-fast-post`; tag `open-run3-fast-post-20261106`) is POST-HOC and is the code of no upload:** `final/` is the sub43 tree with a fast post stage
added to `run.sh` ([`final/post_fast/CHANGE.md`](final/post_fast/CHANGE.md)). The rest of this README describes tag `open-run3-post-final-sub43-20261104`.

**This branch (`release/open-run3-post`; tag `open-run3-post-final-sub43-20261104`):** [`final/`](final/README.md) is the code of
our final upload `sub43`: official run 3's package (`246ff1f1`) plus the post-step (development commit `a25416f5`) that our upload of
its export went through seven times ([`final/README.md`](final/README.md), sections "This folder and our code zip" and "Post-step";
step by step: [`final/REPLICATE.md`](final/REPLICATE.md)). Our code ZIP for `sub43` is this `final/` with `LICENSE`, `NOTICE.md` and a
`ZIP_NOTES.md`, and the post-step files byte for byte (here 4 of them carry redactions in comments). Where the rest of this README
describes `final/`, it means the `final/` of the `main` branch (run 2's package).

This repository holds our entry (username `Vexorium`) for the open-source LLM track of the Lean Refactor Arena (NeurIPS 2026 VERICODEGEN
workshop competition). Every proof in our line is written by one open-weight model, GLM-5.3-Flash (AWQ W4A16), served with vLLM on
4 x A100 80 GB. No hosted model is called during a run, and no model was trained or fine-tuned.

## Final result

**Our final open-track upload is `sub43` (2026-11-04 11:25:51 UTC): leaderboard score 82.55 (L 65.60, H 82.06, Z 100), first place
on the open-track leaderboard at the deadline (2026-11-04 11:59 UTC).**

| | |
|---|---|
| Proofs | the export of our official **run 3** (package `246ff1f1`, GLM-5.3-Flash on an on-demand 4 x A100 80 GB SXM4 box, from the seed proofs; started 2026-11-02 06:43:52 UTC, 48 h clock; stored mean 79.6778 on our meter), then **seven passes of the post-step** `harness/open_post.py` (development commit `a25416f5`: passes 1-2 `--ops v3`, passes 3-4 `--ops v4`, passes 5-7 `--ops all --long`; CPU only, no model, $0): stored mean 82.5560 on our meter |
| Upload file | 60 `{"name", "proof"}` lines, sha256 `8d6d1893d315eb0f55491df50046629877d2f89005848862bc8c892dba3f3e5e` |
| Code | the code ZIP we submitted with it, sha256 `1a49b3566a54cf248afe00cd3af3e54d3519736d4ec32fda2a89cb1e2f8ffc4e` = `final/` of the tag [`open-run3-post-final-sub43-20261104`](https://github.com/bobbercheng/lean-refactor-open/tree/open-run3-post-final-sub43-20261104) (branch `release/open-run3-post`) plus `LICENSE`, `NOTICE.md` and a `ZIP_NOTES.md`. In the repository, 4 post-step files carry redactions in comments; the ZIP has them byte for byte |
| Replicate | that tag's [`final/README.md`](https://github.com/bobbercheng/lean-refactor-open/blob/open-run3-post-final-sub43-20261104/final/README.md) (sections "This folder and our code zip" and "Post-step", with "Pass 6" and "Pass 7") and [`final/REPLICATE.md`](https://github.com/bobbercheng/lean-refactor-open/blob/open-run3-post-final-sub43-20261104/final/REPLICATE.md) (step by step, with our numbers) |

Disclosures for the final upload (details in that tag's `final/README.md`, section "Post-step"):

- **Kernel skip on 4 rows.** Four lines carry `set_option debug.skipKernelTC true in` in front of a closing `decide +kernel`
  (FTheory `isPhenoClosedQ5_viableCharges` and `isPhenoClosedQ10_viableCharges`, and two PauliMatrix rows). The Q10 line was written
  by the run's own model; the post-step's `kskip` op added the other three. The option makes Lean skip the kernel's check of the
  declaration. It is not on the Arena's forbidden list, and the Arena graded these rows. One of the four,
  `PauliMatrix.pauliContr_mul_pauliContrDown_mul_pauliContr`, is **not** a valid proof with the kernel check on: post-step edits made
  after the option was in place broke it. With its last kernel-valid form, the 60-row stored mean would be about 0.16 lower. The
  other three pass a re-check with a plain `decide +kernel`. We kept these lines knowingly and disclose them.
- **Elaborator options on 14 rows.** The op `hb_smartunfold` adds `set_option smartUnfolding false in` and `backward.isDefEq.*`
  options where they save heartbeats. These options are sound: the kernel still checks the final proof term.
- **The post-step was developed on the final benchmark** after its release. Most of its ops came from agent sessions of closed
  models (Claude, GPT, Gemini) and from our own censuses, which compared our open proofs with our closed-track proofs of the same
  rows. The README's paragraph "The post-step is not independent of the final benchmark" gives the source of every op. The ops are
  general rewrite rules that hold no row names and no proof text. No model runs in the step, and a rewrite is kept only if it
  compiles on every listed toolchain and scores higher.

All our uploads on the 60-problem final benchmark, under username `Vexorium` (the leaderboard shows a team's latest upload):

| Upload | Uploaded (UTC) | Leaderboard | What it was |
|---|---|---|---|
| `sub21` | 11-02 01:57 | 68.42 (L 41.54, H 63.72, Z 100) | probe: run 2's best proofs about 14 h into the run, with run 2's code zip |
| `sub24` | 11-02 18:15 | 68.77 (L 42.60, H 63.70, Z 100) | probe: run 3's best proofs 11.5 h into the run |
| `sub26` | 11-03 06:00 | 74.82 (L 51.09, H 73.38, Z 100) | probe: run 3's best proofs about 23 h into the run |
| `sub28` | 11-03 14:30 | 78.48 | run 2's final export |
| `sub29` | 11-03 14:33 | 79.74 | run 2's export after the post-step's first version (5 rows changed) |
| `sub31` | 11-04 01:03 | 80.76 | run 2's export after the post-step's second version, with its code zip |
| `sub33` | 11-04 04:43 | 81.18 (L 62.97, H 80.57, Z 100) | probe: a run 3 snapshot (2026-11-03 23:32 UTC) after the post-step's third version, run twice |
| `sub35` | 11-04 07:31 | 81.39 (L 62.71, H 81.46, Z 100) | run 3's final export after passes 1-2 (third version) |
| `sub36` | 11-04 07:58 | 81.50 (L 62.60, H 81.90, Z 100) | `sub35` plus one `hb_smartunfold` pass |
| `sub37` | 11-04 08:37 | 81.90 (L 64.24, H 81.45, Z 100) | `sub35` plus pass 3 (fourth version) |
| `sub38` | 11-04 08:44 | 82.21 (L 64.92, H 81.69, Z 100) | plus pass 4 (fourth version) |
| `sub39` | 11-04 09:07 | 82.27 (L 64.80, H 81.99, Z 100) | `sub38` plus one `hb_smartunfold` pass |
| `sub40` | 11-04 10:24 | 82.47 (L 65.43, H 81.98, Z 100) | `sub38` plus pass 5 (fifth version, `--ops all --long`) |
| `sub42` | 11-04 10:49 | 82.51 (L 65.51, H 82.00, Z 100) | plus pass 6 (the same command) |
| `sub43` | 11-04 11:25 | **82.55** (L 65.60, H 82.06, Z 100) | plus pass 7 (the same command): **our final upload** |

The run records and the uploaded proof files are not in this repository.

## Contents

| Folder | What it is |
|---|---|
| [`final/`](final/README.md) | **Run 2's package (released benchmark, 60 problems).** The release export of package commit `2dcf255f`, which is run 2's code `748d964c` with only switched-off code removed (see [`final/CODE_VERSION.md`](final/CODE_VERSION.md); the exact export is the tag `open-run2-exact-748d964c`) (`setup.sh`, `run.sh`, harness, scorer, model-free end stage), the 60 released rows in `final/data/official/rows.jsonl`, our own run orchestration on a rented vast.ai box in [`final/official_run/`](final/official_run/README.md), and the environment fixes we applied on that box in [`final/official_run/env_fixes/`](final/official_run/env_fixes/NOTES.md). **The code of our final upload** (run 3's package plus the post-step) is the `final/` of the tag [`open-run3-post-final-sub43-20261104`](https://github.com/bobbercheng/lean-refactor-open/tree/open-run3-post-final-sub43-20261104) (section "Final result" above). |
| [`warmup/`](warmup/README.md) | **The last warm-up rehearsal** (15 warm-up problems, p85 / p85b, Oct 30 to Nov 1): the package export that ran, the scripts that rented, ran, watched and stopped the boxes, and the environment setup. Scripts and configs only, no run outputs. |

The earlier warm-up material (the Oct 6-13 A100 line: run data, trajectories and per-problem state; 82.03, 82.29 with the normalizer
post-pass) is in this repository's git history, up to commit `b244fbd`.

## Our official runs

All three runs started from the seed proofs on the released benchmark. Each ran on its own on-demand 4 x A100 80 GB SXM4 box.

- **Run 3** (the source of our final upload): package `246ff1f1`, started 2026-11-02 06:43:52 UTC with a 48-hour clock. It is run 2's
  package plus the `envfix` setup step, the opt-in automation card (on in our run) and the funind dialect family, without the
  switched-off options. It ran side by side with run 2 on a second box. Its export (2026-11-04 06:03 UTC) stored 79.6778 on our meter. To rerun it, use the
  tag's `final/` (section "Final result").
- **Run 2**: package `748d964c`, started 2026-11-01 11:55:21 UTC. The package in this branch's `final/` is the same code with
  switched-off code removed. Its defaults are 11 concurrent sessions, at most 12 sessions per row, a per-session context cap of
  200,000 tokens, a staggered first wave, the pipelined end stage on, and a 2-hour end stage at the deadline. Its final export stored
  78.4585 on our meter (uploaded as `sub28`). To rerun this package on your own 4 x A100 server, start with
  [`final/README.md`](final/README.md): `bash setup.sh`, then the required environment step
  `python3 official_run/env_fixes/envfix_auto.py --rows data/official/rows.jsonl` (our box had this edit; see below), then
  `bash run.sh`.
- **Run 1**: package `1d1a31d4`, stopped after about 4 hours (below). It was not uploaded.

Operational notes on runs 1 and 2 (recorded in `final/official_run/`; no code was changed during either run):

- Environment fixes on our box before the first clock started, including an env-side workaround for 5 released rows whose reference
  proof failed in our measured compile (`final/official_run/env_fixes/NOTES.md`). The package fix is pending: a rerun without the same
  environment edit (`envfix.py`) has the same failure on these 5 rows.
- **Run 1** (package `1d1a31d4`, 14 concurrent sessions) started at 07:56:49 UTC. Its 14 first sessions started together and reached long
  contexts at the same time, which saturated the vLLM KV cache and cut the server's output to about a third. We stopped five long
  sessions between 09:36 and 10:59 UTC (three by hand, two by an automatic shedder; their rows kept their best proofs) and relaunched run 1 with
  11 sessions at 11:00 UTC. At 11:48 UTC we stopped run 1 (its export, 60 rows, stored mean 44.79, is kept as a record, not uploaded),
  installed package `748d964c`, restarted vLLM and started run 2 from the seed proofs with a new 48-hour clock
  (`final/official_run/README.md`, "Run 1 and run 2"). In run 2 the KV cache stayed below 75% (no saturation).

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
- **No stored proofs in the official runs:** every row starts from the seed proof in the rows file; no proof from an earlier run is
  reused.
- **Closed-model example pairs:** the opt-in style step and its 9 encoded closed-model example pairs (two from our internal development
  sets) were removed from `final/` on 2026-11-02 together with the other switched-off options; the step was off in our official runs, and
  the example file was never in this repository or its history. `warmup/package/` leaves it out too.
- **Closed-line prompt texts:** `final/harness/agent.py` also holds prompt texts mined from our closed-model lines (`--closed-lessons`
  and a review lever). `--open-package` forces them off, but the model's shell tool can read the file.
- **Shared end stage:** the model-free end stage (the r10 rounds, on by default) is shared with our closed-track final. It holds
  mechanical rewrite families and contains no model output.
- **Isolation:** each row's sessions learn only from that row's own history (its best proof, attempts, notes and winning edits). The
  model's shell tool runs on the host, so isolation between rows is by convention, not enforced.
- **Run operations** (rentals, environment setup, monitoring, the interventions above) were supervised by Claude Code; it wrote no
  proofs and changed no prompt or harness code during a run.

**Removed for public release.** Credentials and private values (the vLLM bearer key, TLS pairs, the bucket key, the Kaggle key, the
vast.ai CLI configuration, the private push-notification topic) are not in this repository; the scripts read them from
`~/.config/vexorium/` and from files you create (see `final/official_run/README.md`). A since-rotated push topic remains in commit
`eee8f07`. Our operation diaries (rentals, bids, credit and host details) stay in our private development repository.
[`NOTICE.md`](NOTICE.md) lists every edit made for public release and what was kept.

## License

Our code, notes and run records are licensed under the [PolyForm Noncommercial License 1.0.0](LICENSE): free for study, research and
other noncommercial use. **Commercial use needs a separate license**: contact b.cheng@vexorium.net. Third-party material (upstream
Lean library sources, competition data, model outputs, the model checkpoint) keeps its own terms; see [`NOTICE.md`](NOTICE.md).
