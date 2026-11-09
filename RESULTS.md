# Results and runs: open-weight track (team Vexorium)

The record behind the summary in [`README.md`](README.md): our final upload, every upload on the final benchmark, our three official
runs and our warm-up results. The disclosures for these results are in [`DISCLOSURES.md`](DISCLOSURES.md).

## Final result

**Our final open-track upload is `sub43` (2026-11-04 11:25:51 UTC): leaderboard score 82.55 (L 65.60, H 82.06, Z 100), first place
on the open-track leaderboard at the deadline (2026-11-04 11:59 UTC).**

| | |
|---|---|
| Proofs | the export of our official **run 3** (package `246ff1f1`, GLM-5.3-Flash on an on-demand 4 x A100 80 GB SXM4 box, from the seed proofs; started 2026-11-02 06:43:52 UTC, 48 h clock; stored mean 79.6778 on our meter), then **seven passes of the post-step** `harness/open_post.py` (development commit `a25416f5`: passes 1-2 `--ops v3`, passes 3-4 `--ops v4`, passes 5-7 `--ops all --long`; CPU only, no model, $0): stored mean 82.5560 on our meter |
| Upload file | 60 `{"name", "proof"}` lines, sha256 `8d6d1893d315eb0f55491df50046629877d2f89005848862bc8c892dba3f3e5e` |
| Code | the code ZIP we submitted with it, sha256 `1a49b3566a54cf248afe00cd3af3e54d3519736d4ec32fda2a89cb1e2f8ffc4e` = `final/` of the tag [`open-run3-post-final-sub43-20261104`](https://github.com/bobbercheng/lean-refactor-open/tree/open-run3-post-final-sub43-20261104) plus `LICENSE`, `NOTICE.md` and a `ZIP_NOTES.md`. At that tag, 4 post-step files carry redactions in docstrings; the ZIP has them byte for byte |
| Replicate | that tag's [`final/README.md`](https://github.com/bobbercheng/lean-refactor-open/blob/open-run3-post-final-sub43-20261104/final/README.md) (sections "This folder and our code zip" and "Post-step", with "Pass 6" and "Pass 7") and [`final/REPLICATE.md`](https://github.com/bobbercheng/lean-refactor-open/blob/open-run3-post-final-sub43-20261104/final/REPLICATE.md) (step by step, with our numbers) |

The disclosures for this upload are in [`DISCLOSURES.md`](DISCLOSURES.md), section "The final upload": a kernel skip on 4 rows, one of
which is not a valid proof with the kernel check on (about 0.16 of the stored mean); elaborator options on 14 rows; and a post-step
developed on the final benchmark.

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

## What this repository holds

**[`final/`](final/README.md)** is the code of our final upload `sub43` (official run 3's package `246ff1f1` plus the post-step,
development commit `a25416f5`) with a fast post stage added to `run.sh` ([`final/README.md`](final/README.md), first section;
[`final/post_fast/MANIFEST.json`](final/post_fast/MANIFEST.json) lists every changed file). `LRA_POST_ROUTE=off` restores the job.
The replication of `sub43` itself is the tag `open-run3-post-final-sub43-20261104` (section "Final result"). Run 2's package, which
was `main`'s `final/` until 2026-11-08, is the `final/` of tag [`open-final-probe-20261102`](https://github.com/bobbercheng/lean-refactor-open/tree/open-final-probe-20261102/final).

| Folder | What it is |
|---|---|
| [`final/`](final/README.md) | **The code of our final upload `sub43`, with the fast post stage (released benchmark, 60 problems).** The release export of official run 3's package `246ff1f1` (`setup.sh`, `run.sh`, harness, scorer, model-free end stage; `final/EXPORT.json`), the post-step `final/harness/open_post.py` and `final/harness/post/` (development commit `a25416f5`, with additions that only the fast post stage turns on), the fast post stage in `final/post_fast/`, which `run.sh` runs by default, and the 60 released rows in `final/data/official/rows.jsonl`. [`final/post_fast/MANIFEST.json`](final/post_fast/MANIFEST.json) lists every file that differs from the tag [`open-run3-post-final-sub43-20261104`](https://github.com/bobbercheng/lean-refactor-open/tree/open-run3-post-final-sub43-20261104), the code of our final upload (section "Final result" above). **Run 2's package** (the release export `2dcf255f` of run 2's code `748d964c`), with our run orchestration on a rented vast.ai box (`official_run/`) and the environment fixes we applied on that box (`official_run/env_fixes/`), is the `final/` of the tag [`open-final-probe-20261102`](https://github.com/bobbercheng/lean-refactor-open/tree/open-final-probe-20261102/final); the exact export is the tag `open-run2-exact-748d964c`. |
| [`warmup/`](warmup/README.md) | **The last warm-up rehearsal** (15 warm-up problems, p85 / p85b, Oct 30 to Nov 1): the package export that ran, the scripts that rented, ran, watched and stopped the boxes, and the environment setup. Scripts and configs only, no run outputs. |

The earlier warm-up material (the Oct 6-13 A100 line: run data, trajectories and per-problem state; 82.03, 82.29 with the normalizer
post-pass) is at the tag [`open-warmup-a100-line-20261101`](https://github.com/bobbercheng/lean-refactor-open/tree/open-warmup-a100-line-20261101).

## Our official runs

All three runs started from the seed proofs on the released benchmark. Each ran on its own on-demand 4 x A100 80 GB SXM4 box.

- **Run 3** (the source of our final upload): package `246ff1f1`, started 2026-11-02 06:43:52 UTC with a 48-hour clock. It is run 2's
  package plus the `envfix` setup step, the opt-in automation card (on in our run) and the funind dialect family, without the
  switched-off options. It ran side by side with run 2 on a second box. Its export (2026-11-04 06:03 UTC) stored 79.6778 on our meter. To rerun it, use the
  tag's `final/` (section "Final result"); `final/` on `main` is the same package with the fast post stage (`LRA_POST_ROUTE=off`
  restores the job).
- **Run 2**: package `748d964c`, started 2026-11-01 11:55:21 UTC. The `final/` of tag `open-final-probe-20261102` holds the same code with
  switched-off code removed. Its defaults are 11 concurrent sessions, at most 12 sessions per row, a per-session context cap of
  200,000 tokens, a staggered first wave, the pipelined end stage on, and a 2-hour end stage at the deadline. Its final export stored
  78.4585 on our meter (uploaded as `sub28`). To rerun this package on your own 4 x A100 server, start with
  that tag's [`final/README.md`](https://github.com/bobbercheng/lean-refactor-open/blob/open-final-probe-20261102/final/README.md): `bash setup.sh`, then the required environment step
  `python3 official_run/env_fixes/envfix_auto.py --rows data/official/rows.jsonl` (our box had this edit; see below), then
  `bash run.sh`.
- **Run 1**: package `1d1a31d4`, stopped after about 4 hours (below). It was not uploaded.

Operational notes on runs 1 and 2 (recorded in `final/official_run/` of tag `open-final-probe-20261102`; no code was changed during either run):

- Environment fixes on our box before the first clock started, including an env-side workaround for 5 released rows whose reference
  proof failed in our measured compile (that tag's `final/official_run/env_fixes/NOTES.md`). Run 2's package needs this edit by hand:
  a rerun without it (`envfix.py`) has the same failure on these 5 rows. Run 3's package, in `final/`, makes it in its setup step
  `envfix` ([`final/REPLICATE.md`](final/REPLICATE.md), step 1a).
- **Run 1** (package `1d1a31d4`, 14 concurrent sessions) started at 07:56:49 UTC. Its 14 first sessions started together and reached long
  contexts at the same time, which saturated the vLLM KV cache and cut the server's output to about a third. We stopped five long
  sessions between 09:36 and 10:59 UTC (three by hand, two by an automatic shedder; their rows kept their best proofs) and relaunched run 1 with
  11 sessions at 11:00 UTC. At 11:48 UTC we stopped run 1 (its export, 60 rows, stored mean 44.79, is kept as a record, not uploaded),
  installed package `748d964c`, restarted vLLM and started run 2 from the seed proofs with a new 48-hour clock
  (that tag's `final/official_run/README.md`, "Run 1 and run 2"). In run 2 the KV cache stayed below 75% (no saturation).

## Warm-up results on the public board

| Submission | When | Official score | What |
|---|---|---|---|
| sub19 | 2026-10-31 22:06 UTC | **86.66** (L 74.66, H 85.33, Z 100) | p85 / p85b rehearsal, 23 h from the seed proofs |
| sub18 | 2026-10-31 17:26 UTC | 85.13 | the same rehearsal, earlier |
| sub13 | 2026-10-27 02:53 UTC | 83.31 | the Oct 6-13 A100 line after a model-free end stage (tag `open-warmup-a100-line-20261101`) |
