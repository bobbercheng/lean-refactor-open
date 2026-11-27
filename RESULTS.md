# Results and runs: open-weight track (team Vexorium)

The record behind the summary in [`README.md`](README.md): our final upload, every upload on the final benchmark, our three official
runs and our warm-up results. The disclosures for these results are in [`DISCLOSURES.md`](DISCLOSURES.md).

## Changes in this version (2026-11-24)

- **The code.** `final/` on `main` is the revised package (tag `open-camready-20261125`). A proof that sets any `debug.*` option is
  rejected at every stage and at export (the option guard: debug options are not allowed in benchmark proofs;
  [`final/README.md`](final/README.md), section "Changes in this version (2026-11-24)"), and an axiom guard at export, added after
  the held-out test below, sets back a proof that uses an axiom beyond the standard ones and its reference proof's. The code of
  `sub43` is the tag `open-run3-post-final-sub43-20261104`. The files changed on 2026-11-24 are listed in `final/README.md`, the
  edits of 2026-11-25 in [`NOTICE.md`](NOTICE.md), section "Changes in this version (2026-11-24)";
  `final/post_fast/MANIFEST.json` gives the sha256 of this version's files, and `final/REVISIONS.json` lists every file of `final/`
  that differs from the export record `final/EXPORT.json`.
- **The revised package, measured.** Section [Revised package, measured (2026-11-24)](#revised-package-measured-2026-11-24) below:
  the revised post stage on the 60 final problems (tier B, measured on this version's code), a re-check of the tier C file, a
  held-out test registered before its run, and the axiom guard on the measured outputs.

## Revised package, measured (2026-11-24)

Labels: (M) measured, (C) computed from measured values, (E) estimate. Times UTC. Every run below used one Azure F80as_v7 VM (AMD
EPYC 9V45, 80 cores, one thread per core); the post stage ran pinned to 64 of its cores. A *stored* score is the one the package's
meter recorded when a proof was adopted. A *fresh read* compiles a proof again on each listed toolchain, prints its axioms (a forced
`#print axioms`) and scores it with the package's own meter. All scores are on our meter, (length % + heartbeat % + toolchain %) / 3
against the row's reference proof; they are not board scores.

**Code.**

| | |
|---|---|
| This version | tag `open-camready-20261125`: the code that ran tier B (2026-11-25), with the axiom guard at export ([`final/README.md`](final/README.md#axiom-guard-at-export-added-2026-11-24-after-the-held-out-test)) and this release's documents and records |
| The post stage | the seven scripts that ran tier B (`final/post_fast/`: `post_stage.sh`, `pf_drive.py`, `pf_svc.py`, `pf_worker.py`, `prefix_backend.py`, `snapshot.py`, `merge_post.py`): fingerprint `b4ac6d42002767a0` (the sha256 of each file, one per line in this order, then the sha256 of those lines, first 16 hex digits; `final/tests/test_axiom_guard.py` recomputes it) (C). The post-step's ops that they run are `final/harness/open_post.py` and `final/harness/post/` |
| Code of 2026-11-24 | tag `open-camready-measured-20261124` (commit `82f6f2d`) ran the held-out test and the earlier tier B run below; tag `open-camready-20261124` (commit `f8f990b`) adds the axiom guard at export (commit `d2d6e3c`), which ran on the outputs below. The seven post-stage scripts are byte-identical at both tags (fingerprint `916734a742e664be`) and differ from this version's only in names, comments, messages and the summary's `--target` default; this version's `final/harness/axiom_guard.py` differs from that tag's only in names and comments. This version's edits of 2026-11-25: [`NOTICE.md`](NOTICE.md), section "Changes in this version (2026-11-24)" |
| Records | [`final/REVISIONS.json`](final/REVISIONS.json): the numbers of this section with the sha256 prefixes of the inputs and outputs, and the sha256 of every file that differs from the export record `final/EXPORT.json`. Not in this repository: the proofs themselves (inputs and outputs), except the tier C file ([`proofs/tier-c/`](proofs/tier-c/README.md)), the held-out test's registration (a commit in our private development repository, not independently timestamped), its 66 rows, the fresh-read verifier and the registered reader. `final/harness/axiom_guard.py` reads axioms the way that verifier does (a forced `#print axioms` of the plain and the namespace-qualified name) |

### Tier B: the revised post stage on the 60 final problems

| | |
|---|---|
| What ran | `post_stage.sh` of this version, once, on 2026-11-25, with an 85-minute cap: 85 min, the cap (M) |
| Input | the picks of our submitted run 3 at 45.25 h, with one problem's proof replaced by the best other proof of that problem from the run's sessions, as in tier A: stored mean 78.7697, sha256 `3043ed87cc1a...`. A fresh read of it (2026-11-24): 78.7789 (M) |
| Output | stored mean **81.4665** (81.47 in the report; from 78.7697, a gain of +2.6968); 57 rows changed, 57 rose, 0 fell; 353 adoptions on 57 rows; sha256 `a065894fec79...` (M) |
| Checks on the output | no line sets a debug option; the axiom guard: 60 of 60 rows pass, nothing set back; the option guard accepts the output (M) |

**The earlier run.** On 2026-11-24 the same stage ran once on the same input, with the same cap on the same
VM, with the code of tag `open-camready-measured-20261124` (above), from 01:58:02 to 03:23:03 (5101 s): stored mean **81.4660**,
a gain of +2.6963; 57 rows changed, 57 rose, 0 fell; 352 adoptions on 57 rows; sha256 `414daf5b2616...`
(M). A fresh read of its output: 81.4651, 60 of 60 rows; the axioms are within `propext`, `Classical.choice` and `Quot.sound` on
the 117 of 127 (row, toolchain) pairs where the forced print runs, and it lists the same 16 items as the fresh read of the input
(section "The tier C file, re-checked" below) (M). The split below comes from that run, and the sections below call its output
"the earlier tier B output".

**Where the gain came from (C).** In this version's run (the table above), the adoptions split by the group of the op that made each one (the groups of
[`DISCLOSURES.md`](DISCLOSURES.md), "Provenance"); a merged adoption whose ops fall in more than one group is "mixed". This is an
attribution by the adopting op, from the stage's own readings at each adoption, not a run without those ops (none was made).

| Group of the adopting op | Ops | Adoptions | Row points | Of the mean | Share |
|---|---:|---:|---:|---:|---:|
| Written after study of closed-model proofs of the final problems | 31 | 254 | 130.53 | 2.18 | 81 % |
| Aggregate statistics of closed-model proofs only | 8 | 62 | 19.81 | 0.33 | 12 % |
| No closed-model origin (`hb_smartunfold`) | 1 | 6 | 1.56 | 0.03 | 1 % |
| Mixed | | 31 | 9.21 | 0.15 | 6 % |

The row points sum to 161.12, 2.685 of the mean, against that run's gain of 2.697 (the rows' stored gains sum to 161.81); the rest
(0.69 row points, 0.012 of the mean) is the difference between the stage's own readings at each adoption, which this split adds up,
and the rows' stored scores (C).

### The tier C file, re-checked

The tier C file is the file of the report's tier C: the submitted file with four problems' proofs taken from a separate chain of
post-step passes (stored mean 81.4367 on our meter; never uploaded or graded). One fresh read (2026-11-24): **81.4217** (81.4223
from scores rounded to 2 decimals), 60 of 60 rows: the compile passes on each listed toolchain, the axioms are within `propext`,
`Classical.choice` and `Quot.sound` wherever the forced print runs, and the meter reads (M). It lists 16 items on 13 rows and
nothing else, the same as the fresh read of tier B's input: the v4.27.0 toolchains of the 10 Strata rows, where the axiom print
cannot run inside a `module` file (their other toolchain reads standard axioms), and 6 pairs of 3 ArkLib rows (v4.30.0 and v4.31.0)
whose passing compile shows a `declaration uses sorry` message of another declaration of the same library file (M). The file
itself is in this repository since 2026-11-24: [`proofs/tier-c/`](proofs/tier-c/README.md) (sha256 `391c880ae869...`; also an
asset of the release `open-camready-20261124`).

### Held-out test, registered before its run

**Registration.** The question, the rows, the subsets, the metric and the pass line were written down and committed in our private
development repository at 02:42 UTC (the commit's time; not independently timestamped), before any start proof of the test was read
on the VM and before the stage was run on these rows. Before registering we had seen one earlier test's results on these rows
(2026-11-23: the pre-release chain's gain, and the gain of other rules run on top of it, +1.59 on the 27 T-primary rows); by that
test's records no op of the post stage had been run on them. One row whose start proof failed the fresh read of the input was
declared not readable in a commit at 03:34:46, before the run started at 03:34:57, as the registration requires. The question: does
the revised post stage raise the score of proofs of problems it was not developed on?

**Rows.** 66 library proofs of 55 lines or more, one row per family, selected from the libraries' sources for one of our tests of
2026-11-23: ArkLib 40, PhysLib 20, Strata 5, CSLib 1; no Mathlib, LeanPool or PutnamBench row. None is a final problem: the
selection left out every file that holds one of 287 rows of our other sets (the 60 final and 15 warm-up problems, and our
development and sealed test rows) and every near-duplicate statement or proof, and a scan for overlap with those rows found none. 14 rows share a folder or a namespace
with a final problem of their library; they are reported apart. Each row lists one toolchain, the newest pin of its library (4
environments, all among the 17 of the final problems, at the same commits), so the toolchain part of the score is 100 by
construction. Every row has a reference proof and reference tokens and heartbeats measured on the VM on 2026-11-23 (M).

| Subset | Rows | Start proof | Start, stored mean | By library | Sharing a folder or namespace with a final problem |
|---|---:|---|---:|---|---:|
| **T-primary** (registered) | 27 | the output of our pre-release zero-cost rewrite chain on the reference proof (that chain had raised these rows by +7.34 on average) | 40.6904 | ArkLib 17, PhysLib 8, Strata 2 | 5 |
| T-other | 9 | the same; these rows finished out of the registered order of that chain's test, so they are not a random sample | 41.2389 | ArkLib 5, PhysLib 2, Strata 1, CSLib 1 | 5 |
| R | 30 | the library's reference proof (33.33 by the package's rule) | 33.3300 | ArkLib 18, PhysLib 10, Strata 2 | 4 |

**Run.** One run of `post_stage.sh` of tag `open-camready-measured-20261124` (its post-stage scripts differ from this version's
only in names, comments, messages and the summary's `--target` default; the axiom guard at export was added after this test), unchanged, on all 66 rows at once, with tier B's
settings (85-minute cap, the same VM pinned to 64 cores); only the rows file and the reference-heartbeats file were the held-out
rows'. It ran on 2026-11-24 from 03:34:57 to 04:59:59 (5102 s): stored mean 37.4195 -> 56.8164, 66 rows changed, 0 fell. A fresh
read of the output: 56.8163 (M).

**Metric and pass line (as registered).** A row's gain is the fresh score of its output minus the fresh score of its start proof
(the meter's exact score rounded to 2 decimals). A row improves when its text changed and its gain is above 0. A row is read when
its start proof and its output both pass the fresh read; two side cases known from tier B (the `module` print and another
declaration's sorry message) do not fail a row. SE: row bootstrap, 2,000 resamples, seed 20261124. On T-primary the line reads
HELD-OUT GAIN SHOWN if the mean gain minus 2 SE is above 0 and at least 10 % of the read rows and at least 4 rows improve, NOT SHOWN
otherwise, and NOT READ if fewer than 20 rows are readable. Any other failure stops the reader with NO VERDICT until its cause is
found and written down.

**Result (M, fresh reads).**

| Group | Rows read (of) | Mean gain | SE | Mean - 2 SE | Improved | Fell | Start -> final |
|---|---|---:|---:|---:|---:|---:|---|
| **T-primary (registered)** | 26 (27) | **+16.70** | 1.55 | **+13.60** | 26 | 0 | 40.85 -> 57.55 |
| T-primary, sharing no folder or namespace with a final problem | 22 (22) | +16.08 | 1.72 | +12.64 | 22 | 0 | 41.29 -> 57.37 |
| T-other | 9 (9) | +13.81 | 2.37 | +9.07 | 9 | 0 | 41.24 -> 55.04 |
| R (start = the library's proof) | 29 (30) | +23.13 | 2.14 | +18.86 | 29 | 0 | 33.35 -> 56.48 |
| All rows | 64 (66) | +19.21 | 1.31 | +16.58 | 64 | 0 | 37.50 -> 56.71 |

**The registered line (T-primary): HELD-OUT GAIN SHOWN.** Only that line gates anything; the other lines are reported.

- **Declared not readable before the run: row 25 (T-primary; ArkLib, `ProximityGap.all_affine_elements_close` in
  `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineSpaces/Basic.lean`).** Its start proof reads `sorryAx` in a compile with no
  sorry message, and so does the library's own reference proof of the same theorem: the theorem rests on a lemma that the library
  proves by `sorry` (M).
- **The reader's NO VERDICT: row 42 (R; ArkLib, `OracleVerifier.simulateLiftContextQueryImpl`, a private theorem in
  `ArkLib/OracleReduction/LiftContext/OracleReduction.lean`).** The registered reader exited NO VERDICT because of one output
  outside T-primary. Row 42 (its start is the library's reference proof, which reads the standard axioms) has an output that
  compiles with no Lean message of any kind and scores 69.21 (from 33.33), but the forced `#print axioms` reads `sorryAx` alone: the
  proof's value is `sorry`, and the output is not a proof (M). The stage adopted 10 steps on this row. The start and steps 1 to 6
  read the standard axioms; step 7, a merge of two ops (two `rewrite` lines removed, one `rw` turned into `simp only`, and the last
  step of a `calc` block removed), and every step after it read `sorryAx` alone (M). The cause: the stage's gate runs the export's
  axiom audit, which reads `#print axioms` and rejects `sorryAx` unless the reference proof reads it too, but skips the print inside
  a Lean `module` file and there checks only for Lean's sorry message. Every held-out row is in such a file (the audit took that
  path on all 66 rows; on the earlier tier B output it read the axioms on every toolchain of 17 rows and skipped the print on at
  least one toolchain of 40, with 3 rows unchanged), so the gate accepted a step that compiles with no error and no sorry message (M). Why
  Lean gave no message was not traced: most likely the failed part of the proof was elaborated to `sorry` under Lean's rule of not
  reporting an error whose message already holds a synthetic `sorry` (E). As registered, the line was read only after this cause
  was written down; row 42 is left out of R's reading (29 of 30), and the registered line does not depend on it.
- **Where the gain came from (C,** the stage's own readings at each adoption, not the fresh read; a merged step is split equally
  over its ops). On T-primary, ops written after study of closed-model proofs of the final problems made 86.5 % of the adopted row
  points, ops from aggregate statistics 11.1 %, and the op with no closed-model origin 2.3 %; over all 66 rows 89.5 %, 8.8 % and
  1.7 %.

**What it shows.** On 26 library problems that the post-step was never developed on, starting from proofs that our pre-release
rewrite chain had already improved, every read row improved, by +16.70 a row on average. On these rows, ops
written after study of closed-model proofs of the final problems made 86.5 % of the adopted row points (attributed to the adopting
op, not a run without them): those ops also raise proofs of problems they were not written on.

**What it does not show.** How much of the post-step's in-sample gain on the 60 final problems would hold on unseen problems of that
kind (+2.24, the post-step's gain in our report: from the job's export, 79.20 (C), to the tier C file, 81.44; tier B above goes
from 78.77 to 81.47 in one run from the earlier picks at 45.25 h):
the final problems' start proofs were the model's output after a 45-hour agent run, at about 79, and these start proofs are at about
41, so there is far more to gain, and the two numbers are not on one scale. It says nothing about model outputs. It covers four libraries (CSLib's one row is not in T-primary), the libraries and pins of 40 of the 60 final
problems, and one toolchain per row. It does not change where the ops came from ([`DISCLOSURES.md`](DISCLOSURES.md),
"Provenance"). On R the stage starts from the reference proof, so its gain there includes what the pre-release chain alone would
have found.

### The axiom guard on the measured outputs

The axiom guard at export of tag `open-camready-20261124` (this version's `final/harness/axiom_guard.py` differs from it only in
names and comments) was run on 2026-11-24 on copies of the outputs above on the same VM, with its defaults unless stated
([`final/README.md`](final/README.md#axiom-guard-at-export-added-2026-11-24-after-the-held-out-test), "Results" and "Cost"). Its
run on this version's tier B output is in the row "Checks on the output" of the section "Tier B" above.

| File | Result (M) |
|---|---|
| The earlier tier B output | exit 0: 60 of 60 rows pass, 117 of 127 readings read the standard axioms and the other 10 are the v4.27.0 toolchains where the print gives no list; no reference proof needed; no row set back; the file unchanged |
| The tier C file (stored 81.4367) | the same: exit 0, 60 pass, the file unchanged. Its first read, right after the cold start in the Time row, left 11 rows not read (exit 3, every row kept) |
| The held-out output (66 rows, stored 56.8164) | exit 0: 65 pass; row 42 reads `sorryAx` alone and is set back to the stage's input on that row (its reference proof), stored 69.21 -> 33.33; row 25 passes only through the allowance (its reference proof reads `sorryAx` too); stored mean 56.8164 -> 56.2727. Written on a copy, only row 42's line changed. On row 42's chain of 10 steps, the start and steps 1 to 6 pass and steps 7 to 10 read bad |
| Time, 60 rows (127 readings) | 41 s (the tier C file) and 51 s (the earlier tier B output, 16 compiles at once) with the files of the Lean environments in memory; on the earlier tier B output with the page cache dropped first, 216 s (48 compiles at once) and 225 s (16), these two with a budget of 1800 s and 900 s per compile (no compile took over 201 s). After the VM was started from a deallocated state, the first read (the earlier tier B output) left 41 of 60 rows not read within the 420 s budget (88 of 127 readings hit the 300 s compile timeout), and the next (the tier C file) left 11 (398 s, 21 timeouts): both exit 3, every row kept (in a job: exit code 5). A later read of the earlier tier B output took 193 s and read every row (exit 0) |

The guard changed no proof of the earlier tier B output or of the tier C file.
These readings, and the fresh reads above, rest on the axiom list Lean prints, which a proof text that registers its own command
handler can make false; a text scan finds no such handler in the proofs read here (M;
[`DISCLOSURES.md`](DISCLOSURES.md), "A limit of the axiom checks, found after publication"), so these readings stand.

### The finer sorry check on `main`, measured (2026-11-25)

After the camera-ready, `main` adds the finer sorry check to the axiom guard and the guard's rule to the post stage's gate (both
on by default; [`final/README.md`](final/README.md), section "On `main` after the camera-ready"). One VM session on 2026-11-25,
judged by criteria written down before the runs, passed all three runs (M): tier B again, 81.4652 (bar 81.4160), no row fell,
nothing set back; the held-out run again, no row set back, every text adopted on row 42 reads the standard axioms, row 42 ends at
68.61 (first run: set back to 33.33); checks on copies, 123 of 123. The reported numbers above are unchanged: they were measured
with the guard and the gate of tag `open-camready-20261125`.

## Final result

Our final open-track upload is
`sub43` (2026-11-04 11:25:51 UTC).

| | |
|---|---|
| Proofs | the export of our official **run 3** (package `246ff1f1`, GLM-5.3-Flash on an on-demand 4 x A100 80 GB SXM4 box, from the seed proofs; started 2026-11-02 06:43:52 UTC, 48 h clock; tier A: 79.20 on our meter, computed from the export with one problem's proof replaced by the best other proof of that problem from the run's sessions), then **seven passes of the post-step** `harness/open_post.py` (development commit `a25416f5`: passes 1-2 `--ops v3`, passes 3-4 `--ops v4`, passes 5-7 `--ops all --long`; CPU only, no model, $0) |
| Upload file | 60 `{"name", "proof"}` lines, sha256 `8d6d1893d315eb0f55491df50046629877d2f89005848862bc8c892dba3f3e5e` |
| Code | the code ZIP we submitted with it, sha256 `1a49b3566a54cf248afe00cd3af3e54d3519736d4ec32fda2a89cb1e2f8ffc4e` = `final/` of the tag [`open-run3-post-final-sub43-20261104`](https://github.com/bobbercheng/lean-refactor-open/tree/open-run3-post-final-sub43-20261104) plus `LICENSE`, `NOTICE.md` and a `ZIP_NOTES.md`. At that tag, 4 post-step files carry redactions in docstrings; the ZIP has them byte for byte |
| Replicate | that tag's [`final/README.md`](https://github.com/bobbercheng/lean-refactor-open/blob/open-run3-post-final-sub43-20261104/final/README.md) (sections "This folder and our code zip" and "Post-step", with "Pass 6" and "Pass 7") and [`final/REPLICATE.md`](https://github.com/bobbercheng/lean-refactor-open/blob/open-run3-post-final-sub43-20261104/final/REPLICATE.md) (step by step, with our numbers) |

The disclosures for this upload are in [`DISCLOSURES.md`](DISCLOSURES.md), section "The final upload": elaborator options on 14
rows, and a post-step developed on the final benchmark.

All our uploads on the 60-problem final benchmark, under username `Vexorium` (the leaderboard shows a team's latest upload):

| Upload | Uploaded (UTC) | What it was |
|---|---|---|
| `sub21` | 11-02 01:57 | probe: run 2's best proofs about 14 h into the run, with run 2's code zip |
| `sub24` | 11-02 18:15 | probe: run 3's best proofs 11.5 h into the run |
| `sub26` | 11-03 06:00 | probe: run 3's best proofs about 23 h into the run |
| `sub28` | 11-03 14:30 | run 2's final export (graded 78.48 by the Arena) |
| `sub29` | 11-03 14:33 | run 2's export after the post-step's first version (5 rows changed) |
| `sub31` | 11-04 01:03 | run 2's export after the post-step's second version, with its code zip |
| `sub33` | 11-04 04:43 | probe: a run 3 snapshot (2026-11-03 23:32 UTC) after the post-step's third version, run twice |
| `sub35` | 11-04 07:31 | run 3's final export after passes 1-2 (third version) |
| `sub36` | 11-04 07:58 | `sub35` plus one `hb_smartunfold` pass |
| `sub37` | 11-04 08:37 | `sub35` plus pass 3 (fourth version) |
| `sub38` | 11-04 08:44 | plus pass 4 (fourth version) |
| `sub39` | 11-04 09:07 | `sub38` plus one `hb_smartunfold` pass |
| `sub40` | 11-04 10:24 | `sub38` plus pass 5 (fifth version, `--ops all --long`) |
| `sub42` | 11-04 10:49 | plus pass 6 (the same command) |
| `sub43` | 11-04 11:25 | plus pass 7 (the same command): **our final upload** |

The run records and the uploaded proof files are not in this repository. The one file of our proofs of the final problems here is the tier
C file, which was never uploaded ([`proofs/tier-c/`](proofs/tier-c/README.md)).

## What this repository holds

**[`final/`](final/README.md)** is the revised package. It builds on the code of our final upload `sub43` (official run 3's
package `246ff1f1` plus the post-step, development commit `a25416f5`) and adds a fast post stage to `run.sh`
([`final/README.md`](final/README.md), first section; [`final/post_fast/MANIFEST.json`](final/post_fast/MANIFEST.json) lists every
changed file). `LRA_POST_ROUTE=off` runs the job without the fast post stage.
The replication of `sub43` itself is the tag `open-run3-post-final-sub43-20261104` (section "Final result"). Run 2's package, which
was `main`'s `final/` until 2026-11-08, is the `final/` of tag [`open-final-probe-20261102`](https://github.com/bobbercheng/lean-refactor-open/tree/open-final-probe-20261102/final).

| Folder | What it is |
|---|---|
| [`final/`](final/README.md) | **The revised package, built on the code of our final upload `sub43` (released benchmark, 60 problems).** The release export of official run 3's package `246ff1f1` (`setup.sh`, `run.sh`, harness, scorer, model-free end stage; `final/EXPORT.json`), the post-step `final/harness/open_post.py` and `final/harness/post/` (from development commit `a25416f5`, with additions that only the fast post stage turns on), the fast post stage in `final/post_fast/`, which `run.sh` runs by default, and the 60 released rows in `final/data/official/rows.jsonl`. [`final/post_fast/MANIFEST.json`](final/post_fast/MANIFEST.json) lists every file that differs from the tag [`open-run3-post-final-sub43-20261104`](https://github.com/bobbercheng/lean-refactor-open/tree/open-run3-post-final-sub43-20261104), the code of our final upload (section "Final result" above). **Run 2's package** (the release export `2dcf255f` of run 2's code `748d964c`), with our run orchestration on a rented vast.ai box (`official_run/`) and the environment fixes we applied on that box (`official_run/env_fixes/`), is the `final/` of the tag [`open-final-probe-20261102`](https://github.com/bobbercheng/lean-refactor-open/tree/open-final-probe-20261102/final); the exact export is the tag `open-run2-exact-748d964c`. |
| [`proofs/tier-c/`](proofs/tier-c/README.md) | **The tier C proof file** (added 2026-11-24): the file the report's tier C counts, the submitted file with four problems' proofs taken from a separate chain of post-step passes (60 proofs, never uploaded or graded), with its sha256 and what was measured on it (on our meter, in sample: the post-step's ops were developed on these problems) |
| [`warmup/`](warmup/README.md) | **The last warm-up rehearsal** (15 warm-up problems, p85 / p85b, Oct 30 to Nov 1): the package export that ran, the scripts that rented, ran, watched and stopped the boxes, and the environment setup. Scripts and configs only, no run outputs. |

The earlier warm-up material (the Oct 6-13 A100 line: run data, trajectories and per-problem state; 82.03, 82.29 with the normalizer
post-pass) is at the tag [`open-warmup-a100-line-20261101`](https://github.com/bobbercheng/lean-refactor-open/tree/open-warmup-a100-line-20261101).

## Our official runs

All three runs started from the seed proofs on the released benchmark. Each ran on its own on-demand 4 x A100 80 GB SXM4 box.

- **Run 3** (the source of our final upload): package `246ff1f1`, started 2026-11-02 06:43:52 UTC with a 48-hour clock. It is run 2's
  package plus the `envfix` setup step, the opt-in automation card (on in our run) and the funind dialect family, without the
  switched-off options. It ran side by side with run 2 on a second box. Its export (2026-11-04 06:03 UTC) gives tier A: 79.20 on our
  meter, computed from the export with one problem's proof replaced by the best other proof of that problem from the run's sessions. To rerun it,
  use the tag's `final/` (section "Final result"); `final/` on `main` is the revised package built on it (`LRA_POST_ROUTE=off` runs
  the job without the fast post stage).
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
