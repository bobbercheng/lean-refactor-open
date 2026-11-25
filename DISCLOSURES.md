# Disclosures: open-weight track (team Vexorium)

What our open-track results rest on and what this public repository leaves out. The results themselves are in
[`RESULTS.md`](RESULTS.md); the package and its settings in [`final/README.md`](final/README.md).

## Changes in this version (2026-11-24)

- **Official result.** Our entry is the runner-up of the open-source track (announced by the organizers on 2026-11-23).
- **Debug options are rejected.** In `final/` on `main`, a proof that sets any `debug.*` option is rejected at every stage (the
  model's check tools, the end stages, every adoption of the post-step and of the fast post stage, the merges) and at export, by
  one guard, `final/harness/option_guard.py` (the option guard): debug options are not allowed in benchmark proofs. A stage that
  reads such a proof from an export or a run stops and names the problems, or replaces each of them by the benchmark's reference
  proof when asked to. Details: [`final/README.md`](final/README.md), section "Changes in this version (2026-11-24)".
- **An axiom guard at export.** In a held-out test of the revised post stage, its gate let through one unsound step; an axiom
  guard at export, added after that test, sets such a row back at export (section "Provenance" below, which also states a limit
  of the axiom checks found after publication). The measurements of the revised package are in
  [`RESULTS.md`](RESULTS.md#revised-package-measured-2026-11-24).
- **The post-step's provenance** is stated in full in section "Provenance" below: how its ops were made, their share of the gain
  in the revised package's runs, and an audit of whether the open model makes the same edits on its own.
- **The sections below** describe the final upload and its code (tag `open-run3-post-final-sub43-20261104`), except where they
  say otherwise.

## The final upload (`sub43`)

Details are in `final/README.md` of the tag [`open-run3-post-final-sub43-20261104`](https://github.com/bobbercheng/lean-refactor-open/blob/open-run3-post-final-sub43-20261104/final/README.md), section "Post-step".

- **Elaborator options on 14 rows.** The op `hb_smartunfold` adds `set_option smartUnfolding false in` and `backward.isDefEq.*`
  options where they save heartbeats.
- **The post-step was developed on the final benchmark** after its release. Most of its ops came from agent sessions of closed
  models (Claude, GPT, Gemini) and from our own censuses, which compared our open proofs with our closed-track proofs of the same
  rows. That README's paragraph "The post-step is not independent of the final benchmark" gives the source of every op. The ops are
  general rewrite rules that hold no row names and no proof text. No model runs in the step, and a rewrite is kept only if it
  compiles on every listed toolchain and scores higher.

## Provenance

- **The harness** (prompts, technique cards, turn rules, tools, the model-free end stage) was developed on the 15 warm-up problems and
  on internal development sets, with our own analyses and development tools, including Claude Code, which wrote the harness code. The
  prompts carry general practices (proof patterns, a rewrite-first workflow, a token and heartbeat cost table).
- **The post-step and the fast post stage** (`final/harness/open_post.py`, `final/harness/post/`, `final/post_fast/`) were developed
  on the final benchmark after its release; no model runs in either. Section "The final upload" above gives the sources of the post-step's ops.
- **The post-step's ops and the final problems (added 2026-11-24).** Labels: (M) measured, (C) computed. Every op of the post-step
  was developed on the 60 final problems after their release, and each was screened on our own outputs for those problems, so its
  gain on them is not free of that work; the result that does not depend on it is the job's export. We classify the ops by what
  their makers had seen (from our audit of who wrote each op; a classification, not a measurement). Of the 40 ops of this version,
  31 were written after study of closed-model proofs of the final problems (3 of them copied from our closed-track entry, 28
  written by agents that compared our open proofs with closed-model proofs of the same problems), 8 come from aggregate statistics
  of closed-model proofs only, and 1 (`hb_smartunfold`) has no closed-model origin. Their share of the adopted row points,
  attributed to the op that made each adoption (not a run without those ops, which was never made): in the revised post stage's
  earlier run on tier B's input (2026-11-24; [`RESULTS.md`](RESULTS.md), section "Tier B"), 81 % for the first group, 12 % for
  aggregate statistics, 1 % for the op with no closed-model origin, and 6 % for merged adoptions whose ops fall in more than one
  group (C); on the 27
  registered rows of the held-out test (T-primary, merged steps split equally over their ops), 86.5 % for the first group, 11.1 %
  and 2.3 % (C). So these rules carry knowledge learned from closed-model proofs of the final problems, and they also raise proofs
  of problems they were not written on ([`RESULTS.md`](RESULTS.md#revised-package-measured-2026-11-24)).
- **Does the open model make these edits on its own? (re-derivation audit, 2026-11-24).** We ran the candidate generators of the
  31 ops of the first group offline, without Lean, on the accepted steps of the open model's sessions in our official runs 2 and 3
  (run 1 was stopped after about 4 hours), and compared. 26 of the 31 have a candidate generator that runs without the compiler (20 fully, 6 in part). For
  18 of them, an accepted step of the model, before any end-stage write-back and outside rows with the automation card or with reads
  of another run's or the end stage's files (the clean steps), equals one of the candidates the op generates for that proof: 109
  edits on 36 problems (M). Over all accepted steps the count is 20 ops (284 edits on 54 problems) (M). For the other 6, no accepted
  step equals such a candidate (for the 6 with a partial generator: none of the candidates that need no compiler). Leaving out the
  6 ops with the most generic candidate sets (each holds at least 10 % of one kind of single deletion of the reference proofs: a
  line, a list item or a token), the two counts are 12 and 14 (M). The remaining 5 ops take their text from the compiler and cannot
  be tested this way; for 4 of them the model made an edit of the same shape (M). The model makes edits of these kinds; this does
  not show that the ops could have been written without the closed-model proofs.
- **One unsound adoption; the axiom guard at export sets such a row back (2026-11-24).** The post stage's gate runs the export's
  axiom audit, but inside a Lean `module` file that audit skips the axiom print and checks only for Lean's sorry message. Every
  held-out row is in such a file, so there the gate's only check for `sorry` was the sorry message. In the held-out test it
  adopted, on one row outside the registered subset (row 42, whose start was the library's reference proof), a step after which
  the proof's value is `sorry` with no Lean message: the forced `#print axioms` reads `sorryAx` alone (1 of 66 rows) (M). The full
  re-check of the tier C file reads only the standard axioms wherever the axiom print runs (M). The axiom guard at export, added
  after the test
  ([`final/README.md`](final/README.md#axiom-guard-at-export-added-2026-11-24-after-the-held-out-test)), reads every exported
  proof's axioms and sets a failing row back to its newest earlier proof that passes; run on a copy of the held-out output, it set
  that row back (stored 69.21 -> 33.33) and changed no other row; run on the earlier tier B output and on the tier C file, it
  changed no proof (M; [`RESULTS.md`](RESULTS.md), section "The axiom guard on the measured outputs", which also gives its run on
  this version's tier B output). The gate itself is unchanged: within a run the stage can still build on such a step, and the export sets the row back. A row
  the guard cannot read in time keeps its proof (the job then ends with exit code 5), and on a toolchain where the reference proof
  itself reads `sorryAx` the guard cannot tell a proof whose own value became `sorry` from one that only uses the library's.
- **A limit of the axiom checks, found after publication (2026-11-24).** A proof text that registers its own Lean command handler can make the axiom list that
  `#print axioms` shows false. The axiom guard at export reads that list, and so do the export's axiom audit and the post stage's
  gate where they run the print (outside Lean `module` files; inside them they read only the sorry message, as the bullet above
  says). The package's checks reject some such texts but not every one. A proof whose unsound part draws no `sorry` message from
  Lean (for example one that rests on a lemma of the library proved by `sorry`, or a value that became `sorry` with no Lean message,
  held-out row 42's fault) could then pass all three. Only the printed list is false: in the case we confirmed, Lean accepted the
  proof, `sorryAx` being an axiom. We found this in an adversarial review of further checks we are
  building and confirmed it on one local compile (a plain file, Lean v4.31.0): the published parser reads a standard axiom alone
  from its messages and the published checks accept the text (M); that the guard, the audit and the gate then pass it follows
  from their code (C). A text scan for the forms that register an elaborator, macro, parser or other hook (the hook test of a check
  not yet published) finds none in the 498 proof texts (414 distinct) of eight files (M): the tier C file, the upload `sub43`, tier
  B's input and the earlier tier B output (2026-11-24; [`RESULTS.md`](RESULTS.md), section "Tier B"), the held-out run's input and
  output, and the reference proofs of the 60 final and the 66 held-out problems. So no reading or score reported for these files changes. A check that rejects such texts is not in tag
  `open-camready-20261125` or in the release `open-camready-20261124`. Since 2026-11-25 `main` has one, on by default: the hook
  check of the finer sorry check and of the post stage's gate audit ([`final/README.md`](final/README.md), section "On `main` after
  the camera-ready"). It reads text, so a hook form it does not know is not caught.
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
- **Run operations** (rentals, environment setup, monitoring, the interventions in [`RESULTS.md`](RESULTS.md), section "Our official runs") were supervised by Claude Code; it wrote no
  proofs and changed no prompt or harness code during a run.

## Removed for public release

Credentials and private values (the vLLM bearer key, TLS pairs, the bucket key, the Kaggle key, the
vast.ai CLI configuration, the private push-notification topic) are not in this repository; the scripts read them from
`~/.config/vexorium/` and from files you create (see `final/official_run/README.md` of tag `open-final-probe-20261102`). A since-rotated push topic was in an earlier
version of one script; since 2026-11-09 it is in none of this repository's files or commits ([`NOTICE.md`](NOTICE.md), "History replaced (2026-11-09)"). Our operation diaries (rentals, bids, credit and host details) stay in our private development repository.
[`NOTICE.md`](NOTICE.md) lists every edit made for public release and what was kept.
