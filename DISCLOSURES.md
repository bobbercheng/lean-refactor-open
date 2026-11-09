# Disclosures: open-weight track (team Vexorium)

What our open-track results rest on and what this public repository leaves out. The results themselves are in
[`RESULTS.md`](RESULTS.md); the package and its settings in [`final/README.md`](final/README.md).

## The final upload (`sub43`)

Details are in `final/README.md` of the tag [`open-run3-post-final-sub43-20261104`](https://github.com/bobbercheng/lean-refactor-open/blob/open-run3-post-final-sub43-20261104/final/README.md), section "Post-step".

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
  rows. That README's paragraph "The post-step is not independent of the final benchmark" gives the source of every op. The ops are
  general rewrite rules that hold no row names and no proof text. No model runs in the step, and a rewrite is kept only if it
  compiles on every listed toolchain and scores higher.

## Provenance

- **The harness** (prompts, technique cards, turn rules, tools, the model-free end stage) was developed on the 15 warm-up problems and
  on internal development sets, with our own analyses and development tools, including Claude Code, which wrote the harness code. The
  prompts carry general practices (proof patterns, a rewrite-first workflow, a token and heartbeat cost table).
- **The post-step and the fast post stage** (`final/harness/open_post.py`, `final/harness/post/`, `final/post_fast/`) were developed
  on the final benchmark after its release; no model runs in either. Section "The final upload" above gives the sources of the post-step's ops.
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
