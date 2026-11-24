# Lean Refactor Arena: open-weight track (team Vexorium)

This is our entry (username `Vexorium`) in the open-source LLM track of the
[Lean Refactor Arena](https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena), a NeurIPS 2026 VERICODEGEN workshop
competition. The task is to rewrite each benchmark problem's Lean proof so that it is shorter and cheaper to check, while it still
compiles on every listed toolchain.

One open-weight model writes every proof: GLM-5.3-Flash (AWQ W4A16), served with vLLM on 4 x A100 80 GB. It runs many short, resumed,
tool-using sessions per problem. Model-free CPU stages then search mechanical rewrites of each problem's best proof. Every replacement
passes one gate: the exact statement, no forbidden pattern, no `set_option debug.*` option, no `sorry` message, a compile on no fewer
listed toolchains than the current proof, and a higher score on our meter. A proof can rest on `sorry` without any message; since
2026-11-24 an axiom guard at export reads every exported proof's axioms (section "Changes in this version (2026-11-24)" below). No
hosted model is called during a run, and no model was trained or fine-tuned.

**Official result:** runner-up of the open-source track (announced by the organizers on 2026-11-23). Our final upload `sub43`
scored **82.55** (L 65.60, H 82.06, Z 100) on the open-track leaderboard at the deadline (2026-11-04 11:59 UTC). That score includes
four proofs that are not kernel-checked, and one of the four is not a valid proof with the kernel check on (section "Changes in this
version (2026-11-24)" below).

![Figure 1: the submitted pipeline](docs/figure1.png)

*Figure 1 (from our report): the submitted pipeline with the agent stage opened up (hours from clock start; not to scale). Means are
current bests in the run's trace, polished bests included. Flat: last 3 sessions without gain.*

- **Report:** [OpenReview](https://openreview.net/forum?id=cvXHNZWtn8) ([PDF](https://openreview.net/pdf?id=cvXHNZWtn8)).
- **Code of the final upload:** tag
  [`open-run3-post-final-sub43-20261104`](https://github.com/bobbercheng/lean-refactor-open/tree/open-run3-post-final-sub43-20261104).
- **Code of this version (2026-11-24):** tag
  [`open-camready-20261124`](https://github.com/bobbercheng/lean-refactor-open/tree/open-camready-20261124) (the published code,
  with the axiom guard; its release holds a ZIP of `final/`). The code we measured on 2026-11-24 is tag
  [`open-camready-measured-20261124`](https://github.com/bobbercheng/lean-refactor-open/tree/open-camready-measured-20261124)
  (commit `82f6f2d`).
- **Results, all uploads and our official runs:** [`RESULTS.md`](RESULTS.md). **Disclosures:** [`DISCLOSURES.md`](DISCLOSURES.md).

## Changes in this version (2026-11-24)

- **The kernel-skip operator is removed.** The post-step's op `kskip` put `set_option debug.skipKernelTC true in` in front of a
  closing `decide +kernel`. It is gone from the post-step and from the fast post stage: no op order, mode or flag runs it.
- **Proofs that set a debug option are rejected at every stage and at export.** One guard, `final/harness/kernel_guard.py`, rejects
  any proof text with a `set_option debug.*` option. It runs wherever a proof can become a problem's best or be written out: the
  model's check tools in the agent stage (the candidate is refused, and the model reads that the option disables kernel checking and
  is not allowed), the model-free end stages and their write-back, every adoption of the post-step and of the fast post stage, the
  merges, and the export. The export stops and names the problem if such a proof reaches it. Elaborator options such as
  `smartUnfolding` and `backward.isDefEq.*` are not affected: the kernel still checks the proof with them.
- **Inputs from the earlier version.** A stage that reads a proof with a debug option (an earlier export, or the saved state of an
  earlier run) stops and names the problems. `LRA_DEBUG_ROWS=reference` replaces each such proof by the benchmark's reference proof
  before the stage starts.
- **Why.** The option disables the kernel's check of the declaration, so a proof that carries it is not a verified proof. Four
  proofs of our competition submission `sub43` carry it, and one of the four is not a valid proof with the check on. The Arena
  submission itself cannot be changed.
- **What describes the earlier version.** The tag `open-run3-post-final-sub43-20261104` stays the code of `sub43`. The text about
  how `sub43` was made ([`RESULTS.md`](RESULTS.md), [`DISCLOSURES.md`](DISCLOSURES.md), the section "Post-step" of
  [`final/README.md`](final/README.md), [`final/REPLICATE.md`](final/REPLICATE.md)) describes that version; with this version's
  code those commands do not reproduce `sub43`.
- **An axiom guard at export (added after the held-out test below).** At the end of the job and in `run.sh export`,
  `final/harness/axiom_guard.py` compiles every problem's proof on its listed toolchains with `#print axioms` forced. A proof that
  shows Lean's sorry message on its declaration, or uses an axiom beyond `propext`, `Classical.choice`, `Quot.sound` and those of
  the problem's reference proof on the same toolchain (such as `sorryAx`), is set back to the problem's newest earlier proof that
  passes. Details: [`final/README.md`](final/README.md#axiom-guard-at-export-added-2026-11-24-after-the-held-out-test).
- **Measured (2026-11-24; (M) measured, (C) computed).** Details in [`RESULTS.md`](RESULTS.md#revised-package-measured-2026-11-24).
  - *The revised post stage on the 60 final problems (tier B).* One 85-minute run on the submitted run's picks, with the one
    kernel-skipped proof the model wrote replaced by the run's best kernel-checked proof of that problem: stored mean 81.47 from
    78.77 (M). A fresh read of all 60 output proofs with the kernel on: 81.47, 60 of 60 pass, only the standard axioms wherever the
    axiom print runs (M). No output proof sets a `debug.*` option.
  - *A held-out test, registered before its run.* The same stage, one 85-minute run on 66 library problems it was never developed
    on. On the 27 registered problems (start proofs from our pre-release rewrite chain; 26 read), the mean gain with the kernel on is
    +16.70 a proof (SE 1.55; 40.85 -> 57.55), all 26 improved and none fell: HELD-OUT GAIN SHOWN (M). These start proofs are much
    weaker than the final problems' (40.85 against 78.77), so the test does not say how much of the in-sample gain would hold. The
    registered reader stopped with NO VERDICT on one output outside the registered problems: the stage adopted a step after which
    that proof's value is `sorry`, with no Lean message. The axiom guard above sets such a row back at export; run on that output,
    it set the row back. The stage's gate itself is unchanged, a row the guard cannot read in time keeps its proof (the job then
    ends with exit code 5), and on a problem whose reference proof itself rests on a library lemma proved by `sorry`, the guard
    cannot tell such a proof from one that only uses that lemma
    ([`final/README.md`](final/README.md#axiom-guard-at-export-added-2026-11-24-after-the-held-out-test)).
  - *Measured code and published code.* The measured code is tag `open-camready-measured-20261124` (commit `82f6f2d`); the
    published code is tag `open-camready-20261124`, which adds the axiom guard. The seven post-stage scripts are byte-identical at
    both tags (fingerprint `916734a742e664be`) (C), and the axiom guard, run on the measured output, changed no proof: 60 of 60 pass
    (M).

The details, the files changed and the tests are in [`final/README.md`](final/README.md), section "Changes in this version
(2026-11-24)"; [`final/REVISIONS.json`](final/REVISIONS.json) lists every change after the export the package was built from.

## Run it on the full benchmark (60 problems)

The package is [`final/`](final/README.md). The 60 released problems and their reference heartbeats are already in it, in
`final/data/official/`.

**What you need**

- One node with 4 x A100 80 GB SXM and NVLink, 64 or more CPU cores, 256 GB RAM, and about 400 GB of disk (the model is 191 GB).
- A container runtime with NVIDIA GPU access: podman-hpc, Shifter, Apptainer/Singularity or Docker.
- bash 4 or newer, coreutils, git, curl, tar, sha256sum, and Python 3.11 or newer with `requests`. No root is needed.
- Internet during setup only. The job makes no outbound connection. No API key and no hosted model is used.

**Commands** (run every step as the same user, at the same absolute path)

```bash
git clone https://github.com/bobbercheng/lean-refactor-open.git
cd lean-refactor-open/final
sha256sum data/official/rows.jsonl   # d53690b057f9972f44643678ee6b5eee7a66f56e1a7d2678a2e5ff47fadbd682 (the 60 released rows)

bash setup.sh   # once, before the job: needs the internet, takes 1.5-3 h, ends with "SETUP OK"

# The 48 h job with our run's recipe (the package defaults plus the automation card).
# It ends with "DONE: .../runs/final/proofs.jsonl (60 rows)".
LRA_EXTRA="--automation-card on --automation-card-min-ref-tokens 1000" bash run.sh

# The upload file: one {"name", "proof"} line per problem, in the rows file's order.
. .lra/setup.env
"$LRA_PYTHON" -c 'import json,sys; [print(json.dumps({"name": r["name"], "proof": r["proof"]}, ensure_ascii=False)) for r in map(json.loads, open(sys.argv[1]))]' \
    runs/final/proofs.jsonl > runs/final/upload.jsonl
```

- **The fast post stage.** On `main`, `run.sh` runs our fast post stage inside the job by default, in place of the end stage, so
  `runs/final/proofs.jsonl` is already the post-processed output. No 48 h job has run this route yet. `LRA_POST_ROUTE=off` in front of
  the `run.sh` command runs the job as at the final upload's tag, with the kernel guard of 2026-11-24 (section above).
- **Cost.** Node time only: setup plus the 48 h job. Our run 3 used an on-demand 4 x A100 80 GB SXM4 box at $4.504 per hour, so the job
  was about $216 of node time.
- **To replicate `sub43` itself.** Use the tag `open-run3-post-final-sub43-20261104`: the same setup and job, then seven passes of the
  model-free post-step on the job's output (about 282 min, CPU only, $0). That tag's
  [`final/REPLICATE.md`](https://github.com/bobbercheng/lean-refactor-open/blob/open-run3-post-final-sub43-20261104/final/REPLICATE.md)
  gives every command, its expected output and our numbers.
- **More detail.** [`final/README.md`](final/README.md) covers Slurm, the container runtimes, every setting, test runs, and what to do if
  the job is cut short. [`final/REPLICATE.md`](final/REPLICATE.md) gives the steps in order, with wall times, and a check of the upload
  file.

## Documents

| Document | What it holds |
|---|---|
| [`RESULTS.md`](RESULTS.md) | the final upload (proof file and code ZIP hashes), every upload on the final benchmark, our three official runs, our warm-up results, what each folder and tag holds, and the revised package's measurements of 2026-11-24 (tier B, the tier C re-check, the held-out test, the axiom guard) |
| [`DISCLOSURES.md`](DISCLOSURES.md) | the final upload's kernel skip on 4 rows (one of them is not a valid proof with the kernel check on) and elaborator options on 14 rows; how the post-step and the harness were developed, the post-step's provenance and its share of the gain; isolation; what was removed for public release |
| [`final/README.md`](final/README.md) | the package reference: requirements, setup, the job, every setting, the fast post stage, and the post-step and its ops |
| [`final/REPLICATE.md`](final/REPLICATE.md) | step-by-step replication, with expected output, wall time and cost per step, and our own numbers |
| [`final/docs/open_package_readme.md`](final/docs/open_package_readme.md) | the package's technical appendix: stages, flags and measurements |
| [`warmup/README.md`](warmup/README.md) | the last warm-up rehearsal (15 warm-up problems, Oct 30 to Nov 1): the package that ran and its scripts |
| [`NOTICE.md`](NOTICE.md) | third-party material and its terms, and every edit made for public release |
| [Report](https://openreview.net/forum?id=cvXHNZWtn8) | our technical report on OpenReview |

## License

Our code, notes and run records are licensed under the [PolyForm Noncommercial License 1.0.0](LICENSE): free for study, research and
other noncommercial use. **Commercial use needs a separate license**: contact b.cheng@vexorium.net. Third-party material (upstream
Lean library sources, competition data, model outputs, the model checkpoint) keeps its own terms; see [`NOTICE.md`](NOTICE.md).
