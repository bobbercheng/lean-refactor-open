# Replicating our open-track upload: run 3 + post-step

This folder is the code of our official run 3 (package commit `246ff1f1`) plus the post-step (`harness/open_post.py`, development
commit `5cb18d3b`) that our upload of this run's output goes through. To replicate that file: set up this folder (step 1; its `envfix`
step makes the environment fix, step 1a), run the 48 h job with our run's recipe (step 2), run the post-step on the job's output (step
3), and check the file (step 4). Our own numbers are in "How our run compares".

This page puts the commands of `README.md` in order (its sections "Quick start", "Step 1", "Step 2", "If the job is cut short" and
"Post-step"), with what each one prints at its end, its wall time and its cost. Run every command from this folder (the one that holds
`setup.sh` and `run.sh`), as the same user and at the same absolute path for every step: the Lean environments are git worktrees that
record absolute paths. `README.md` stays the reference for every setting.

## Overview

| step | command | ends with | wall | cost |
|---|---|---|---|---|
| 0 | `sha256sum data/official/*.jsonl` | the two values in step 0 | seconds | - |
| 1 | `bash setup.sh` | `SETUP OK: next, the job: bash run.sh ...` | 1.5-3 h | needs the internet; node time |
| 1a | (part of step 1: setup's `envfix` step) | a setup line `envfix: ENVFIX DONE fixed 5, unchanged (reference ok) 2, not fixed 0; ...` | 1-3 min | - |
| 2 | `LRA_EXTRA="--automation-card on --automation-card-min-ref-tokens 1000" bash run.sh` | `DONE: .../runs/final/proofs.jsonl (60 rows); ...` | the 48 h job clock | node time; no hosted model, no API key, no internet |
| 3 | the post-step, then `upload.jsonl` | `[post] done: ... -> runs/post/proofs.post.jsonl` | about 27 min on our run-2 box; at most 7,200 s plus one row's 2,400 s | $0: CPU only, no model, no GPU, no internet |
| 4 | the check of the upload file | `UPLOAD FILE OK` | seconds | - |

**The file to upload is `runs/post/upload.jsonl`** (step 3): one `{"name", "proof"}` line per row, in the rows file's order.

## Prerequisites

From the README's section "Requirements" (it has the details):

- One node with 4 x A100 80 GB SXM and NVLink, 64 or more CPU cores and 256 GB RAM.
- About 400 GB of disk on the filesystem that holds this folder (the model is 191 GB).
- A container runtime with NVIDIA GPU access: podman-hpc, Shifter, Apptainer/Singularity or Docker. `setup.sh` takes the first one
  present; `LRA_RUNTIME` chooses one. Without any, see the README's section "No container runtime".
- bash 4 or newer, coreutils, git, curl, tar, sha256sum; Python 3.11 or newer with `requests` (setup makes a venv when the system
  Python is older). No root.
- The internet during setup only (GitHub, the Mathlib cache, Hugging Face, Docker Hub). The job, the post-step and the check make no
  outbound connection. No API key and no hosted model is used anywhere.

**Our box.** Our run 3 ran on an on-demand vast.ai box: 4 x A100 80 GB SXM4, 76 CPUs, 420 GB disk, at $4.504 per hour (a 48 h job:
about $216 of node time at that price). Our run was not started through `setup.sh` / `run.sh`: our own rental orchestration (not in
this folder) built the environments, served the model with this package's server script `infra/vast/run_vllm.sh` (max-num-seqs 16, as
`run.sh` starts it), and started the driver `harness/open_package.py run` with the flags quoted in the README's section "This folder
and our code zip". `run.sh` with the `LRA_EXTRA` of step 2 starts the same driver with the same flags.

## Step 0: the data files

`data/official/rows.jsonl` (the 60 released rows) and `data/official/heartbeats.jsonl` (the reference heartbeats our run used) are
already in this folder. With both in place, `setup.sh` and `run.sh` take them without arguments, and setup uses the heartbeats as they
are (its refhb step, which would measure them, does not run).

```bash
sha256sum data/official/rows.jsonl data/official/heartbeats.jsonl
# d53690b057f9972f44643678ee6b5eee7a66f56e1a7d2678a2e5ff47fadbd682  data/official/rows.jsonl
# 2d777f145d0c4bf0fe66c4825b0fb590b57be75c0aa2ebec9e20f9ddcd56688b  data/official/heartbeats.jsonl
```

To use your own copy of the released rows, put it at `data/official/rows.jsonl` (the same sha256 means the same file). Without a
heartbeats file, setup measures the reference heartbeats on your node (README, "Step 1", refhb) and the job scores against those
values instead of ours.

## Step 1: setup (once, before the job)

```bash
bash setup.sh
```

- It prints one line per step and ends with `SETUP OK: next, the job: bash run.sh (settings in <this folder>/.lra/setup.env)`. On a
  failure it prints `FAILED: ...` and the log to read; a re-run keeps finished work and continues.
- 1.5-3 h (README): the image (5-20 min), the model (6-30 min), the Lean environments (40 min-2 h), the self-check, and on a GPU node
  one offline start of the server (~16 min). The README's table "Step 1" lists every step.
- Best on the GPU node. If setup ran on a node without GPUs, run `bash run.sh check` once on the GPU node, in an allocation like the
  job's: it ends with `CHECK OK` or lists everything that would stop the job.
- `.lra/setup.env` records what setup chose (Python, Lean, rows, heartbeats, model snapshot); `run.sh` and the commands below read it.

## Step 1a: the environment fix (part of setup)

Five released rows have their declaration under a chain of `... in` lines (`omit`, `set_option`, `open`). In the package's measured
compile that chain binds to the heartbeat-measuring command instead of the theorem, so the reference proof and every candidate on
those rows would fail. This package's setup has a step `envfix` (`infra/refhb/envfix.py`; README, "Step 1") that compiles the
reference of every row with such a chain, removes the chain's trailing ` in` in the environment's copy of the row's file where the
reference fails (every toolchain pin, line count unchanged), checks again, and undoes an edit that does not help. Nothing to run by
hand; check its line in setup's output:

```
envfix: ENVFIX DONE fixed 5, unchanged (reference ok) 2, not fixed 0; backups in ...
```

That is the line the same code printed on the 60 released rows on our run-3 box. The full log is `.lra/logs/setup-envfix.log`;
`LRA_SKIP=envfix` would skip the step (do not, for a replication). A re-run of setup restores the edited files before it builds the
environments and edits them again.

## Step 2: the job (48 h)

```bash
LRA_EXTRA="--automation-card on --automation-card-min-ref-tokens 1000" bash run.sh
```

- `run.sh` takes the job clock first, checks the node (the preflight that `bash run.sh check` runs alone), starts the vLLM server in
  the pinned image (~16 min, on the clock), then runs the driver `harness/open_package.py run` until the clock's end; the export of
  the best proof per row runs in the last 15 min. The clock is 48 h minus a 10 min margin (README, "Step 2", Clock), and never longer
  than a Slurm allocation.
- It ends with `DONE: <this folder>/runs/final/proofs.jsonl (60 rows); summary <this folder>/runs/final/summary.json` and exit code 0.
- `runs/final/RUN_CMD` holds the exact driver command; `LRA_DRY=1 LRA_EXTRA="--automation-card on --automation-card-min-ref-tokens
  1000" bash run.sh` prints the server and driver commands without starting anything.
- Every hour `runs/final/interim/proofs.jsonl` holds the bests so far (same format).
- A test before the real job uses its own output directory: `LRA_OUT=runs/test LRA_JOB_SECONDS=3600 LRA_EXTRA="--automation-card on
  --automation-card-min-ref-tokens 1000" bash run.sh`.
- `LRA_EXTRA` adds our run's two automation-card flags to the package defaults (README, section "This folder and our code zip", "Our
  run's command"); every other flag of our run is a package default. Without it, `bash run.sh` runs the package's own default recipe
  (the card off), not our run's.
- Under Slurm: the README's section "Under Slurm", with `export LRA_EXTRA="--automation-card on --automation-card-min-ref-tokens
  1000"` in the batch script before the `exec bash /path/to/package/run.sh` line.

## Step 3: the post-step and the upload file

After `run.sh` has printed `DONE`, from this folder: the commands of the README's section "Post-step" (paragraph "Run it"), unchanged.

```bash
. .lra/setup.env && export ELAN_HOME     # the Python, Lean toolchains, rows and heartbeats that setup.sh chose and run.sh used
FAST=$("$LRA_PYTHON" infra/orgserver/orgtools.py fastdir) && export LRA_MEMGATE_DIR=$FAST LRA_LOCK_DIR=$FAST/locks   # as run.sh: node-local locks
mkdir -p runs/post
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/final/proofs.jsonl --out runs/post --jobs 60
"$LRA_PYTHON" -c 'import json,sys; [print(json.dumps({"name": r["name"], "proof": r["proof"]}, ensure_ascii=False)) for r in map(json.loads, open(sys.argv[1]))]' \
    runs/post/proofs.post.jsonl > runs/post/upload.jsonl
```

- The step reads `runs/final/proofs.jsonl` and never writes it. It logs one line per row it works on and ends with `[post] done: N
  row(s) adopted, paired gain +G, stored mean A -> B, C compiles, S s -> runs/post/proofs.post.jsonl`.
- Outputs in `runs/post/`: `proofs.post.jsonl` (one line per row; an unchanged row keeps its input line byte for byte),
  `post_report.json` (per row: status, readings before and after, ops), `post/rows.jsonl` and `post/decisions.jsonl`, and, from the
  second command, `upload.jsonl`: the file to upload.
- Wall: About 27 min for the first version of this step (`5cb18d3b`) on our run 2's export, on that run's box with 64 compile slots
  (1,596 s); a row stops at its 2,400 s (plus the compile in flight), the step at 7,200 s. It needs no key, no model and no GPU.
  `LRA_HBTOOL_SLOTS` is the number of Lean compiles at once (the command above uses 32; we used 64 on our box).
- Cost: $0 (CPU only). The README's section "Post-step" describes the ops, the accept gate and the `debug.skipKernelTC` option the
  step can add.
- No model runs in the step, so the same input gives the same candidates; the accept decisions use Lean heartbeat readings, which can
  differ by a few heartbeats between runs and machines. A row that reaches its 2,400 s (`--row-seconds`) keeps its input line, so a
  much slower node can change fewer rows.

## Step 4: check the upload file

```bash
. .lra/setup.env
"$LRA_PYTHON" - "$LRA_SETUP_ROWS" runs/post/upload.jsonl <<'PY'
import json, sys
sys.path.insert(0, ".")
from scorer.forbidden import check_forbidden
from scorer.tokenize import split_declaration
rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
up = [json.loads(l) for l in open(sys.argv[2]) if l.strip()]
print(len(up), "lines for", len(rows), "rows")
assert [u["name"] for u in up] == [r["name"] for r in rows], "not one line per row in the rows file's order"
assert all(sorted(u) == ["name", "proof"] for u in up), "a line is not {name, proof}"
bad = [r["name"] for r, u in zip(rows, up) if split_declaration(u["proof"], r["statement"]) is None]
assert not bad, f"does not start with the row's exact statement and ':=': {bad}"
hits = [(u["name"], check_forbidden(u["proof"])) for u in up if check_forbidden(u["proof"])]
assert not hits, f"the package's forbidden-construct check (scorer/forbidden.py): {hits}"
print("UPLOAD FILE OK")
PY
grep -c 'debug.skipKernelTC' runs/post/upload.jsonl    # rows whose proof skips the kernel check (README, "About debug.skipKernelTC")
```

Expected: `60 lines for 60 rows`, then `UPLOAD FILE OK`. The count depends on the job's proofs: the post-step adds the option only in
front of a closing `decide +kernel`, and run 3's own model wrote one such proof during the run (README, "About `debug.skipKernelTC`").
The check needs no Lean: the job and the post-step already compiled every proof on every listed toolchain.

## How our run compares

**Run 3's numbers: pending.** Run 3's 48 h job clock ends 2026-11-04 06:43:52 UTC, after this version of this page was written: the
sha256 and stored mean of its export, the post-step's result on it and the Arena's score of the upload are not in this folder. Run 3
started from the seed proofs on 2026-11-02 06:43:52 UTC with the flags of step 2.

| file | run 3 (this package) | for comparison: our run 2 (package `748d964c`, the same rows and reference heartbeats, no automation card) |
|---|---|---|
| `runs/final/proofs.jsonl` (the job's export) | pending | sha256 `e64b53ee9a699e1e...`; stored mean 78.4585; Arena 78.48 |
| `runs/post/upload.jsonl` (after the post-step `5cb18d3b`) | pending | sha256 `4c9dc38a078b763a...`; stored mean 79.7167 (5 rows changed); Arena 79.74 |

**What to expect from a rerun.** The job's sessions sample the model: the package sets no sampling temperature and no seed (the
model's and the server's defaults apply), and several sessions share the GPUs and the job clock. A rerun's proofs therefore differ
from ours row by row, and the sha256 values above identify our files, not a rerun's. For scale: our official runs 2 and 3 (the same
rows and reference heartbeats, near-identical packages) were 1.13 points apart in the 60-row stored mean at the same elapsed time
(22.85 h, our meter; run 3 ahead on 36 rows and behind on 22; 0.65 points without the one row on which run 3's model wrote a
kernel-skipped proof). The post-step runs no model (step 3).

## If the job is cut short

From the README's section "If the job is cut short":

- `runs/final/proofs.jsonl` is written by the export in the last 15 min of the clock. If the job is stopped earlier, `run.sh` traps
  `SIGTERM` / `SIGINT`: it writes the interim proofs, copies them to `runs/final/proofs.jsonl` unless the export already wrote that
  file, and stops the driver, its sessions and the server.
- `runs/final/interim/proofs.jsonl` always holds the bests as of the last hour.
- `LRA_EXTRA="--automation-card on --automation-card-min-ref-tokens 1000" bash run.sh export` writes `runs/final/proofs.jsonl` from
  everything the job saved (with the axiom audit of each pick, for at most a few minutes once the clock has run out).
- To continue the same run: inside the same Slurm job, the same command as in step 2 (it continues the clock in `runs/final`; each row
  resumes from its saved state); in a NEW job, `LRA_RESUME=1` in front of it (the same clock, ending no later than the new
  allocation). Without `LRA_RESUME=1` a new job moves `runs/final` aside to `runs/final.prev-<start>` and starts over. Keep the same
  `LRA_EXTRA` on every one of these commands.
- Then run steps 3 and 4 on whatever `runs/final/proofs.jsonl` holds: the post-step takes any export of the job.
- Without the post-step, the `{"name", "proof"}` lines of `runs/final/proofs.jsonl` are the upload (README, "Post-step", "To disable
  it"):

```bash
. .lra/setup.env
"$LRA_PYTHON" -c 'import json,sys; [print(json.dumps({"name": r["name"], "proof": r["proof"]}, ensure_ascii=False)) for r in map(json.loads, open(sys.argv[1]))]' \
    runs/final/proofs.jsonl > runs/final/upload.jsonl
```

- If the post-step itself is stopped, it has not written `proofs.post.jsonl` (it writes that file once, at its end): run step 3 again,
  with a new `--out` directory (e.g. `runs/post2`, and `runs/post2/...` in the second command). `--seconds` shortens its wall.

