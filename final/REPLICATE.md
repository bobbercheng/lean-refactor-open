# Replicating our open-track upload: run 2 + post-step

Our open-track upload is the output of our official run 2 (package commit `748d964c`, this folder's code) after the post-step
(`harness/open_post.py`, development commit `5cb18d3b`). To replicate it: set up this folder (step 1), make the environment fix our
run's box had (step 1a, required), run the 48 h job (step 2), run the post-step on the job's output (step 3), and check the file (step
4). Our own numbers for each file are in "How our run compares".

This page puts the commands of `README.md` in order (its sections "Quick start", "Step 1", "Step 2", "If the job is cut short" and
"Post-step"), with what each one prints at its end, its wall time and its cost. Run every command from this folder (the one that holds
`setup.sh` and `run.sh`), as the same user and at the same absolute path for every step: the Lean environments are git worktrees that
record absolute paths. `README.md` stays the reference for every setting.

## Overview

| step | command | ends with | wall | cost |
|---|---|---|---|---|
| 0 | `sha256sum data/official/*.jsonl` | the two values in step 0 | seconds | - |
| 1 | `bash setup.sh` | `SETUP OK: next, the job: bash run.sh ...` | 1.5-3 h | needs the internet; node time |
| 1a | the environment fix: `official_run/env_fixes/envfix_auto.py` (REQUIRED) | `ENVFIX DONE fixed 5, unchanged (reference ok) 2, not fixed 0; ...` | a few minutes | node time |
| 2 | `bash run.sh` | `DONE: .../runs/final/proofs.jsonl (60 rows); ...` | the 48 h job clock | node time; no hosted model, no API key, no internet |
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

**Our box.** Our run 2 ran on an on-demand vast.ai box: 4 x A100 80 GB SXM4, 128 CPUs, 500 GB disk, at $6.028 per hour (the 47.41 h
job: about $286 of node time at that price). The post-step ran on the same box after the job. Our run was not started through
`setup.sh` / `run.sh`: our own rental orchestration (not in this folder) built the environments, served the model with this package's
server script `infra/vast/run_vllm.sh` (max-num-seqs 16, as `run.sh` starts it), and started the driver `harness/open_package.py run`
with the recipe flags quoted in the README's section "This folder and our code zip". `run.sh` starts the same driver with the same
flags (the package defaults).

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

## Step 1a: the environment fix (required for this package)

Five released rows have their declaration under a chain of `... in` lines (`omit`, `set_option`, `open`). In this package's measured
compile that chain binds to the heartbeat-measuring command instead of the theorem, so the reference proof and every candidate on
those rows fail ([`official_run/env_fixes/NOTES.md`](official_run/env_fixes/NOTES.md), section 1). Our run's box had the environment
edit that fixes this; `envfix_auto.py` makes the same edit automatically. Run it after `SETUP OK` (the environments must be built) and
before `bash run.sh`:

```bash
. .lra/setup.env && export ELAN_HOME     # the Python and Lean toolchains that setup.sh chose
FAST=$("$LRA_PYTHON" infra/orgserver/orgtools.py fastdir) && export LRA_MEMGATE_DIR=$FAST LRA_LOCK_DIR=$FAST/locks   # node-local locks, as run.sh
"$LRA_PYTHON" official_run/env_fixes/envfix_auto.py --rows data/official/rows.jsonl
```

- This is the README's command (`python3 official_run/env_fixes/envfix_auto.py --rows data/official/rows.jsonl`, section "This folder
  and our code zip") with the Python and Lean of `.lra/setup.env`. A plain `python3` works too when it is Python 3.11 or newer and the
  toolchains are in `$ELAN_HOME` or `~/.elan`.
- It compiles the reference proof of every row that has such a chain in a file no other row uses (on its newest toolchain, through the
  measured compile). Only where the reference fails, it removes the chain's trailing ` in` in the environment's copy of the file
  (every toolchain pin, line count unchanged) and checks the reference again; an edit that does not help is undone. A second run
  changes nothing. Backups go to `data/official/rows.jsonl.envfix/`; each edited environment gets a marker
  `envs/<env>/.lra_envfix.json` that lists the edited files and lines.
- It ends with `ENVFIX DONE fixed 5, unchanged (reference ok) 2, not fixed 0; backups in ...`: the line the same code printed on the
  60 released rows on our run-3 box (there as the setup step `envfix` of our run-3 package). It takes a few minutes.
- `data/official/heartbeats.jsonl` is in place, so setup measured no reference heartbeats and need not run again. If you re-run
  `setup.sh` later anyway, first restore the files that each `envs/<env>/.lra_envfix.json` lists (`git -C envs/<env> checkout --
  <file>`), then run this step again after setup.

## Step 2: the job (48 h)

```bash
bash run.sh
```

- `run.sh` takes the job clock first, checks the node (the preflight that `bash run.sh check` runs alone), starts the vLLM server in
  the pinned image (~16 min, on the clock), then runs the driver `harness/open_package.py run` until the clock's end; the export of
  the best proof per row runs in the last 15 min. The clock is 48 h minus a 10 min margin (README, "Step 2", Clock), and never longer
  than a Slurm allocation.
- It ends with `DONE: <this folder>/runs/final/proofs.jsonl (60 rows); summary <this folder>/runs/final/summary.json` and exit code 0.
- `runs/final/RUN_CMD` holds the exact driver command; `LRA_DRY=1 bash run.sh` prints the server and driver commands without starting
  anything.
- Every hour `runs/final/interim/proofs.jsonl` holds the bests so far (same format).
- A test before the real job uses its own output directory: `LRA_OUT=runs/test LRA_JOB_SECONDS=3600 bash run.sh`.
- Sessions at once: the README's "Step 2" text and its settings table say 14; this package's default, which our run used and `run.sh`
  keeps on a whole node, is 11 (`DEFAULT_WORKERS` in `harness/open_package.py`; the preflight logs `package default sizing (11
  workers, auto compile slots)`).
- Under Slurm: the README's section "Under Slurm" (`exec bash /path/to/package/run.sh` in a 48 h, 4-GPU, exclusive allocation).

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
- Wall: 1,596 s (27 min) on our run's box with 64 compile slots; a row stops at its 2,400 s (plus the compile in flight), the step at
  7,200 s. It needs no key, no model and no GPU. `LRA_HBTOOL_SLOTS` is the number of Lean compiles at once (the command above uses 32;
  we used 64 on our box).
- Cost: $0 (CPU only). The README's section "Post-step" describes the ops, the accept gate and the `debug.skipKernelTC` option the
  step can add.
- No model runs in the step, so the same input gives the same candidates; the accept decisions use Lean heartbeat readings, which can
  differ by a few heartbeats between runs and machines. A row that reaches its 2,400 s (`--row-seconds`) keeps its input line, so a
  much slower node can change fewer rows.
- Our checks of this command on run 2's export (sha256 `e64b53ee9a699e1e...`): from our code zip of run 2 unpacked on another machine
  (2026-11-03, 20:12-20:34 UTC), it wrote `proofs.post.jsonl` byte for byte as our run of the step on run 2's box (sha256
  `486b15b894e9126a...`); three runs on a third machine, restricted with `--problems` to `putnam_1964_a4` (and `putnam_2001_b1`),
  wrote the same `upload.jsonl` (that row's new proof as in our upload) and differed by 1 in that row's heartbeat reading in
  `proofs.post.jsonl`.

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

Expected: `60 lines for 60 rows`, then `UPLOAD FILE OK`. Our upload has 4 such rows (the `grep -c` prints 4); a rerun's count depends
on its proofs. The check needs no Lean: the job and the post-step already compiled every proof on every listed toolchain.

## How our run compares

Our files, from our official run 2 (2026-11-01 11:55:21 UTC to 2026-11-03 11:20:08 UTC, 47.41 h, ended on its own) and our run of this
post-step on its output (2026-11-03 14:00:14-14:26:51 UTC, on run 2's box, 64 compile slots):

| file | sha256 | 60-row stored mean (our meter) | Arena |
|---|---|---|---|
| `runs/final/proofs.jsonl` (the job's export) | `e64b53ee9a699e1ef337cea9c9a33c27c0d4f68988622900c44eedffa90ad2a0` | 78.4585 | 78.48 (its `{"name", "proof"}` lines, sha256 `1853cfb5f0c07c32...`, uploaded alone as a probe, 2026-11-03 14:30 UTC; 60/60 compiled) |
| `runs/post/proofs.post.jsonl` (the post-step) | `486b15b894e9126a...` | 79.7167 (5 rows changed) | - |
| `runs/post/upload.jsonl` (our upload) | `4c9dc38a078b763adac5948d9d5aa546e6d3b41d859e06284660752b556b8e56` | 79.7167 | **79.74** (uploaded 2026-11-03 14:33 UTC; 60/60 compiled, the 4 kernel-skipped rows included) |

The post-step's run: 1,596 s, 117 compiles; 52 rows without a site, 3 kept, 5 changed (the table in the README's paragraph "Our run of
it"). The Arena's scores of both files were 0.02 above our meter's means.

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
- `bash run.sh export` writes `runs/final/proofs.jsonl` from everything the job saved (with the axiom audit of each pick, for at most
  a few minutes once the clock has run out).
- To continue the same run: inside the same Slurm job, the same command as in step 2 (it continues the clock in `runs/final`; each row
  resumes from its saved state); in a NEW job, `LRA_RESUME=1` in front of it (the same clock, ending no later than the new
  allocation). Without `LRA_RESUME=1` a new job moves `runs/final` aside to `runs/final.prev-<start>` and starts over.
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

