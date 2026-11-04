# Replicating our open-track upload: run 3 + post-step

This folder is the code of our official run 3 (package commit `246ff1f1`) plus the post-step (`harness/open_post.py`, development
commit `6b28b8e1`) that our upload of this run's output went through, three times. To replicate that file: set up this folder (step 1;
its `envfix` step makes the environment fix, step 1a), run the 48 h job with our run's recipe (step 2), run the post-step three times
on the job's output (step 3), and check the file (step 4). Our own numbers are in "How our run compares".

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
| 3 | the post-step three times (passes 1 and 2 with the 24 ops of `OPS24`, pass 2 on pass 1's output; pass 3 `--ops hb_smartunfold` on pass 2's output), then `upload.jsonl` | `[post] done: ... -> runs/post3/proofs.post.jsonl` (pass 3) | about 84 min for the three passes (50 min on run 3's box, 29 min on the second host, 5 min on the third); each pass at most 7,200 s plus one row's 2,700 s | $0: CPU only, no model, no GPU, no internet |
| 4 | the check of the upload file | `UPLOAD FILE OK` | seconds | - |

**The file to upload is `runs/post3/upload.jsonl`** (step 3): one `{"name", "proof"}` line per row, in the rows file's order.

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
Our upload runs the step three times: pass 1 with the third version's 24 ops (`--ops "$OPS24"`) on the job's export (`--out
runs/post`), pass 2, the same command on pass 1's output (`--input runs/post/proofs.post.jsonl --out runs/post2`), then pass 3 with
`hb_smartunfold` alone (`--ops hb_smartunfold --jobs 30`) on pass 2's output (`--input runs/post2/proofs.post.jsonl --out
runs/post3`); the upload file is written from pass 3's output.

```bash
. .lra/setup.env && export ELAN_HOME     # the Python, Lean toolchains, rows and heartbeats that setup.sh chose and run.sh used
FAST=$("$LRA_PYTHON" infra/orgserver/orgtools.py fastdir) && export LRA_MEMGATE_DIR=$FAST LRA_LOCK_DIR=$FAST/locks   # as run.sh: node-local locks
ulimit -n 65536   # open files: with every row at once the ops need more than the usual default of 1024 (Errno 24)
mkdir -p runs/post runs/post2 runs/post3
# the third version's 24 ops (every op of harness/open_post.ORDER but hb_smartunfold), for passes 1 and 2
OPS24=kskip,implied,closerprep,inlineeq,hintgrind,projpath,lexsurf,jointres,t4ind,ctorsearch   # the first and second versions' 10 ops
OPS24=$OPS24,argon_funind,argon_hbelab,argon_hpcert,sonnet_listdrop,sonnet_lintdrop,opus_hoist,opus_stepdrop   # the third version's 14 ops
OPS24=$OPS24,opus_rundrop,opus_scaffold,opus_armfold,opus_goalmerge,opus_patfuse,sonnet_surface,sol_harvest
# pass 1: the job's export -> runs/post
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/final/proofs.jsonl --out runs/post --jobs 60 --ops "$OPS24"
# pass 2: the same command on pass 1's output -> runs/post2
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/post/proofs.post.jsonl --out runs/post2 --jobs 60 --ops "$OPS24"
# pass 3: hb_smartunfold alone on pass 2's output -> runs/post3
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/post2/proofs.post.jsonl --out runs/post3 --jobs 30 --ops hb_smartunfold
# the upload file: the {"name", "proof"} lines of pass 3's output
"$LRA_PYTHON" -c 'import json,sys; [print(json.dumps({"name": r["name"], "proof": r["proof"]}, ensure_ascii=False)) for r in map(json.loads, open(sys.argv[1]))]' \
    runs/post3/proofs.post.jsonl > runs/post3/upload.jsonl
```

- Pass 1 reads `runs/final/proofs.jsonl`, pass 2 reads pass 1's `runs/post/proofs.post.jsonl`, pass 3 reads pass 2's
  `runs/post2/proofs.post.jsonl`; no pass writes its input. Each pass logs one line per row it works on and ends with `[post] done: N
  row(s) adopted, paired gain +G, stored mean A -> B, C compiles, S s -> <its --out>/proofs.post.jsonl`; a pass's mean before is the
  previous pass's mean after.
- Outputs of each pass in its `--out` (`runs/post/`, `runs/post2/`, `runs/post3/`): `proofs.post.jsonl` (one line per row; a row the
  pass did not change keeps its input line byte for byte), `post_report.json` (per row: status, readings before and after, ops),
  `post/rows.jsonl` and `post/decisions.jsonl`; from the last command, `runs/post3/upload.jsonl`: the file to upload.
- Each pass starts every row from the previous pass's proof with a fresh row budget, so it can find and adopt further rewrites (also
  of proofs that an earlier pass rewrote); every adoption passes the same gate against that proof, so no row's stored score goes down.
  With fewer passes, the upload is the `{"name", "proof"}` lines of the last pass's `proofs.post.jsonl` (the last command with
  `runs/post` or `runs/post2` in place of `runs/post3`).
- Wall: 3,014 s for pass 1 on run 3's box (76 CPU cores, Intel Xeon Platinum 8368 at 2.40 GHz) with 64 compile slots, 1,755 s for pass
  2 on a second host (Azure Standard_D64ads_v7: 64 vCPUs, AMD EPYC 9V45) with 56 compile slots, and 277 s for pass 3 (one op) on a
  third host of the same Azure size with 32 compile slots (about 84 min in all); per pass, a row stops at its 2,700 s (plus the
  compile in flight; it keeps the proof it has confirmed) and 240 compiles, and no row starts after 7,200 s. It needs no key, no model
  and no GPU, and an open-file limit of 65536 (`ulimit -n 65536`, in the command). `LRA_HBTOOL_SLOTS` is the number of Lean compiles
  at once (the command above uses 32; our pass 1 used 64 on run 3's box, our pass 2 56 on the second host, our pass 3 32 on the third
  host).
- Cost: $0 (CPU only). The README's section "Post-step" describes the ops, the accept gate and the `debug.skipKernelTC` option the
  step can add.
- No model runs in the step; the accept decisions use Lean heartbeat readings, which can differ by a few heartbeats between runs and
  machines. A row that reaches its 2,700 s (`--row-seconds`) keeps the last proof it confirmed, and the third version's ops and
  `hb_smartunfold` skip their queries when a row's wall left is short against its compile time, so a much slower node can change fewer
  rows.
- `ulimit -n 65536` (in the block) is needed: with `--jobs 60` the step's 25 ops hold more files open than the usual default limit of
  1024 (`OSError: [Errno 24] Too many open files`). It cannot go above the hard limit (`ulimit -Hn`).
- Most of the ops size their probe files and compile rounds by measured compile times (copies per file, rounds per call, a probe wall
  per row), so on a slower or busier node they can try fewer candidates and change fewer rows; the gate is the same.
- Pass 3's op `hb_smartunfold` adds `set_option <option> false in` for sound elaborator options (`smartUnfolding`,
  `backward.isDefEq.lazyWhnfCore`, ...): the kernel still checks every such proof (README, "Post-step", "About `smartUnfolding` and
  the other options of `hb_smartunfold`").

## Step 4: check the upload file

```bash
. .lra/setup.env
"$LRA_PYTHON" - "$LRA_SETUP_ROWS" runs/post3/upload.jsonl <<'PY'
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
grep -c 'debug.skipKernelTC' runs/post3/upload.jsonl    # rows whose proof skips the kernel check (README, "About debug.skipKernelTC")
grep -cE 'set_option (smartUnfolding|backward\.[A-Za-z.]+|cleanup\.letToHave) false in' runs/post3/upload.jsonl    # rows with hb_smartunfold's options (README, "About smartUnfolding")
```

Expected: `60 lines for 60 rows`, then `UPLOAD FILE OK`. Our upload has 4 such rows (the job's export has 1:
`FTheory.SU5.ChargeSpectrum.isPhenoClosedQ10_viableCharges`, the run's own line, unchanged by the step; the step added the option to
`FTheory.SU5.ChargeSpectrum.isPhenoClosedQ5_viableCharges` (`kskip:inplace`),
`PauliMatrix.pauliContrDown_mul_pauliContr_mul_pauliContrDown` (`kskip:inplace` then `inlineeq:simpa`) and
`PauliMatrix.pauliContr_mul_pauliContrDown_mul_pauliContr` (`kskip:inplace` then `inlineeq:simpa`); the `inlineeq` edits were made
after the option was in place, README, "About `debug.skipKernelTC`"); a rerun's count depends on its proofs. The last command counts
the rows that carry `hb_smartunfold`'s elaborator options (ours: 16; README, "About `smartUnfolding` and the other options of
`hb_smartunfold`"); those proofs are kernel-checked. The check needs no Lean: the job and the post-step already compiled every proof
on every listed toolchain.

## How our run compares

Our files, from our official run 3 (2026-11-02 06:43:52 UTC to 2026-11-04 06:03:56 UTC, 47.33 h, ended on its own before the 48 h
clock) and our three passes of this post-step on its output (2026-11-04 06:04-07:55 UTC; pass 1 on run 3's box (76 CPU cores, Intel
Xeon Platinum 8368 at 2.40 GHz), 64 compile slots, and pass 2 on a second host (Azure Standard_D64ads_v7: 64 vCPUs, AMD EPYC 9V45), 56
compile slots, both with the third version's 24 ops (commit `c059dfbd`); pass 3 on a third host of the same Azure size, 32 compile
slots, `--ops hb_smartunfold`, this zip's code; README, "Post-step", "Our run of it", has the exact commands):

| file | sha256 | 60-row stored mean (our meter) |
|---|---|---|
| `runs/final/proofs.jsonl` (the job's export) | `0664621ddcf923b0c4b0285cccf425375a270cd80977a81dccf712fd87afc95f` | 79.6778 |
| `runs/final/summary.json` (the job's summary) | `3505b06d1749efefe63360c9a41c34ffebd083ae8698d461badc0a4466dafd3f` | - |
| `runs/post/proofs.post.jsonl` (pass 1) | `a52fd4c65968faec3e91dbe1ea11e29c3d74709fb00f1e65f083b5bd789f5731` | 80.9703 (48 rows changed, none lower; 3,014 s, 2,438 compiles) |
| `runs/post2/proofs.post.jsonl` (pass 2, on pass 1's output) | `e333ec44d8efa424aa8d6f28f789a2525eb6f53b83319721d29b967ecefc55a5` | 81.3902 (27 rows changed, none lower; 1,755 s, 2,354 compiles) |
| `runs/post3/proofs.post.jsonl` (pass 3, `--ops hb_smartunfold`, on pass 2's output) | `1a8fc0e9dd4c75368d5c12f95b9b200f54350c780789e9400b1e6f9d4218c871` | 81.4985 (16 rows changed, none lower; 277 s, 407 compiles) |
| `runs/post3/upload.jsonl` (our upload) | `1fcfe01a06bcefb6bad7a76628b5d84632d181bb9fe232b7a64db72d891ffdb0` | 81.4985 |

A rerun of the step is not byte-identical and can differ from ours on a few rows (README, "Post-step", "Our run of it"). Our three
passes ran on three hosts; on one node, the README's commands run all three.

For comparison, our run 2 (package `748d964c`, the same rows and reference heartbeats, no automation card): export 78.4585 (Arena
78.48); one pass of the post-step's second version (`ee48034b`) 80.7535 (our upload of run 2, Arena 80.76).

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

- If a pass is stopped, it has not written its `proofs.post.jsonl` (it writes that file once, at its end): run that pass again with a
  new `--out` directory (pass 1: e.g. `runs/post-1b`, then pass 2 with `--input runs/post-1b/proofs.post.jsonl`; pass 2: e.g.
  `runs/post2b`, then pass 3 with `--input runs/post2b/proofs.post.jsonl`; pass 3: e.g. `runs/post3b`, and `runs/post3b/...` in the
  last command). `--seconds` shortens a pass's wall.

