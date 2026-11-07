# Replicating our open-track upload: run 3 + post-step

This folder is the code of our official run 3 (package commit `246ff1f1`) plus the post-step (`harness/open_post.py`, development
commit `a25416f5`) that our upload of this run's output went through, seven times (the sixth and seventh passes, added 2026-11-04, run pass 5's command again on
pass 5's, then pass 6's output; README, "Pass 6" and "Pass 7"). To replicate that file: set up this folder (step 1;
its `envfix` step makes the environment fix, step 1a), run the 48 h job with our run's recipe (step 2), run the post-step seven times
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
| 3 | the post-step seven times (passes 1 and 2 `--ops v3`, pass 2 on pass 1's output; passes 3 and 4 `--ops v4`, pass 3 on pass 2's output, pass 4 on pass 3's; pass 5 `--ops all --long` on pass 4's output; pass 6 the same on pass 5's output, pass 7 on pass 6's), then `upload.jsonl` | `[post] done: ... -> runs/post7/proofs.post.jsonl` (pass 7) | about 282 min for the seven passes (50 min on run 3's box, then 29, 36, 37, 70, 30 and 30 min on the second host); each pass at most 7,200 s plus one row's 2,700 s | $0: CPU only, no model, no GPU, no internet |
| 4 | the check of the upload file | `UPLOAD FILE OK` | seconds | - |

**The file to upload is `runs/post7/upload.jsonl`** (step 3): one `{"name", "proof"}` line per row, in the rows file's order.

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
Our upload runs the step seven times: pass 1 with the third version's 24 ops (`--ops v3`) on the job's export (`--out runs/post`), pass
2, the same command on pass 1's output (`--input runs/post/proofs.post.jsonl --out runs/post2`), then pass 3 with the fourth version's
29 ops (`--ops v4`) on pass 2's output (`--input runs/post2/proofs.post.jsonl --out runs/post3`), pass 4, the same command on pass 3's
output (`--input runs/post3/proofs.post.jsonl --out runs/post4`), and pass 5 with all 41 ops in the long-pass mode (`--ops all --long
--long-seconds 6515 --row-seconds 6515`) on pass 4's output (`--input runs/post4/proofs.post.jsonl --out runs/post5`), and pass 6, the same long-pass command on pass 5's
output with walls of 1794 s (`--input runs/post5/proofs.post.jsonl --out runs/post6 ... --long-seconds 1794 --row-seconds 1794`), and pass 7, the same
on pass 6's output (`--input runs/post6/proofs.post.jsonl --out runs/post7`); the upload file is written from pass 7's output.

```bash
. .lra/setup.env && export ELAN_HOME     # the Python, Lean toolchains, rows and heartbeats that setup.sh chose and run.sh used
FAST=$("$LRA_PYTHON" infra/orgserver/orgtools.py fastdir) && export LRA_MEMGATE_DIR=$FAST LRA_LOCK_DIR=$FAST/locks   # as run.sh: node-local locks
ulimit -n 65536   # open files: with every row at once the ops need more than the usual default of 1024 (Errno 24)
mkdir -p runs/post runs/post2 runs/post3 runs/post4 runs/post5
# pass 1: the third version's 24 ops (--ops v3) on the job's export -> runs/post
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/final/proofs.jsonl --out runs/post --jobs 60 --ops v3
# pass 2: the same command on pass 1's output -> runs/post2
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/post/proofs.post.jsonl --out runs/post2 --jobs 60 --ops v3
# pass 3: the fourth version's 29 ops (--ops v4: the third version's 24 and the fourth version's 5) on pass 2's output -> runs/post3
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/post2/proofs.post.jsonl --out runs/post3 --jobs 60 --ops v4
# pass 4: the same command on pass 3's output -> runs/post4
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/post3/proofs.post.jsonl --out runs/post4 --jobs 60 --ops v4
# pass 5: all 41 ops (--ops all) in the long-pass mode (--long; our walls: 6515 s for the pass and for a row) on pass 4's output -> runs/post5
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/post4/proofs.post.jsonl --out runs/post5 --jobs 60 --ops all --long --long-seconds 6515 --row-seconds 6515
# pass 6: the same long-pass command on pass 5's output (our walls: 1794 s for the pass and for a row) -> runs/post6
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/post5/proofs.post.jsonl --out runs/post6 --jobs 60 --ops all --long --long-seconds 1794 --row-seconds 1794
# pass 7: the same long-pass command on pass 6's output (our walls: 1794 s for the pass and for a row) -> runs/post7
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/post6/proofs.post.jsonl --out runs/post7 --jobs 60 --ops all --long --long-seconds 1794 --row-seconds 1794
# the upload file: the {"name", "proof"} lines of pass 7's output
"$LRA_PYTHON" -c 'import json,sys; [print(json.dumps({"name": r["name"], "proof": r["proof"]}, ensure_ascii=False)) for r in map(json.loads, open(sys.argv[1]))]' \
    runs/post7/proofs.post.jsonl > runs/post7/upload.jsonl
```

- Pass 1 reads `runs/final/proofs.jsonl`, pass 2 reads pass 1's `runs/post/proofs.post.jsonl`, pass 3 reads pass 2's
  `runs/post2/proofs.post.jsonl`, pass 4 reads pass 3's `runs/post3/proofs.post.jsonl`, pass 5 reads pass 4's
  `runs/post4/proofs.post.jsonl`; no pass writes its input. Each pass logs one line per row it works on and ends with `[post] done: N
  row(s) adopted, paired gain +G, stored mean A -> B, C compiles, S s -> <its --out>/proofs.post.jsonl`; a pass's mean before is the
  previous pass's mean after.
- Outputs of each pass in its `--out` (`runs/post/`, `runs/post2/`, `runs/post3/`, `runs/post4/`, `runs/post5/`): `proofs.post.jsonl`
  (one line per row; a row the pass did not change keeps its input line byte for byte), `post_report.json` (per row: status, readings
  before and after, ops), `post/rows.jsonl` and `post/decisions.jsonl`; from the last command, `runs/post7/upload.jsonl`: the file to
  upload.
- Each pass starts every row from the previous pass's proof with a fresh row budget, so it can find and adopt further rewrites (also
  of proofs that an earlier pass rewrote); every adoption passes the same gate against that proof, so no row's stored score goes down.
  With fewer passes, the upload is the `{"name", "proof"}` lines of the last pass's `proofs.post.jsonl` (the last command with
  `runs/post`, `runs/post2`, `runs/post3` or `runs/post4` in place of `runs/post5`).
- Wall: 3,014 s for pass 1 on run 3's box (76 CPU cores, Intel Xeon Platinum 8368 at 2.40 GHz) with 64 compile slots, then 1,755 s,
  2,132 s, 2,222 s and 4,211 s for passes 2, 3, 4 and 5 on a second host (Azure Standard_D64ads_v7: 64 vCPUs, AMD EPYC 9V45) with 56
  compile slots (about 222 min in all); per pass, a row stops at its 2,700 s (pass 5: 6515 s) (plus the compile in flight; it keeps
  the proof it has confirmed) and 240 compiles, and no row starts after 7,200 s. It needs no key, no model and no GPU, and an
  open-file limit of 65536 (`ulimit -n 65536`, in the command). `LRA_HBTOOL_SLOTS` is the number of Lean compiles at once (the command
  above uses 32; our pass 1 used 64 on run 3's box, our passes 2 to 5 56 on the second host).
- Cost: $0 (CPU only). The README's section "Post-step" describes the ops, the accept gate and the `debug.skipKernelTC` option the
  step can add.
- No model runs in the step; the accept decisions use Lean heartbeat readings, which can differ by a few heartbeats between runs and
  machines. A row that reaches its 2,700 s (`--row-seconds`) keeps the last proof it confirmed, and the ops of the third, fourth and
  fifth versions skip their queries when a row's wall left is short against its compile time, so a much slower node can change fewer
  rows.
- `ulimit -n 65536` (in the block) is needed: with `--jobs 60` the step's 41 ops hold more files open than the usual default limit of
  1024 (`OSError: [Errno 24] Too many open files`). It cannot go above the hard limit (`ulimit -Hn`).
- Most of the ops size their probe files and compile rounds by measured compile times (copies per file, rounds per call, a probe wall
  per row), so on a slower or busier node they can try fewer candidates and change fewer rows; the gate is the same.
- The step's ops can rewrite a proof that carries `debug.skipKernelTC`; such rewrites are not checked by the kernel. In our upload,
  `PauliMatrix.pauliContr_mul_pauliContrDown_mul_pauliContr` fails the kernel check (README, "Post-step", "One kernel-skipped proof of
  our upload fails the kernel check").
- Pass 5's op `hb_smartunfold` adds `set_option <option> false in` for sound elaborator options (`smartUnfolding`,
  `backward.isDefEq.lazyWhnfCore`, ...): the kernel still checks every such proof (README, "Post-step", "About `smartUnfolding` and
  the other options of `hb_smartunfold`").

## Step 4: check the upload file

```bash
. .lra/setup.env
"$LRA_PYTHON" - "$LRA_SETUP_ROWS" runs/post7/upload.jsonl <<'PY'
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
grep -c 'debug.skipKernelTC' runs/post7/upload.jsonl    # rows whose proof skips the kernel check (README, "About debug.skipKernelTC")
grep -cE 'set_option (smartUnfolding|backward\.[A-Za-z.]+|cleanup\.letToHave) false in' runs/post7/upload.jsonl    # rows with hb_smartunfold's options (README, "About smartUnfolding")
```

Expected: `60 lines for 60 rows`, then `UPLOAD FILE OK`. Our upload has 4 such rows (the job's export has 1:
`FTheory.SU5.ChargeSpectrum.isPhenoClosedQ10_viableCharges`, the run's own line);
`FTheory.SU5.ChargeSpectrum.isPhenoClosedQ5_viableCharges` (pass 1: `kskip:inplace`);
`PauliMatrix.pauliContrDown_mul_pauliContr_mul_pauliContrDown` (pass 1: `kskip:inplace`, `inlineeq:simpa`; pass 5:
`hb_hotctl:simponly>simp_rw`); `PauliMatrix.pauliContr_mul_pauliContrDown_mul_pauliContr` (pass 1: `kskip:inplace`, `inlineeq:simpa`;
pass 3: `sonnet_listdrop:verified`, `jointres:joint`; pass 4: `sonnet_listdrop:verified`, `jointres:joint`, `jointres:joint`; pass 5:
`sonnet_listdrop:verified`; passes 6 and 7 changed none of the 4); edits made after the option is in place are not kernel-checked, and our upload's proof of
`PauliMatrix.pauliContr_mul_pauliContrDown_mul_pauliContr` fails the kernel check: README, "One kernel-skipped proof of our upload
fails the kernel check"); a rerun's count depends on its proofs. The last command counts the rows that carry `hb_smartunfold`'s
elaborator options (ours: 14, from passes 5 to 7; README, "About `smartUnfolding` and the other options of `hb_smartunfold`"); those
proofs are kernel-checked. The check needs no Lean: the job and the post-step already compiled every proof on every listed toolchain.

## How our run compares

Our files, from our official run 3 (2026-11-02 06:43:52 UTC to 2026-11-04 06:03:56 UTC, 47.33 h, ended on its own before the 48 h
clock) and our five passes of this post-step on its output (2026-11-04 06:04-08:52 UTC; pass 1 on run 3's box (76 CPU cores, Intel
Xeon Platinum 8368 at 2.40 GHz), 64 compile slots, and pass 2 on a second host (Azure Standard_D64ads_v7: 64 vCPUs, AMD EPYC 9V45), 56
compile slots, both with the third version's 24 ops (commit `c059dfbd`); passes 3 and 4 on the second host, 56 compile slots, with the
fourth version's 29 ops (commit `715cd39d`); pass 5 on the second host, 56 compile slots, `--ops all --long --long-seconds 6515
--row-seconds 6515`, this zip's code; this zip's code runs passes 1 to 4 as `--ops v3` and `--ops v4`; README, "Post-step", "Our run
of it", has the exact commands):

| file | sha256 | 60-row stored mean (our meter) |
|---|---|---|
| `runs/final/proofs.jsonl` (the job's export) | `0664621ddcf923b0c4b0285cccf425375a270cd80977a81dccf712fd87afc95f` | 79.6778 |
| `runs/final/summary.json` (the job's summary) | `3505b06d1749efefe63360c9a41c34ffebd083ae8698d461badc0a4466dafd3f` | - |
| `runs/post/proofs.post.jsonl` (pass 1) | `a52fd4c65968faec3e91dbe1ea11e29c3d74709fb00f1e65f083b5bd789f5731` | 80.9703 (48 rows changed, none lower; 3,014 s, 2,438 compiles) |
| `runs/post2/proofs.post.jsonl` (pass 2, on pass 1's output) | `e333ec44d8efa424aa8d6f28f789a2525eb6f53b83319721d29b967ecefc55a5` | 81.3902 (27 rows changed, none lower; 1,755 s, 2,354 compiles) |
| `runs/post3/proofs.post.jsonl` (pass 3, `--ops v4`, on pass 2's output) | `f2399dcaec7abd4b4790dec88742b2ef98e1560dfd55aceb9a285dd680081f22` | 81.9002 (36 rows changed, none lower; 2,132 s, 4,316 compiles) |
| `runs/post4/proofs.post.jsonl` (pass 4, `--ops v4`, on pass 3's output) | `951c1c3886992afc60d3e82bb9e7af0ae249a1358890af1b8f0c0725f126a2bd` | 82.2083 (22 rows changed, none lower; 2,222 s, 3,766 compiles) |
| `runs/post5/proofs.post.jsonl` (pass 5, `--ops all --long`, on pass 4's output) | `c87eac9f57cb010f8c74288655ac2e0d3512b94b2ef33328307bfd96c4aa203e` | 82.4740 (43 rows changed, none lower; 4,211 s, 7,430 compiles) |
| `runs/post5/upload.jsonl` (our 10:24:47 upload, replaced) | `082af747fa07b0384a931a22948bb87c6be0f6b0a6bf33d0ca300b6485f05110` | 82.4740 |
| `runs/post6/proofs.post.jsonl` (pass 6, `--ops all --long`, walls 1794 s, on pass 5's output) | `c86ba4cab48b459e1d56e0fdf87c9828e3655d084094bb70f1ec1c0b389514fd` | 82.5080 (16 rows changed, none lower; 1,800 s, 3,276 compiles) |
| `runs/post6/upload.jsonl` (our 10:49:49 upload, replaced) | `d2edaadf0765fcb063c4b47429e68c7cd6621f4adbcb62086395156822f9fd57` | 82.5080 |
| `runs/post7/proofs.post.jsonl` (pass 7, `--ops all --long`, walls 1794 s, on pass 6's output) | `c09e4b98a1ae7ef78741fdcc59de6e7cd434c7a8e9bce78d8367cee419dba1be` | 82.5560 (8 rows changed, none lower; 1,746 s, 2,833 compiles) |
| `runs/post7/upload.jsonl` (our final upload, 2026-11-04 11:25:51 UTC) | `8d6d1893d315eb0f55491df50046629877d2f89005848862bc8c892dba3f3e5e` | 82.5560 |

A rerun of the step is not byte-identical and can differ from ours on a few rows (README, "Post-step", "Our run of it"). Our five
passes ran on two hosts; on one node, the README's commands run all five.

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
  `runs/post2b`, then pass 3 with `--input runs/post2b/proofs.post.jsonl`; pass 3: e.g. `runs/post3b`, then pass 4 with `--input
  runs/post3b/proofs.post.jsonl`; pass 4: e.g. `runs/post4b`, then pass 5 with `--input runs/post4b/proofs.post.jsonl`; pass 5: e.g.
  `runs/post5b`, and `runs/post5b/...` in the last command). `--seconds` shortens a pass's wall.
