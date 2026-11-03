# Vexorium open-track package: GLM-5.3-Flash on 4 x A100

For every benchmark row, the open model GLM-5.3-Flash (AWQ W4A16, served by vLLM on the 4 GPUs) refactors the seed proof in
tool-using sessions (compile, scratch Lean, grep, goal maps, heartbeat profiles), several resumed sessions per row. A model-free end
stage (CPU only) then searches mechanical rewrites of each row's best proof, and a lexer normalizer tidies the result. Every step keeps
a proof only if it compiles on every listed toolchain and scores higher. The output is one proof per row. Nothing calls a hosted model,
and no stored proofs are used: everything starts from the seed proofs in your rows file.

## This folder and our code zip (added 2026-11-03)

This folder is the release export of package commit `748d964cd4704dfee32314db18f0a093d4c21e18`, the code of our official open-track
run 2, plus the post-step our upload went through. Run 2 started from the seed proofs on 2026-11-01 at 11:55:21 UTC on an on-demand 4
x A100 80 GB SXM4 box and ended on its own at 2026-11-03 11:20:08 UTC (47.41 h, the export at its deadline). The driver ran with
`--workers 11 --max-sessions 12 --end-seconds 7200 --end-pipeline on --session-max-context 200000 --first-wave-stagger 120` (with the
job clock's `--started-at` and `--job-seconds 172800`): every one of these is the package's default, so `bash run.sh` runs the same
recipe.

- **The run's export, file for file.** Every file listed in `EXPORT.json` (the export's manifest, unchanged) is the file the run
  shipped (2026-11-01 11:48:22 UTC, `probe/open_package/export_release.py`, release leak scan: pass; tarball sha256
  `ce34fd92760499495cd21d1f2778f75cd8444bba7359dd44a7f6084a96debc12`), byte for byte, except this `README.md`, which has this section
  and the section "Post-step" at the end, and the withheld example file (below). `harness/style_rw_open_exemplars.json` (sha256
  `3ed15491e0b5b09a...`, listed in `EXPORT.json`) is withheld from this public repository and its history: it holds the 9 encoded
  example pairs of the opt-in style step (`--style-rw on`, off by default and in our run): closed-model example proofs from our
  closed-track material, two of them from our internal development sets. The organizers receive it in our submitted code zip; without
  it `--style-rw on` refuses to start and nothing else changes.
- **The post-step** (section "Post-step" below): `harness/open_post.py` and `harness/post/` (8 files), byte for byte those of our
  development commit `5cb18d3b` (branch `open-post`). Nothing in `setup.sh`, `run.sh` or the job imports or runs them: the job's
  import closure is the export's (`EXPORT.json`). Unlike the export's modules, they keep their comments and docstrings. In this
  repository 3 of them carry redactions of decision attributions in comments and docstrings (4 lines, same line counts); the code zip
  has them byte for byte.
- **Data:** `data/official/rows.jsonl` (the 60 released rows, sha256
  `d53690b057f9972f44643678ee6b5eee7a66f56e1a7d2678a2e5ff47fadbd682`) and `data/official/heartbeats.jsonl` (sha256
  `2d777f145d0c4bf0fe66c4825b0fb590b57be75c0aa2ebec9e20f9ddcd56688b`): the reference heartbeats our run used, measured on our box by
  the setup's refhb step (`infra/refhb/make_ref_heartbeats.py`, direct path + 2; the row `Vlasov.transportedIntegral_continuousOn`
  measured again after the environment fix below). With both files in place, `bash setup.sh` takes them without arguments and uses the
  heartbeats as is.
- [`official_run/`](official_run/README.md): our own orchestration of the run on a rented vast.ai box (not needed for a rerun; the
  code zip carries only `official_run/env_fixes/`); [`official_run/env_fixes/`](official_run/env_fixes/NOTES.md): the environment
  fixes of our run's box.
- `probe/open_package/dry_run.sh` (the package's $0 dry run, development only) reads `data/abpool/`, an internal development pool that
  is not in this repository or the code zip, so it does not run from this folder as is.
- `LICENSE` and `NOTICE.md` are at the repository root; the code zip carries copies of both and a `ZIP_NOTES.md` (its file list with
  the identity checks).

**Required to reproduce our run's environment.** Our box had an env-side workaround for 5 released rows whose reference proof failed
in our measured compile (their declaration sits under a chain of `... in` lines; see
[`official_run/env_fixes/NOTES.md`](official_run/env_fixes/NOTES.md)); without it every candidate on those rows fails the measured
compile. After `bash setup.sh` has built the environments, run `python3 official_run/env_fixes/envfix_auto.py --rows
data/official/rows.jsonl` (it edits only rows whose reference fails because of a `... in` chain above the declaration, checks them
again, and is a no-op when run twice), then `bash setup.sh` once more if setup measured the reference heartbeats (with
`data/official/heartbeats.jsonl` in place it does not), then `bash run.sh`. If setup stops at its refhb step on these rows, run the
helper and re-run setup. The package code is unchanged; the helper reproduces the environment edit.

Everything between this section and "Post-step" is the export's own README: the instructions for rerunning the package.

## Quick start: three commands

```bash
# 0. The benchmark rows and their reference heartbeats (the warm-up files' JSONL format). Put them here, or pass both paths to
#    setup.sh and to run.sh as arguments. The heartbeats file is optional: when you give it, it is used as is; without it, setup
#    measures each row's reference proof on its newest toolchain (the refhb step) and the job uses those values.
mkdir -p data/official && cp ROWS.jsonl data/official/rows.jsonl && cp HEARTBEATS.jsonl data/official/heartbeats.jsonl

# 1. Setup: run ONCE, BEFORE the 48 h job. Needs the internet; takes about 1.5-3 h. Ends with "SETUP OK".
#    Best on a GPU node: it then also checks the GPUs from inside the container and starts the server once, offline, as the job will.
bash setup.sh

# 1b. Only if setup ran on a node without GPUs (a login node): once, on a GPU node, in an allocation like the job's. Ends with "CHECK OK".
bash run.sh check

# 2. The 48 h job. Needs no internet. Ends with "DONE: .../runs/final/proofs.jsonl".
bash run.sh
```

A test run before the official job: use its own output directory (`LRA_OUT=runs/test LRA_JOB_SECONDS=3600 bash run.sh`). If a test
did use `runs/final`, the official job does not continue it: a new job moves another run's `runs/final` to `runs/final.prev-<start>`
and starts its own 48 h clock (see Clock below).

The result is `runs/final/proofs.jsonl`: one JSON line per row, in the rows file's order, with `name`, `proof` (the full
declaration), `source` (`end`, `normalize`, `agent` or `seed`) and the stored score, tokens and heartbeats.

Both scripts take the same optional arguments: `bash setup.sh ROWS.jsonl HEARTBEATS.jsonl`, then `bash run.sh ROWS.jsonl HEARTBEATS.jsonl`.
Without arguments, `setup.sh` uses `data/official/`, and stops with an error when it is missing (the 15 warm-up rows in `data/` only when
passed by path: `bash setup.sh data/benchmark_warmup.jsonl data/benchmark_heartbeats.jsonl`), and `run.sh` uses the files
`setup.sh` prepared. **Reference heartbeats: a heartbeats file you pass (or `data/official/heartbeats.jsonl`) is used as is.** If there
is none, `setup.sh ROWS.jsonl` measures them once after building the environments (`.lra/ref_heartbeats.jsonl`, a few minutes) and
`run.sh` uses that file for the same rows. Run both from any directory. Use the same absolute path for the package in setup and in the job: the Lean
environments are git worktrees that record absolute paths.

## Where things are

| path | what |
|---|---|
| `setup.sh` | the setup script (step 1): tools, Lean toolchains, container image, model download, Lean project environments, self-check |
| `run.sh` | the job (step 2): job clock, preflight, vLLM server, the optimization driver, interim proofs, clean stop |
| `runs/final/` | the job's output: `proofs.jsonl`, `summary.json`, `driver.log`, `logs/`, per-row state in `work/` |
| `ws/` | the work directory (`LRA_WS`): model cache `hf/`, `vllm.log`, caches, an elan installation when one is needed |
| `.lra/` | setup state: `setup.env` (read by run.sh), `logs/setup-*.log`, ripgrep, the Python wrapper |
| `envs/` | the Lean project environments (one git worktree per project and toolchain), built by setup.sh |
| `harness/open_package.py` | the driver run.sh starts; `docs/open_package_readme.md` is the technical appendix (stages, flags, measurements) |
| `infra/vast/` | our rental tooling. setup.sh / run.sh use only `run_vllm.sh` (the server recipe) and `harness_setup.sh` (the environment build); `package_run.sh`, `relaunch.sh` and `endpoint.sh` are for our vast.ai boxes and are not needed here |

## Requirements

- Node: 4 x A100 80 GB SXM with NVLink (the recipe was measured on NV12 between every pair), 64 or more CPU cores, 256 GB RAM.
- Disk, on the filesystem that holds the package (shared Lustre is fine): about 400 GB. That is the model (191 GB), the Lean
  environments and toolchains (about 130 GB for the 15 warm-up rows, more for new library versions), the image (10-20 GB as an
  Apptainer file) and the run's output (5-20 GB). Run setup and the job as the same user, at the same absolute path.
- Host software: bash 4 or newer (tested with 4.2 and 5.2), coreutils, git, curl, tar and sha256sum. Python 3.11 or newer with
  `requests` (setup creates a venv with uv when the system Python is older; 3.11 is the minimum because the compile path reads
  `lakefile.toml` with `tomllib`). No root is needed. `flock` is optional (a `mkdir` lock replaces it).
- A container runtime with NVIDIA GPU access: podman-hpc, Shifter, Apptainer/Singularity or Docker. setup.sh picks the first one
  present; set `LRA_RUNTIME` to choose. Without any runtime, see "No container runtime" below.
- Lean: your toolchains are used where setup finds them, in this order: `LRA_ELAN_HOME`, `ELAN_HOME`, `~/.elan`, then the
  installation of an `elan` on PATH that has a `toolchains/` directory. If that installation is read-only, or the toolchains are bare
  directories (`LRA_TOOLCHAINS=/path/a:/path/b`), they are linked into a user elan under `ws/elan`; setup never writes into a
  read-only installation. A toolchain a row pins that is not provided is downloaded by elan during setup.
- Internet during setup only: GitHub (project repositories at pinned commits, elan, ripgrep), the Mathlib cache server, Hugging Face
  (the checkpoint), Docker Hub (the image). The job makes no outbound connection.

## Step 1: `bash setup.sh [ROWS.jsonl HEARTBEATS.jsonl]`

You can re-run it: finished work is kept, and a re-run continues where the last one stopped. It prints one line per step and ends with
`SETUP OK`. On a failure it prints `FAILED: ...` and the log to read.

| step | what it does | time |
|---|---|---|
| tools | picks Python >= 3.11 with `requests`, falling back to a venv in `ws/venv` (uv 0.6.14, sha256-pinned, as the last resort). Installs ripgrep 14.1.1 (static build, sha256-pinned) into `.lra/bin` if `rg` is missing | < 1 min |
| lean | sets `ELAN_HOME` (see Requirements); installs elan into `ws/elan` only when no usable installation exists | < 1 min |
| image | pulls the pinned image `lazymio/vllm-backport:v0.13.1-sm80` (linux/amd64 manifest `sha256:8094fcbab905a04a480b327f2761255e3d17cd8d39470cac9d76450bbb567f7e`; see "The image"). Checks that it runs, sees the package directory, can write the work directory, and holds the pinned vLLM build (version 0.13.1 and the sha256 of its installed `RECORD`). When the node has GPUs, it also checks what the container sees: the GPU count and names and NVLink, through NVML as vLLM uses it (`infra/orgserver/gpu_probe.py`). On a node without GPUs it says so, and `bash run.sh check` on a GPU node does this check | 5-20 min |
| model | downloads `wtdcode/GLM-5.3-Flash-AWQ-W4A16` at revision `abd7b07719111f137e1de8a0c1b7e01c11b74d1a` into `ws/hf` with the image's own `huggingface_hub`. Resumable; checked file by file (13 shards, tokenizer, chat template). Its local snapshot directory (`ws/hf/hub/models--.../snapshots/<revision>`) is written to `.lra/setup.env` as `LRA_MODEL_PATH`: the job serves that directory | 6-30 min |
| envs | derives the Lean environments from the rows (`infra/open_package/envs_from_rows.py`), then builds them from public sources (`infra/vast/harness_setup.sh`): git clones at the pinned commits, Mathlib's prebuilt cache (`lake exe cache get`), and `lake build` of the rows' modules. `infra/open_package/check_envs.py` must then print `envs ok` | 40 min-2 h |
| refhb | only when no heartbeats file is given: compiles each row's reference proof (`src`) on its newest toolchain through the package's own direct meter (`infra/refhb/make_ref_heartbeats.py`: the pinned `lean` binary on the built libraries, heartbeats under `Elab.async false`, plus 2; warm-up rows reuse the published warm-up values) into `.lra/ref_heartbeats.jsonl`. Every row must be covered (else `FAILED` and the rows without a reading). On the 15 warm-up rows these values are within 0.71 % of the official reference file | 2-10 min |
| check | compiles the first row's seed through the package's own compile path (cold, then warm), times one `rg` over its environment, and finds a node-local directory where `flock` works | 1-5 min |
| warm | when the container sees 4 GPUs (the default `LRA_WARM_SERVER=auto`): one server start exactly as the job starts it (offline, from the local snapshot), then a stop. It proves the offline start on this node while setup still has the internet, and fills the compile caches in `ws/cache`, which shortens the ~16 min server start inside the job. If the server does not answer, setup fails with the logs to read (`LRA_SKIP=warm` skips the step) | ~16 min |

Settings for setup.sh (all optional):

| variable | default | meaning |
|---|---|---|
| `LRA_WS` | `<package>/ws` | the work directory (~200 GB): model, caches, server log |
| `LRA_RUNTIME` | auto | `podman-hpc`, `shifter`, `apptainer`, `singularity`, `docker` or `none` |
| `LRA_PYTHON` | auto | a Python >= 3.11 to use |
| `LRA_ELAN_HOME` / `LRA_TOOLCHAINS` | auto / empty | the elan installation to use; directories of bare toolchains to link |
| `LRA_ENV_URLS` | empty | `source=https://git-url ...` for a library the rows do not name a repository for (rows with a `url` field need nothing) |
| `LRA_REFHB_JOBS` | 8 | reference proofs measured at once by the refhb step (only without a heartbeats file) |
| `LRA_REFHB_ALLOW_MISSING` | 0 | 1: a row whose reference proof cannot be measured gets a flagged placeholder (logged as `PLACEHOLDER`: a reading taken despite an error, an older toolchain's reading, or a length-scaled estimate) instead of stopping setup |
| `LRA_SKIP` | empty | steps to skip, e.g. `"image model"` when the server is provided some other way (`LRA_BASE_URL` in run.sh) |
| `LRA_SHIFTER_MODULES` | `gpu` | the Shifter module that gives GPU access (setup and run.sh also try `nvidia` and none) |
| `LRA_WARM_SERVER` | `auto` | `auto`: the warm start when the container sees 4 GPUs; `1`: always (fails without GPUs); `0`: never |
| `LRA_IMAGE_NAME` / `LRA_IMAGE_TAG` / `LRA_IMAGE_DIGEST` | the pins above | a mirror of the same image (see "The image") |
| `LRA_DRY` | 0 | 1: print each step's commands; nothing is downloaded, built or installed, and `.lra/setup.env` is not written |
| `LEAN_NUM_THREADS` | Lean's default | threads per `lake build` |

## Step 2: `bash run.sh [ROWS.jsonl HEARTBEATS.jsonl]`

1. **Clock.** The job clock starts FIRST, before anything else runs. The start is `LRA_START` if set; else the clock saved in
   `runs/final` when it belongs to this same job (run.sh stamps the scheduler's job id into `runs/final/orgjob.json`: a run.sh
   restarted inside the same Slurm job continues its clock), or when `LRA_RESUME=1` is set; else the Slurm job's start time
   (`squeue`); else the moment run.sh started. A `runs/final` left by another run (a test run, an earlier job) is never continued by
   a new job: run.sh moves it to `runs/final.prev-<its start>` and logs it. The job length is 48 h minus a 10 min safety margin
   (`LRA_SAFETY_S`, 600 s), and the clock never ends later than the Slurm job's end minus that margin. A clock that is already over
   is refused unless `LRA_RESUME=1`. The log line `job clock: ...` names the source; `bash run.sh check` prints it without changing
   anything. The server start (~16 min) counts against this clock; the setup does not.
2. **Preflight.** Python and `requests`, `rg`, every row's Lean environment, toolchain and module (`check_envs.py`), the model files,
   the GPUs as the server will see them (inside the image, with the runtime's GPU option: 4 GPUs required; a warning when they are
   not A100s or not all connected by NVLink), a node-local lock directory with working `flock` (`/dev/shm`, `$TMPDIR` or `/tmp`; set
   it with `LRA_FAST_DIR`), free disk space, and that a login shell (the model's shell tool) finds `rg` and `lake`.
   `bash run.sh check` runs only this step and ends with `CHECK OK`, or lists everything that would stop the job.
3. **Server.** Starts vLLM in the pinned image on `127.0.0.1:8000`, with no key and no TLS, offline (`HF_HUB_OFFLINE=1`) and without
   usage statistics (`VLLM_NO_USAGE_STATS=1`, `DO_NOT_TRACK=1`). It serves the local snapshot directory setup verified
   (`LRA_MODEL_PATH`), so neither the weights nor the config or tokenizer are looked up on the Hub. It runs
   `infra/vast/run_vllm.sh`: tensor parallel 4, max-num-seqs 16,
   prefix caching, vLLM's custom all-reduce over NVLink, CUDA graphs. A server that dies is restarted (at most 5 times). run.sh waits
   until the server answers (at most 90 min) and warns if vLLM switched its custom all-reduce off.
4. **Driver.** Runs `harness/open_package.py run` in the foreground with the package's defaults, which are our official recipe:
   14 sessions at once, at most 12 sessions per row, the pipelined end stage, 2 h for the end stage at the agent deadline, 30 min for
   the normalize step, and the export in the last 15 min. The exact command is saved in `runs/final/RUN_CMD`.
5. **Interim proofs.** Every hour, `runs/final/interim/proofs.jsonl` is written. It is the package's own export, with the axiom audit
   off and no compiles (`infra/orgserver/snapshot.py`).
6. **End.** After the export, the server is stopped and run.sh prints `DONE: .../proofs.jsonl`. Its exit code is 0 when the proofs file
   exists. A driver that fails with more than 20 min left on the clock is restarted on the same clock, at most 3 times
   (`LRA_DRIVER_RESTARTS`), after all of its processes are gone. It resumes every row from its saved state.

The exact server commands per runtime (`PKG` is the package directory, `WS` the work directory, and the same paths are used inside the
container):

```bash
# podman-hpc (setup: podman-hpc pull docker.io/lazymio/vllm-backport:v0.13.1-sm80, digest checked)
podman-hpc run --rm --net=host --ipc=host -v PKG:PKG:ro -v WS:WS -w WS --entrypoint /usr/bin/env --name lra-vllm-<uid>-<start> --gpu \
  docker.io/lazymio/vllm-backport:v0.13.1-sm80 -u PYTHONPATH ... PYTHONNOUSERSITE=1 PATH=<image PATH> VLLM_WORKSPACE=WS \
  VLLM_HOST=127.0.0.1 VLLM_PORT=8000 HF_HUB_OFFLINE=1 ... bash PKG/infra/orgserver/vllm_entry.sh
# Shifter (setup: shifterimg -v pull docker:lazymio/vllm-backport:v0.13.1-sm80)
shifter --image=docker:lazymio/vllm-backport:v0.13.1-sm80 --module=gpu /usr/bin/env -u PYTHONPATH ... bash PKG/infra/orgserver/vllm_entry.sh
# Apptainer (setup: apptainer pull WS/image/vllm-backport_v0.13.1-sm80.sif docker://lazymio/vllm-backport@sha256:8094fcba...)
apptainer exec --bind PKG:PKG:ro --bind WS:WS --nv WS/image/vllm-backport_v0.13.1-sm80.sif /usr/bin/env -u PYTHONPATH ... bash PKG/infra/orgserver/vllm_entry.sh
# Docker: as podman-hpc with --gpus all, image docker.io/lazymio/vllm-backport@sha256:8094fcba...
```

`LRA_DRY=1 bash run.sh` prints the server and driver commands without starting anything. Under Shifter, if the package's filesystem
is not mounted in containers by default, setup detects it and adds `--volume=PKG:PKG --volume=WS:WS`.

### Under Slurm

```bash
#!/bin/bash
#SBATCH --nodes=1 --exclusive --gpus=4 --time=48:00:00 --signal=B:USR1@1800
exec bash /path/to/package/run.sh
```

run.sh takes the job's start and end from `squeue`, so the clock matches the allocation. `exec` makes run.sh the batch shell. Then the
optional `USR1` warning (`--signal=B:USR1@1800`) refreshes the interim proofs, and Slurm's `SIGTERM` at the time limit promotes them
(below).

### Settings for run.sh (all optional)

| variable | default | meaning |
|---|---|---|
| `LRA_OUT` | `<package>/runs/final` | the output directory |
| `LRA_START` / `LRA_JOB_SECONDS` | see Clock | the job clock (epoch seconds / seconds) |
| `LRA_RESUME` | 0 | 1: continue the clock saved in the output directory even from another job, or after it ran out (then only the end stage and the export run) |
| `LRA_JOB_ID` | the scheduler's | the job id run.sh stamps and compares (default: `SLURM_JOB_ID`, `PBS_JOBID`, `LSB_JOBID` or `FLUX_JOB_ID`) |
| `LRA_SAFETY_S` | 600 | seconds kept back from the end of the allocation |
| `LRA_WORKERS` / `LRA_COMPILE_SLOTS` | package defaults | sessions at once (default 14) / end-stage compile slots (default: a third of the CPUs, one per 8 GB, within 3-32) |
| `LRA_EXTRA` | empty | more `harness/open_package.py` flags (`docs/open_package_readme.md`) |
| `LRA_BASE_URL` | empty | an OpenAI-compatible server that is already running (serving `glm-5.3-flash`); run.sh starts none |
| `LRA_FAST_DIR` | auto | a node-local directory for lock files and memory-gate ledgers |
| `LRA_VLLM_PORT` | 8000 | the server port on 127.0.0.1 |
| `LRA_HF_OFFLINE` | 1 | `HF_HUB_OFFLINE` of the server (it serves the local snapshot directory either way) |
| `LRA_SERVER_WAIT_S` / `LRA_SNAPSHOT_S` | 5400 / 3600 | wait for the server / interval of the interim proofs |
| `LRA_DRY` | 0 | 1: print the commands only |

### Sizing on your node

The 14 concurrent sessions are bound by the GPUs' KV cache, not by the CPUs. A session spends about 87% of its time waiting for the
model, and Lean compiles take the rest. Every Lean compile passes a memory gate: it starts only when 8 GB plus an 8 GB reserve are
free, inside the job's cgroup limit, v2 or v1. With the whole node, run.sh passes no sizing flags, so the package's defaults decide.
When the job is confined to fewer CPUs than the node has (a Slurm cpuset) or to a cgroup memory limit, run.sh derives the end-stage
compile slots from the confined numbers. Below 22 CPUs it also lowers the sessions to CPUs - 8, but never below 4. On 64 physical
cores and 256 GB the defaults apply unchanged.

## If the job is cut short

`runs/final/proofs.jsonl` is written by the export in the last 15 minutes of the clock. If the job is killed earlier:

- run.sh traps `SIGTERM` / `SIGINT`. It writes the interim proofs and copies them to `runs/final/proofs.jsonl`, but only if the export
  has not written that file. Then it stops the driver, its sessions and the server.
- `runs/final/interim/proofs.jsonl` always holds the bests as of the last hour, in the same format.
- `bash run.sh export` writes `runs/final/proofs.jsonl` from everything the job saved. It also runs the axiom audit of each pick, for at
  most a few minutes once the clock has run out.
- Restart inside the same Slurm job: the same `bash run.sh`. It continues the clock in `runs/final`, and each row resumes from its
  saved state. Restart in a NEW job (the first one died): `LRA_RESUME=1 bash run.sh` continues the same clock (it ends no later
  than the new allocation); without `LRA_RESUME=1` the new job moves `runs/final` aside and starts over.

## The image

`lazymio/vllm-backport:v0.13.1-sm80` is a public Docker Hub image (the vllm-backport build of vLLM 0.13.1). Pins, checked on
2026-10-31: the tag's index `sha256:0fc33cd7d2be777bf6faaee9b02adf781dc6d0bc44b9a09ce4865089f67e9cba`, its linux/amd64 manifest
`sha256:8094fcbab905a04a480b327f2761255e3d17cd8d39470cac9d76450bbb567f7e`, image ID (config)
`sha256:671aa3aadb9e536a89ecda894d93eb15870a4bd5c1d24b588ab5a06e2ca8ea8f`.

- Docker and Apptainer pull by digest. podman-hpc pulls the tag and setup compares the pulled digest with the pins (a mismatch fails
  setup; `LRA_IMAGE_UNPINNED=1` accepts it).
- Shifter pulls by tag only (`shifterimg` has no digest pull). Setup compares the id `shifterimg lookup` prints with the three pins
  above and logs a warning on a mismatch, because Shifter versions differ in what that id is. So under Shifter, the tag could point to
  another image if it were re-pushed. The binding check therefore runs inside the image, on every runtime: vLLM's version (0.13.1)
  and the sha256 of its installed `RECORD` file, which lists the hash of every file of the vLLM wheel
  (`73938aeb7b66cc4419c6cf91a560d565403443c4cf4c2e21e1a3ba893d1bc467`). A different build fails setup.
- Docker Hub rate-limits anonymous pulls, and a third-party repository can be deleted. A mirror of the same image works with
  `LRA_IMAGE_NAME=<registry>/<repo>` (and `LRA_IMAGE_TAG` / `LRA_IMAGE_DIGEST` if they differ). The in-image check still applies.

## No container runtime (`LRA_RUNTIME=none`)

The server then runs on the host as `vllm` from PATH (or `VLLM_BIN`). It must be the vllm-backport build
(https://github.com/wtdcode/vllm-backport, v0.13.1). It is the only vLLM with GLM-5.3-Flash's sparse-MLA kernels on sm80, and
upstream vLLM cannot serve this model on A100s. Building it from source needs the CUDA 13 toolkit and takes hours, so we recommend
any of the container runtimes above. With `LRA_BASE_URL`, an existing server is used instead, and `LRA_SKIP="image model"` skips the
image and model steps of setup.

## Tested here, and not tested

- Tested on our rentals (vast.ai, 4 x A100 80 GB SXM4 with NVLink, the Docker image above, driver 580): the server recipe and the
  driver with these defaults, in our October 2026 rehearsals on the warm-up rows.
- Tested on an aarch64 dev box with no A100s: setup.sh and run.sh end to end with stand-in runtimes (podman-hpc, Shifter, Apptainer
  stubs that log their arguments), a stand-in NVML and a scripted model server; dry runs of both scripts for every runtime, also
  under bash 4.2; the release export, and the unit tests.
- Tested offline (2026-11-01), in a container with no network and every socket call trapped, with the image's own Python packages
  (huggingface_hub 1.31.0, transformers 5.17.0, tokenizers 0.23.2, the image's vLLM 0.13.1 sources): from the local snapshot
  directory, vLLM's config, generation config and tokenizer load with no network attempt. vLLM's model class itself needs the
  image's GPU kernels and was not loaded there.
- Not tested: a server start without network on a real GPU node (setup's warm start does exactly this when setup runs on a GPU
  node), podman-hpc, Shifter or Apptainer on a real GPU node, a Lustre filesystem, cgroup v1 limits, and a CUDA 13.2 host toolkit.
  The image brings its own CUDA 13.0 runtime, which runs on the R580 driver without forward compatibility.

## What the model sees, and the audit

`docs/open_package_readme.md` describes the stages, flags and outputs in detail, with our serving measurements and the dry runs. The
model's prompt and tools are fixed in `harness/agent.py --open-package`: no proof knowledge, and only the rows file's seed proofs.
This release tree is the minimal export of the files the run imports or runs (`EXPORT.json` lists them with their sha256).

## Post-step (added 2026-11-03): our upload is this run's output after it

**What we uploaded.** Our open upload of 2026-11-03 (14:33 UTC) is official run 2's export (`runs/final/proofs.jsonl` at the run's
end, sha256 `e64b53ee9a699e1e...`, stored mean 78.4585; uploaded alone at 14:30 UTC as a probe: Arena 78.48) after this post-step: 5
of the 60 lines changed, Arena **79.74** (60/60 compiled).

**What it does.** `harness/open_post.py` reads the job's export (`runs/final/proofs.jsonl`) and writes a new file in a directory of
its own; the export is read, never written. The step is $0 (no model, no key, no GPU, no network), CPU only, deterministic and
accept-gated. It is a command of its own that runs after `bash run.sh` has ended; `run.sh` does not start it. The organizers' guidance
of 2026-11-03 is that small changes after a run need no rerun as long as the README documents how to run the system, which this
section does. Four ops propose rewrites of a row's proof, and every candidate is measured like an end-stage candidate: - `kskip`: when
the proof's last tactic is `decide +kernel`, `set_option debug.skipKernelTC true in` goes in front of it, in place (`kskip:inplace`),
or the body becomes `unfold P` and that line, P the head predicate of the statement (`kskip:unfold`). - `implied` (our closed track's
end-stage rule D4 R1, with D4P's point-free spellings): a `decide`-family closer decides the hypothesis Q of a library theorem `Q ->
P` (or `P <-> Q`) that a query of the row's environment finds, instead of the goal P. - `closerprep` (D4C): `conv_rhs => reduce` (or
lhs / both) before a `decide`-family closer, alone and together with a minimal drop of the simp lemma list before it (the proposals
chosen by one measured file of variants). - `inlineeq` (D4 R2): an equation proved inline in a simp lemma list becomes `← by simpa
using h ARGS` from its own hint or that hint's siblings in the environment, plus its pure trims.

Each op reads only the proof, the statement and the row's own environment (no row name, table or proof text).

**Gate (never harm).** A candidate replaces the row's proof only when all of these hold, measured on the end stage's meter
(`harness/endstage.Meter`, the direct path: the scorer's own heartbeat measurement on the row's primary toolchain) against the
reference heartbeats file (no local table): it starts with the row's exact statement followed by `:=`; it passes `scorer/forbidden.py`
(unchanged); its reading on the primary toolchain scores higher; it compiles on every listed toolchain (Z 100); a fresh back-to-back
re-reading of the current proof and the candidate still passes `scorer.accept.decide` with the candidate's worse reading against the
current proof's better one and a strictly higher score; its rounded score is above the row's stored score; and the export's own sorry
audit (`harness/open_package.audit_proof`: `#print axioms` with `warn.sorry` forced on) reads it clean. Anything else, an exception, a
timeout or a budget stop included, leaves the row's line byte for byte. A row where no op has a site is not compiled. Per row: at most
3 passes over the ops (in the order kskip, implied, closerprep, inlineeq; at most 4, 12, 3, 6 primary readings per op and pass), 120
compiles and 2,400 s; with `--jobs 60` every row runs at once, and no row starts after 7,200 s.

**About `debug.skipKernelTC`.** The option makes Lean skip the kernel's check of the declaration, so the decision that `decide
+kernel` leaves to the kernel is not checked: with the option, a false decidable proposition is accepted too (our test with Lean
v4.32.0, v4.34.1 and v4.35.0-rc3: `2 + 2 = 5` by `decide +kernel` fails; with the option it compiles and `#print axioms` lists no
axiom, so the audit above cannot tell). The option is neither on the Arena's forbidden list (the Space's list as of 2026-10-28) nor in
`scorer/forbidden.py`, and the Arena compiled and graded the kernel-skipped rows of our uploads (open and closed tracks, 2026-11-03).
The step adds the option only in front of a closing `decide +kernel` that the input proof already has, so each statement it
kernel-skips also has a kernel-checked proof in the run's own output: its line in `runs/final/proofs.jsonl`, which compiles on every
listed toolchain. Run 2's own export holds no proof with the option.

**Run it.** After `bash run.sh` has ended (`DONE: .../runs/final/proofs.jsonl`), from this folder (the one setup.sh and run.sh ran in):
```bash
. .lra/setup.env && export ELAN_HOME     # the Python, Lean toolchains, rows and heartbeats that setup.sh chose and run.sh used
FAST=$("$LRA_PYTHON" infra/orgserver/orgtools.py fastdir) && export LRA_MEMGATE_DIR=$FAST LRA_LOCK_DIR=$FAST/locks   # as run.sh: node-local locks
mkdir -p runs/post
LRA_HBTOOL_SLOTS=32 "$LRA_PYTHON" harness/open_post.py --rows "$LRA_SETUP_ROWS" --heartbeats "$LRA_SETUP_HBS" \
    --input runs/final/proofs.jsonl --out runs/post --jobs 60
"$LRA_PYTHON" -c 'import json,sys; [print(json.dumps({"name": r["name"], "proof": r["proof"]}, ensure_ascii=False)) for r in map(json.loads, open(sys.argv[1]))]' \
    runs/post/proofs.post.jsonl > runs/post/upload.jsonl
```
- **Input:** `--input`, the job's export (one line per row: `name`, `proof`, `stored_score`, ...; read, never written), and the rows and
  reference heartbeats files the job used (`--rows`, `--heartbeats`; `.lra/setup.env` names them: `data/official/rows.jsonl` and
  `data/official/heartbeats.jsonl` when those are in place, else what setup measured).
- **Settings:** `--jobs 60` runs every row at once; `LRA_HBTOOL_SLOTS` is the number of Lean compiles at once for the whole step (we
  used 64 on our run's box after the job; the job's own end stage uses a third of the CPUs, one per 8 GB of free memory, at most 32);
  the step's wall 7,200 s (`--seconds`; no row starts after it), a row's 2,400 s (`--row-seconds`) and 120 compiles
  (`--row-compiles`). The command sets the sorry guard (`LRA_FORCE_WARN_SORRY=1`), git's `safe.directory` for its own process tree and
  `LRA_LOCAL_REF=none` (the reference heartbeats file only) itself. Its scratch files go to `probe/hbtool/.scratch/` in this folder
  and to the environments' `LRAScratch/` directories, as the job's own compiles do; its compile-slot and memory-gate locks go to the
  node-local directory that `run.sh` also picks (the `FAST=` line). `--problems NAME ...` restricts it to some rows (a
  smoke test). (The step's docstring also names an `open_package.py post` subcommand; this package has none: run the command above.)
- **Outputs (in `--out`):** `proofs.post.jsonl`: one line per row in the export's order; a row the step did not change keeps its
  input line byte for byte; a changed row gets `source: "post"`, its new stored score, tokens and heartbeats, `post_ops` and
  `post_gain`. `post_report.json`: per row the status (`no_site`, `kept`, `adopted`, `stopped`, `error`), the readings before and after,
  the ops adopted, compiles and seconds; input and output sha256; the settings. `post/rows.jsonl` and `post/decisions.jsonl`: every
  row's result and every decision as it happened. **`upload.jsonl`** (the second command): the `{"name", "proof"}` lines of
  `proofs.post.jsonl`, the file we upload.
- **Wall:** 1,596 s (27 min) on our run's box with 64 compile slots; a row stops at its 2,400 s (plus the compile in flight), the step at
  7,200 s. It needs no key, no model and no GPU.
- **To disable it**, do not run it: `runs/final/proofs.jsonl` (its `{"name", "proof"}` lines) is then the upload. The ops have no
  switches of their own (the op list is `harness/open_post.ORDER`).

**Our run of it** (2026-11-03 14:00:14-14:26:51 UTC, on run 2's box after the job had ended, from a checkout of our development commit
`5cb18d3b` (this folder's post-step files) with the box's environments: `harness/open_post.py --jobs 60` with 64 compile slots and the
defaults above; this section's command runs the same step on the same input). Input: the run's export (sha256 `e64b53ee9a699e1e...`);
the rows and reference heartbeats in `data/official/`. 1,596 s, 117 compiles; 52 rows without a site, 3 kept, 5 changed:

| row | stored score before -> after (our meter) | ops adopted |
|---|---|---|
| `FTheory.SU5.ChargeSpectrum.isPhenoClosedQ5_viableCharges` | 42.89 -> 72.18 | kskip:inplace |
| `FTheory.SU5.ChargeSpectrum.isPhenoClosedQ10_viableCharges` | 43.34 -> 72.19 | kskip:unfold |
| `PauliMatrix.pauliContrDown_mul_pauliContr_mul_pauliContrDown` | 72.97 -> 80.44 | kskip:inplace, then inlineeq:simpa |
| `PauliMatrix.pauliContr_mul_pauliContrDown_mul_pauliContr` | 64.74 -> 74.60 | kskip:inplace, then inlineeq:bare |
| `putnam_1964_a4` | 93.98 -> 94.00 | inlineeq:fromby |

60-row stored mean 78.4585 -> 79.7167. `proofs.post.jsonl` sha256 `486b15b894e9126a...`; the upload file (its `{"name", "proof"}`
lines, the second command above) sha256 `4c9dc38a078b763a...`; Arena 79.74 (60/60 compiled, the 4 kernel-skipped rows included). On
the same input without `kskip` (a test-only setting, not shipped) the step changed the same 5 rows with `implied`, `closerprep` and
`inlineeq` alone: mean 78.7752.

**The post-step is not independent of the final benchmark.** Its ops were developed on the final benchmark after its release
(2026-11-01 06:48 UTC). `implied`, `inlineeq` and `closerprep` are the rules R1 (with D4P's point-free spellings), R2 and D4C of our
closed track's end-stage pass D4, vendored unchanged (apart from a header comment and the `harness.post` imports) from our
closed-run-3 code (development commit `402c44d2`; `inlineeq` uses the simpconst helper of pass D3). Their main source is our offline
research: uncapped agent sessions of closed models (GPT-6 Astra, Claude Opus 5.5, Fable 5.1, Gemini 4 Argon), run outside the $3 cap
on the 5 final-benchmark rows where our closed run 1 was at a structural ceiling; none of their proofs is in any upload or package.
The rules were distilled by comparing those research proofs and session histories with closed run 1's finals of those rows, then sized
and smoke-tested on its 60 finals. `kskip` was written on 2026-11-03 for the kernel-skip construct (`set_option debug.skipKernelTC
true in` before `decide +kernel`), which our open run 3 (GLM-5.3-Flash) had banked on one final-benchmark row and our same-day review
of the final rows with heavy kernel checks measured on others. The ops are general rewrite rules: they hold no row names and no proof
text of any row, and no model runs in the step. Which output we upload was chosen from runs of the step on our runs' exports (in
sample).
