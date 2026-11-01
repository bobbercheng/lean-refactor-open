# vast.ai scripts for the A100 line

Decisions (2026-10-06): POC on 4×A100 80 GB (the reproduction hardware class), **interruptible bid** instances
because they are cheaper, check availability without renting, and have every script ready before renting.
Runbook with the reasoning: `docs/a100_poc_runbook.md`. The replication steps are in `../../README.md` §4.

Pins: image `lazymio/vllm-backport:v0.13.1-sm80` (sha256:8094fcbab905…, 2026-09-16, GLM-5.3-Flash supported since v0.11.2);
checkpoint `wtdcode/GLM-5.3-Flash-AWQ-W4A16` @ `abd7b07719111f137e1de8a0c1b7e01c11b74d1a` (190.8 GB; the file count, 24, has no
source in this tree and is unverified).

The staged copies of most scripts here lost their executable bit. Run `chmod +x infra/vast/*.sh` once before using them.

## Scripts

The **replication** column says whether the replication route in `../../README.md` §4 uses the script: **yes** (it does), **optional**,
**history** (it ran part of our line but a replication does not need it), or **no** (other experiments, not part of the line).

### Rent and serve (control machine, except where noted)

| Script | Does | Spends money? | replication |
|---|---|---|---|
| `search.sh` | lists 4×A100-80GB offers (bid + on-demand, verified and all hosts) and the account credit | no | yes |
| `_fmt.py` | formats `vastai search offers --raw` output, one line per offer (used by `search.sh`) | no | yes |
| `provision.sh [attempts=3]` | rent + bootstrap with automatic replacement: cheapest verified bid offer not in `bad_machines.txt`, bid = min_bid + $0.01; a host dropped by bootstrap (exit 3/5) is blacklisted and a new one rented; any other failure stops with the instance kept. On success it writes `probe/a100-instance-id`, starts the TLS bridge (`lra-bridge`) and the health watchdog (`lra-health`) as systemd user units, arms the outbid sentry, and prints `READY <id>` only if the bridge path answers | **yes** (CONFIRM=yes) | yes |
| `bad_machines.txt` | machines `provision.sh` must skip (empty as staged) | — | yes |
| `create.sh <offer> <bid>` | rents the instance (image, `DISK` GB, default 300; ssh, port 8000, `onstart.sh`, bid price); **dry-run unless `CONFIRM=yes`** | yes | yes (via `provision.sh`) |
| `last_create.json` | the last `create` response; its per-instance key is redacted | — | no |
| `onstart.sh` | runs in the container on every start, minimal: repair the SSH key file modes, refuse occupied hosts (`/workspace/BAD_HOST`), and relaunch `/workspace/run_vllm.sh` if the bootstrap installed it (what brings the server back after a pre-emption resume) | — | yes |
| `bootstrap.sh <id>` | over SSH, observable and re-runnable: wait for SSH (port must open within 3 min or the host is destroyed, exit 3) → host check + nvtop install within 4 min (else destroyed, exit 5) → install `/workspace/env` (API key, pins) + `run_vllm.sh` and the pinned TLS pair → pre-download the checkpoint with progress → start the server → wait for READY | no | yes |
| `run_vllm.sh` | the server launcher installed on the instance (pinned vLLM-backport recipe, `--api-key`, TLS, logs `/workspace/vllm.log`, marker `/workspace/READY`) | — | yes |
| `server_up.sh <id> [--bridge]` | THE readiness check: vast record → TCP → pinned-TLS /v1/models → real 2-token completion → (bridge); one line UP / DOWN layer=… with an inside-the-box diagnosis; exit 0/1 | no | yes |
| `tls_bridge.sh <id>` | self-healing local bridge 127.0.0.1:8000 → the instance's TLS port (socat, pinned certificate, real-path probe) | no | yes when the harness runs on another machine; not used on the instance |
| `health.py <id>` | continuous watchdog (service `lra-health`, every 60 s): pre-emption, credit, direct SSH, server path, vLLM alive, GPUs/ECC/temp, disk, new engine errors, stalls; WARN/CRITICAL/RECOVERED lines in `probe/a100-health.log` | no | optional |
| `status.sh` | instance state, $/h, bid flag; server health through a local tunnel or bridge | no | optional |
| `bench.py` | N concurrent 2k-token generations (default 3) → tok/s per stream and aggregate → `accounting/a100_poc.md` | no | optional |
| `destroy.sh <id>` | destroys the instance; **dry-run unless `CONFIRM=yes`** | stops spend | yes |
| `common.sh` | sourced by the scripts: login PATH and `require <tools>` | — | yes |
| `tunnel.sh <id>` | `ssh -L 8000:localhost:8000` to the instance (foreground). Replaced by `tls_bridge.sh` from 2026-10-06 22:43 | no | history |
| `tunnel_keepalive.sh` | restarted the SSH tunnel during pass 1 | no | history |

### Outbids and pre-emptions (control machine)

| Script | Does | replication |
|---|---|---|
| `outbid_sentry.sh <id> <cap>` | armed by `provision.sh` at rental; every 30 s reads vast and starts `bid_ladder.sh` on any stop; logs `SWITCH INSTANCES` when a ladder ends at the cap | optional (bid rentals) |
| `bid_ladder.sh <id> [cap] [step] [interval]` | raises the bid in small steps up to a cap until vast runs the instance again | optional (bid rentals) |
| `winback.sh` | wins back an instance stopped before the run was on it, then re-runs its bootstrap, bridge and health | optional |
| `regain.sh` | races winning back the old instance against renting a new verified offer; keeps whichever is READY first | optional |
| `resume_watch.sh <id> <pass> <last>` | waits until a stopped instance runs again, starts `resume_pass_instance.sh` there, re-arms `finalize_a100.sh` | optional (needs `finalize_a100.sh`'s missing files for the re-arm) |

### Harness on the instance (passes 6–8 and the replication route)

| Script / file | Does | replication |
|---|---|---|
| `harness_setup.sh` | runs on the instance: installs elan, ripgrep, jq, zstd and `requests`; full clones of the project repos (`envs/<repo>.git-main`); builds the 15 Lean environments in `harness_envs.json`; ends with `SETUP DONE ok=<n> failed=<m>` | yes |
| `harness_envs.json` | the environments `harness_setup.sh` builds (repo, URL, pinned commit, modules to build, whether to fetch Mathlib's cache). It does not pin the upstream clones' HEADs: `envs/pin_upstream.sh` does | yes |
| `envs_kaggle.tsv` | our public Kaggle packs of the built x86_64 envs, with sizes and checksums (their restore script is not in this tree) | optional |
| `endpoint.sh` | sourced: sets the model endpoint (`LRA_BASE_URL`, or our vast TLS setup), `AGENT_EXTRA`, the extra flags from `LRA_AGENT_FLAGS` or the file `AGENT_FLAGS`, and `preflight()` | yes |
| `start_chain_instance.sh FIRST LAST` | starts the optional sidecar and W&B updater when their credentials exist, then `chain_on_instance.sh` | yes |
| `chain_on_instance.sh FIRST LAST` | preflight, then one pass at a time through `harness/replicate.sh` (tag `fresh-a100`, 4 workers), import and assembly after each pass, stop rules | yes |
| `resume_pass_instance.sh PASS LAST` | after a vast stop: waits for a real model answer, finishes the cut pass for every problem without an `end` record, then continues the chain | yes |
| `autostart_instance.sh` | started the chain the moment the env build finished (pass 6) | history |
| `finalize_a100.sh` | stopped the run at the target, uploaded and checked the backups, pushed the repo, destroyed the instance. Needs `infra/sync/`, `assemble/live_line.py` and `harness/push.sh`, which are not in this tree | no |

### Line history: passes 1–5 on the workstation

| Script | Does | replication |
|---|---|---|
| `chain_pass2.sh` | chained pass 2 onto pass 1 (`--max-tokens 6000` plus the go-file flags) | history |
| `pass3.sh` | pass 3: preconditions, effort probe (needs `probe/effort_probe.py`, not included), smoke, pass, validation | history |
| `chain_pass3.sh` | the first pass-3 attempt, which never ran a pass and released the instance (lesson 18 in `docs/a100_poc_log.md`) | history |
| `chain_a100_80.sh` | passes 4–5 on the workstation through the bridge; hard-codes our checkout path | history |
| `handover_gb10.sh` | stopped the workstation chain after pass 5 so the instance could take over | history |
| `resume_after_provision.sh` | restarted the evaluation, scaling and trial jobs after a pre-emption (2026-10-08) | no |

### Other experiments on the A100 (not part of the line)

| Script | Does | replication |
|---|---|---|
| `lreval_chain.sh` | one-shot Lean-refactor skill eval at three effort settings (needs `probe/lr_eval.py`, not included) | no |
| `scale_test.sh`, `scale_report.py` | worker-scaling test and its report (`docs/a100_scale_test.md`) | no |
| `model_trial.sh` | second-model serving trial (retired) | no |

## Flow used for passes 1–5 (history)

`search.sh` → pick an offer (prefer verified, ≥ 1 Gbps, reliability ≥ 0.95; bid = min_bid + $0.01; when outbid, raise in small steps, never a jump: 2026-10-08) → top up the credit →
`CONFIRM=yes create.sh <offer> <bid>` → `bootstrap.sh <id>` (waits for SSH, checks the host, downloads, starts, waits for READY — all visible) → `tunnel.sh <id>` (separate terminal; from 2026-10-06 22:43 the TLS bridge `tls_bridge.sh <id>`) → `bench.py` → harness smoke and the fresh pass (`docs/a100_poc_runbook.md` §4, with
`--max-api-retries 20` so a pre-emption pause does not kill the run) → `CONFIRM=yes destroy.sh <id>`.

Interruptible caveats: when outbid the instance is paused, the server dies, and `onstart.sh` restarts it on resume
(download skipped thanks to the on-disk HF cache; load + cudagraph capture ≈ 10 min). The harness waits up to ≈ 1.5 h
per call with `--max-api-retries 20`; a longer pause loses that problem's remaining turns (its best is kept).

Every script sources `common.sh` (login PATH + `require <tools>`): systemd user services otherwise lack `vastai` (miniconda) and `socat` (~/.local/bin).
SSH: direct only (`ssh -p <port> root@<ip>`, shown by `status.sh`); the vast proxy is not used.
