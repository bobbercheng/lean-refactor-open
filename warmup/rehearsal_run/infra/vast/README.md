# vast.ai scripts for the A100 proof of concept

Operator decisions (2026-10-06): POC on 4×A100 80 GB (the reproduction hardware class), **interruptible bid** instances
because they are cheaper, check availability without renting, and have every script ready before renting.
Runbook with the reasoning: `docs/a100_poc_runbook.md`.

Pins: image `lazymio/vllm-backport:v0.13.1-sm80` (sha256:8094fcbab905…, 2026-09-16, GLM-5.3-Flash supported since v0.11.2);
checkpoint `wtdcode/GLM-5.3-Flash-AWQ-W4A16` @ `abd7b07719111f137e1de8a0c1b7e01c11b74d1a` (190.8 GB, 24 files).

| Script | Does | Spends money? |
|---|---|---|
| `search.sh` | lists 4×A100-80GB offers (bid + on-demand, verified and all hosts) and the account balance | no |
| `create.sh <offer> <bid>` | rents the instance (image, 300 GB disk, ssh, port 8000, `onstart.sh`, bid price); **dry-run unless `CONFIRM=yes`** | yes |
| `onstart.sh` | runs in the container on every start, minimal: repair the SSH key file modes, refuse occupied hosts (`/workspace/BAD_HOST`), and relaunch `/workspace/run_vllm.sh` if the bootstrap installed it (what brings the server back after a pre-emption resume) | — |
| `bootstrap.sh <id>` | from the GB10 over SSH, observable and re-runnable: wait for SSH (port must open within 3 min or the host is destroyed, exit 3) → host check + nvtop install within 4 min (else destroyed, exit 5) → install `/workspace/env` (API key, pins) + `run_vllm.sh` → pre-download the checkpoint with progress → start the server → wait for READY | no |
| `server_up.sh <id> [--bridge]` | THE readiness check: vast record → TCP → pinned-TLS /v1/models → real 2-token completion → (bridge); one line UP / DOWN layer=… with an inside-the-box diagnosis; exit 0/1 | no |
| `health.py <id>` | continuous watchdog (service `lra-health`, every 60 s): pre-emption, credit, direct SSH, server path, vLLM alive, GPUs/ECC/temp, disk, new engine errors, stalls; WARN/CRITICAL/RECOVERED lines in `probe/a100-health.log` | no |
| `provision.sh [attempts=3]` | rent + bootstrap with automatic replacement: cheapest verified bid offer not in `bad_machines.txt`, bid = min_bid + $0.01; a host dropped by bootstrap (exit 3/5) is blacklisted and a new one rented; any other failure stops with the instance kept; writes `probe/a100-instance-id` | **yes** (CONFIRM=yes) |
| `run_vllm.sh` | the server launcher installed on the instance (pinned vLLM-backport recipe, `--api-key`, logs `/workspace/vllm.log`, marker `/workspace/READY`) | — |
| `status.sh` | instance state, $/h, bid flag; server health through the tunnel | no |
| `tunnel.sh <id>` | `ssh -L 8000:localhost:8000` to the instance (foreground) | no |
| `bench.py` | 3 concurrent 2k-token generations → tok/s per stream and aggregate → `accounting/a100_poc.md` | no |
| `launch_line.sh FIRST LAST [OLD]` | rent + prepare + start in parallel (operator 2026-10-09): `provision.sh`; as soon as a host's bootstrap reaches the model download, `PHASE=prep migrate_harness.sh` runs beside it (code, tools, then Kaggle envs and bucket state side by side); at READY only `PHASE=start` (re-sync, start or resume the chain, watchers, release OLD) | yes |
| `outbid_sentry.sh <id> [cap]` | armed by `provision.sh` at rental (unit `lra-a100-sentry`): any stop starts `bid_ladder.sh` within 30 s; credit stops get a CREDIT line; at the cap it logs SWITCH INSTANCES | bids |
| `regain.sh <old> [new_cap] [old_cap]` | races the old instance's ladder against new offers (every 20 s), keeps whichever wins, releases the other | yes |
| `winback.sh <id> [cap]` | an instance outbid before the run started: ladder (or wait for the sentry's), then the resumable bootstrap, bridge, health | bids |
| `start_chain_instance.sh FIRST LAST` | on the instance: sidecar, W&B live, then `chain_on_instance.sh` for new passes | — |
| `destroy.sh <id>` | destroys the instance, 3 attempts, verified gone; exit 0 gone / 1 still listed (never rent a replacement) / 2 HELD; **dry-run unless `CONFIRM=yes`** | stops spend |
| `spend_guard.sh <id> <credit>` | armed by `provision.sh` at rental (unit `lra-a100-spendguard`): destroys EVERY instance when spend >= SPEND_CAP ($68), credit < $5, a KEPT marker is 45 min old without an ack, or `probe/a100-stop-now` exists; runs the PRE_DESTROY pull first; stops the units; logs CREDIT-STOP | stops spend |
| `rehearsal.sh <phase>` | the A100 rehearsal of the open package (docs/a100_rehearsal.md): plan, export, rows, rent (CONFIRM=yes), prep, leanpool, run, status, release | rent/run: yes |
| `package_run.sh` | ON the node: preflight (endpoint ok, envs complete, disk), then `open_package.py run` detached; writes RUN_CMD + relaunch.sh | — |
| `relaunch.sh` | ON the node after an outbid resume (onstart.sh hook, package_watch.sh): waits for READY, re-runs RUN_CMD if no driver is alive | — |
| `package_watch.sh <id>` | GB10 unit `lra-a100-watch`: relaunch after a stop, rsync-pull results every 5 min, no-progress watchdog (KEPT marker), release when the run is done | stops spend |
| `build_publish_leanpool.sh` | ON the node: build the LeanPool env (x86-64), pack it with the new toolchain (`pack_envs.sh` subsets); the publish is driven by `rehearsal.sh leanpool` with the Kaggle key piped over SSH | — |
| `probe/a100/dry_run.sh vast\|package` | $0 dry runs against `probe/a100/fake_vastai.py` (and the package's fake model): every path above without renting | no |

Flow: `search.sh` → pick an offer (prefer verified, ≥ 1 Gbps, reliability ≥ 0.95; bid = min_bid + $0.01; when outbid, raise in small steps, never a jump: operator rule 2026-10-08) → top up the balance →
`CONFIRM=yes create.sh <offer> <bid>` → `bootstrap.sh <id>` (waits for SSH, checks the host, downloads, starts, waits for READY — all visible) → `tunnel.sh <id>` (separate terminal) → `bench.py` → harness smoke and the fresh pass (`docs/a100_poc_runbook.md` §4, with
`--max-api-retries 20` so a pre-emption pause does not kill the run) → `CONFIRM=yes destroy.sh <id>`.

Interruptible caveats: when outbid the instance is paused, the server dies, and `onstart.sh` restarts it on resume
(download skipped thanks to the on-disk HF cache; load + cudagraph capture ≈ 10 min). The harness waits up to ≈ 1.5 h
per call with `--max-api-retries 20`; a longer pause loses that problem's remaining turns (its best is kept).

Every script sources `common.sh` (login PATH + `require <tools>`, ONE bid cap `BID_CAP_DEFAULT` = $2.00, the `kept` marker helper, the unit
suffix and the `LRA_FAKE_VAST_BIN` shim hook of the dry runs): systemd user services otherwise lack `vastai` (miniconda) and `socat` (~/.local/bin).
The Oct 6-9 pass-line scripts (`launch_line.sh`, `migrate_harness.sh`, `chain_on_instance.sh`, `resume_watch.sh`, `finalize_a100.sh`, `autostart_instance.sh`)
are NOT used for the package rehearsal (review 2026-10-28): they copy the whole dev checkout and resume `agent.py` passes, not `open_package.py`.
SSH: direct only (`ssh -p <port> root@<ip>`, shown by `status.sh`); the vast proxy is not used.
