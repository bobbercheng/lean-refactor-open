# Our official open-track run: orchestration scripts (2026-11-01)

These are the scripts we used to run the package (`../`, release export of `1d1a31d4`) for our own official open-track run on a rented
vast.ai on-demand 4 x A100 SXM4 box. They are a record of how we ran it. The organizers' rerun on their own server does not need them:
it uses `../setup.sh` and `../run.sh` (see `../README.md`).

Source: our development repository at commit `26e5be1a` (branch `a100-rehearsal`; = `1d1a31d4` + one commit adding the
`OFF/HOLD_START` gate in `official_ondemand.sh` on 2026-11-01). Every file below is a byte copy of that commit (paths kept as in the
development repository; the package files they call, such as `infra/vast/run_vllm.sh`, `harness_setup.sh`, `endpoint.sh`,
`relaunch.sh`, `infra/sync/restore_envs.sh`, `harness/open_package.py`, are in `../`).

## Entry points

| File | Role |
|---|---|
| `infra/vast/official_ondemand.sh` | the release-time driver: `go` = wait for the release, rows + export, rent the on-demand box, bootstrap, vLLM recipe, environments, reference heartbeats, then `official.sh start` and arm the watch / guard / alarm. Stops before `start` while `OFF/HOLD_START` exists (re-running `go` resumes). |
| `infra/vast/official.sh` | the phases on a box: `rows`, `envs`, `start` (CLOCK_START: the 48 h job clock starts at `start`), `arm`, `pull`, `final`, `stop-p85b`; reads `DECISIONS.env` at every phase |
| `infra/vast/official_envs_host.sh` | runs ON the box: plans the environments missing for the rows and builds them with `harness_setup.sh` |
| `infra/vast/package_run.sh` | runs ON the box: launches `harness/open_package.py run` detached and writes `RUN_CMD` + `relaunch.sh` (also in `../infra/vast/`) |
| `infra/vast/vllm_recipe_host.sh` | runs ON the box: installs and starts the vLLM recipe (`std`) as `/workspace/run_vllm.sh` |
| `DECISIONS.env` | the run's decisions (sanitized copy: values only, notes shortened) |

## Helpers they call (not in the export)

| File | Role |
|---|---|
| `infra/vast/common.sh` | sourced by every `infra/vast` script: PATH, `require`, unit-name suffix, KEPT marker |
| `infra/vast/create.sh`, `destroy.sh` | rent (`ONDEMAND=1`: no bid) / release a vast.ai instance; vast's reply with the instance key goes to an ignored log, masked |
| `infra/vast/onstart.sh` | vast's on-start hook inside the container (SSH modes, occupied-GPU refusal, relaunch of vLLM and the driver after a restart) |
| `infra/vast/bootstrap.sh`, `server_up.sh` | over SSH: checkpoint download, TLS endpoint, vLLM start, readiness |
| `infra/vast/scoped_vastai/vastai` | a `vastai` wrapper scoped to one instance id, so the spend guard can only see / destroy the official box |
| `infra/vast/spend_guard.sh` | spend cap on the box (asks first while the run is busy) |
| `infra/vast/package_watch.sh`, `package_stop_host.sh` | periodic pulls of the run directory, relaunch on stall, final pull; graceful stop of a run on a box |
| `probe/a100-alarm/alarm.py`, `run_busy.py`, `tunnel_watch_host.sh` | alarms (session errors, driver / vLLM / GPU / disk, unreachable box) and the box-side status writer / SSH tunnel watch |
| `infra/sync/sidecar.py` | box-side copy of run data to our bucket (reads a bucket-only key file by path) |

## Not included, and why

- Credentials and private values: the vLLM bearer key, the TLS pairs (`~/.config/vexorium/vllm_tls*`), the bucket key file, the Kaggle
  key, the vast.ai CLI configuration, and the private push-notification topic file (`probe/a100-ntfy-topic`). The scripts read each of
  them from a file path; none of the values is in this repository.
- Run state and logs of the official run (`probe/a100-official/state`, `official.log`, `rental-*.json`, the bad-machine list): host
  and billing details; not part of this sync.
- `probe/a100/official_dry_run.sh`, `probe/a100/ondemand_dry_run.sh` and their fake `vastai`: our $0 local tests of these scripts.
- The bid-market tooling of the warm-up line (sentry, bid ladder, bid keeper): not used by the on-demand official run.

## Environment fixes

[`env_fixes/NOTES.md`](env_fixes/NOTES.md): what we fixed on the box on 2026-11-01 and why, with `envfix.py`, `env_audit.py` and the
environment pins the run uses (`env_fixes/harness_envs.official.json`, written by `infra/open_package/envs_from_rows.py` from the
released rows).
