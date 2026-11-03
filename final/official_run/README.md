# Our official open-track run: orchestration scripts (2026-11-01)

These are the scripts we used to run the package (`../`, release export of `748d964c`; run 1 used `1d1a31d4`) for our own official
open-track run on a rented vast.ai on-demand 4 x A100 SXM4 box. They are a record of how we ran it. The organizers' rerun on their own server does not need them:
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
- The tunnel server's client secret: `probe/a100-alarm/tunnel_watch_host.sh` keeps the fixed port of our tunnel server
  (`bore.vexorium.net`) as its default. The server requires a client secret, which is not in this repository.
- Run state and logs of the official run (`probe/a100-official/state`, `official.log`, `rental-*.json`, the bad-machine list): host
  and billing details; not part of this sync.
- `probe/a100/official_dry_run.sh`, `probe/a100/ondemand_dry_run.sh` and their fake `vastai`: our $0 local tests of these scripts.
- The bid-market tooling of the warm-up line (sentry, bid ladder, bid keeper): not used by the on-demand official run.

## Run 1 and run 2 (2026-11-01)

The box first ran package `1d1a31d4` (run 1, started 07:56:49 UTC, 14 concurrent sessions). From about 09:10 UTC the 14 first sessions
reached long contexts together and filled the vLLM KV cache, which cut the server's output to about a third; at 11:00 UTC run 1 was
relaunched with 11 sessions. Package `748d964c` (the fixes listed in `../README.md`) was then exported and run 2 started from the seed
proofs on the same box and the same environments:

1. `run2_switch/box_stop_archive.sh` (on the box): stops run 1 with the package's own stop script (sessions ended by their process tag,
   run 1 exported as a record: 60 rows, stored mean 44.79) and moves run 1's directories aside, so run 2 starts with no state.
2. `infra/vast/official.sh export` and `ship` (with `FINAL_COMMIT` = `748d964c` in `DECISIONS.env`): the release export and its install
   on the box (code only: environments and released rows stay).
3. `run2_switch/box_vllm_restart.sh` (on the box): restarts vLLM with the same recipe script, stopping it by process group.
4. `CLOCK_RESET=1 infra/vast/official.sh start` (a new 48 h clock: run 2 started 11:55:21 UTC, ends 2026-11-03 11:55:21 UTC), then `arm`.

Run 2 is our official run: its export is what we upload. `infra/vast/package_run.sh` in this folder is the copy from `26e5be1a` (default
14 sessions); the one in `../infra/vast/` is the run's (default 11), and `DECISIONS.env` sets 11 either way. The two `run2_switch/`
scripts were written for the switch on 2026-11-01 and are not in any commit of our development repository; their comments are edited
for public release.

## Environment fixes

[`env_fixes/NOTES.md`](env_fixes/NOTES.md): what we fixed on the box on 2026-11-01 and why, with `envfix.py`, `env_audit.py` and the
environment pins the run uses (`env_fixes/harness_envs.official.json`, written by `infra/open_package/envs_from_rows.py` from the
released rows). `envfix.py` and `env_audit.py` were written for this run on 2026-11-01; they are not in any commit of our development
repository.
