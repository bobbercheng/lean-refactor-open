# Warm-up rehearsal of the open package (open-weight track, team Vexorium)

This folder holds the scripts and environment setup of our last open-track rehearsal on the 15 warm-up problems: the **p85 / p85b**
runs of GLM-5.3-Flash (AWQ W4A16), self-hosted with vLLM on rented 4x A100 80 GB SXM4 boxes on vast.ai, from 2026-10-30 to 2026-11-01.
It replaces the earlier `warmup/` material of the Oct 6-13 A100 line (82.03 / 82.29). That material is still in this repository's git
history, up to commit `b244fbd`.

Scope: the scripts (code and small configs) that built the package, rented and set up the boxes, ran and watched the run, picked the
upload and stopped everything. No run outputs and no proofs (see "Not included").

## 1. What ran

| | |
|---|---|
| Model / serving | GLM-5.3-Flash AWQ W4A16 on vLLM (`vllm-backport` sm80 image), tensor parallel 4, custom all-reduce on (from 2026-10-31 05:52), recipe in `package/infra/vast/run_vllm.sh` + `rehearsal_run/infra/vast/vllm_recipe_host.sh` |
| Driver | `harness/open_package.py run` from the release export (`package/`): agent stage, then the eager end pipeline and the export |
| p85 | export of commit `b2240a2d`; started 2026-10-30 21:27 UTC (job clock from 22:57 UTC after the first outbid); 15 warm-up rows + 3 non-sealed LeanPool dev rows; 8 then 12 workers |
| p85b | export of commit **`528c9694`** (= `package/`), resumed from p85's own state on the 15 warm-up rows; 12 then 15 workers, `--max-sessions` 6 then 12, `--end-pipeline on`, `--end-seconds 7200` |
| p85c patch | from 2026-10-31 17:12 UTC: `package/p85c/p85c_patch_host.sh` adds an `--open-card` flag to the box copy of `harness/agent.py`, and the driver passes `--agent-arg=--open-card=/workspace/p85c/open_card_dialect.md` (the generic compact-dialect card, `package/p85c/open_card_dialect.md`). The shipped package was not changed |
| RUN_CMD (final box) | `python3 harness/open_package.py run --rows /workspace/lra-run-p85b/rows.jsonl --heartbeats /workspace/lra-run-p85b/heartbeats.jsonl --out /workspace/out-p85b --tag p85b --base-url https://lra-a100:8000/v1 --api-key-file /root/.config/vexorium/vllm_api_key --api-model glm-5.3-flash --started-at 1793443016 --job-seconds 91384 --workers 15 --max-sessions 12 --end-seconds 7200 --end-pipeline on --agent-arg=--open-card=/workspace/p85c/open_card_dialect.md` |
| Side scheduler | p85e (`rehearsal_run/probe/p85e/`), running beside the p85b driver from 2026-10-31 21:58 UTC. Versions: v1/v2 (write-back plus extra sessions in the idle slots above the driver's cap), v3 (post-driver mode with an `END_AT` file), v3.1 (KV-cache admission gate after the saturation incident) and v3.2-ab (the b104 A/B, `rehearsal_run/probe/b104/p85e_ab/`) |

### Timeline (UTC)

| when | event |
|---|---|
| Oct 30 20:42 | p85 rented: Iowa box 1 (bid $2.68). Prep restored 15 envs + 10 toolchains from the public Kaggle datasets in ~17 min. Driver started 21:27 |
| Oct 30 22:44 | Outbid. Moved to North Carolina box 1; job clock 22:57 |
| Oct 31 05:31-06:30 | p85 on NC: style step turned off (driver restart), vLLM restarted with custom all-reduce (+36% decode), 12 workers (+46% total tok/s) |
| Oct 31 10:05 | Outbid above the operator's bid cap. New box: Iowa box 2 (bid $2.90, keeper floor `--floor`, commit 528c9694); p85b launched 10:37 from p85's state |
| Oct 31 12:35-12:50 | Iowa host offline ~8 min (not an outbid). A spare was rented and destroyed; p85b resumed in place |
| Oct 31 15:52 | Outbid above the cap. Moved to North Carolina box 2; p85b relaunched 16:08 |
| Oct 31 16:40-16:56 | NC outbid. A spare box in Mississippi rented; NC came back; spare released |
| Oct 31 16:57-17:12 | Workers 12 -> 15, max sessions 6 -> 12; the p85c restart (dialect card through `--open-card`) |
| Oct 31 17:26 | **sub18** uploaded to the open board: **85.13** (predicted 85.14) |
| Oct 31 18:23-18:50 | NC stopped again. Moved to **the Mississippi box** (bid $3.40); p85b relaunched 18:49 (15 workers, cap 12, card; job end Nov 1 12:00) |
| Oct 31 21:58 | p85e side scheduler started (write-back of verified bests + sessions in the idle slots, twins on 5 rows) |
| Oct 31 22:06 | **sub19** uploaded: **86.66** (L 74.66, H 85.33, Z 100; 15/15 compile on every pin; 23 h from seed) |
| Nov 1 00:00-01:34 | **vLLM KV-cache saturation** (KV 0.91-0.98, 127 preemptions, 0-293 tok/s instead of ~450): p85e's long-context twin sessions on top of the driver at max-num-seqs 16. Fixed by p85e v3.1 (cap 14, KV gate 0.75, pacing, self-shedding) and by stopping three long twins by exact pid. Our private repository has the full report (`docs/a100_kv_saturation_2026-11-01.md`); the package-side guard is b101-kvguard |
| Nov 1 04:39-06:34 | b104 late-turn output cap A/B through p85e v3.2-ab, 9 pairs: **NO-GO** (`rehearsal_run/docs/b104_turncap_result.md`) |
| Nov 1 05:39-07:10 | gap6 step test (`rehearsal_run/probe/gap6/`): one structural move per GLM session |
| Nov 1 06:48 | Official benchmark released. The warm-up climb was wound down: `warmup_stop_at_release.sh`, END_AT moved |
| Nov 1 07:10 | p85b ended early with its export (`lra-p85e-final`: STOP, final pull, pick). **Union pick stored 87.49**, not uploaded |

Results: sub18 85.13 and sub19 86.66 are on the public open board. The final union pick (87.49, stored score) was not uploaded.

## 2. Folder layout

```
warmup/
  package/          the release export the p85b box ran (commit 528c9694) + the p85c patch and card
  rehearsal_run/    the scripts that rented, set up, ran, watched, picked and stopped (paths as in our dev checkout)
  env_setup/        how the Lean environments were provisioned (Kaggle restore, build scripts, manifests, as of 528c9694)
```

### package/
- Regenerated with `python3 probe/open_package/export_release.py --commit 528c9694 --out <dir>`, run from a worktree at 528c9694 so the
  exporter's allowlist matches that commit. Result: 79 files, import closure 34 modules, leak scan pass (0 hits, 62 waived), exemplar check
  pass. The file contents are byte-identical to the export shipped to the box (every sha256 in `EXPORT.json` matches; only the `at`
  timestamp differs). The box tarball's checksum is in `BOX_EXPORT.sha256`.
- **Withheld:** `harness/style_rw_open_exemplars.json`. It holds the opt-in style step's exemplar pairs, derived from the closed line's
  step file. p85b never used it: `--style-rw` was off. Its sha256 is still listed in `EXPORT.json`. Without it, `--style-rw on` refuses
  to start (preflight) and nothing else changes.
- `p85c/p85c_patch_host.sh` and `p85c/open_card_dialect.md`: the box-only `--open-card` patch and the card it loaded (identical to
  `harness/open_card_dialect.md` on later commits).
- Start with `package/docs/open_package_readme.md`.

### rehearsal_run/
Versions: tracked scripts come from the `a100-rehearsal` branch at **`7ebb4f91`**, the last commit before the Mississippi relaunch
(Oct 31 18:12 UTC). Scripts that were untracked or changed live (p85e, `pick_union.py`, `p85d_writeback_host.sh`) are the final working-tree
versions. The b104 files come from branch `b104-turncap` 160f4500. The gap6 files come from our dev main.

| path | role |
|---|---|
| `infra/vast/rehearsal.sh` | GB10 orchestrator: `plan export rows rent prep leanpool run status release watch` |
| `infra/vast/provision.sh`, `search.sh`, `create.sh`, `destroy.sh`, `common.sh`, `_fmt.py`, `bad_machines.txt` | offer search, rental (CONFIRM-gated), verified destroy, host blacklist |
| `infra/vast/bootstrap.sh`, `onstart.sh`, `onstart_tunnel.sh`, `server_up.sh` | box bring-up: host guard, model download (bounded), vLLM start, NVLink / all-reduce check |
| `infra/vast/run_vllm.sh`, `vllm_recipe_host.sh`, `endpoint.sh`, `tls_bridge.sh`, `tunnel*.sh` | serving recipe; TLS endpoint with a pinned cert and a bearer key; self-healing local bridge |
| `infra/vast/package_run.sh`, `relaunch.sh`, `package_stop_host.sh` | on the box: preflight + detached driver; relaunch after a resume; stop with export |
| `infra/vast/p85b_launch_host.sh`, `p85b_arm_gb10.sh` | p85b continuation launcher (box) and its GB10 arming (watch, alarm, guard re-arm) |
| `infra/vast/package_watch.sh` | GB10 watcher: pulls, no-progress watchdog, release (honours hold files) |
| `infra/vast/spend_guard.sh`, `outbid_sentry.sh`, `bid_keeper.py` (+ test), `bid_ladder.sh`, `regain.sh`, `winback.sh`, `autostart_instance.sh` | money and outbid handling: spend stop-loss (asks before deleting a busy box), outbid bid ladder, bid keeper with floor and cap |
| `infra/vast/health.py`, `status.sh`, `resume_after_provision.sh`, `resume_watch.sh` | health watchdog, status, in-place resume |
| `infra/vast/scale_test.sh`, `scale_report.py`, `scale_p85b_host.sh`, `bench.py` | throughput / worker-count scaling tests |
| `infra/sync/sidecar.py` | box-side snapshot sidecar to our GCS bucket (needs a bucket key; none here) |
| `probe/a100-alarm/` | GB10 alarm (`alarm.py`: CRITICAL/WARN lines, private push topic read from a file), babysit check, box status writer, tunnel watch / refresh |
| `probe/a100/p85b_dry_run.sh`, `fake_vastai.py` | the $0 dry run of the p85b launcher (fake vast.ai, fake model, real Lean) |
| `probe/p85c/` | p85c coordinated restart, blind-start lineages for three stuck rows, p85d squeeze write-back |
| `probe/p85e/` | side scheduler (`p85e_xloop_host.py` v3.1), `p85e_ctl.sh` (handover / env / end), `p85e_common.sh`, `p85e_wbpush.sh` (write-back push + mirror), `p85e_final.sh` (final pull + pick), `p85e_stop_all.sh`, `p85e_unhold.sh`, `p85e_units_v3.sh`, `warmup_stop_at_release.sh` (the one release-time stop command), `warmup_resetwatch.py` (board-reset watch) |
| `probe/b104/` | `box_patch_agent.py` (opt-in late-turn cap overlay) and `p85e_ab/` (A/B variant builder `make_ab.py`, scheduler v3.2-ab, report, revert) |
| `probe/a100-upload/pick_union.py`, `probe/a100/warmup_upload_measure.py`, `probe/calib/eval_official.py` | upload pick: candidates from the open-line roots (allowlisted, closed-line paths denied), measured on the official all-pin meter; union pick. `eval_official.py` reads `probe/calib/ref_direct.json` (direct-path reference heartbeats of the warm-up rows), which is not included |
| `probe/a100-upload/climb/` | climb guard (ends the warm-up climb on a board reset or at the hard cap), `climb_stop.sh`, `start_guard.sh` |
| `probe/gap6/` | gap6 step test: `detect.py` (one structural move per row, chosen from the row's own GLM best), `gap6_host.py` (paired S/C arms), `gap6_chain.py` (chain mode), `gap6_lemmas.py` (generic lemma-name search), `gap6_start.sh` |
| `session_scripts/` | the babysitter's one-off scripts per box move: `p85b_setup_ia.sh` + `ia_bringup.sh` (Iowa), `p85b_resume_{ib,nc2,ms,ms2}.sh` (resume chains: wait SSH, prep, state restore, aux, relaunch, GB10 re-arm), `relaunch_nc2_w15.sh`, `aux_p85b_host.sh`, `vllm_swap_host.sh` (all-reduce recipe swap by pid), `vllm_sample.py`, `watch88_v3.sh` (pick watcher), `stop_p85b-t06-k1.sh` (stop one session by exact pid) |
| `docs/b104_turncap_result.md` | the late-turn cap test result |

How they fit together: `rehearsal.sh export|rows|rent|prep|run` builds the export, rents a box through `provision.sh` (which arms
`spend_guard.sh` and `outbid_sentry.sh`), runs `bootstrap.sh` (vLLM up), restores the environments (`env_setup/`), then starts
`package_run.sh` on the box and `package_watch.sh` + `alarm.py` on the GB10. After an outbid, the sentry and `bid_keeper.py` fight for
the box up to the operator's cap. Above the cap, a new box is rented and a `session_scripts/p85b_resume_*.sh` chain restores the state and
relaunches through `relaunch.sh`. p85e runs beside the driver, controlled with `p85e_ctl.sh`; the GB10 units `p85e_wbpush.sh` and
`p85e_final.sh` end it. `pick_union.py` produces the upload candidate.

Hard-coded paths (`/home/bobber/source/lra-a100`, `/workspace/...`) are left as they ran; the session scratchpad directory in
`session_scripts/` reads `<scratchpad>`. Values replaced by required variables: the Azure VM address and login user (`LRA_VM_IP`,
`LRA_VM_USER`, in `warmup_stop_at_release.sh` and `climb_stop.sh`) and the fixed tunnel port (`BORE_PORT` / a required argument, in
`probe/a100-alarm/`). The GCS bucket name reads `gs://<bucket>` (`infra/sync/sidecar.py`, `probe/a100-alarm/gcs_status.py`).

### env_setup/
As of commit 528c9694:
- `infra/sync/restore_envs.sh` restores every environment and toolchain archive listed in `infra/vast/envs_kaggle.tsv` from our public
  Kaggle datasets (`bobber/lean-env-*-x86-64`). `pack_envs.sh` and `publish_envs_kaggle.sh` are the other direction (the Kaggle key stays on
  the GB10, piped in, never on a rented disk). `fingerprint.py` checks the result.
- `infra/vast/harness_setup.sh` installs the box tools (pip incl. kaggle, rg, jq, zstd), then the restore. `harness_envs.json` maps
  sources and versions to env directories.
- `infra/vast/build_publish_leanpool.sh` + `envs/build_leanpool.sh`: the one env not on Kaggle at first (LeanPool dev), built and packed on
  an x86-64 box (a GB10 build is aarch64 and cannot be uploaded).
- `envs/build_*.sh`, `setup_mathlib.sh`, `setup_projects.sh`, `manifest.json` / `manifest.py`: how the env checkouts were built and pinned.
- `infra/open_package/envs_from_rows.py`, `rehearsal_rows.py`, `check_envs.py`: the rows -> envs list of a run and the preflight that
  refuses a run with a missing env.

Lessons from the Nov 1 official setup that also apply to these rehearsal boxes: Kaggle-restored envs owned by another user make git
fail with "dubious ownership"; an env directory at an old commit still passes the built-modules check; `ulimit -n 1024` is too low for
`lake exe cache get`. Notes and fixes: [`../final/official_run/env_fixes/NOTES.md`](../final/official_run/env_fixes/NOTES.md).

## 3. Not included

- **Proofs and run outputs:** no `state.json`, `best.lean`, `proofs.jsonl`, `verified.jsonl`, `squeeze_best.jsonl`, candidate or
  submission files, session logs or trajectories. The competition rows in `package/data/` (statements and the given proofs) are the
  organizers' input data.
- **Credentials and endpoints:** no Kaggle key, GCS key, vLLM API key, push topic value, TLS pair, SSH keys, or SSH host:port files. The
  scripts read these from `~/.config/vexorium/`, `probe/a100-ntfy-topic` and the vast.ai CLI's own configuration.
- **Closed-track material:** no closed-model output, closed-track proofs or union content. `pick_union.py` denies closed-line paths and
  run ids. `gap6_chain.py` logs each row's score gap to the closed rehearsal's best proof, read from a local `azure.json` (scores only, not
  included); that proof is never shown to the model.
- Dropped from the copy after the leak scan: `envs/notes.md` (it quotes fragments of warm-up proofs), `probe/calib/ref_direct.json`
  (warm-up reference heartbeats), a vLLM decode benchmark that reads one warm-up library file, and `probe/a100/dry_run.sh`. Also left out:
  the Azure VM squeeze / dialect loops (`probe/a100-upload/sqloop`, `sqvm`, `dialect`; they ran on the closed track's box), their loop
  restarter, and the W&B restart script (it also mirrored closed-track runs).
- Older script versions (`probe/p85e/.v1`-`.v3`, `watch88.sh` v1/v2). Our private development repository keeps the operation diaries
  (`docs/a100_80_babysit.md`, `docs/a100_poc_log.md`, `accounting/`). They contain rental, bid and host details.

Code license: see the repository root (`LICENSE`, `NOTICE.md`).
