# Environment fixes on our official open-track box (2026-11-01)

Factual record of what we changed in the ENVIRONMENTS (not in the package code) of our official run's box on 2026-11-01, and why. The
package commits (`1d1a31d4` for run 1, `748d964c` for run 2 = `../../`) are unchanged by them; the fixes for the package itself are listed at the end as pending. All times UTC.

## 1. Five released rows: reference proof failed in our measured compile (`envfix.py`)

**Symptom.** The reference-heartbeat step (refhb) could not measure 5 of the 60 released rows, and every candidate proof on those rows
failed to compile in our measured compile, although each file compiles fine in plain file order:

- `HermitianMat.inv_convex`
- `Lambda.callOfLFunc_eraseMetadata_congr`
- `ProximityGap.RS_exists_nonzero_kernelVec_of_det_eq_zero_natDegree_le_one`
- `ProximityGap.RS_jointAgreement_of_goodCoeffs_card_gt`
- `Vlasov.transportedIntegral_continuousOn`

**Cause (ours, not the data or the environments).** Each of these declarations sits under a chain of `omit ... in`, `set_option ... in`
or `open ... in` lines. `scorer/compile.py` (`split_modifiers`) leaves that chain above the heartbeat-measuring command it inserts
(`arena_measure`), so the `... in` binds to the measuring command instead of the theorem, and the theorem is compiled without it. The
observed failures: an unused-section-variable warning turned error (the `omit` was lost), `F[X]` without `open Polynomial`, `Tendsto`
without `open Filter`, and a heartbeat timeout at the default limit without the row's `set_option maxHeartbeats`.

**Env-side workaround (`envfix.py`).** For each of the 5 rows and EACH of its toolchain pins, in the environment's copy of the row's
file, strip the trailing ` in` from the `open|omit|set_option|include|unseal|variable ... in` lines directly above the declaration
(docstrings, attributes and blank lines skipped). The line count is unchanged; our compile truncates the file after the declaration, so
the now-global commands reach only the theorem (and the measuring command, which they already reached). Dry run by default; `--apply`
writes and keeps a backup of each file.

```bash
python3 envfix.py ROOT ROWS.jsonl            # dry run: prints each EDIT
python3 envfix.py ROOT ROWS.jsonl --apply --backup DIR
```

Verified before use on our closed-track box (same `scorer/compile.py` code): with the edit, all 5 rows compile in the measured path
on their pins, and refhb measured all 5 directly.

**Caution.** Apply it only AFTER the environment's modules are built. `lake build` compiles whole files, and a now-global `omit` or
`open` can break later declarations of the same module. On our box (07:44-07:45 UTC) the edit was applied to the arklib, physlib and
strata pins at once; the Vlasov edit was reverted in both LeanPool environments while `leanpool-v4.35.0-rc3` was still building, to be
re-applied after the build, followed by a refhb re-measure of the 5 rows. The run's start was held (`OFF/HOLD_START`, see
`../infra/vast/official_ondemand.sh`) so these 5 rows start from fixed files and measured references.

**Pending package fix.** `split_modifiers` must move the whole `... in` chain below `arena_measure` (or setup must apply the same
environment edit). Until then, the organizers' rerun of the package (`748d964c` as well as `1d1a31d4`) has the same failure on these 5 rows unless the environment gets the same edit: `envfix_auto.py` (this folder, added 2026-11-01) makes it automatically for every row whose reference fails for this reason (see ../../README.md, "Required to reproduce our run's environment").

## 2. Environment audit against the pins (`env_audit.py`)

`env_audit.py harness_envs.official.json` (run from the package root) prints, for every environment in the list, the pinned commit and
the commit checked out in `envs/<name>` (`git -c safe.directory=* rev-parse HEAD`): OK, MISMATCH or MISSING.
`harness_envs.official.json` here is the list our run used (17 environments; written by `infra/open_package/envs_from_rows.py` from the
released rows).

Our box at 07:45 UTC: 15 OK, `leanpool-v4.35.0-rc3` at the wrong commit, `leanpool-v4.34.0` missing (both explained below).

## 3. Box fixes (vast.ai host, our box only)

1. **git `safe.directory`.** The environments restored from our Kaggle archives are owned by another user than root. git then refused
   to work in them ("detected dubious ownership"), so `harness_setup.sh` failed to add the `leanpool-v4.34.0` worktree from
   `envs/leanpool.git-main`, while still printing `SETUP DONE ... failed=0`. Fix: `git config --global safe.directory '*'` for root,
   then `git worktree prune` and a rebuild of the missing pin. (The organizers' entry points `setup.sh` / `run.sh` set
   `safe.directory=*` for their own process tree, `infra/orgserver/lib.sh`, since `5074dc3f`; our vast-side builder
   `official_envs_host.sh` -> `harness_setup.sh` does not.)
2. **Off-pin LeanPool environment.** `envs/leanpool-v4.35.0-rc3` came from an older archive at commit `edbe5bd5`; the final pin is
   `630eb920`. The environment check counts a directory with built modules as present and does not compare its commit, so it was
   accepted. Fix: the old directory moved aside (`leanpool-v4.35.0-rc3.edbe5bd5-old`) and the pin rebuilt at `630eb920` with
   `official_envs_host.sh`.
3. **Open-files limit.** The open-files soft limit on the box was 1024, too low for `lake exe cache get` (os error 24, too many open
   files). Fix: raise `ulimit -n` in the shell before environment builds.

**Pending package fixes** (no change made to the frozen package): the vast builder's environment check should compare each
environment's HEAD with its pin, and `harness_setup.sh` should count a failed worktree add as a failure.
