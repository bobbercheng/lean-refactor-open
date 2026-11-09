# Notices

Our own code, notes and run records in this repository are licensed under the PolyForm Noncommercial License 1.0.0
(see [`LICENSE`](LICENSE)): free for study, research and other noncommercial use. Commercial use needs a separate license:
contact b.cheng@vexorium.net.

The following material was not written by us. It keeps its own terms, and the license above does not cover it.

| Material | Where | Terms |
|---|---|---|
| Lean source files of upstream libraries (ArkLib, Strata, cslib, PhysLean), copied as problem context | `**/context.lean`, the per-problem state folders and run trajectories (tag `open-warmup-a100-line-20261101`) | the upstream projects' licenses; the copied files keep their copyright headers (Apache 2.0 where stated) |
| Competition problems, seed proofs, reference proofs and heartbeat data (incl. PutnamBench statements); LeanPool development rows | `**/data/benchmark_*.jsonl`, `final/data/official/rows.jsonl`, `**/data/leanpool_dev/*.jsonl`, problem statements and seed proofs in run records | the competition organizers' and the original sources' terms |
| Model outputs (GLM-5.3-Flash, AWQ W4A16) | run trajectories, logs and the per-problem state (tag `open-warmup-a100-line-20261101`) | recorded as produced; the model's license terms apply |
| The model checkpoint and the serving image | referenced by name and revision in `final/infra/orgserver/`, `final/infra/vast/`, `warmup/README.md` and `warmup/package/infra/vast/`; not included | their publishers' terms |
| Closed-model outputs (9 example pairs for the opt-in style step of run 2's package) | `harness/style_rw_open_exemplars.json` of run 2's package (tag `open-run2-exact-748d964c`) and of `warmup/package/`: withheld from the public repository (sha256 `3ed15491e0b5b09a...`); the organizers received it in the code zips of run 2's package; run 3's package has no style step | the model providers' terms; the step is opt-in and off in our runs |

## What `final/` holds

Since 2026-11-08, `final/` on `main` is the code of our final upload `sub43` with the fast post stage: official run 3's export
(package `246ff1f1`), the post-step (development commit `a25416f5`) and `final/post_fast/`. For the fast post stage, `run.sh` and
`harness/open_package.py` changed, and `harness/open_post.py` and `harness/post/hintgrind.py` carry additions that only the stage
turns on; `final/post_fast/MANIFEST.json` lists every file that differs from tag `open-run3-post-final-sub43-20261104`. Package
`246ff1f1` has no style step and no `official_run/` folder. Until then `final/` held run 2's package, and the entries below that name
`final/` describe that package: run 2's exact export is the `final/` of tag `open-run2-exact-748d964c` (with the style step's code and
`official_run/`), and from 2026-11-02 the `final/` of tag `open-final-probe-20261102` (the same code without its switched-off
options; `official_run/` kept).

Changed for public release: decision attributions are removed or reworded in docstrings of `final/harness/open_post.py`,
`final/harness/post/d4_implied.py`, `kskip.py` and `projpath.py` (as at the `sub43` tag) and in one comment of
`final/harness/post/hintgrind.py`, one or two lines per file; these edits leave the code unchanged (same syntax tree apart from
docstrings). The `sub43` code zip holds the unredacted `d4_implied.py`, `kskip.py`, `projpath.py` and the tag's `open_post.py`;
`MANIFEST.json` gives the unredacted sha256 of `main`'s `open_post.py` and `hintgrind.py` as `measured_sha256`. Apart from these
lines, the post-step's files and `final/post_fast/` keep their comments and docstrings.

## Edits for public release (2026-10-28)

The history of this repository was rewritten on 2026-10-28, before it was made public. Every commit keeps its date and content,
except:

- home-directory paths read `/home/user` (also in logs and trajectories), and the user name in `ls -l` output reads `user`;
- one shell result in a trajectory (`warmup/probe/runs/fresh-a100-p5/`, interleaved row) listed the home directory of the machine
  that ran the driver; that listing is replaced by a note, and the JSON line stays valid;
- vast.ai instance and machine ids read `<instance>` and `<machine>`;
- the three A100 operation diaries (`warmup/docs/a100_poc_log.md`, `warmup/docs/a100_80_babysit.md`,
  `warmup/accounting/a100_poc.md`: rentals, bids, credit and host details) were deleted; `warmup/` still cites them as sources, and
  we keep them in our private development repository;
- internal notes were removed from comments, docstrings, help texts, log messages and docs; the code's behaviour is unchanged
  (same syntax tree apart from help-text strings and log messages);
- the provenance paragraphs of `README.md` and `warmup/README.md` were made more precise about how the harness was developed;
- model-facing prompts and recorded trajectories are unchanged apart from the items above.

## Edits for public release (2026-11-01)

The material added on 2026-11-01 (`final/` as first added, replaced the same day by the run-2 package, and the new `warmup/`) did not go through the 2026-10-28 rewrite. The code under `final/` is the code that ran; only its docs were edited. The `warmup/` scripts and docs are records
kept as they ran, with the edits listed here.

Withheld or changed:

- `final/harness/style_rw_open_exemplars.json` is withheld from the public repository (sha256 `3ed15491e0b5b09a...`). It holds the 9
  closed-model example pairs of the opt-in style step (`--style-rw on`; off by default and in our runs). Two of the nine pairs come from
  our internal development sets, not from benchmark rows. The organizers receive the file in our submitted code zip. Without it,
  `--style-rw on` refuses to start and nothing else changes. `warmup/package/` leaves out the same file. Both `EXPORT.json` files
  still list its sha256.
  On 2026-11-01 the history was rewritten again to remove this file from every commit (it was added on 2026-11-01 with `final/`).
- `final/README.md` has a "Repository layout (added 2026-11-01)" section above the export's own README, so it no longer matches its
  entry in `final/EXPORT.json`. `final/` is the export our official run (run 2, package `748d964c`) shipped, file for file; until
  2026-11-01 ~18:30 UTC it held run 1's package (`1d1a31d4`).
- `final/official_run/DECISIONS.env` is a sanitized copy (values only, notes shortened).
- `warmup/README.md` and `warmup/rehearsal_run/docs/b104_turncap_result.md`: vast.ai instance ids replaced by box labels (Iowa box 1,
  the Mississippi box, ...).
- `warmup/rehearsal_run/infra/sync/sidecar.py` and `probe/a100-alarm/gcs_status.py`: the GCS bucket name reads `gs://<bucket>`.
- Seven scripts in `warmup/rehearsal_run/session_scripts/`: the session scratchpad directory reads `"<scratchpad>"`.
- `warmup/rehearsal_run/probe/a100-upload/climb/climb_stop.sh` and `probe/p85e/warmup_stop_at_release.sh`: the Azure VM address and
  login user are required variables (`LRA_VM_IP`, `LRA_VM_USER`), and the VM's name reads "the closed-track VM".
- `warmup/rehearsal_run/probe/a100-alarm/`: the fixed tunnel port is a required variable or argument (`BORE_PORT`).
- `warmup/rehearsal_run/infra/vast/onstart_tunnel.sh`: the push-notification topic is read from `NTFY_TOPIC` or
  `/workspace/ntfy_topic`.
- `warmup/rehearsal_run/session_scripts/watch88_v3.sh`: a comment no longer names another team.

Kept as they ran (the 2026-10-28 list above does not hold for this material):

- Home-directory paths: the scripts in `warmup/` keep our development paths (`/home/bobber/...`).
- vast.ai instance and machine ids remain in the scripts of `final/official_run/` and `warmup/rehearsal_run/`, including
  `warmup/rehearsal_run/infra/vast/bad_machines.txt`. In the older history, a few vast.ai offer ids and one instance id also remain
  (`warmup/docs/a100_poc_runbook.md`, `warmup/CODE_VERSIONS.md`).
- Internal notes were not removed: comments, help texts, prompts and docs in `final/` and `warmup/` keep dated operator decisions,
  review ids, credit amounts and babysitting notes, and some scripts append to files of our private development repository (operation
  diaries, accounting) by path. In the package itself, the exporter stripped comments from the Python files and cut docstrings to
  their first line before our run; strings, help texts and prompts keep their notes.

Other disclosures:

- A since-rotated push-notification topic was in an earlier version of `warmup/rehearsal_run/infra/vast/onstart_tunnel.sh`. Since
  2026-11-09 it is in none of this repository's files or commits (below).
- `final/official_run/probe/a100-alarm/tunnel_watch_host.sh` keeps the fixed port of our tunnel server as its default. The server
  requires a client secret, which is not in this repository.
- `final/harness/agent.py` (and `warmup/package/harness/agent.py`) has a dev-only Vertex proxy preset whose URL names our GCP project
  id and a local proxy port. `--open-package` does not use it; neither value is a credential.
- `final/official_run/infra/sync/sidecar.py` has our GCS bucket name as its `--bucket` default. The bucket is private; its key is not
  in this repository.
- `final/harness/agent.py` has closed-line prompt texts (the `--closed-lessons` habit, mined from our closed-model lines, and a review
  lever). `--open-package` forces them off, but the model's shell tool can read the file.
- The model-free end stage of the open pipeline (the r10 rounds, on by default: `final/probe/open_package/end_r10.json`,
  `final/harness/endstage_r10.py`) is shared with our closed-track final. It holds mechanical rewrite families and contains no model
  output.
- The dry run's default rows (`final/probe/open_package/dry_run.sh` and its copies in `warmup/`) name two rows of our internal
  development pool (upstream library declarations). The pool's files are not in this repository.

## History replaced (2026-11-09)

On 2026-11-09 we replaced the git history of this repository, so that every commit carries our current author address (Bobber
Cheng, bobbercheng@hotmail.com) and the old commit messages are gone:

- `main` is one commit: the files of `main` on 2026-11-09, with this section and the edits that replace commit ids by tags.
- Each tag is one commit without parents. It holds exactly the files the tag held before and keeps the tag's date; annotated tags keep their messages. The releases were recreated with their titles, notes (commit ids updated) and files.
- Two more tags keep files that only the old history had: `open-warmup-a100-line-20261101` (the files of 2026-11-01 before `warmup/` was
  replaced: the Oct 6-13 A100 warm-up line, run 1's `final/` package and the README of that day) and
  `open-run3-fast-post-20261106-perrow` (the fast post stage as of 2026-11-06, with its per-row input files
  `final/post_fast/partition1.json` and `weights.json`).
- The `release/*` branches were dropped; their files are in the tags.
- Not kept: the old commits and their messages, and the earlier versions of files between these snapshots. Commit ids of this
  repository cited before 2026-11-09 (in the tags' own files, for example) no longer resolve; the tags hold the files. Commit ids of
  our development repository (such as the package and development commits named in this repository) are not affected.
