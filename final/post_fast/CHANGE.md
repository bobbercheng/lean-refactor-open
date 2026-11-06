POST-HOC, not part of any upload; the uploaded open result stays sub43 at Arena 82.55 from the original 4.7 h post-step, which ran after the GPU job.

Replication of sub43 stays at tag `open-run3-post-final-sub43-20261104`.

# The fast post stage inside `run.sh`

This puts our measured post-step speed-up inside `run.sh`, with the smallest change we could make. The post stage runs the same seven passes and accept gate as the uploaded post-step, through a shared compile service with prefix servers and speculative reads. New in its decisions are merged candidates and the hintgrind gate and cache, on in this route and off with `LRA_POST_ROUTE=off`; 156 of T0b's 347 adoptions were merge ops (M). Labels: M measured, D derived, E estimated.

1. The agent stage runs to its deadline as before.
2. The end stage, dialect step and normalize are skipped. The job clock does not change.
3. The driver audits and exports the picks to `proofs.jsonl` and exits as before. `stop_all` stops vLLM.
4. `post_stage.sh` runs on the picks until job end minus 60 s. `JOB_END` is 47:50 on a 48 h job.
5. Every 5 minutes and at the end, the rows that rose go into `proofs.jsonl` by atomic rename.

**The picks are written first and gains are saved every 5 minutes, so a hard kill at any moment leaves a whole file and loses at most about 5 minutes of gains.** A row never goes down, except that a re-run or `run.sh export` writes the picks again before the saved gains return (Details).

Run it with run 3's recipe, which made both measured inputs. Plain `bash run.sh` leaves the automation card off and differs from them. `LRA_POST_ROUTE=off` restores the job of the tag.

`LRA_EXTRA="--automation-card on --automation-card-min-ref-tokens 1000" bash run.sh`

| File | + | - | Why |
|---|---:|---:|---|
| `run.sh` | 13 | 1 | Switch, driver flag, one block after `stop_all`, gains back after `run.sh export` |
| `harness/open_package.py` | 5 | 3 | Flag `--no-end-stages`, three conditions; `Clock` untouched |
| `harness/open_post.py` | 136 | 2 | The runs' code: merged candidates |
| `harness/post/hintgrind.py` | 68 | 0 | The runs' code: gate and cache |
| `README.md` | 7 | 0 | A first section that points here |
| `post_fast/`, new | 14 files | | Executor, `post_stage.sh` (39 lines), `merge_post.py` (47 lines), this file, `MANIFEST.json` |

## Limits

T0b ran from the pick at 45.25 h with no stages, and fullV7m1s from run 3's export. r14 and r37 are rows, counted from 0.

- It has never run on an A100 node or any GPU node, and we accepted that for this package.
- The whole route has run on no machine end to end. What was tested: fake Lean and one real-Lean row (Details).
- The measured runs are on one Azure F64as_v7 with 64 cores, with a warmed page cache. T0b crossed 82.556, the stored mean of the uploaded seven passes, at 53.87 min after about 13.8 min of warm-up, from our own picks, which do not ship.
- All time limits stay at the values measured on the F64, and no reading exists on the organizers' node. A slower node starts to lose gain at about 1.05-1.10 times the F64's wall time (Details). No 48 h score claim is made: the hard stop bounds the time by design, and the score at the stop on a node is unknown.
- It is one run, stopped at target. r37 stopped mid-pass. The 25 rows with the same input in both runs held exactly. 4.17 min of the gain over fullV7m1s is r14's timing; the real saving is the 120.3 min of skipped stages (M).
- 82.5657 is a stored mean. A fresh verification of T0b's final proofs on the same F64 reads an exact mean of 82.5648, .0088 over 82.556, with 60 of 60 rows compiling on every pin (M).
- r14's proof at 84.40 fails a full kernel check in that verification (M). It scores only with `debug.skipKernelTC`, and forced back on r14 alone T0b reads 82.4370, under 82.556 (D).
- T0b's agent stage had 45:15 with no vLLM load on the clock. Under `run.sh` it has about 44:49, or 20-26 min less (D/E), priced at .009-.034 at the final (E), against T0b's .0097 margin over 82.556.
- Only rows named in `partition1.json` get the post stage. For any other rows file use `LRA_POST_ROUTE=off`: the fast route would skip the end stages, do no post work and end early (M, fake Lean).
- If the post stage fails before its first merge, the job still ends with a valid `proofs.jsonl`, but that file is the agent picks, about 79.25 stored, not the 79.68 the stages gave. That floor is a known cost of the smaller change.

# Details

## Node speed

The organizers stated 64 physical cores, 256 GB RAM and 4x A100 80 GB; they did not state the CPU model, and no reading exists on their node. Our only same-proof reading is on a rented box with a Xeon Platinum 8368: its wall time was 1.25-1.31 times an Azure D64's, on one proof with both machines alone, and a D64 alone has the F64's speed (M). If a node is slower than the F64, the fixed limits start to bite at a ratio of about 1.05-1.10, for example `QUERY_TIMEOUT`, where ratio is a host's wall time over the F64's. Lane gain, from the long search ops, is at risk of .012 at ratio 1.31 and .485 at 2.0 (D), against a T0b margin of .0097 over 82.556.

## If it fails

| What happens | `proofs.jsonl` afterwards |
|---|---|
| The post stage cannot start, or under 2 min remain | The picks |
| A part dies or hangs, or TERM arrives | Picks plus all gains logged; the final merge runs. USR1 changes nothing: `promote` never replaces an existing `proofs.jsonl` |
| SIGKILL of the stage or the whole job, at any moment | A whole file: picks plus the gains of the last merge |
| A re-run or `run.sh export` after that | The picks for a while, then the saved gains return |

- A merge compares each row against the current `proofs.jsonl`, so a mid-run read that offers a lower row changes nothing, and a failed merge leaves the file as it was.
- A re-run's driver writes the picks back by rename. The first step of `post_stage.sh` then puts the gains back from `proofs.merged.jsonl`, before its time guard, and `run.sh export` does the same after its export. On a re-run the file reads as the picks from the driver's export until the post stage starts, up to about 11 min (E, the audit plus the token-report join). A kill in that stretch leaves the gains in `proofs.merged.jsonl`, and the next re-run or `run.sh export` returns them. With `LRA_POST_ROUTE=off` nothing is put back.
- `summary.json` describes the picks, not the merged file. In our run the pick at 45.25 h was never audited; in this job the driver audits it.
- After SIGKILL of `post_stage.sh` the compile workers stop at the cap, but the compile service and its prefix servers do not stop by themselves: 121 were still alive 30 s after the job clock (M). That the end of the job on a node kills them is assumed, not tested.

## What is identical to what

- Against the tag: 158 of the 163 files in `final/` are byte-identical, 5 changed (table above), 14 are new, all in `post_fast/`, and 0 were removed. `setup.sh`, `EXPORT.json` and `warmup/` do not change. The repository's root `README.md`, outside the zip, gains a short note that says what this branch is.
- We did not use `--dialect off`, `--no-normalize` or a lower `--end-seconds`: the first turns off the agent stage's own dial pass, and the other two move the agent deadline.
- `pf_svc.py`, `pf_drive.py`, `pf_worker.py`, `prefix_backend.py`, `merge_warm.py`, `snapshot.py`, `prefix_server/`, `partition1.json` and `weights.json` are byte-identical to our local copies of the files those runs used. The runs logged an input hash but no code hash.
- `open_post.py` and `hintgrind.py` are our local copies of the runs' code with one comment line redacted in each, and the same syntax tree apart from the docstring. Their new paths are on by `LRA_POST_MERGE`, `LRA_HG_GATE` and `LRA_HG_PERSIST`, which `post_stage.sh` sets. `MANIFEST.json` gives the sha256 and origin of every file that differs from the tag.
- `post_stage.sh` is the runner of T0b with its `/workspace` paths replaced by arguments, this run's picks as the input and the stop taken from the job clock. The runners `run_T0.sh` and `launch_T0b.sh` hold fixed paths, so they do not ship. `merge_post.py` takes a row's emitted line if its stored score is at least the current one and it passes the export's static check, checks the names against the rows file, in order, and writes by rename after an fsync.
- `EXPORT.json` lists `run.sh` and `harness/open_package.py`, so those two sha256 values no longer match. The README's sentence that every listed file is the run's file holds only at the tag.
- The tag's tree is not exactly the measured tree. Of the tag's 121 Python files, 117 have the measured syntax tree (M). The other four are `open_post.py` and `hintgrind.py`, now replaced, and the release stubs `harness/architect.py` and `harness/lemma_search.py`. The post-step imports only `_KW` and `bound_names` from those stubs, and their docstrings say both were copied verbatim from the development modules.
- `weights.json` is per-row seconds from run 3's post-step on these rows. It sets launch order and compile priority, holds no proof text, and is in-sample.
- Nothing in the job reads a stored proof. The post stage starts from this run's own picks.

## Measured results

Both runs were on one Azure F64as_v7, not through `run.sh`.

| Run | Input | Stored mean | Time | Label |
|---|---|---:|---:|---|
| fullV7m1s | run 3's export `0664621d`, after the stages | 82.56 | 58.03 min | M |
| T0b | the pick at 45.25 h, no end stage, dialect or normalize, stored 79.2505 | 82.5657 | 53.87 min | M |

- Replaying the 5-minute merges on T0b's logs gives the same 82.5657, with 0 rows ending on another proof (D). It would have held 81.98 at 30 min (D).
- T0b's 53.87 min includes the first build of the prefix servers: 8 toolchains, 18.6 s in sum on the F64 (M). No separate build step is needed.

## What was tested

On a development host, from an export tree unpacked from the zip, with fake Lean and a stub model: the real `run.sh` and driver, then the real `pf_svc`, `pf_drive`, `pf_worker`, `snapshot.py` and prefix path, on a short job clock. All numbers here are M.

- 18 main failure cases passed: the cap stop, a dead or hung part, TERM, INT, USR1, SIGKILL of the stage and of the whole job, a read that offers lower rows, no C compiler. Each left 60 rows in order, with 0 torn reads and 0 rows below the picks.
- 46 further cases: signals between any two writes of a merge, write errors, clock edges, re-runs and `run.sh export` after a kill, other rows files. 44 passed, and in the re-run and export cases 0 rows ended below what the kill left. The other 2 are the injected hangs under Smaller limits. Three of the 44 passed only when run one at a time: at a load of about 160 the test's kill came too late for its gate (E), and the file stayed valid.
- `merge_post.py` alone: 13 unit checks passed.
- With `LRA_POST_ROUTE=off`, the dry output, `RUN_CMD`, output file names and `proofs.jsonl` equal the tag's, and the shell trace differs only by the two guard lines and a memory figure.
- Real Lean ran on one row only, `putnam_1964_b2`, from its seed, with a 15 min window on that host: 1 toolchain built, 4 prefix servers, about 270 compiles, 3 adoptions with a clean audit, stored 33.33 to 85.63, stopped by `--cap` 60 s before job end. That shows the parts connect on real Lean. It says nothing about speed or score.
- Not tested: a real vLLM stop, a real scheduler's kill, 60 rows on real Lean, a real full or noexec work dir.

## Smaller limits

- Both measured runs were stopped at about an hour, while the post stage's window here is about 144-158 min (D), so about 1.5 h of it is a stretch neither run measured. T0b's lowest free memory was 119 GB at minute 34 of a 54 min run (M), which says nothing about that stretch. The stop by `--cap` has run on real Lean on one row only.
- `--slots 48` and the cap of 120 servers are fixed. `LRA_WORKERS`, `LRA_COMPILE_SLOTS` and `run.sh`'s sizing do not reach the post stage, so a smaller allocation is unmeasured and may be oversubscribed.
- `$FAST` must allow exec and have room, and its path must stay under about 85 bytes: a longer one skips the post stage in about 60 s, and the job ends on the picks (M, fake Lean). Without exec, compiles go fresh with no alarm, which is slower. With no room, gains are lost with no alarm. Neither can lower a row. `LRA_PREFIX_ROOT` overrides the server location.
- `pf_drive` puts compile scratch under `probe/hbtool/.scratch-pf` in the package tree, not on `$FAST`. The measured runs had it on local disk, so a tree on a network filesystem is unmeasured.
- With no C compiler, compiles also go fresh. No proof is at risk, and the route still works on fake Lean (M). Nothing measures how much slower it is.
- The final stop has no bound if `snapshot.py` or `merge_post.py` hangs, as on a hung filesystem. With an injected hang the job outlived its clock and the file stayed valid (M).
- A TERM in one of two windows of a few milliseconds around the stage's start (E) is not passed on. The stage then runs to its cap, inside the clock, and the file stays valid (M, windows widened by a test).
- A node crash or power loss was not tested. Each merge syncs its file before the rename.
- The README's body and one `run.sh` log line still describe the end stage. `LRA_POST_SAVE_S` (default 300) sets the save interval, for our tests.

## Left out on purpose

None of these can lose or lower a proof, because the only writer of `proofs.jsonl` during the post stage is the merge, by rename, row by row upward.

We left out: a host-speed setting that would scale the time limits to a slower node, and its reading; the health check and the run-time switch back to the stages; an alarm on the share of compiles that use the prefix servers; a done marker, so the post stage simply starts when the driver exits, which can lose up to about 10 min to the token-report join; the warm reader, a step that loads the environment files into the page cache, because the agent stage has already been compiling on these environments, though no reading exists on this route; a vLLM stop check beyond what `stop_all` does; memory limits that read the cgroup; `run.sh check` changes and any speed line; the first-reading fix, a re-read of a row's first compile time when it looks too high; K0, a first pass that only tries the kernel-skip option; the two-batch start, which would run the end stage beside the post stage; more work on the prefix servers; and the give-back, which would move the agent deadline later to return the 20-26 min above.

Tests do not ship. No code from our later, never-run executor ships.
