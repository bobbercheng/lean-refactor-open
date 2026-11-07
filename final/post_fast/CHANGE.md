POST-HOC, not part of any upload; the uploaded open result stays sub43 at Arena 82.55 from the original 4.7 h post-step, which ran after the GPU job.

Replication of sub43 stays at tag `open-run3-post-final-sub43-20261104`.

# The fast post stage inside `run.sh`

This puts our measured post-step speed-up inside `run.sh`, with the smallest change we could make. The post stage runs the same seven passes and accept gate as the uploaded post-step, through a shared compile service with prefix servers and speculative reads. New in its decisions are merged candidates and the hintgrind gate and cache, on in this route and off with `LRA_POST_ROUTE=off`; 156 of T0b's 347 adoptions were merge ops (M). Labels: M measured, D derived, E estimated.

1. The agent stage runs to its deadline as before.
2. The end stage, dialect step and normalize are skipped. The job clock does not change.
3. The driver audits and exports the picks to `proofs.jsonl` and exits as before. `stop_all` stops vLLM.
4. `post_stage.sh` runs on the picks until job end minus 60 s. `JOB_END` is 47:50 on a 48 h job. Its window is 144-158 min (D). It shrinks on slow hosts, where the audit and the token report take longer: 143.6-152.5 min at ratio 2.1, 140.5-150.7 at 2.5 (E), less any start-up stall, median 8.4 min and maximum 15.75 on run 3's box (M).
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
| `README.md` | 12 | 3 | A first section that points here; three corrections in section Post-step |
| `post_fast/`, new | 12 files | | Executor, `post_stage.sh` (42 lines), `merge_post.py` (47 lines), this file, `MANIFEST.json` |

## Where it ran

| Where it ran | Version | What it shows |
|---|---|---|
| A100 box, pf-RT2 | Before the swap, with weights.json | The post stage runs on a real A100 box, at about 1.85 times the F64's wall time on this work (D). We quote no score from it. |
| Azure F64, W1 | As shipped, with the input rule | Stored mean 82.5992 at the 85 min cap; passed 82.556 at 57.4 min (a reading, the package has no score stop); r20 gain 10.32 (its bar was 10); 60 of 60 rows with a non-zero input-rule weight (M). A stored mean, not a fresh check, on the F64, not a node. |

**The swap.** The input rule replaces our earlier runs' per-row seconds table, `weights.json`: a row's weight is sqrt(heartbeats x tokens) from the run's own picks. We chose that rule on run 3 (Spearman .83 against its per-row seconds, D), so it is milder hindsight, not none. The swap is one added line, it sets only launch order and compile priority, and no proof or accept rule changes; no A100 run follows it. Rows start within .1 s of each other (M), so compile priority is the part that acts.

**The noexec fix.** Docker mounts `/dev/shm` noexec, and the prefix servers' driver runs from the work dir there: on the box all 121 server starts failed with Errno 13 and every compile ran fresh, with no alarm (M). `post_stage.sh` now tests exec in the prefix root and, if that fails, moves only `build/` to `$CODE/.lra/prefix-build`. The box then had 0 failed server starts (M).

## Limits

T0b ran from the pick at 45.25 h with no stages, and fullV7m1s from run 3's export. r14, r20 and r37 are rows, counted from 0.

- No 48 h job has run this route on any machine. Beyond the table above and the box's short seed runs behind the noexec fix, what was tested is fake Lean and one real-Lean row (Details).
- The measured runs are on one Azure F64as_v7 with 64 cores, with a warmed page cache. T0b crossed 82.556, the stored mean of the uploaded seven passes, at 53.87 min after about 13.8 min of warm-up, from our own picks, which do not ship (M).
- All time limits stay at the values measured on the F64, and no reading exists on the organizers' node. On a slower host they moved gains more than they lost them (Details). No 48 h score claim is made: the hard stop bounds the time by design, and the score at the stop on a node is unknown.
- T0b is one run, stopped at target. r37 stopped mid-pass. The 25 rows with the same input in both runs held exactly. 4.17 min of the gain over fullV7m1s is r14's timing; the real saving is the 120.3 min of skipped stages (M).
- 82.5657 is a stored mean. A fresh verification of T0b's final proofs on the same F64 reads an exact mean of 82.5648, .0088 over 82.556, with 60 of 60 rows compiling on every pin (M).
- r14's proof at 84.40 fails a full kernel check in that verification (M). It scores only with `debug.skipKernelTC`, and forced back on r14 alone T0b reads 82.4370, under 82.556 (D).
- W1's 82.5992 has had no fresh verification. 4 of its rows use `debug.skipKernelTC`, and its r14 at 86.19 has had no full kernel check (M).
- T0b's agent stage had 45:15 with no vLLM load on the clock. Under `run.sh` it has about 44:49, or 20-26 min less (D/E), priced at .009-.034 at the final (E), against T0b's .0097 margin over 82.556 (D).
- Every row of the picks gets the post stage, for any rows file: 6 of the rows, the 60 reversed and the 60 renamed each ran and rose inside the clock (M, fake Lean). Scores exist only for the final rows.
- If the post stage fails before its first merge, the job still ends with a valid `proofs.jsonl`, but that file is the agent picks, about 79.25 stored, not the 79.68 the stages gave (M). That floor is a known cost of the smaller change.

# Details

## Node speed

The organizers stated 64 physical cores, 256 GB RAM and 4x A100 80 GB; they did not state the CPU model, and no reading exists on their node. Ratio is a host's wall time over the F64's on the same work. A Xeon Platinum 8368 box read 1.25-1.31 against a D64 with the F64's speed, on one proof (M). The A100 box read 1.85, row p10-p90 1.63-1.99 (D), likely from per-core CPU, EPYC 7V12 against EPYC 9V45, inferred with no PMU, no unloaded compile and no F64 clock.

At 1.85 the time limits moved gains more than they lost them and saved no time to target (D). In passes 1-4, long search lanes stay open while a row's wall left is at least max(900, 40 x `compile_s`) s. In pass 1 they closed on 21 rows against T0b's 4 (M): 10 from the fixed 2700 s wall under the 900 s floor, 11 scaled by `compile_s` (D), which is charged seconds, 8.4 real slot-seconds per compile against 4.0 (M). More passes or longer walls gain 0 up to 1.85 (M).

A speed list is not a post-stage ratio: a fixed seed list read 2.49 on that box (M), 1.35 times the 1.85 above (D).

## If it fails

| What happens | `proofs.jsonl` afterwards |
|---|---|
| The post stage cannot start, or under 2 min remain | The picks |
| A part dies or hangs, or TERM arrives | Picks plus all gains logged; the final merge runs. USR1 changes nothing: `promote` never replaces an existing `proofs.jsonl` |
| SIGKILL of the stage or the whole job, at any moment | A whole file: picks plus the gains of the last merge |
| A re-run or `run.sh export` after that | The picks for a while, then the saved gains return |

- A merge compares each row against the current `proofs.jsonl`, so a mid-run read that offers a lower row changes nothing, and a failed merge leaves the file as it was.
- A re-run's driver writes the picks back by rename. The first step of `post_stage.sh` then puts the gains back from `proofs.merged.jsonl`, before its time guard, and `run.sh export` does the same after its export. On a re-run the file reads as the picks from the driver's export until the post stage starts, up to about 11 min (E, the audit plus the token-report join). A kill in that stretch leaves the gains in `proofs.merged.jsonl`, and the next re-run or `run.sh export` returns them. With `LRA_POST_ROUTE=off` nothing is put back.
- Zero or missing heartbeats or tokens, as on a row still on its seed (0 of T0b's 60 picks, M), give that row weight 0, and a failed read of the rule gives every row weight 0; the stage still runs. If no part can read the picks, the job ends on them (M, fake Lean).
- `summary.json` describes the picks, not the merged file. In our run the pick at 45.25 h was never audited; in this job the driver audits it.
- After SIGKILL of `post_stage.sh` the compile workers stop at the cap, but the compile service and its prefix servers do not stop by themselves: 121 were still alive 30 s after the job clock (M, fake Lean). That the end of the job on a node kills them is assumed, not tested.

## What is identical to what

- Against the tag: 158 of the 163 files in `final/` are byte-identical, 5 changed (table above), 12 are new, all in `post_fast/`, and 0 were removed (M). `setup.sh`, `EXPORT.json` and `warmup/` do not change. The repository's root `README.md`, outside the zip, gains a short note that says what this branch is.
- We did not use `--dialect off`, `--no-normalize` or a lower `--end-seconds`: the first turns off the agent stage's own dial pass, and the other two move the agent deadline.
- `pf_svc.py`, `pf_drive.py`, `pf_worker.py`, `prefix_backend.py`, `merge_warm.py`, `snapshot.py` and `prefix_server/` are byte-identical to our local copies of the files those runs used. The runs logged an input hash but no code hash.
- `open_post.py` and `hintgrind.py` are our local copies of the runs' code with one comment line redacted in each, and the same syntax tree apart from the docstring. Their new paths are on by `LRA_POST_MERGE`, `LRA_HG_GATE` and `LRA_HG_PERSIST`, which `post_stage.sh` sets. `MANIFEST.json` gives the sha256 and origin of every file that differs from the tag.
- `post_stage.sh` is the runner of T0b with its `/workspace` paths replaced by arguments, this run's picks as the input, the input rule in place of the runs' per-row files and the stop taken from the job clock. The runners `run_T0.sh` and `launch_T0b.sh` hold fixed paths, so they do not ship. `merge_post.py` takes a row's emitted line if its stored score is at least the current one and it passes the export's static check, checks the names against the rows file, in order, and writes by rename after an fsync.
- `EXPORT.json` lists `run.sh` and `harness/open_package.py`, so those two sha256 values no longer match. The README's sentence that every listed file is the run's file holds only at the tag.
- The tag's tree is not exactly the measured tree. Of the tag's 121 Python files, 117 have the measured syntax tree (M). The other four are `open_post.py` and `hintgrind.py`, now replaced, and the release stubs `harness/architect.py` and `harness/lemma_search.py`. The post-step imports only `_KW` and `bound_names` from those stubs, and their docstrings say both were copied verbatim from the development modules.
- Nothing in the job reads a stored proof. The post stage starts from this run's own picks.

## Measured results

All three ran on one Azure F64as_v7, not through `run.sh`. fullV7m1s and T0b ran before the swap; W1 ran `post_stage.sh` as shipped.

| Run | Input | Stored mean | Time | Label |
|---|---|---:|---:|---|
| fullV7m1s | run 3's export `0664621d`, after the stages | 82.56 | 58.03 min | M |
| T0b | the pick at 45.25 h, no end stage, dialect or normalize, stored 79.2505 | 82.5657 | 53.87 min | M |
| W1 | the same pick | 82.5992 | 85 min, the cap; last adoption at 77.1 min | M |

- Replaying the 5-minute merges on T0b's logs gives the same 82.5657, with 0 rows ending on another proof (D). It would have held 81.98 at 30 min (D).
- T0b's 53.87 min includes the first build of the prefix servers: 8 toolchains, 18.6 s in sum on the F64 (M). No separate build step is needed.

## What was tested

On a development host, from a clean export tree, with fake Lean and a stub model: the real `run.sh` and driver, then the real `pf_svc`, `pf_drive`, `pf_worker`, `snapshot.py` and prefix path, on a short job clock. Numbers here are M unless labelled.

- 18 main failure cases passed: the cap stop, a dead or hung part, TERM, INT, USR1, SIGKILL of the stage and of the whole job, a read that offers lower rows, no C compiler. Each left 60 rows in order, with 0 torn reads and 0 rows below the picks.
- 8 cases of the input rule and the noexec fix passed: normal picks, zero or missing heartbeats or tokens, bad values, a failed read, unreadable picks, a broken last line, and an exec probe that fails as on a noexec mount.
- 46 further cases: signals between any two writes of a merge, write errors, clock edges, re-runs and `run.sh export` after a kill, other rows files. 44 passed, and in the re-run and export cases 0 rows ended below what the kill left. The other 2 are the injected hangs under Smaller limits. Three of the 44 passed only when run one at a time: at a load of about 160 the test's kill came too late for its gate (E), and the file stayed valid.
- `merge_post.py` alone: 13 unit checks passed, and 400 rounds, 106 of them killed by SIGKILL at a random moment and 294 finished first, gave 0 torn reads in 368,100 and 0 rows that fell.
- With `LRA_POST_ROUTE=off`, `RUN_CMD`, output file names and `proofs.jsonl` equal the tag's. The dry output differs by a memory figure, and the shell trace by that, process ids, a seconds-left reading and the two guard lines.
- On that host real Lean ran on one row only, `putnam_1964_b2`, from its seed, in a 15 min window. Each of 5 runs was stopped by `--cap` about 60 s before job end. The 2 earliest, before the swap: 138 and about 270 compiles, 2 and 3 adoptions with a clean audit, stored 33.33 to 43.78 and to 85.63. The 3 latest, one after another: 2 as shipped and 1 control from the tree before the swap, 59-63 compiles, no adoption, stored 33.33. The control matched, so the swap did not cause the drop; the cause is not established. No real-Lean run after the swap has adopted a proof on this host. The runs show the parts connect on real Lean. They say nothing about speed or score. On the F64, W1 adopted as shipped: 357 adoptions on 56 rows (M).
- Not tested: a real scheduler's kill, a real full work dir, a 48 h job.

## Smaller limits

- T0b and fullV7m1s were stopped at about an hour and W1 at 85 min, while the post stage's window here is about 144-158 min (D), so no F64 run and no run as shipped measured about the last hour of it. pf-RT2 ran its full 150 min before the swap, about 81 F64 minutes of work at 1.85 (D), so the work late in the window stays unmeasured. The lowest free memory was 119 GB at minute 34 of 54 in T0b and 115 GB at minute 49 of 85 in W1 (M), which says nothing about that stretch.
- `--slots 48` and the cap of 120 servers are fixed. `LRA_WORKERS`, `LRA_COMPILE_SLOTS` and `run.sh`'s sizing do not reach the post stage, so a smaller allocation is unmeasured and may be oversubscribed.
- `$FAST` must have room, and its path must stay under about 85 bytes: a longer one skips the post stage in about 60 s, and the job ends on the picks (M, fake Lean). With no room, gains are lost with no alarm, but no row can fall. `LRA_PREFIX_ROOT` overrides the server location.
- `pf_drive` puts compile scratch under `probe/hbtool/.scratch-pf` in the package tree, not on `$FAST`. The measured runs had it on local disk, so a tree on a network filesystem is unmeasured.
- With no C compiler, compiles go fresh. No proof is at risk, and the route still works on fake Lean (M). Nothing measures how much slower it is.
- The final stop has no bound if `snapshot.py` or `merge_post.py` hangs, as on a hung filesystem. With an injected hang the job outlived its clock and the file stayed valid (M).
- A proof that holds U+2028, U+2029 or U+0085 would stop later merges: the file stays whole and the gains so far stay, later ones are lost (M, one probe). 0 of 2,895 real proofs hold one (M).
- A TERM in one of two windows of a few milliseconds around the stage's start (E) is not passed on. The stage then runs to its cap, inside the clock, and the file stays valid (M, windows widened by a test).
- A node crash or power loss was not tested. Each merge syncs its file before the rename.
- The README's body and one `run.sh` log line still describe the end stage. `LRA_POST_SAVE_S` (default 300) sets the save interval, for our tests.

## Left out on purpose

None of these can lose or lower a proof, because the only writer of `proofs.jsonl` during the post stage is the merge, by rename, row by row upward.

We left out: a host-speed setting that would scale the time limits to a slower node, and its reading; the health check and the run-time switch back to the stages; an alarm on the share of compiles that use the prefix servers; a done marker, so the post stage simply starts when the driver exits, which can lose up to about 10 min to the token-report join (D); the warm reader, a step that loads the environment files into the page cache, because the agent stage has already been compiling on these environments, though no reading exists on this route; a vLLM stop check beyond what `stop_all` does; memory limits that read the cgroup; `run.sh check` changes and any speed line; the first-reading fix, a re-read of a row's first compile time when it looks too high; K0, a first pass that only tries the kernel-skip option; the two-batch start, which would run the end stage beside the post stage; more work on the prefix servers; and the give-back, which would move the agent deadline later to return the 20-26 min above.

Tests do not ship. No code from our later, never-run executor ships.
