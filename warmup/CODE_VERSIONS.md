# Code versions: which harness each pass ran

The code in this tree (`harness/`, `llm/`, `scorer/`, `bank/`, `assemble/`, `probe/verify_candidates.py`, `infra/`, `envs/`) is
repository commit **`e9dbd81`**, the commit pass 8 loaded, with the staging changes listed in the next section. `postpass_normalizer/`
is a separate copy of the code as it stood on 2026-10-12, when the normalizer post-pass ran.

## How this tree differs from `e9dbd81`

The files below differ from their source commit **in comments, docstrings and help text only**, apart from the one code change named
under `harness/discover.py`. Before staging, every comment, docstring or help string that referred to our non-warm-up evaluation runs
(their names, run ids or results) was reworded or removed. No other logic changed.

| file | difference from its source |
|---|---|
| `harness/agent.py` | comments, docstrings and help text only |
| `harness/leantools.py` | comments and the module docstring only |
| `postpass_normalizer/harness/leantools.py` | comments only, relative to the 2026-10-12 code it was copied from. It differs from `harness/leantools.py` in one line, the second line of the module docstring. That line still names the CLI wrappers removed below. |
| `harness/discover.py` | its guard's comment and message are generic. **Code change:** the guard's list of run prefixes that must never be mined, `RESTRICTED`, is now an empty tuple, so in this tree the guard refuses nothing. The ledger `discover.py` backfilled before pass 4 is already in `harness/work_fresh-a100/*/state.json`. A rerun that repeats that step on its own passes 1–3 (`README.md` §4.4) is unaffected by the change. |

**Removed:**

- `envs/build_full_newest.sh` and `envs/build_full_older.sh`: they build every module of each project, which the warm-up does not need.
- `infra/vast/migrate_harness.sh`: it depends on `infra/sync/`, which is not in this tree. `README.md` §4.3 gives the steps by hand.
- `harness/tools/`: CLI wrappers used by our closed-model comparison lines. This line never used them.

**Added:**

- `harness/replicate.sh`: the per-pass driver from `e9dbd81`, which the chain scripts call.
- `envs/pin_upstream.sh`: new, written for this repository and not part of `e9dbd81`. It pins the upstream clones to the HEADs the
  passes saw (see "Upstream repositories each pass saw" below).

**Redacted:** in `infra/vast/last_create.json`, the per-instance key returned by the last rental's `create` call is replaced with
`REDACTED`.

**Disclosure: `--closed-lessons`.** `harness/agent.py` in `e9dbd81` has an opt-in flag, `--closed-lessons`, that is off by default.
It appends three general habits mined from our closed-model lines to the first message. The flag was never passed in passes 1–8: no
shipped trajectory contains its text. The comment above the structural-pass rule in `agent.py` names where that rule came from: an
analysis comparing closed-model proofs with Flash's. The rule is generic prompt logic (it prescribes structural rewrites once local
edits stall) and contains no proof text.

**Disclosure: the normalizer's other modes.** `postpass_normalizer/harness/normalize.py` has three `--bests` modes:

- `a100`: this line's bests. It is the only mode that made the records in `probe/runs/fresh-a100-normalize1/`.
- `flash`: z.ai records from the bank.
- `union`: reads run directories of our closed-model comparison lines. Those directories are not in this tree.

## Where the commit hashes come from

- `docs/a100_80_babysit.md` and `docs/a100_poc_log.md`;
- for passes 6–8, the `HARNESS_COMMIT` value the on-instance chain wrote to its log. That log is `probe/a100-80-chain-instance.log`
  in our development repository; it is not in this tree.

Git history is not part of this tree, so these files alone cannot confirm the commits. The `e9dbd81` attribution for this tree also
rests on the docs. It is consistent with the code: `agent.py` has both pass-8 flags, and `resume_pass_instance.sh` has the cycle-79
resume rule. Every trajectory header records the settings its pass actually ran with, and the table's settings columns come from
those headers.

| pass | started (UTC) | harness code loaded | settings (trajectory headers) | tools offered to the model |
|---|---|---|---|---|
| 1 | 2026-10-06 21:16 | the 2026-10-06 harness; no commit recorded in the included files | effort `default` (the GLM template renders Max), max_tokens 6000, turn budget 60 | 6: `read_file`, `write_file`, `lean_check`, `lean_run`, `shell`, `finish` |
| 2 | 2026-10-07 02:12 | the 2026-10-07 harness; no commit recorded | effort `default`, max_tokens 6000, turn budgets 20–60 | the same 6 |
| 3 | 2026-10-07 16:49 | the 2026-10-07 harness; no commit recorded | effort `low`, max_tokens 4000, turn budgets 20–50 | 7: adds `lean_check_variants` |
| 4 | 2026-10-08 22:12 | `bbfcd4c` = tag `a100-80-run` (`0588bc3`) + an off-by-default `--simp-prune` flag | effort `low`, max_tokens 4000 | 12: adds `lean_mine`, `lean_search`, `lean_skeleton`, `lean_profile`, `lean_goals` |
| 5 | 2026-10-09 00:10 | `f82d59e`; harness files unchanged since `bbfcd4c` | as pass 4 | as pass 4 |
| 6 | 2026-10-09 03:32 | harness files = `bbfcd4c` (freeze); `HARNESS_COMMIT` `018bbbe`, and `6f7577e` for the part finished after the 12:12 migration | as pass 4 | as pass 4 |
| 7 | 2026-10-09 12:32 | harness files = `bbfcd4c` (freeze); `HARNESS_COMMIT` `6f7577e` | as pass 4 | as pass 4 |
| 8 | 2026-10-09 21:34 | **`e9dbd81`**, with `--relative-error-lines --variant-scores` | as pass 4 | as pass 4 |
| normalizer post-pass | 2026-10-12 | `harness/normalize.py` at `a0b35293` (the `normalizer` field of every record in `probe/runs/fresh-a100-normalize1/verified.jsonl`) | no model | n/a |

## Upstream repositories each pass saw

The opening message of a project problem can carry an `UPSTREAM` block. `upstream_digest` in `harness/leantools.py` builds it from
the HEAD of the project's clone, `envs/<repo>.git-main`. The prompt also tells the model to check the project's git history for a later
simplification of the declaration. So what the model saw depends on the clones' HEADs. `infra/vast/harness_setup.sh` and
`envs/setup_projects.sh` clone each project's current main, which has moved since. Each trajectory records the HEAD as
`upstream HEAD (<hash> <date>)`:

| passes | Strata | cslib | physlib | ArkLib | pin with |
|---|---|---|---|---|---|
| 1–3 | no `UPSTREAM` block in any trajectory; HEADs not recorded | | | | n/a |
| 4–5 | `02f873ed7` (2026-10-05) | `ea16de3` (2026-10-05) | `bae4db68` (2026-10-05) | `35ddcaa83` (2026-10-04) | `envs/pin_upstream.sh 4-5` (full hashes) |
| 6–8 | `d1fc3a083` (2026-10-08) | `a3da622f` (2026-10-08) | `a7b32c82` (2026-10-08) | `db7005f84` (2026-10-08; passes 6–7) | `envs/pin_upstream.sh 6-8` (short hashes, resolved after a fetch) |

- **Pass 8 and ArkLib:** pass 8 started no session on an ArkLib problem, so it recorded no ArkLib HEAD.
- **Passes 1–5:** they ran on the same workstation clones, and the pass-4 HEADs are dated before pass 1 started. So passes 1–3 probably
  saw the same HEADs, but the trajectories do not record it.
- **The code in this tree builds the block in every pass,** including passes 1–3 of a rerun.

## Passes 1–3 (`docs/a100_poc_log.md`, `accounting/a100_poc.md`)

**Where they ran.** The harness ran on our workstation ("GB10" in the logs), against the A100 server through an SSH tunnel and, from
2026-10-06 22:43, through the TLS bridge. The logs name no commit, only the dates and the flags.

**Fixes made before pass 1's clean start (21:16):**

- the OpenAI client path sends the model's earlier thinking back in the conversation history;
- `--fresh` deletes the old state file, so an aborted run cannot leak into a fresh one.

**Pass 1** was started by `harness/replicate.sh` with `--fresh` and 4 workers.

**Pass 2** was chained by `infra/vast/chain_pass2.sh`: `--max-tokens 6000` plus extra flags read from a go-file. The go-file is not in
this tree. Its effective settings, effort `default` and max_tokens 6000, are in the pass-2 trajectory headers.

**Pass 3** ran through `infra/vast/pass3.sh` with the settings the log calls "z.ai-identical": effort `low`, a 4000-token base cap,
and a structural-mode bump to `high`. It was a resumed pass, using 4 workers.

## Passes 4–7 (`docs/a100_80_babysit.md`, "Harness code each pass ran")

**The freeze.** We froze the harness for this run on 2026-10-08 at about 23:05 UTC. From then until the run closed
(2026-10-09 14:33), `harness/agent.py`, `harness/leantools.py`, `harness/replicate.sh` and the modules they import were not changed.

- **Pass 4, attempt 1** (21:54, commit `0588bc3` with uncommitted edits) was outbid before any model call. Its 0-attempt run entries
  were removed and the run was archived as `aborted-fresh-a100-p4-outbid`, which is not in this tree.
- **Pass 4, attempt 2** loaded `bbfcd4c`. That is the tag plus a `--simp-prune` flag, 20 lines in `agent.py`, and its helper, 64
  lines in `leantools.py`. The chain never passed the flag, so behaviour is identical to the tag.
- **Pass 5** loaded `f82d59e`. A git diff at its start confirmed that the harness files were unchanged since `bbfcd4c`.
- **Passes 6 and 7** ran on the A100 instance, from a copy of the repository.
  - The copy's `HARNESS_COMMIT` was the then-current head: `018bbbe` at the 02:50 copy, and `6f7577e` after the 11:47–12:43
    migration to instance 55014773.
  - Under the freeze, the harness files in those copies equal `bbfcd4c` (babysit table). The babysit log records only these other
    changes during the run: infrastructure scripts, documents, and a read-only `--kg-json` export added to `harness/discover.py`,
    which `agent.py` does not import.
- **Before pass 4,** `harness/discover.py` backfilled the line's ledger from passes 1–3, at 21:31 on 2026-10-08, as part of the tag.
  The pre-backfill states are kept as `harness/work_fresh-a100/*/state.json.bak-discover-20261008-213252`.
- **Pass-6 environment gap.** The first harness instance had no ripgrep, so in pass 6 the harness's lemma search failed 16 times and
  12 of the model's `rg` calls failed. The harness code itself was unchanged; ripgrep was then added to `infra/vast/harness_setup.sh`.

## Pass 8 (`docs/a100_80_babysit.md`, 21:26–21:34 entries)

**What it loaded.** Pass 8 was launched by hand at 21:27 on instance <instance>, loading `e9dbd81` with the extra flags
`--relative-error-lines --variant-scores`. The chain log confirms it: "chain on instance start: passes 8-9; line 81.72; harness
e9dbd81".

**Why `e9dbd81` and not `4de49ac`.** The pre-launch review entry (21:00) names `4de49ac` for the planned automatic launch. That launch
did not fire, so `e9dbd81` is the code that ran.

**Flags in `e9dbd81`:**

- `--relative-error-lines` (cycle 76): `lean_check`-family errors give positions as lines of the compiled declaration rather than
  of the scratch file.
- `--variant-scores` (cycle 78): `lean_check_variants` rows show each compiling variant's provisional score and its comparison with
  the stored best.
- Other opt-in flags present in `e9dbd81` were not passed, including `--simp-prune` and `--closed-lessons`.

**Consistency check.** Both flags exist in `harness/agent.py` in this tree. The resume rule in `infra/vast/resume_pass_instance.sh`
(cycle 79: re-run every session without an `end` record) is also present. Both are consistent with this tree being the pass-8 code.

## Normalizer post-pass (`postpass_normalizer/`)

**What the tree is.** `postpass_normalizer/` is the normalizer and the files it needs, copied on 2026-10-12: `harness/normalize.py`,
`harness/leantools.py`, `scorer/`, `bank/store.py`, `probe/verify_candidates.py`, `data/`, and the run script
`probe/normalize/record_a100.py`.

**Differences from the pass-8 tree:**

- `scorer/compile.py` gains an optional `lean_args` parameter. It is empty by default, so "every existing caller compiles exactly as
  before".
- `scorer/memgate.py` gains a bounded wait, via `LRA_MEMGATE_RELAX_S` and `LRA_MEMGATE_MAX_WAIT_S`.
- `harness/leantools.py` differs in one docstring line (see the first section).
- `scorer/score.py`, `scorer/tokenize.py`, `scorer/forbidden.py`, `bank/store.py`, `probe/verify_candidates.py` and
  `data/benchmark_warmup.jsonl` are identical in both trees.
- `harness/normalize.py` exists only in `postpass_normalizer/`.

**How the records were made.** The recorded records (2026-10-12) were stamped `harness/normalize.py@a0b35293`: the repository head
when `record_a100.py` ran. `record_a100.py` needs Python 3.12 or newer: line 34 nests double quotes inside an f-string. Python 3.11
rejects it, and every other `.py` file in this tree parses on 3.11.
