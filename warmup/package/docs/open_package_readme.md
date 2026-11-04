# Vexorium open-track package: README draft for the organizers (2026-10-27, DRAFT)

What it does: for every benchmark row, the open model GLM-5.3-Flash (AWQ W4A16, served by vLLM on the 4 x A100) refactors the seed proof
in tool-using sessions (compile, scratch Lean, grep, multi-variant checks, goal maps, goals at `sorry` holes, heartbeat profiles),
several resumed sessions per row; then a model-free end
stage (CPU only) searches mechanical rewrites of each row's best proof and keeps only edits that compile on every listed toolchain and
score higher, and a lexer normalizer (CPU only) rewrites the result's spellings that the arena tokenizer counts as extra tokens
(`fun x =>` -> `λx =>`, a parenthesised last argument -> `$`, ...) under the same compile-and-score gate; the result is one proof
per row. Everything starts from the seed proofs you provide; no stored proofs, no hosted model, no per-problem knowledge. What the model is shown and where each piece comes from: docs/open_package_audit.md.

## 1. Requirements
- 1 node, 4 x A100 80 GB **SXM4 (NVLink between the GPUs) recommended**: the serving recipe uses vLLM's custom all-reduce, which
  needs NVLink; on PCIe A100s vLLM falls back to NCCL automatically and decode is ~25% slower (fewer sessions per problem in 48 h);
  64 physical cores; RAM: 256 GB or more recommended (vLLM host memory + up to ~32 concurrent Lean compiles);
  disk: ~200 GB for the checkpoint + ~130 GB for the Lean environments and toolchains of the 15 warm-up rows (measured: 118 GiB unpacked, 4
  projects + Mathlib, 10 toolchains) + ~20 GB for a LeanPool environment (its Mathlib cache and a full `lake build LeanPool`).
- Network: GitHub (project repositories, Mathlib cache), Hugging Face (checkpoint), Docker Hub (vLLM image).
- Software: Docker with the NVIDIA runtime (for vLLM), Python 3.10+ with `requests`, git, curl, ripgrep (`rg`, used by the model's shell
  tool), zstd; elan installs the Lean toolchains.

## 2. Install
```bash
git clone <the release repository> lra && cd lra && git checkout <release tag>   # the minimal release export (audit F.4), never this dev repository
python3 -m pip install requests
# Lean environments for the rows you will run (ROWS = your benchmark JSONL in the warm-up file's format):
python3 infra/open_package/envs_from_rows.py --rows ROWS.jsonl --out infra/vast/harness_envs.json   # knows strata, physlib, cslib, arklib, putnambench, leanpool; another project: --url NAME=<git url>, or a `url` field in its rows
bash infra/vast/harness_setup.sh          # elan, repos, pinned worktrees, Mathlib cache, `lake build` of the rows' modules; ends "SETUP DONE ok=N failed=0"
```
`envs_from_rows.py` reproduces our warm-up environment list exactly (test: harness/test_open_package.py EnvsTest) and knows LeanPool
(github.com/LeanPool/lean-pool, the sixth library of the final set). A source it does not know needs its repository URL on the command
line (or a `url` field in the row). Before the run, `python3 infra/open_package/check_envs.py --rows ROWS.jsonl` proves every row's
environment, toolchain and module olean exist (exit 1 otherwise).

## 3. Serve the model (pinned)
Image `lazymio/vllm-backport:v0.13.1-sm80` (the only vLLM path with GLM-5.3-Flash's sparse-MLA kernels on sm80), checkpoint
`wtdcode/GLM-5.3-Flash-AWQ-W4A16` at revision `abd7b07719111f137e1de8a0c1b7e01c11b74d1a` (run_vllm.sh's default), flags as in `infra/vast/run_vllm.sh` (tensor parallel 4, max-num-seqs 16,
prefix caching OFF (the fork's open bugs with MTP), MTP speculative decoding 3 tokens, tool parser glm47, reasoning parser glm45,
served name `glm-5.3-flash`). On the same node no TLS or key is needed: serve on 127.0.0.1:8000.
```bash
mkdir -p $HOME/lra-workspace   # /workspace in the container: HF cache (hf/), vllm.log, READY
docker run -d --name lra-vllm --gpus all --ipc=host -p 127.0.0.1:8000:8000 -v $PWD:/lra:ro -v $HOME/lra-workspace:/workspace \
  --entrypoint bash lazymio/vllm-backport:v0.13.1-sm80 -c "bash /lra/infra/vast/run_vllm.sh && tail -f /workspace/vllm.log"
for i in $(seq 1 360); do curl -sf 127.0.0.1:8000/v1/models >/dev/null && break; sleep 15; done   # ~10-16 min after the download: load, CUDA graphs; bounded at 90 min: read $HOME/lra-workspace/vllm.log if it never answers
```

## 4. Run the benchmark (one command, one clock)
```bash
START=$(date +%s)   # take it at the very start of the job, before the install: setup time counts against the 48 h
python3 harness/open_package.py run --rows ROWS.jsonl --heartbeats HEARTBEATS.jsonl --out runs/final \
  --base-url http://127.0.0.1:8000/v1 --api-model glm-5.3-flash --started-at $START --job-seconds 172800
```
Defaults: 4 concurrent sessions (the serving's measured knee: 263 tok/s aggregate at 4 streams, collapsing above), at most 12 sessions
per row, the end stage gets 4 h (R5 clock), the normalize step the last 30 min before the export, the export the last 15 min.
The driver is restartable with the same command (it
keeps its job clock in runs/final/clock.json, counts sessions already run and resumes each row from its saved state). Run it in a
memory-capped cgroup if the node is shared (every compile also passes a memory gate).

### Cost ports from the closed line (2026-10-28; audit section P)
Mechanical infrastructure from the closed line, no proof knowledge; on by default unless marked opt-in:
- `--no-compact-tool-json`: the sessions run `agent.py --compact-tool-json` by default: tool results as compact JSON with Lean's unicode
  kept (lean_check results were `\uXXXX`-escaped). With the next item, one of the two changes to what the model sees (the result format;
  same fields and values; the system prompt and tool list unchanged; a long unicode-heavy result now reaches the 12,000-character result
  cap later, since a symbol counts 1 character instead of 6). Measured on the A100 line's recorded GLM sessions with the model's own tokenizer: lean_check
  results -24%, all tool results -4.7%, prefill tokens -0.7% (prefix caching is off, so every turn re-sends them).
- `--no-skeleton-combinator-holes`: `agent.py --skeleton-combinator-holes` by default: lean_skeleton reads a `sorry` after
  `all_goals` / `any_goals` / `try` / `repeat` / `iterate n` / `focus` / a `first` alternative as a tactic hole and returns its goal
  (the default reading wrote a term hole there, which does not parse).
- `--connect-budget-seconds S` (default 7200): a refused or failed connection to the model server (vLLM restarting or reloading) waits up
  to S seconds per call, polling at most every 144 s (120 s x jitter), without using one of `--max-api-retries` (whose chain of 20
  retries lasts ~80 min). Read timeouts, resets after a request was sent and 5xx replies keep the retry path. agent.py wraps every
  `--endpoint openai` call this way (not flag-gated, as in the closed line; its own default budget is 1800 s).
- `<out>/token_report.json`, written in the background while the end stage runs (the driver waits for it at most 10 min after the
  export): per session index and in total, input / output tokens per turn, the opening's share,
  turns at the output cap, budget-forcing rescues, junk events and a junk scan of every model message, connect and API retries, tool-result
  sizes and the compact-JSON share ($0, read from the trajectories; a failure is logged and never stops the run).
- `--schedule room` (the **default** since 2026-10-28, operator decision; `--schedule ladder` restores the old order): after every row's
  first session, the next session goes to the ready row with the most room, (100 - best) / (sessions so far + 1), x0.3 while its last 3
  sessions were flat. Replay of the GLM lines' sessions: +0.5 to +1.5 mean points expected at 3-4 sessions per row; on the A100 tapes under
  a time budget the point estimate is +0.46 and its interval includes 0 (the reason it started as an opt-in).

### Sorry guard (operator decision 2026-10-28; `--no-audit` turns the export audit off, the env stays)
PhysLib's lakefile turns Lean's sorry warning off, so on those rows a proof that depends on `sorryAx` without the literal word (Lean core's
`impossible by simp|decide|grind` from v4.31, `stop`) would compile "ok". Every compile the package runs (the agent sessions, the end
stage, the normalize step) now carries `LRA_FORCE_WARN_SORRY=1` (`scorer.compile.force_warn_sorry`: warn.sorry forced on where the pin
turns it off; heartbeats unchanged), and the export audits every row's chosen proof with `#print axioms` on every pin: a proof flagged
`sorry` is passed over for the next candidate (end stage output -> agent best -> seed; the seed is never passed over), an audit that
cannot decide keeps the proof. `summary.json` carries `audit` (counts, fallbacks); each `proofs.jsonl` record its `audit` status and, when
passed over, `audit_passed_over`. Fault injection with real Lean: `probe/open_package/guard_check.py` (PhysLib warm-up rows, `sorry`,
`stop <tactics>` and `exfalso; impossible by simp` bodies compile "ok" without the guard, are rejected with it, and the audit passes them
over for the seed; the seed audits `skipped` (PhysLib files are modules: sorry message only); an audit that times out keeps the proof).
Review 2026-10-29 (audit section S.1): the export writes the picks to `proofs.jsonl` BEFORE the audit (a stop during the audit leaves
them, as before the audit existed; the file is replaced atomically), then audits `AUDIT_JOBS` = 4 rows at once (at most the compile
slots), the rows whose pin turns the sorry warning off first, and stops `AUDIT_WRITE_S` = 60 s before the job end (each compile's timeout
is cut to the time left): a row it does not reach keeps its pick with `audit` = `unaudited`. Statuses: `clean`, `skipped` (module file:
the sorry message check only), `seed` (the seed itself, or every other candidate flagged), `unknown` (kept: timeout, errors, no pin, no
axiom output), `unaudited` (kept: the clock). The audit's cost, serial, on the 15 warm-up seeds: 190 s for 36 pins (2.5-36 s per row;
ArkLib 21-36 s), i.e. ~13 min for 60 rows serial against the 15 min export margin, hence the parallel, clock-bounded form.

### Normalize step (operator ruling 2026-10-27; `--no-normalize` turns it off)
After the end stage (also when the clock stopped it), `harness/normalize.py` runs once per row on the proof the export would pick (the
end stage's output, else the agent's best, else the seed), scored from your `--rows` / `--heartbeats` files only (official reference
heartbeats, no local tables). Five rewrites (`fun x =>` -> `λx =>`; `f (fun x => e)` -> `f fun x => e`; `f a (g x)` -> `f a $ g x`;
`<|` -> `$`; `a; b` -> two lines): all sites are applied, the ones that break the compile are bisected out, the result must compile on
every listed toolchain and score strictly higher than a fresh measurement of the input, else the row keeps its proof. Mathlib's style
linters may warn on `$` / `λ`; warnings do not fail a compile. Clock: `--normalize-seconds` (default 1800) is reserved after the end
stage (the agent stage ends that much earlier), each row is bounded by `--normalize-row-seconds` (default 900), at most
min(`--end-jobs`, `--compile-slots`) rows run at once, no row starts with less than 2 min before the export margin, and rows finished at
the deadline are kept. A row whose step fails keeps its proof, a failing step never blocks the export, and a stopped row leaves no
Lean compile behind. `--no-normalize`: no step and no reservation (the previous timeline). `python3 harness/open_package.py
normalize ...` runs the step and the export alone (restartable: rows already done for the same input proof are not run again).

### Style step (opt-in, 2026-10-30; `--style-rw on`, default off)
After the normalize step, `harness/style_rw_open.py` runs once per row (one process each, `--style-rw-jobs` rows at once) on the proof
the export would pick: the package's OWN model (the same `--base-url` / `--api-model` / `--api-key-file` as the sessions; with the
default `--style-rw-effort default` its thinking is OFF, `chat_template_kwargs {"enable_thinking": false}`; `--style-rw-max-tokens` 7000 per call) is asked to rewrite that proof into the shorter "scoring dialect" (auto-named
hypotheses, positional case handling, uniform closers), shown compiled before/after pairs of OTHER theorems
(`harness/style_rw_open_exemplars.json`, sha pinned by `--style-rw-exemplars`; a pair is never shown on its own theorem). Every
candidate is compiled on every listed toolchain with the forbidden-pattern check and the sorry guard, the best one passes the axiom
audit and the end stage's $0 tools, and it replaces the row's proof only if a confirm read (old and new back to back) shows it at least
0.05 points higher; otherwise the row keeps its proof byte-identical. Each row has a hard wall (`--style-rw-wall-s`, 900 s: the process
is stopped and nothing of it is taken); the step's share of the job, `--style-rw-seconds` (7200), is reserved before the end stage like
the normalize share. Off: no reservation, the module is never loaded, the export ignores `style_rw.jsonl`.

### Blind first session (opt-in, 2026-10-31; `--blind-start on`, default off)
Each row's FIRST agent session (the one that starts from the seed) starts from the statement instead of the reference proof:
`candidate.lean` holds the exact statement with a `sorry` body (a `sorry` is never banked), and the opening carries a facts sheet
computed from the reference's text by `harness/blind_facts.py` at no cost: the names it refers to, its induction / cases targets, its
case labels, its tactics (names and counts), its tokens and heartbeats, the exchange rate between them and the toolchains; no line of
the proof. The reference stays the row's banked best (score 33.33) and is shown in one message ("REFERENCE PROOF, now shown") only if
nothing of the session's own is banked after a third of its turns, or when it asks to finish before that. Shell reads of the row's own
source file, the rows file or the theorem's name are counted as violations (not blocked) in the trajectory and the session's line
(`agent_sessions.jsonl`, `blind`). Later sessions of the row are unchanged. Off: the sessions' commands and prompts are byte-identical.

## 5. Outputs (runs/final/)
- `proofs.jsonl`: one line per row in the rows file's order: `name`, `proof` (the full declaration), `source` (end / agent / seed /
  normalize; a normalized row also carries `normalized_from` and `normalize_gain`), the stored score, tokens and heartbeats. A row falls
  back to the agent's best, then to the seed, if the end stage's proof fails the forbidden-pattern check; the normalized proof is taken
  only for exactly that proof, when it starts with the row's exact statement and passes the forbidden-pattern check.
- `normalize.jsonl` (one line per row: candidate source, input sha, status, before / after, the proof when improved) and
  `normalize_stage.json` (the step's counts).
- With `--style-rw on`: `style_rw.jsonl` (one line per row: input sha, status improved / kept / skipped / stopped / error, before / after,
  gain, the proof when improved), `style_rw_stage.json`, `style_rw/` (per-row records and the model calls' full prompts and answers in
  `style_rw/trajectories/`); a taken row's `source` is `style_rw` with `style_from` and `style_gain`.
- `summary.json`, `agent_sessions.jsonl` (one line per session: row index, run id, seconds, model output tokens, score before / after),
  `prompt_audit.json` (every harness-written message checked against the withheld material), `token_report.json` (the sessions' token
  usage, section 4), `end/report.jsonl` and `end/finals.json`
  (the end stage per row), `logs/` (one log per session, `end.log`, `normalize.rKK.log`), `work/` (per-row state, notes), and the sessions' full
  trajectories under `probe/runs/<run id>/`.

## 6. Time budget for ~60 rows on 4 x A100 + 64 cores (measured throughput, docs/a100_poc_log.md)
Measured on the same serving (Oct 6-9, 15 warm-up rows, 4 workers, harness at the time): pass 1 4 h 55 min (incl. ~37 min of tunnel
stalls; clean ~4 h 20 min) = ~69 min per row-session (60-turn first sessions); pass 2 2 h 51 min = ~46 min per row-session; pass 3 52 min
= ~14 min (near-ceiling rows get 10-20-turn polish sessions); later passes ~1 h. The serving's knee is 4 concurrent streams (66 tok/s
each); compiles use the CPU, not the GPUs.

| phase | 60 rows, 4 sessions at once | cumulative |
|---|---|---|
| setup: environments (Kaggle-style restore 2 min, build ~40-60 min), checkpoint download (191 GB: 6-30 min), server start ~16 min | ~1.5 h | 1.5 h |
| session 1 of every row (69 min each) | 60 x 69 / 4 = 17.3 h | 18.8 h |
| session 2 (46 min) | 11.5 h | 30.3 h |
| session 3 (14 min avg) | 3.5 h | 33.8 h |
| sessions 4+ until the agent deadline (~16 min avg each) | ~9.5 h = ~2.4 more sessions per row | 43.3 h |
| end stage, R5 clock (sealed look: ~1,980 row-seconds and ~166 compiles per row at 3 slots; at 21-32 slots (auto_slots on 64 physical cores: 21 without SMT, 32 with it) 60 rows need ~1.6-2.5 h) | 4 h reserved | 47.25 h |
| normalize step (warm-up measurement: 0-185 s per row, 0-19 compiles; 60 rows at 21-32 rows in flight: ~10 min) | 30 min reserved | 47.75 h |
| export | 15 min | 48 h |

So about 5 sessions per row fit (the warm-up evaluation's budget-shaped input, "about 4 passes of a 50-row job", gave 78.60 raw ->
81.18 after the end stage, with the A100 line's old prompt; see the audit, section 0). The async ladder starts a row's next session as
soon as its last one ends (no pass barrier), so short polish sessions do not leave GPUs idle; breadth first, every row gets session k
before any row gets session k+1. If the setup takes longer, `--started-at` moves the agent deadline earlier and the end stage keeps
its 4 h. Compile slots: `auto_slots()` = a third of the logical CPUs, at most one per 8 GB available, within [3, 32] (128 logical CPUs,
500 GB -> 32; override with `--compile-slots`).

## 7. Dry run ($0, fake model, 2 non-benchmark rows; 2026-10-27)
`probe/open_package/dry_run.sh` in a 48G unit: the whole `run` path against `probe/open_package/fake_model.py` (a scripted
OpenAI-compatible server: lean_check, lean_goals, a lean_check_variants batch, write notes, a call to a withheld tool, finish) on two
data/abpool rows (strata, 1 pin; arklib, 3 pins), 2 workers x 2 sessions, end stage with a 1,500 s R5 clock, 3 compile slots.
`PICK=name1,name2` takes other data/abpool rows (never a benchmark row); `LRA_FAKE_SORRY_PROOFS=1` makes the fake model add a
`stop <tactics>` and an `exfalso; impossible by simp` variant to its batch (section S); `probe/open_package/env_probe.py OUT STOPFILE`,
started in the same unit, records for every process of the run whether `LRA_FORCE_WARN_SORRY=1` is in its environment and, per `lean`
process, its warn.sorry argument and project directory (counts only).

Dry run result (unit lra-opk-dry2, 2026-10-27 10:23:34-10:49:44 UTC, 0 runaway-guard kills in the window; output
~/source/lra-ab/opk/dry2, sessions probe/runs/opkdry-s0{0,1}-k{1,2}/; rc 0):
- agent stage: 4 sessions (2 per row, breadth first: both rows' session 1 before any session 2), 11-27 s each against the fake model,
  rc 0; row 1 33.33 -> 33.45, row 0 unchanged (33.33); stage ended "every row parked or at --max-sessions" at 10:24:14.
- the withheld-tool call (`lean_search`) was refused in every session ("unknown tool lean_search in this session (tools: read_file,
  write_file, lean_check, lean_run, ..."); prompt audit: 30 harness-written messages in 4 trajectory files, 0 banned phrases.
- end stage: open_frozen.json minus hr (families sweep, hp, t3, t1, t2, t4, gr), meter `direct` (self-test: direct vs lake heartbeats
  -1 / -8), 3 slots, 0 s slot wait; row 0 33.33 -> 45.42 (315 compiles, 1,505 s), row 1 33.45 -> 51.99 (603 compiles, 1,462 s). The slower
  row ran 5 s past the 1,500 s R5 clock (its last compile), inside the 300 s export margin.
- export: proofs.jsonl with 2 rows, both `source: end`, stored mean 48.705.
- The first attempt (03:09-03:36) ended in `ModuleNotFoundError: No module named 'scorer'` at the export after a clean end stage (the
  driver run as a script has harness/ as sys.path[0]); fixed in open_package.py, pinned by test_open_package.test_export_as_script.
Same window: unit tests (harness.test_open_package, test_speed2_knobs, test_hb_tool_eval: 25 OK), probe/open_rederive tests 37 passed,
harness/selftest.py 32/32 PASS, leak_scan 0 hits.

Dry run 3 (2026-10-27 22:33-22:35 UTC, unit lra-opkra-dry3, after the operator ruling of 22:30 UTC re-admitting lean_skeleton and
lean_profile, audit section H): `CMD=agent TAG=opkdry3 probe/open_package/dry_run.sh` (agent stage, prompt audit, export; no end stage),
the fake model now also calling lean_skeleton and lean_profile. 4 sessions, rc 0; every request carried the same system prompt
(sha256 bbfdbae9756a2915) and the 10 offered tools; lean_skeleton returned each hole's goal and lean_profile the per-block heartbeats,
the floor and the official reference on both rows; lean_search refused; prompt audit 38 messages, 0 banned phrases.
Same window: unit tests (harness.test_open_package, test_speed2_knobs, test_hb_tool_eval) 30 OK, probe/open_rederive 37 passed,
harness/selftest.py 32/32 PASS, leak_scan 0 hits.

Dry run 4 (2026-10-27 23:55:32 - 2026-10-28 00:23:10 UTC, unit lra-opknorm-dry4, branch open-package-norm, the normalize step on by
default; `PORT=18473 TAG=opknormdry probe/open_package/dry_run.sh`, the full `run` path of dry run 2), rc 0: agent stage 4 sessions
(breadth first, rc 0; row 1 33.33 -> 33.45), prompt audit 38 harness-written messages, 0 banned phrases; the agent deadline 0.50 h
after the start (5,400 s job - 1,500 s end stage - 1,800 s normalize share - 300 s margin). End stage: R5 clock 1,500 s, row 0 33.33
-> 46.55 (365 compiles, 1,505 s), row 1 33.45 -> 51.99 (610 compiles, 1,355 s), exit 00:22:49. Normalize step: 2 rows at once, 3,463 s
before the export margin; row 0 46.54 -> 46.71 (+0.17, `semi` 1, 3 compiles, 12 s), row 1 51.89 -> 52.18 (+0.29, `lam` 2 + `dollar` 1,
7 compiles, 21 s), Z 100 before and after (the step reads the input afresh on the lake path, hence 46.54 / 51.89 next to the end
stage's direct-meter 46.55 / 51.99). Export: 2 rows, both `source: normalize` (normalized_from `end`), stored mean 49.445; summary
`normalize` {taken 2, taken_from end 2, gain_sum 0.46}. Sessions probe/runs/opknormdry-s0{0,1}-k{1,2}/. Same window: unit tests
(harness.test_open_package, test_speed2_knobs, test_hb_tool_eval) 39 OK (30 + 9 new), probe/open_rederive 37 passed, the tests of
normalize.py's other callers (test_hb_rewrite 24/24, test_lint_delete 22/22, test_autobrief 9 PASS, test_hb_tool 47, test_postpass
53, test_certify 16, test_hb_tool_config 18 OK), leak_scan 0 hits (62 waived table hits).

Dry run 5 (2026-10-28 01:51:23 - 02:21:10 UTC, unit lra-ol-cost-dry5, branch open-package-cost, the cost ports of the audit's
section P on by default plus `--schedule room` (then opt-in, now the default); `PORT=18475 TAG=opkcostdry FAKE_DELAY=40 EXTRA="--schedule room"
probe/open_package/dry_run.sh`, the full `run` path of dry run 4 with the fake model started 40 s after the driver), rc 0. Agent stage: both
first sessions met a refused connection and waited for the server without using an attempt (`--max-api-retries 2`): 11 + 23 + 43 s and
10 + 24 s, `connect_retry` records, then ran normally; 4 sessions breadth first (both session 2 starts logged their room priority), row 1
33.33 -> 33.45; 34 requests, every one with system sha256 bbfdbae9756a2915 and the 10 tools (unchanged); every JSON tool result compact
with Lean's unicode as text (20 of 20, 0 `\u` escapes); lean_skeleton on the `all_goals sorry` draft returned the hole as a tactic hole
with its goal on both rows; lean_search refused; prompt audit 38 harness-written messages, 0 banned phrases; token_report.json written
(4 sessions, 34 turns, 5 connect retries, junk 0). End stage (R5 clock 1,500 s, 3 slots, the dev box shared with two other workflows'
units): row 0 seed -> 38.89 (200 compiles), row 1 33.45 -> 50.52 (458 compiles), exit 02:20:31; normalize +0.16 (`semi`) and +0.20
(`lam` 2); export 2 rows `normalize` (from `end`), stored mean 44.83 (dry run 4: 46.55 / 51.99 at 365 / 610 compiles: the end stage is
untouched by the ports; the difference is the compile count on the shared box). Sessions probe/runs/opkcostdry-s0{0,1}-k{1,2}/.

Dry runs 6 and 7 (2026-10-29, the section S review, audit section S.1): `PICK` with a PhysLib abpool row, `LRA_FAKE_SORRY_PROOFS=1`,
`env_probe.py` in the unit: rc 0; every session / end-stage / normalize / lake / lean process carried `LRA_FORCE_WARN_SORRY=1` (614 lean
processes in dry run 6); the `stop` / `impossible` variants were rejected in-session with Lean's sorry message on the PhysLib pin; an
export of a copy with those bodies injected as the end output and the agent best passed both over for the seed.

## 8. Known limits (draft)
- No package number yet: the clean prompt (SYSTEM_OPEN, no cards) has not been run on the A100 serving; the 82.03 / 83.37 warm-up
  numbers came from the old prompt (audit section 0). A rehearsal on non-benchmark rows is the next measurement.
- Sessions write trajectories under `probe/runs/` of the checkout (agent.py's fixed location).
- The model's `shell` tool can read any file on the node (writes, network and git history are blocked, reads are not), so the
  release must be the minimal export of the files the open path runs, with fresh Lean environments: a clone of the dev repository
  would expose TAINTED material (audit F.4). Built by probe/open_package/export_release.py (2026-10-28, branch a100-rehearsal): an
  explicit allowlist from a fresh `git archive`, comments removed and docstrings cut to their first line, two dev modules replaced by
  one-symbol stubs, proved by compile + import closure + leak scan (docs/a100_rehearsal.md). Still readable through the model's
  shell: the gated closed-line prompt literals inside harness/agent.py (SYSTEM, the digest's ledger messages); listed as an open item.
- Lean environments of a project we have not seen need its repository URL (section 2).
