# Vexorium open-track package: technical appendix (2026-10-27; the commands to run are in README.md at the root)

The organizers' run (2026-10-31): `bash setup.sh` once before the job, then `bash run.sh` (README.md). This appendix describes the stages,
flags, outputs and our measurements. Names of `docs/*.md`, `harness/test_*.py`, `probe/open_package/guard_check.py` and `data/abpool`
below are files of our development repository, not part of this release.

What it does: for every benchmark row, the open model GLM-5.3-Flash (AWQ W4A16, served by vLLM on the 4 x A100) refactors the seed proof
in tool-using sessions (compile, scratch Lean, grep, multi-variant checks, goal maps, goals at `sorry` holes, heartbeat profiles),
several resumed sessions per row; then a model-free end
stage (CPU only) searches mechanical rewrites of each row's best proof and keeps only edits that compile on every listed toolchain and
score higher, and a lexer normalizer (CPU only) rewrites the result's spellings that the arena tokenizer counts as extra tokens
(`fun x =>` -> `λx =>`, a parenthesised last argument -> `$`, ...) under the same compile-and-score gate; the result is one proof
per row. Everything starts from the seed proofs you provide; no stored proofs, no hosted model, no per-problem knowledge. What the model is shown and where each piece comes from: docs/open_package_audit.md.

## 1. Requirements
- 1 node, 4 x A100 80 GB **SXM4 (NVLink between the GPUs) recommended**: the recipe was measured on 4 x A100 80 GB SXM4 with NVLink
  between every pair of GPUs (`nvidia-smi topo -m`: NV12) and vLLM's custom all-reduce, which needs NVLink; on PCIe A100s vLLM falls back
  to NCCL automatically (no error, same flags) and decode is ~25% slower, so each problem gets fewer sessions in the 48 h;
  64 physical cores; RAM: 256 GB or more recommended (vLLM host memory + up to ~32 concurrent Lean compiles);
  disk: ~200 GB for the checkpoint + ~130 GB for the Lean environments and toolchains of the 15 warm-up rows (measured: 118 GiB unpacked, 4
  projects + Mathlib, 10 toolchains) + ~20 GB for a LeanPool environment (its Mathlib cache and a full `lake build LeanPool`).
- Network: GitHub (project repositories, Mathlib cache), Hugging Face (checkpoint), Docker Hub (vLLM image).
- Software: Docker with the NVIDIA runtime (for vLLM), Python 3.10+ with `requests`, git, curl, ripgrep (`rg`, used by the model's shell
  tool), zstd; elan installs the Lean toolchains.

## 2. Install
```bash
# setup.sh (README.md) runs these steps for you; the manual equivalent, from the release directory (the minimal export, never the dev repository):
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
prefix caching ON, no speculative decoding (MTP off), vLLM's custom all-reduce with NCCL defaults, CUDA graphs at 1, 2, 4, 8, 16,
gpu-memory-utilization 0.92, tool parser glm47, reasoning parser glm45, served name `glm-5.3-flash`; 2026-10-30/31 measurements in
section 4). On the same node no TLS or key is needed: serve on 127.0.0.1:8000.
```bash
mkdir -p $HOME/lra-workspace   # /workspace in the container: HF cache (hf/), vllm.log, READY
docker run -d --name lra-vllm --gpus all --ipc=host -p 127.0.0.1:8000:8000 -v $PWD:/lra:ro -v $HOME/lra-workspace:/workspace \
  --entrypoint bash lazymio/vllm-backport:v0.13.1-sm80 -c "bash /lra/infra/vast/run_vllm.sh && tail -f /workspace/vllm.log"
for i in $(seq 1 360); do curl -sf 127.0.0.1:8000/v1/models >/dev/null && break; sleep 15; done   # ~10-16 min after the download: load, CUDA graphs; bounded at 90 min: read $HOME/lra-workspace/vllm.log if it never answers
```

## 4. Run the benchmark (one command, one clock)
```bash
START=$(date +%s)   # run.sh takes it at its own start, before the server starts; setup.sh runs before the job and is not on the clock (organizers, 2026-10-31)
python3 harness/open_package.py run --rows ROWS.jsonl --heartbeats HEARTBEATS.jsonl --out runs/final \
  --base-url http://127.0.0.1:8000/v1 --api-model glm-5.3-flash --started-at $START --job-seconds 172800 \
  --workers 11 --max-sessions 12 --end-seconds 7200 --end-pipeline on --session-max-context 200000 --first-wave-stagger 120
```
`HEARTBEATS.jsonl` holds the reference heartbeats, one `{"name": ..., "heartbeat": <int>}` line per row (the warm-up release's format).
**A heartbeats file you have (the organizers' reference file) is used as is.** Without one (the final's references are not public), measure
them once, after the environments are built and before the run (about 2-10 min for 60 rows; warm-up rows reuse the published warm-up values):
```bash
python3 infra/refhb/make_ref_heartbeats.py --rows ROWS.jsonl --out HEARTBEATS.jsonl --jobs 8
```
It compiles each row's reference proof (`src`) on its newest toolchain with the same direct Lean invocation the package's meter uses, and
writes `HEARTBEATS.jsonl` (+ `.meta.json`, per-row method and timing) only when every row is covered (exit 0; else `HEARTBEATS.jsonl.partial`
and exit 1). On the 15 warm-up rows its values are within 0.71 % of the official reference file (mean 0.16 %).

These four flags are our official run's recipe and also the package's defaults (2026-10-31): 14 concurrent sessions, at most 12 sessions
per row (within the cap the 48 h deadline and the room schedule decide how many each row gets), the pipelined end stage on
(a row with no session in flight is polished by the end stage on spare CPU during the agent stage, 2 rows at a time; then the closed
final's $0 end stage r10 runs on the same best beside that polish, and a second r10 round on the better output with the polish and the
normalized best as crossover parents, 3 rows at a time: `--end-pipe-r10 on`, docs/open_end_pipeline.md section 7), the end stage at
the agent deadline gets 2 h (R5 clock) for the rows whose current best has no finished polish, the normalize step the last 30 min before
the export, the export the last 15 min. The driver is restartable with the same command (it keeps its job clock in
runs/final/clock.json, counts sessions already run and resumes each row from its saved state). Run it in a memory-capped cgroup if the
node is shared (every compile also passes a memory gate).

Serving measurements behind these numbers (2026-10-31, our rental: 4 x A100 80 GB SXM4, NVLink NV12 between every pair, the
`infra/vast/run_vllm.sh` recipe above; vLLM's own metrics during live package runs on the warm-up rows):

| workers | running requests (mean) | output tok/s (all streams) | per stream |
|---|---|---|---|
| 8 | 6.7 | 359 | 53.5 |
| 12 | 10.75 | 522 | 48.6 |
| 14 | projected | +8.7% over 12 (step-time model on 435 decode windows, interval 7.5-9.7%) | ~7% below 12 |

- KV cache: 2,445,549 tokens. At 12 workers late in sessions: 0 requests waiting, 0 preemptions, KV use mean 0.45, max 0.74; at 14 the
  projected p99 is ~0.82-0.85 (16 workers ~0.91-0.94: too close to preemption, hence 14). Session contexts grow from ~15k tokens to past
  100k; the KV cache, not the interconnect, sets how many sessions fit.
- KV guard (`--kv-guard on`, the default since 2026-11-01; `--kv-guard off` restores the previous driver exactly): before a session
  starts, the driver reads vLLM's `/metrics` on the `--base-url` server (with the sessions' own key) at most every 20 s and holds the
  start while the KV cache use is >= 0.90 (until it is below 0.85), or requests wait while preemptions rose within 3 min; it never holds
  while fewer than `--workers` - 4 sessions are in flight, admits one start per 30 min of a hold, never stops a running session, and
  does nothing when `/metrics` cannot be read within 10 s (said once in the log). Holds and releases go to the log and `runs/final/kv_guard.jsonl`.
  `--session-max-seconds S` (default 0 = off) stops a session S seconds after its start (its banked best stays).
- KV shed, context cap, staggered first wave (b105, 2026-11-01, docs/open_kv_guard.md section 6; all off by default): `--kv-shed on`
  asks ONE session to end at its next turn boundary when the KV cache stays >= 0.95 (or requests wait while preemptions rise) for 3 min
  with more than `--workers` - 4 sessions in flight: the one with the largest last prompt, at least 15 min old, not of the row shed last,
  one per 10 min, none while one is pending; the driver writes `runs/final/shed/<run id>.stop` and the session (agent.py `--stop-file`)
  ends as after its last turn (never a signal, never counted dry). `--session-max-context N` passes agent.py `--max-context-tokens N`
  (a session ends after a turn whose prompt was >= N). `--first-wave-stagger S` starts the first wave one session per S seconds. A
  session stopped by a signal is counted by its trajectory's output tokens (not dry when it produced output).
- A session's time is ~87% model time (almost all decode; prefill and queueing ~1% with prefix caching) and ~13% Lean tools. Session length at 12
  workers: ~100 min from the seed (90-turn budget below 45), ~85 min for a row at 70-80, ~58 min at 80 and above.
- Output caps per call: 18,000 tokens until a turn of the session hits its cap, 24,000 from then on, 6,000 for the forced follow-up
  (3 x / 4 x / 1 x `--max-tokens` 6000); 7.7% of turns hit the cap (24% of output tokens) and are rescued by the forced tool call, not
  discarded.
- On PCIe A100s (no NVLink) vLLM falls back to NCCL for the all-reduce automatically (same flags, no error): decode ~25% slower, i.e.
  fewer sessions per row in the 48 h; the package flags stay the same.

### Cost ports from the closed line (2026-10-28; audit section P)
Mechanical infrastructure from the closed line, no proof knowledge; on by default unless marked opt-in:
- `--no-compact-tool-json`: the sessions run `agent.py --compact-tool-json` by default: tool results as compact JSON with Lean's unicode
  kept (lean_check results were `\uXXXX`-escaped). With the next item, one of the two changes to what the model sees (the result format;
  same fields and values; the system prompt and tool list unchanged; a long unicode-heavy result now reaches the 12,000-character result
  cap later, since a symbol counts 1 character instead of 6). Measured on the A100 line's recorded GLM sessions with the model's own tokenizer: lean_check
  results -24%, all tool results -4.7%, prefill tokens -0.7% (measured while prefix caching was off, so every turn re-sent them).
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

### Dialect pass (2026-10-31; `--dialect on|off`, default on; docs/open_end_pipeline.md section 8)
A deterministic, model-free pass (`harness/dialect.py`, `harness/dialect_unhyg.py`) of source rewrites into the compact dialect (bullet /
case / alternative merges, unused binder names dropped, ascription / `show` drops, lemma-list item drops, `iterate` forms, calc tails, type
holes, let inlining) and of `unhygienic` renames whose names Lean itself prints (`trace_state`), plus T4. It runs through
`harness/endstage.py` with only these families, so every candidate is screened, decided against the re-measured input and confirmed on
every toolchain exactly like the end stage's own edits; a row's proof never gets worse. Where: in the pipelined end stage after a best's
r10 rounds (stage `dial`), and after the end stage on every row not yet through it, inside the end stage's own 2 h window (it never moves
the agent deadline or the normalize share). Per row: 600 s of search (`--dialect-row-seconds`), 400 compiles, one compile slot; rows at
once after the end stage = the compile slots (`--dialect-jobs`). `--dialect off`: nothing of it runs. rc2 (2026-11-01): the pass runs
under the open frozen config's acceptance noise floor (its `accept` block, as the end stage does) with T4 on the shipped op set
(`t4:intro`, `t4:rcases`, `t4:all`); the last `--dialect-seconds` (default 900 s) of the end stage's window are reserved for the step
after the end stage (the end stage stops that much earlier; the agent deadline does not move), so the step runs even when the end stage
uses its whole clock; the write-back before a session never takes a dialect output (the agent keeps editing a readable proof), the
export does. Measured (section 8 of
docs/open_end_pipeline.md, the package's paired meter): +0.77 per row on average over 15 warm-up agent bests (11 improved), +1.90 over
10 non-benchmark rows' reference proofs (10 improved), at most ~12 min per row.

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

### Write-back of the pipelined polish (2026-10-31; `--end-pipe-writeback on`, the default, acts with `--end-pipeline on`)
Right before a row's next session starts (the row has no session in flight then, so nothing races the session's own state writes), the
driver checks the pipelined end stage's output for the row's CURRENT best, the one the export takes (the second r10 round's, else the
better of the open polish and the first r10 round; it waits while that best's r10 rounds are queued or running): when every record it
rests on is valid (its input measured, a real stage) and it beats that best on both counts, the paired delta (measured on every pin in
the same end-stage run; summed over the rounds it rests on) above 0 and its stored score more than 0.005 above the best's stored score,
and it passes the export's checks (exact statement, forbidden patterns), it becomes the row's best
(`work/<row>/state.json` best with the polish's own score, tokens, heartbeats, L, H, Z and per-pin compatibility, and `best.lean`, both
written atomically; the previous state kept as `state.json.before-writeback`), and the session starts from it (`candidate.lean` holds
it). One line per write-back in `writeback.jsonl`. Restart-safe: a polish never applies twice (afterwards the current best IS the
polished proof; a later polish of it is a new write-back), a stop between the state write and its log line is repaired from the best's
own `writeback` record when the driver resumes, a stop before the state write finds the same polish again. Rows with no further session
are not touched (the export already takes the polish of the current best). `--end-pipe-writeback off`: the agent stage runs exactly as
before.

### Dialect card (opt-in, 2026-10-31; `--dialect-card on`, default off)
Every session's opening message gets one generic card (`harness/open_card_dialect.md`, the same text for every row, sha256 pinned in
`open_package.DIALECT_CARD_SHA16`; `agent.py --open-card PATH`): compact Lean 4 idioms to try as single-edit variants once a proof
compiles, and the reminder that heartbeats count too. The driver refuses to start when the card is missing or changed. Off (the
default): the sessions' commands and prompts are byte-identical to before.

Both `--dialect-card` and `--end-pipe-writeback` are frozen per output directory (`method_flags.json`, written by the first `run` /
`agent` call): a resume with other values is refused, so one run never mixes two methods.

## 5. Outputs (runs/final/)
- `proofs.jsonl`: one line per row in the rows file's order: `name`, `proof` (the full declaration), `source` (end / agent / seed /
  normalize; a normalized row also carries `normalized_from` and `normalize_gain`), the stored score, tokens and heartbeats. A row falls
  back to the agent's best, then to the seed, if the end stage's proof fails the forbidden-pattern check; the normalized proof is taken
  only for exactly that proof, when it starts with the row's exact statement and passes the forbidden-pattern check.
- `normalize.jsonl` (one line per row: candidate source, input sha, status, before / after, the proof when improved) and
  `normalize_stage.json` (the step's counts).
- With `--dialect on`: `end-pipe/<row>/<sha>/dial/` (the pipelined stage) and `dialect/<row>/<input sha>/` (the step after the end
  stage), each the end stage's own report.jsonl / finals.json; `dialect_stage.json` (the step's counts).
- With `--style-rw on`: `style_rw.jsonl` (one line per row: input sha, status improved / kept / skipped / stopped / error, before / after,
  gain, the proof when improved), `style_rw_stage.json`, `style_rw/` (per-row records and the model calls' full prompts and answers in
  `style_rw/trajectories/`); a taken row's `source` is `style_rw` with `style_from` and `style_gain`.
- `writeback.jsonl` (one line per write-back: row, the session it preceded, from / to proof sha and score, the paired delta, the polish's
  directory) and `method_flags.json` (the frozen `--dialect-card` / `--end-pipe-writeback`).
- `summary.json`, `agent_sessions.jsonl` (one line per session: row index, run id, seconds, model output tokens, score before / after),
  `prompt_audit.json` (every harness-written message checked against the withheld material), `token_report.json` (the sessions' token
  usage, section 4), `end/report.jsonl` and `end/finals.json`
  (the end stage per row), `logs/` (one log per session, `end.log`, `normalize.rKK.log`), `work/` (per-row state, notes), and the sessions' full
  trajectories under `probe/runs/<run id>/`.

## 6. Time budget for ~60 rows on 4 x A100 + 64 cores (14 workers, --max-sessions 12; docs/a100_throughput_60.md section 6)
Measured on our rental with the recipe of section 3 at 12 workers (2026-10-31, the warm-up rows): sessions take ~100 min from the seed,
~85 min for a row at 70-80 and ~58 min at 80 and above; at 14 workers the output rate is projected +8.7% overall and ~7% lower per
stream (sessions ~6% longer, ~1.09x the sessions per hour). Compiles use the CPU, not the GPUs.

| phase | 60 rows, 14 sessions at once | cumulative |
|---|---|---|
| server start ~16 min (setup.sh, before the job and off the clock: environments ~40-60 min, checkpoint download 191 GB 6-30 min) | ~0.3 h | 0.3 h |
| session 1 of every row (~106 min each from the seed at 14 workers) | 60 x 106 / 14 = ~7.6 h | ~9.1 h |
| sessions 2+ until the agent deadline (~62-90 min each by score band), room schedule; rows with no session in flight are polished by the pipelined end stage on spare CPU | ~36 h = ~510 worker-hours = ~5.5-6.5 more sessions per row on average | 45.25 h |
| end stage at the agent deadline, R5 clock (rows whose current best has no finished polish; auto_slots on 64 physical cores: 21-32 slots) for 1 h 45 min, then the dialect step in its reserved last 15 min (`--dialect-seconds 900`) plus whatever the end stage left (rows not yet through the pass: at most 60 x 900 s / 21-32 slots = 28-43 min; rows that do not start in time keep their pick) | 2 h reserved | 47.25 h |
| normalize step (warm-up measurement: 0-185 s per row, 0-19 compiles; 60 rows at 21-32 rows in flight: ~10 min) | 30 min reserved | 47.75 h |
| export | 15 min | 48 h |

So ~6.5-7.5 sessions per row on average fit, and `--max-sessions 12` caps any one row (at 12 workers 5 sessions x 60 rows needed ~390-430
of ~525 worker-hours: a cap of 5 would have left the GPUs idle for the last ~8-11 h). The room schedule gives the next session to the row
with the most room, (100 - best) / (sessions so far + 1), after every row's first session; the async ladder starts a row's next session
as soon as its last one ends (no pass barrier). If the setup takes longer, `--started-at` moves the agent deadline earlier and the end
stage keeps its 2 h. Compile slots: `auto_slots()` = a third of the logical CPUs, at most one per 8 GB available, within [3, 32] (128
logical CPUs, 500 GB -> 32; override with `--compile-slots`); the pipelined end stage uses its own 2 x 1 slots at lower CPU priority,
its r10 rounds 3 x (1 slot + 1 workbench Lean) at the same priority (at most 8 pipelined Lean processes beside the 14 sessions' ~10-20
busy cores on 64 physical cores; `--end-pipe-r10-jobs`, `--end-pipe-r10-row-s` 7200, `--end-pipe-r10 off` restores the pre-2026-10-31
pipeline).
On PCIe A100s (section 1) decode is ~25% slower and every session ~20-30% longer: ~5-6 sessions per row.

## 7. Dry run ($0, fake model, 2 non-benchmark rows; 2026-10-27)
`probe/open_package/dry_run.sh` in a 48G unit: the whole `run` path against `probe/open_package/fake_model.py` (a scripted
OpenAI-compatible server: lean_check, lean_goals, a lean_check_variants batch, write notes, a call to a withheld tool, finish) on two
data/abpool rows (strata, 1 pin; arklib, 3 pins), 2 workers x 2 sessions, end stage with a 1,500 s R5 clock, 3 compile slots.
`KNOBS=""` (2026-10-31) runs on the package defaults (`--workers 11 --max-sessions 12 --end-seconds 7200 --end-pipeline on --session-max-context 200000 --first-wave-stagger 120`; before b105: `--workers 14`, no cap, no stagger) with
`JOB_S` seconds on the clock, `PICK_N=N` on the first N one-pin data/abpool rows.
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

Dry run 8 = release smoke of the new defaults (2026-10-31 16:03:18-18:11:43 UTC, unit lra-b93-smoke-def, branch b93-pkg-defaults),
started FROM THE EXPORT TREE of 2722ac99 (79 files, import closure 34 modules, leak scan 0 hits; envs and data/abpool linked in) on the
package's OWN defaults: `KNOBS="" JOB_S=10500 PICK_N=16 probe/open_package/dry_run.sh` (no `--workers` / `--max-sessions` /
`--end-seconds` / `--end-pipeline`; 16 one-pin data/abpool rows, 0 benchmark rows), rc 0. Driver: `agent stage: 14 worker(s) over 16
row(s), at most 12 session(s) per row`, 14 sessions in flight from the first second; 192 sessions (every row at --max-sessions 12
after 13 min), all rc 0, 0 dry, 0 tool errors (session logs and trajectories), prompt audit 1,904 harness-written messages, 0 banned
phrases; clock.json `end_seconds` 7200. Pipelined end stage on: 7 offers (3 idle, 4 final), 2 rows polished during the agent stage
(744 / 826 s, valid polish), so the end stage took the other 14 rows: `R5 clock 7200 s`, exit 0 after 6,604 s. Normalize 16 rows (14
improved, +5.5 summed); export 16 rows (end 2, normalize 14), stored mean 49.31 (agent bests 33.34); audit clean 6 / skipped 10, 0
fallbacks. Unit memory peak 3.8 GB (48G cap). Same window: `infra/vast/package_run.sh` from the same tree without WORKERS /
MAX_SESSIONS / END_SECONDS / END_PIPELINE wrote RUN_CMD `... --workers 14 --max-sessions 12 --end-seconds 7200 --end-pipeline on`, and with
official.sh's shape (EXTRA "--end-pipeline on ...") a RUN_CMD byte-identical to the previous package_run.sh; the package gate (every test
module of harness/, scorer/, probe/open_rederive/) 46/46.

Dry run 9 = release smoke of the write-back and the dialect card (2026-10-31 20:34:30-21:36:09 UTC, unit lra-b94b-gate, branch
b94b-writeback-card-infra), started FROM THE EXPORT TREE of 8254a72a (80 files, import closure 34 modules, leak scan 0 hits, the card
scanned as model-facing text): `LRA_FAKE_TURN_S=40 PICK_N=3 JOB_S=6000 KNOBS="--workers 1 --max-sessions 2 --end-seconds 900
--end-pipe-row-s 400 --dialect-card on" probe/open_package/dry_run.sh` (3 one-pin data/abpool rows, 0 benchmark rows; the fake model
waits 40 s per answer so a row's polish finishes while it waits for its next session), rc 0. method_flags.json `dialect_card on` (sha
2739cca463aa35aa), `end_pipe_writeback on`; `open card: open_card_dialect.md` in 6 of 6 session logs and the card in 6 of 6 openings;
prompt audit 56 harness-written messages, 0 banned phrases; 0 tool errors. Write-back end to end: row 0's session 1 banked 33.36, the
pipeline polished it while rows 1 and 2 ran (401 s, valid, paired delta +9.67), and right before row 0's session 2 the driver logged
`write-back ...: agent best 33.36 -> 43.12 (end-pipe polish of 8125ab62b3291bac, paired delta +9.6702); session 2 starts from it`; that
session's opening read "Best so far: score 43.12 (tokens 633, heartbeats 5301); candidate.lean holds it" and its line has score_before
43.12; one writeback.jsonl line (k 2). The new best was polished again as a final offer (324 s, valid), the end stage took the other 2
rows (R5 900 s, exit 0), normalize 2 improved; export 3 rows (end 1, normalize 2), stored mean 43.46, audit clean 2 / skipped 1. Unit
memory peak 5.1 GB (40G cap). Same unit: the package gate (every test module of harness/, scorer/, probe/open_rederive/) 47/48: the one
failure, harness/test_v2_flags.py, was the new `open_card` key missing from its default-off key list (fixed in the next commit) plus one
`exact?` library lead that differed between two runs of the closed-line path under load; rerun in its own 40G unit: 9/9 OK.

## 8. Known limits
- Measured numbers: the A100 rehearsals of 2026-10-30/31 on the warm-up rows (sections 4 and 6); before them, the 82.03 / 83.37 warm-up
  numbers came from the old prompt (audit section 0).
- Sessions write trajectories under `probe/runs/` of the checkout (agent.py's fixed location).
- The model's `shell` tool can read any file on the node (writes, network and git history are blocked, reads are not), so the
  release must be the minimal export of the files the open path runs, with fresh Lean environments: a clone of the dev repository
  would expose TAINTED material (audit F.4). Built by probe/open_package/export_release.py (2026-10-28, branch a100-rehearsal): an
  explicit allowlist from a fresh `git archive`, comments removed and docstrings cut to their first line, two dev modules replaced by
  one-symbol stubs, proved by compile + import closure + leak scan (docs/a100_rehearsal.md). Still readable through the model's
  shell: the gated closed-line prompt literals inside harness/agent.py (SYSTEM, the digest's ledger messages); listed as an open item.
- Lean environments of a project we have not seen need its repository URL (section 2).
