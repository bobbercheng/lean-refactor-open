# A100 proof of concept: self-hosted GLM-5.3-Flash on 4×A100 80 GB (runbook, 2026-10-06)

Goal (2026-10-06): prove the harness runs against our own serving on the competition's reproduction hardware class, measure throughput, and get a fresh pass-1 score to compare with OpenRouter NVFP4 (64.69) and the z.ai control. The same recipe is the candidate final pipeline for the organizers' reproduction, so everything below is pinned and recorded.

Why these choices (details in `docs/h100_poc_research.md`): the official FP8 checkpoint is 328 GB and does not fit four GPUs; A100 (sm80) has no upstream vLLM kernel path for GLM-5.3-Flash's sparse-MLA layers; the only working route is the `wtdcode/vllm-backport` fork with the `wtdcode/GLM-5.3-Flash-AWQ-W4A16` checkpoint (routed experts INT4 g128, rest BF16, ~191 GB), which its author verified with MTP-3 on 4×A100-80GB.

## 0. Budget and timeline
| Step | Time | Cost at $5.19/h |
|---|---|---|
| Rent + container start | 5 min | — |
| Download 191 GB (4.4 Gbps node) | ~8 min | $0.7 |
| Model load + cudagraph capture | ~10 min | $0.9 |
| Throughput benchmark (3 concurrent) | 10 min | $0.9 |
| Fresh pass 1, 15 problems, 3 workers | 2–3 h (depends on tok/s) | $10–16 |
| **Total** | **3–4 h** | **≈ $20–25** |

Approval needed before renting. Stop the instance as soon as the pass ends.

## 1. Rent (vast.ai)
Provider comparison for 4×A100 80 GB with ≥ 64 CPU cores (live queries, 2026-10-06 18:05 UTC):

| Provider | Offer | $/h (4 GPUs) | CPU / RAM with it | Notes |
|---|---|---|---|---|
| vast.ai, verified host | A100 SXM4 ×4, NVLink | **5.19** | 128 vCPU (64 physical cores, EPYC 7763), 504 GB | 2.4 TB disk, 4.4 Gbps, reliability 0.99, North Carolina |
| vast.ai, verified host | A100 SXM4 ×4 | 5.87 / 6.46 | 64 vCPU (32 physical), 504 GB | slower links (0.7 / 1.7 Gbps) |
| vast.ai, unverified host | A100 PCIe ×4 (no NVLink) | 3.74–4.00 | 64–128 vCPU, 503 GB | UK, 9 Gbps, but only 60–400 GB disk; PCIe all-reduce is slower for TP4 |
| vast.ai, interruptible bid | same $5.19 node | 1.07 (min bid) | 128 vCPU | can be pre-empted mid-run; not for the POC |
| RunPod Community Cloud | A100 SXM 80 GB ×4 | 5.56 (4 × 1.39) | fixed per-GPU vCPU/RAM template, not selectable (not re-verified today) | API reported stock "Low" for 4 GPUs |
| RunPod Secure Cloud | A100 SXM/PCIe 80 GB ×4 | 6.36 (4 × 1.59) | same | — |

vast.ai is ~7 % cheaper than RunPod Community and ~18 % cheaper than Secure, and it is the only one of the two where 64 physical cores come with the four GPUs (RunPod sells a fixed vCPU allocation per GPU). The cores matter only when the Lean compile pool also moves to the node (the full reproduction rehearsal); for the POC the GB10 compiles.

- Filter: 4× A100 SXM4 80 GB, verified, on-demand, ≥ 64 vCPU, ≥ 300 GB disk, ≥ 1 Gbps download. On 2026-10-06 the best verified offer was $5.19/h (North Carolina, 128 vCPU, 504 GB RAM, 2.4 TB disk, 4.4 Gbps, reliability 0.99, NVLink).
- Template: Docker image `lazymio/vllm-backport:v0.13.0-sm80` (pinned; `latest-sm80` tracks main), **disk 300 GB**, expose port 8000 (or use the SSH tunnel: `ssh -L 8000:localhost:8000 root@<node>`), on-start command empty (we launch vLLM by hand so we can read the logs).
- Record: offer id, image digest (`docker inspect --format '{{index .RepoDigests 0}}' lazymio/vllm-backport:v0.13.0-sm80`), driver version (`nvidia-smi`), and the HF revision of the checkpoint (`huggingface-cli download wtdcode/GLM-5.3-Flash-AWQ-W4A16 --revision <sha>`; take the sha from the model page's commit history at rental time).

### 1b. Interruptible (bid) availability check — 18:17 UTC, via the vast CLI, no rental (`infra/vast/search.sh`)
Prefer interruptible bids (cheaper); scripts in `infra/vast/` (search / create / onstart / status / tunnel / bench / destroy; create and destroy are dry-run unless `CONFIRM=yes`). Account balance is **$0** — top up before `create.sh`.

| Offer id | Bid now | min bid | GPUs | vCPU | disk | down | reliability | host | notes |
|---|---|---|---|---|---|---|---|---|---|
| 52216384 | **$0.86/h** | $0.77 | A100 PCIe ×4 (no NVLink) | 64 | 333 GB | 9.3 Gbps | 0.988 | UK, unverified | cheapest credible: 191 GB downloads in ~3 min; disk is tight (191 GB + image) but enough; TP4 over PCIe is slower |
| 51417952 | $0.62/h | $0.53 | A100 PCIe ×4 | 128 | 397 GB | 9.1 Gbps | 0.840 | UK, unverified | cheaper but low reliability |
| 53873551 | $1.82/h | $1.60 | A100 SXM4 ×4, NVLink | 64 | 3.2 TB | 470 Mb/s | 0.954 | NC, unverified | SXM/NVLink like a datacenter node; slow link: download ≈ 55 min |
| 40747957 | $2.86/h | $2.67 | A100 SXM4 ×4, NVLink | 64 | 2.3 TB | 1.7 Gbps | 0.853 | MS, **verified** | the only verified bid offer; reliability 0.85 |
| 53793967 | $2.75/h | $2.67 | A100 SXM4 ×4 | 64 | 6.3 TB | 0.8 Gbps | 0.953 | JP, unverified | 1 TB RAM |

On-demand for comparison: the verified Mississippi node is $6.65/h with 300 GB storage priced in. Suggested plan: validate the fork + harness on the $0.86/h PCIe node first (whole POC ≈ $4), then a 1-hour SXM/NVLink throughput check on 53873551 or the verified 40747957 (≈ $2–3) so the tech report can quote NVLink numbers. Bid ≈ min bid + $0.10.

Inside the container (the image's entrypoint is `vllm serve`; use `--entrypoint bash` when starting it by hand):
```bash
export HF_HUB_ENABLE_HF_TRANSFER=1 NCCL_ALGO=Ring NCCL_PROTO=Simple
vllm serve wtdcode/GLM-5.3-Flash-AWQ-W4A16 \
  --revision <pinned-sha> \
  --host 0.0.0.0 --port 8000 \
  --served-model-name glm-5.3-flash \
  --tensor-parallel-size 4 \
  --max-model-len 131072 \
  --gpu-memory-utilization 0.92 \
  --max-num-seqs 16 \
  --max-num-batched-tokens 8192 \
  --no-enable-prefix-caching \
  --enable-prompt-tokens-details \
  --disable-custom-all-reduce \
  --compilation-config '{"cudagraph_mode":"FULL_AND_PIECEWISE","cudagraph_capture_sizes":[1,2,4,8,16],"max_cudagraph_capture_size":16}' \
  --speculative-config '{"method":"mtp","num_speculative_tokens":3}' \
  --enable-auto-tool-choice --tool-call-parser glm47 --reasoning-parser glm45 \
  2>&1 | tee /workspace/vllm.log
```
Differences from the fork's README command, on purpose: `--no-enable-prefix-caching` (its issues #107/#108 are prefix caching + MTP: cross-request context pollution and illegal memory access) and `--max-model-len 131072` (our turns stay under ~100k tokens; frees KV memory). Keep `--max-num-seqs 16`.

Health: `curl -s localhost:8000/v1/models` lists `glm-5.3-flash`. Smoke:
```bash
curl -s localhost:8000/v1/chat/completions -H 'content-type: application/json' -d '{"model":"glm-5.3-flash","max_tokens":64,"reasoning_effort":"low","messages":[{"role":"user","content":"Reply with the single word: ready"}]}'
```
Check that the reply has `reasoning_content` (parser works) and that `reasoning_effort` is honoured (short reasoning). If the server rejects `reasoning_effort`, drop it from the harness call with `--extra-body-json '{}'` and compare lengths.

## 3. Throughput benchmark (from the GB10)
```bash
python3 - <<'EOF'
import concurrent.futures as cf, time, requests
URL="http://localhost:8000/v1/chat/completions"
def one(i):
    t=time.time(); r=requests.post(URL,json={"model":"glm-5.3-flash","max_tokens":2000,"reasoning_effort":"low","messages":[{"role":"user","content":f"Write a 1500-word essay on topic {i} about Lean 4 tactic design."}]},timeout=900).json()
    u=r["usage"]; return u["completion_tokens"], time.time()-t
with cf.ThreadPoolExecutor(3) as ex: res=list(ex.map(one,range(3)))
for c,s in res: print(f"{c} tokens in {s:.1f}s = {c/s:.1f} tok/s per stream")
print("aggregate", sum(c for c,_ in res)/max(s for _,s in res), "tok/s")
EOF
```
Record tok/s per stream and aggregate in `accounting/a100_poc.md` with the instance details.

## 4. Harness run (from the GB10, through the tunnel)
```bash
# 2-turn smoke on one problem
python3 harness/agent.py --problems putnam_1964_b2 --turns 3 --workers 1 --model glm-5.3-flash --reasoning-effort low \
  --endpoint openai --base-url http://localhost:8000/v1 --api-model glm-5.3-flash --serving-tag vllm-a100-awq-w4a16 \
  --fresh --work-root harness/work_smoke --run-id smoke-a100-01 --no-adaptive-turns
# fresh pass 1 over all 15 problems, 3 workers (= 3 concurrent requests), full trajectories
AGENT_EXTRA="--base-url http://localhost:8000/v1 --api-model glm-5.3-flash --serving-tag vllm-a100-awq-w4a16" \
  nohup harness/replicate.sh fresh-a100 openai 1 3 > probe/replicate-fresh-a100.log 2>&1 &
```
Records carry provenance `glm-5.3-flash-vllm-a100-awq-w4a16@openai`, so they never enter the z.ai public assembly; `python3 assemble/best.py --include-dev-only --only-run-prefix fresh-a100-` gives the pass-1 score.

## 5. What to compare and record
- tokens/s per stream at 3 concurrent agents, and wall time per pass (OpenRouter NVFP4 pass 1 took 2 h 18 min at 4 workers).
- Fresh pass-1 assembled score vs OpenRouter NVFP4 64.69 and the z.ai control; per-problem table; truncation rate; compile rate.
- Any serving fault (illegal memory access, context pollution: a reply that references another problem's proof is the #107 signature).
- All pins (image digest, checkpoint sha, driver, flags) into `accounting/a100_poc.md` and PLAN §7.5 / the tech report's reproduction section.

## 6. If it fails
- OOM at cudagraph warmup → `--gpu-memory-utilization 0.88`, `--max-num-seqs 8`.
- Garbage or cross-talk between requests → confirm prefix caching is off; drop MTP (`--speculative-config` removed) and re-measure.
- Parser errors on tool calls → compare `--tool-call-parser glm47` vs `glm45`; worst case run with `--extra-body-json '{"tool_choice":"none"}'` is not an option for the agent, so report and stop.
- Fork cannot serve at all → the A100 path is blocked; escalate to the team and the organizers (hardware question).

## 7. Provisioning review and transport security (2026-10-06 20:12 UTC)

**TLS / certificate validation (verified live):** every remote endpoint we use presents a valid chain and our clients verify it — console.vast.ai (Amazon RSA 2048 M04, expires 2026-12-02), openrouter.ai (Google Trust Services WE1, 2026-12-26), huggingface.co (Amazon RSA 2048 M01, 2027-02-27), api.z.ai (Sectigo DV R36, 2026-11-27). Python `requests` (used by `llm/openai_compat.py`, `infra/vast/bench.py`) verifies by default; nothing in `harness/`, `llm/`, `infra/`, `probe/` disables verification (no `verify=False`, `--insecure`, `HF_HUB_DISABLE_SSL`, `PYTHONHTTPSVERIFY`). The vast CLI's only `verify=False` is in `cli/commands/machines.py` line 897 (a host-side machine progress call we never make); `search/create/show/destroy` go over verified HTTPS. Inside the instance, `huggingface_hub` downloads the checkpoint over verified HTTPS (default).

**SSH:** host keys are trust-on-first-use (`StrictHostKeyChecking=accept-new`): the first connection records the key, any later change is refused. Vast publishes no host keys, so TOFU is the available model; the proxy hosts (`sshN.vast.ai`) and the direct IP are both recorded (hashed known_hosts). Only the ed25519 key is used.

**API port:** the harness goes through the SSH tunnel (encrypted, authenticated). The direct public mapping of port 8000 (`-p 8000:8000`) is plain HTTP; it was unauthenticated on the first two instances — fixed 20:10 UTC: `create.sh` passes a bearer token (`~/.config/vexorium/vllm_api_key`, mode 600, generated locally with `secrets.token_urlsafe`) into the container, `onstart.sh` starts vLLM with `--api-key`, and `bench.py`/`status.sh`/the harness (`--api-key-file`) send it. Instance <instance> was created before this fix: its server is restarted with the key as soon as SSH is up.

**Provisioning process review (what runs, in order):**
1. `search.sh` — read-only offer search (4× A100 80 GB, ≥ 64 vCPU, ≥ 300 GB disk, storage priced at 300 GiB); verified; shows credit.
2. `create.sh <offer> <bid>` — `vastai create instance` with: pinned image `lazymio/vllm-backport:v0.13.1-sm80`, `--disk 300`, `--ssh --direct` (sshd injected by vast, direct port mapping), `--env` with the 8000 mapping, `HF_HUB_ENABLE_HF_TRANSFER=1` and the API key, `--onstart onstart.sh`, `--label lra-a100-poc`, `--bid_price` (interruptible), `--cancel-unavail`; dry-run unless `CONFIRM=yes`. Verified: creates the instance, returns `new_contract`.
3. `onstart.sh` (inside the container, every start) — (a) repair `/root/.ssh` ownership and modes immediately and for two minutes in the background; (b) HF cache on `/workspace/hf` (instance disk, survives pause/resume); (c) **host guard**: abort with `/workspace/BAD_HOST` if any GPU already has > 12 GB used; (d) `vllm serve` with the pinned revision and flags, `--api-key`; (e) wait up to 60 min for `/v1/models`, then `/workspace/READY`.
4. From the GB10: `status.sh` → `tunnel.sh <id>` → `bench.py` → harness smoke → `replicate.sh fresh-a100 openai 1 3` with `AGENT_EXTRA` (base URL, model id, serving tag, `--api-key-file`, `--max-api-retries 20`).
5. `destroy.sh <id>` — the CLI's destroy with `-y` and a verification that the id is gone from the account.

**Defects found today and fixed:** (1) instance <instance>'s host had another tenant's 67–70 GB on every GPU → the host guard (step 3c); (2) instance <instance>'s host injected `authorized_keys` with bad modes, sshd refused every key → step 3a; (3) the CLI's destroy prompts "[y/N]" and prints "Aborted." with exit 0 when stdin is not a terminal — the first teardown silently did nothing and the instance billed ~10 extra minutes → `-y` + verification; (4) a torn-down machine's ask can stay "listed but not available" for several minutes → retry or take another host; (5) the public API port had no auth → bearer token.

**Remaining known risks:** bid pre-emption pauses the server (harness waits ≈ 1.5 h with `--max-api-retries 20`); the fork's open bugs (prefix caching + MTP) are avoided by `--no-enable-prefix-caching`; the vast proxy SSH hosts are shared infrastructure (TOFU), so nothing beyond proofs and logs transits them.

## 8. Critical-path design checklist (added 2026-10-06 after the tunnel incident)

Apply to every component the harness cannot run without (model data path, Lean compile path, submission path):

1. **No long-lived multiplexed channel.** The data path is TLS on the instance's public port with a pinned self-signed certificate; the local bridge (`infra/vast/tls_bridge.sh <instance id>`) opens a fresh verified connection per request. SSH is control-plane only, via the direct address (`public_ipaddr` + mapped 22), never the shared `sshN.vast.ai` proxy.
2. **Probe the real path.** The bridge's health probe is a ~200 KB `POST /tokenize` (no GPU time) every 60 s; `GET /v1/models` proves nothing about large bodies.
3. **Progress-based stall detection.** A run that writes no trajectory for 15 min while the server reports 0 running requests is stalled, whatever the health endpoints say.
4. **Client-side guards for known failure classes.** Context overflow: `llm/openai_compat.py` shrinks `max_tokens` and retries once on a context-length 400; transient errors: `--max-api-retries` with capped backoff; window sized for the longest conversation plus the largest output cap (524k on the A100 server).
5. **Self-healing with a cooldown.** Three consecutive probe failures re-resolve the instance address from `vastai` (a pre-emption resume changes the mapped ports) and restart the bridge; forked handlers finish in-flight requests. Restarts are rate-limited so a slow recovery is not mistaken for a new failure.
6. **Cache the last known good configuration** (`probe/a100-bridge.addr`) so the bridge comes up even when the control API is down.
7. **Per-flow dead-path detection.** A real-path probe proves the path works for new connections, not that every existing flow is alive. Outbound sockets carry `TCP_USER_TIMEOUT` (60 s) and keepalives, the bridge supervisor kills a child whose Send-Q stays > 64 KB for 60 s, and the client's read timeout is bounded by the longest legitimate generation (900 s), never 30 min.
8. **Quote shell health checks** (`-H "Authorization: Bearer $KEY"`); an unquoted header variable word-splits and the check never passes.
8. **Release only on evidence of work.** Any chain that destroys an instance must first verify the run log (≥ N `DONE` lines) — a failed launch exits instantly and looks like completion. Scripts run from copies must get `REPO_ROOT`.
9. **Drop bad hosts early (2026-10-07).** `bootstrap.sh` gives the SSH port 180 s (`SSH_DEADLINE_S`) from the instance reporting running; if TCP never opens, the host is bad: it is destroyed automatically and the bootstrap exits 3. If TCP opens but login fails for 120 s, that points to our own provisioning (keys, modes): the bootstrap stops without destroying (exit 4) so the script gets fixed instead of burning hosts. Observed: healthy hosts open SSH in 1–2 min; instance <instance> took 6.5 min (kept, since the rule did not exist yet).
10. **nvtop in the provision as a health probe (2026-10-07).** `bootstrap.sh` installs nvtop right after the host check, before the 190 GB download, under `APT_DEADLINE_S` (240 s, apt update + install). A timeout means a bad host: destroyed, exit 5. A fast apt error is not a slowness signal and only warns. `provision.sh` wraps create + bootstrap and rents a replacement (bid min_bid + $0.01, failed machine blacklisted in `infra/vast/bad_machines.txt`, at most 3 attempts) whenever bootstrap drops a host.
11. **One readiness check: `infra/vast/server_up.sh <id> [--bridge]` (2026-10-07: a reliable check that the server is up).** It walks the real path and stops at the first failing layer: vast record (running; IP and ports resolved fresh) → TCP to the API port → `/v1/models` over pinned TLS → a real 2-token completion (the engine, not just the API process) → optionally the same completion through the local bridge. On a failure it looks inside over SSH (vLLM process alive? READY? last log line) and prints one line, `UP …` or `DOWN layer=<x>: <reason> [inside: …]`. bootstrap, provision and the eval chain all wait on it; nothing waits on a log line any more. All vast scripts source `infra/vast/common.sh` (full PATH plus a `require` check for the tools each script needs), because systemd user services do not get the login PATH.
12. **Continuous health watchdog: `infra/vast/health.py <id>` as service `lra-health` (2026-10-07: catch any critical error as early as possible).** Every 60 s: vast record (pre-emption/stop = CRITICAL), credit and hours left, direct SSH login, `server_up.sh --bridge`, and inside the box vLLM alive, 4 GPUs, nvidia-smi responsive, uncorrected ECC, temperature, /workspace space, new error lines in vllm.log, stalls (requests running but no generation). One-off misses are WARN, 3 in a row CRITICAL; hard faults are CRITICAL at once. Heartbeat lines go to `probe/a100-health.log`. It reports and does not act. `provision.sh` starts it, and it exits when the instance is released.
13. **SSH is direct only (2026-10-07).** `ssh -p <22/tcp HostPort> root@<public_ipaddr>`, printed by `status.sh`. The vast proxy (`sshN.vast.ai`) is not used or checked: at 20:36 it was down, and the instance's reverse tunnel to it kept restarting, while direct SSH worked.
14. **vast credit lives in `credit`, not `balance`** (`balance` reads 0). provision/search/health read `credit`.
15. **Saturation is not an outage (2026-10-07 21:04).** With the eval at 16 streams (= `--max-num-seqs`), server_up's 2-token probe queued behind them and timed out, which raised a false `DOWN layer=engine`. On a failed probe, server_up now reads `/metrics` twice, 10 s apart. If requests are running and `generation_tokens_total` rises, it reports `UP (engine saturated …)`; if the counter is flat, the engine is stalled and it reports DOWN. Measured: 16 streams ≈ 340 tok/s aggregate vs ≈ 130 at 8 streams.
16. **Release holds (2026-10-07).** `destroy.sh` refuses while `probe/a100-hold-<id>` exists (`FORCE=yes` overrides). This lets a follow-up job keep an instance that an already-running chain would otherwise release. First use: the harness worker-scaling test (`infra/vast/scale_test.sh`, service `lra-scale`) after the LR eval. Phases of 4/8/12 workers × 10/20/20 min on fresh scratch workspaces; the summary goes to `docs/a100_scale_test.md`; the instance is released afterwards, or kept if the eval failed.
17. **Bid by iteration, not jumps (2026-10-08).** Rentals start at min_bid + $0.01 (`provision.sh`). When outbid, raise the bid in small steps with `vastai change bid <id> --price …` and watch whether the instance resumes; never jump (a proposed "min + 35%" margin was rejected). Jump only when the next price is known (e.g. the winning bid is visible) or there is no choice (machine withdrawn from the market → re-rent, option A).

