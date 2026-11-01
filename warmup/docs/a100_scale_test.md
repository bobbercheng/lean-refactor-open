# A100 harness worker-scaling test (2026-10-08)

Instance <instance> (4x A100 SXM4 80 GB, vLLM backport, TP4, MTP-3, max-num-seqs 16, KV cache 1.87 M tokens). Harness flags as A100 pass 3 (z.ai-identical:
effort low, --max-tokens 4000, 40 turns), fresh scratch workspaces, all 15 problems. Lean compiles run on the GB10 (shared with POC 2 and the miner),
behind the memory gate, so holds are reported; in the official run compiles run on the A100 host.

| workers | minutes | turns | turns/min | out tok/s (vLLM) | mean running | mean waiting | p50 s/turn | memgate holds |
|---|---|---|---|---|---|---|---|---|
| 4 | 10 | 214 | 21.4 | 134 | 3.3 | 0.1 | 9 | 0 |
| 8 | 20 | 175 | 8.8 | -3 | 4.6 | 0.0 | 16 | 9 |
| 12 | 20 | 202 | 10.1 | 138 | 9.6 | 0.0 | 28 | 27 |

## Conclusion (generated)

- 4 workers: 134 tok/s (1.00x the 4-worker phase), mean 3.3 requests running, 0.1 waiting, p50 9 s per turn, 0 memgate holds, 0 API errors
- 8 workers: -3 tok/s (-0.02x the 4-worker phase), mean 4.6 requests running, 0.0 waiting, p50 16 s per turn, 9 memgate holds, 0 API errors
- 12 workers: 138 tok/s (1.03x the 4-worker phase), mean 9.6 requests running, 0.0 waiting, p50 28 s per turn, 27 memgate holds, 0 API errors

Highest aggregate throughput: **12 workers**. Queueing (waiting > 0) means more workers than max-num-seqs (16) can serve; memgate holds mean the GB10's Lean compiles, not the A100, were the limit in that phase.

## Reading (manual, 2026-10-08 11:05 UTC)
The generated conclusion ("highest throughput: 12 workers") does not hold:
- **The A100 was never the limit.** At most ~10 requests ran at once and none waited (max-num-seqs 16); vLLM had headroom at every worker count.
- **The GB10's Lean compiles were the limit.** Memory-gate holds rose 0 → 9 → 27 and the median turn time rose 9 → 16 → 28 s; turns per minute fell from 21.4 (4 workers) to 8.8 and 10.1. In this setup more workers just queue on compiles.
- **The phases are not comparable as run:** each phase starts fresh workspaces, and the 4-worker phase lasted 10 min (opening turns are cheap reads), the others 20 min. The 8-worker tok/s value (−3) is a metrics-read artefact (counter not sampled), not a measurement.
- **Run history:** pre-empted during the first 8-worker attempt (09:31), resumed 10:09, re-run from phase 1.

**For the official run** (compiles on the A100 host's ~61 cores, not the GB10), this test says nothing about the right worker count beyond "the server handles ≥ 10 concurrent agent requests without queueing". A valid test needs compiles on the A100 host (or equal-length phases with the GB10 otherwise idle). Open item for B18 (official-run budget).
