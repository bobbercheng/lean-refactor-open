#!/usr/bin/env bash
# Installed on the instance at /workspace/run_vllm.sh by bootstrap.sh; started by bootstrap.sh and re-started by onstart.sh after a
# pre-emption resume. Serves GLM-5.3-Flash AWQ W4A16 on 4 GPUs with the pinned vllm-backport recipe; logs to /workspace/vllm.log;
# touches /workspace/READY when /v1/models answers. Idempotent: an already-running server is left alone.
set -u
[ -f /workspace/env ] && . /workspace/env   # VLLM_API_KEY=..., MODEL_REPO, MODEL_REV written by bootstrap.sh
MODEL_REPO=${MODEL_REPO:-wtdcode/GLM-5.3-Flash-AWQ-W4A16}
MODEL_REV=${MODEL_REV:-abd7b07719111f137e1de8a0c1b7e01c11b74d1a}
export HF_HUB_ENABLE_HF_TRANSFER=1 HF_HOME=/workspace/hf HF_HUB_OFFLINE=${HF_HUB_OFFLINE:-0}
# 2026-10-31: NCCL defaults and vLLM's custom all-reduce (NVLink): +36% decode per stream on p85 (docs/a100_throughput_60.md section 6);
# the Ring/Simple export and --disable-custom-all-reduce came from the fork's README (Oct 7) and were never measured
# TLS on the public port (no SSH tunnel in the data path): /workspace/tls/{cert,key}.pem uploaded by bootstrap; the client pins cert.pem
if [ -f /workspace/tls/cert.pem ] && [ -f /workspace/tls/key.pem ]; then TLS="--ssl-certfile /workspace/tls/cert.pem --ssl-keyfile /workspace/tls/key.pem"; URL=https://localhost:8000; CURL="curl -sfk"; else TLS=""; URL=http://localhost:8000; CURL="curl -sf"; fi
# health check as a function: an unquoted header variable word-splits, so the old check never succeeded and READY never appeared
health() { if [ -n "${VLLM_API_KEY:-}" ]; then $CURL -H "Authorization: Bearer $VLLM_API_KEY" "$URL/v1/models"; else $CURL "$URL/v1/models"; fi >/dev/null 2>&1; }
rm -f /workspace/READY
if health; then echo "server already up"; touch /workspace/READY; exit 0; fi
nohup vllm serve "$MODEL_REPO" \
  --revision "$MODEL_REV" \
  --host 0.0.0.0 --port 8000 \
  --served-model-name glm-5.3-flash \
  --tensor-parallel-size 4 \
  --max-model-len 524288 \
  --gpu-memory-utilization 0.92 \
  --max-num-seqs 16 \
  --limit-mm-per-prompt '{"image":0,"video":0}' \
  --max-num-batched-tokens 8192 \
  --enable-prefix-caching \
  --enable-prompt-tokens-details \
  --compilation-config '{"cudagraph_mode":"FULL_AND_PIECEWISE","cudagraph_capture_sizes":[1,2,4,8,16],"max_cudagraph_capture_size":16}' \
  --enable-auto-tool-choice --tool-call-parser glm47 --reasoning-parser glm45 \
  ${VLLM_API_KEY:+--api-key "$VLLM_API_KEY"} $TLS \
  > /workspace/vllm.log 2>&1 &
echo "vllm serve started (pid $!) $(date -u +%H:%M:%S)"
for i in $(seq 1 240); do
  if health; then touch /workspace/READY; echo "READY after $((i*15)) s"; exit 0; fi
  if ! kill -0 "$!" 2>/dev/null; then echo "vllm exited; see /workspace/vllm.log"; exit 1; fi
  sleep 15
done
echo "not ready after 60 min; see /workspace/vllm.log"; exit 1
