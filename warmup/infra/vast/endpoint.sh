# Model endpoint for the on-instance harness; sourced by chain_on_instance.sh and resume_pass_instance.sh. Exports EP_URL, EP_KEY and
# AGENT_EXTRA, and defines preflight() (one real completion through the harness's own client; prints "ok").
# Replication (the organizers run the official benchmark on their own server, 2026-10-09): set LRA_BASE_URL to their OpenAI-compatible
# server, e.g. http://127.0.0.1:8000/v1 with no TLS, and LRA_API_KEY_FILE only if it needs a bearer token. Without LRA_BASE_URL this is our
# vast setup: vLLM serves TLS only, with a pinned self-signed cert (SANs lra-a100 and the public IP) and an API key.
if [ -n "${LRA_BASE_URL:-}" ]; then
  EP_URL=$LRA_BASE_URL; EP_KEY=${LRA_API_KEY_FILE:-}
else
  grep -q " lra-a100$" /etc/hosts || echo "127.0.0.1 lra-a100" >> /etc/hosts   # a container restart rewrites /etc/hosts
  cat "$(python3 -c 'import certifi; print(certifi.where())')" /workspace/tls/cert.pem > /workspace/tls/ca-bundle.pem
  export REQUESTS_CA_BUNDLE=/workspace/tls/ca-bundle.pem   # the harness client is plain requests, so the cert is trusted without code changes
  EP_URL=https://lra-a100:8000/v1; EP_KEY=/root/.config/vexorium/vllm_api_key
fi
export EP_URL EP_KEY LRA_API_MODEL=${LRA_API_MODEL:-glm-5.3-flash}
export AGENT_EXTRA="--base-url $EP_URL ${EP_KEY:+--api-key-file $EP_KEY} --api-model $LRA_API_MODEL --serving-tag ${LRA_SERVING_TAG:-vllm-a100-awq-w4a16} --max-api-retries 20"
# Extra harness flags for the line (pass 8, 2026-10-09: --relative-error-lines --variant-scores): LRA_AGENT_FLAGS, else the file AGENT_FLAGS
# beside HARNESS_COMMIT (written by migrate_harness.sh), so a resume after a vast stop runs with the same flags as the pass it finishes.
LRA_AGENT_FLAGS=${LRA_AGENT_FLAGS:-$(cat AGENT_FLAGS 2>/dev/null)}
[ -n "$LRA_AGENT_FLAGS" ] && AGENT_EXTRA="$AGENT_EXTRA $LRA_AGENT_FLAGS"
export LRA_AGENT_FLAGS
# What the GCS sidecar snapshots for passes FIRST..LAST (earlier passes are already in the bucket); missing paths are skipped each cycle.
sidecar_paths() { echo harness/work_fresh-a100 $(for k in $(seq "$1" "$2"); do echo "probe/runs/fresh-a100-p$k probe/fresh-a100-p$k.log"; done) probe/a100-80-chain-instance.log accounting; }
preflight() {
  timeout 300 python3 -c "
import os
from llm import openai_compat as o
k = os.environ.get('EP_KEY'); key = open(k).read().strip() if k and os.path.exists(k) else 'EMPTY'
o.create(base_url=os.environ['EP_URL'], api_key=key, model=os.environ['LRA_API_MODEL'], max_tokens=200, system='Answer in one word.',
         tools=[], messages=[{'role': 'user', 'content': 'Say OK.'}]); print('ok')" 2>&1 | tail -n 1
}
# Optional services, never needed to replicate: the GCS backup sidecar (our bucket-only key) and the W&B live traces (our netrc entry).
gcs_on() { [ -f "$HOME/.config/vexorium/gcs_sync_key.json" ] && [ "${LRA_NO_GCS:-0}" != 1 ]; }
wandb_on() { [ "${LRA_NO_WANDB:-0}" != 1 ] && python3 -c "import wandb" 2> /dev/null && { [ -n "${WANDB_API_KEY:-}" ] || grep -qs "api.wandb.ai" "$HOME/.netrc"; }; }
