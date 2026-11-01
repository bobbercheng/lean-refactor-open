#!/usr/bin/env bash
# Second-model trial on the rented A100.
# Runs after the LR eval and the worker-scaling test (it holds the instance via probe/a100-hold-trial-<id>). For each candidate: stop the current
# server, download the pinned revision, serve it on the same port with the same TLS cert and API key, wait for server_up, run the 71-item LR skill
# eval at 1 sample/item. Then release the instance. Scoring (Lean) happens on the GB10 afterwards.
#   Usage: infra/vast/model_trial.sh <instance_id>     (systemd user service lra-trial)
set -u
cd "${REPO_ROOT:-$(dirname "$0")/../..}" || exit 2
. infra/vast/common.sh; require vastai curl python3 ssh
ID=${1:?instance id}; KEY=$(cat ~/.config/vexorium/vllm_api_key)
log() { echo "[$(date -u -Is)] $*"; }
log "waiting for the scaling test to finish"
until ! systemctl --user is-active -q lra-scale && grep -q "Conclusion" docs/a100_scale_test.md 2>/dev/null; do sleep 60; done
J=$(vastai show instance "$ID" --raw); read -r IP SSHP < <(echo "$J" | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d["public_ipaddr"], d["ports"]["22/tcp"][0]["HostPort"])')
SSH="ssh -i $HOME/.ssh/id_ed25519 -o BatchMode=yes -o ConnectTimeout=20 -o ServerAliveInterval=30 -p $SSHP root@$IP"
systemctl --user stop lra-bridge 2>/dev/null
systemd-run --user --unit=lra-bridge --collect -p WorkingDirectory="$PWD" /usr/bin/bash -c "exec infra/vast/tls_bridge.sh $ID >> probe/a100-tls-bridge.log 2>&1" >/dev/null
# name | repo | revision | TP | max-model-len | effort | extra vllm flags   (2026-10-08: gpt-oss-120b is old; newest < 200B candidates)
TRIALS=("leanstral-1.5|mistralai/Leanstral-1.5-119B-A6B|81592da95d94ab0439bfce16df1d55b402e598b6|4|65536|none|--tokenizer-mode mistral --config-format mistral --load-format mistral"
        "qwen3.8-27b|Qwen/Qwen3.8-27B|1d4bf0f2ff6012fd82039f2fa52739d0dd7c60c0|4|65536|none|--reasoning-parser qwen3"
        "goedel-v2-32b|Goedel-LM/Goedel-Prover-V2-32B|851bf85d329b0f819e1a44db30e05d16e07d15c0|4|40960|none|")
for spec in "${TRIALS[@]}"; do
  IFS="|" read -r NAME REPO REV TP LEN EFF EXTRA <<< "$spec"
  log "trial $NAME: stopping the current server, downloading $REPO@${REV:0:12}"
  $SSH "pkill -f '[v]llm serve' ; sleep 15; rm -f /workspace/READY; export HF_HOME=/workspace/hf; (hf download $REPO --revision $REV >/dev/null 2>&1 || huggingface-cli download $REPO --revision $REV >/dev/null 2>&1); du -sh /workspace/hf | tail -n 1" 2>/dev/null | grep -v "Welcome\|Have fun"
  $SSH "export HF_HOME=/workspace/hf; setsid nohup vllm serve $REPO --revision $REV --served-model-name $NAME --host 0.0.0.0 --port 8000 --tensor-parallel-size $TP --max-model-len $LEN --gpu-memory-utilization 0.90 --max-num-seqs 16 --api-key $KEY --ssl-certfile /workspace/tls/cert.pem --ssl-keyfile /workspace/tls/key.pem $EXTRA > /workspace/vllm_$NAME.log 2>&1 < /dev/null & sleep 2; echo started" 2>/dev/null | grep -v "Welcome\|Have fun"
  echo "$NAME" > probe/a100-served-model
  ok=0
  for k in $(seq 1 60); do V=$(infra/vast/server_up.sh "$ID" --bridge 2>&1) && { ok=1; break; }; sleep 30; done
  log "$NAME: $V"
  if [ "$ok" != 1 ]; then log "$NAME did not come up in 30 min; last server log:"; $SSH "tail -n 5 /workspace/vllm_$NAME.log" 2>/dev/null | grep -v "Welcome\|Have fun"; continue; fi
  log "$NAME: LR eval (71 items x 1 sample, effort $EFF)"
  python3 probe/lr_eval.py run --endpoint a100 --api-model "$NAME" --effort "$EFF" --samples 1 --workers 16 --tag "trial-$NAME" >> probe/lr_eval/trial-gen.log 2>&1
  log "$NAME: $(wc -l < probe/lr_eval/runs/trial-$NAME.jsonl 2>/dev/null || echo 0) samples"
done
echo glm-5.3-flash > probe/a100-served-model
rm -f probe/a100-hold-trial-"$ID"
printf -- "- %s UTC second-model trial done (Leanstral 1.5, Qwen3.8-27B, Goedel-Prover-V2-32B); releasing instance %s\n" "$(date -u +%Y-%m-%dT%H:%M)" "$ID" >> accounting/a100_poc.md
CONFIRM=yes infra/vast/destroy.sh "$ID"
systemctl --user stop lra-bridge 2>/dev/null
log "trial done; score with: python3 probe/lr_eval.py score --tag trial-<name>"
