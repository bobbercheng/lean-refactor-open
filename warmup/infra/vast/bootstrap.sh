#!/usr/bin/env bash
# SSH-driven bootstrap of a vast.ai A100 POC instance, run from the GB10 with everything observable:
#   wait for SSH -> check the on-start guard -> install /workspace/env + /workspace/run_vllm.sh -> pre-download the pinned
#   checkpoint with progress -> start the server -> wait until server_up.sh says UP. Re-runnable; each step is skipped if already done.
# Usage: infra/vast/bootstrap.sh <instance_id>
set -eu
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai ssh openssl python3
ID=${1:?instance id}
HERE=$(cd "$(dirname "$0")" && pwd)
KEY=$(cat ~/.config/vexorium/vllm_api_key)
MODEL_REPO=wtdcode/GLM-5.3-Flash-AWQ-W4A16
MODEL_REV=abd7b07719111f137e1de8a0c1b7e01c11b74d1a
# the port map appears only once the instance is running: wait for it (up to 20 min) instead of failing on the first read
echo "[0/5] waiting for the instance to come up and publish its port map"
for i in $(seq 1 80); do
  J=$(vastai show instance "$ID" --raw 2>/dev/null)
  PORT=$(echo "$J" | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d["ports"]["22/tcp"][0]["HostPort"])' 2>/dev/null) && break
  echo "  $(date +%H:%M:%S) status=$(echo "$J" | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d.get("actual_status"), (d.get("status_msg") or "")[:60])' 2>/dev/null)"
  sleep 15; [ "$i" = 80 ] && { echo "instance never published a port map"; exit 1; }
done
HOST=$(echo "$J" | python3 -c 'import json,sys; print(json.load(sys.stdin)["public_ipaddr"])')   # direct address, not the shared sshN.vast.ai proxy
SSH="ssh -i $HOME/.ssh/id_ed25519 -o StrictHostKeyChecking=accept-new -o BatchMode=yes -o ConnectTimeout=20 -o ServerAliveInterval=30 -p $PORT root@$HOST"
# Drop bad hosts early (2026-10-07: drop a host at once when SSH is unreachable instead of waiting; the
# principle is to drop a bad instance as early as possible unless our own provision script has a bug):
#   * TCP to the SSH port not open within SSH_DEADLINE_S (180 s) of the instance reporting running -> bad host: destroy, exit 3;
#   * TCP open but SSH auth/command failing for 120 s -> likely OUR provisioning (keys, modes): stop WITHOUT destroying, exit 4.
SSH_DEADLINE_S=${SSH_DEADLINE_S:-180}
echo "[1/5] waiting for SSH at $HOST:$PORT (deadline ${SSH_DEADLINE_S}s for the port to open)"
T0=$(date +%s); TCP_OPEN_AT=""
while true; do
  if timeout 8 bash -c "</dev/tcp/$HOST/$PORT" 2>/dev/null; then
    [ -z "$TCP_OPEN_AT" ] && { TCP_OPEN_AT=$(date +%s); echo "  ssh port open after $((TCP_OPEN_AT - T0))s"; }
    if $SSH 'echo SSH_OK' 2>/dev/null | grep -q SSH_OK; then break; fi
    if [ $(( $(date +%s) - TCP_OPEN_AT )) -gt 120 ]; then
      echo "SSH port open but login fails for 120s: likely a provisioning bug (keys/modes); NOT destroying instance $ID"; exit 4; fi
  elif [ $(( $(date +%s) - T0 )) -gt "$SSH_DEADLINE_S" ]; then
    echo "BAD HOST: ssh port not reachable ${SSH_DEADLINE_S}s after running; destroying instance $ID"
    CONFIRM=yes "$HERE/destroy.sh" "$ID"; exit 3
  fi
  sleep 10
done
echo "[2/5] host check"
$SSH 'cat /workspace/ONSTART_OK 2>/dev/null; if [ -e /workspace/BAD_HOST ]; then echo BAD_HOST; cat /workspace/BAD_HOST; exit 2; fi; nvidia-smi --query-gpu=index,name,memory.used,memory.total --format=csv,noheader; df -h /workspace | tail -n 1' 2>/dev/null | grep -v "Welcome\|Have fun"
# nvtop is part of the provision AND a cheap end-to-end health probe (2026-10-07: if it is very slow or times out during the
# provision, destroy the instance and rent a new one). Runs before the 190 GB download so a bad host costs minutes, not an hour.
#   timeout (apt update+install not done within APT_DEADLINE_S) -> bad host: destroy, exit 5 (provision.sh rents a replacement);
#   fast apt error (lock, missing package) -> not a slowness signal: warn and continue.
APT_DEADLINE_S=${APT_DEADLINE_S:-240}
echo "  installing nvtop (deadline ${APT_DEADLINE_S}s; slow apt = bad host)"
T0=$(date +%s); set +e
timeout $((APT_DEADLINE_S + 60)) $SSH "command -v nvtop >/dev/null && exit 0; export DEBIAN_FRONTEND=noninteractive; timeout $APT_DEADLINE_S bash -c 'apt-get -o DPkg::Lock::Timeout=60 update -qq >/dev/null 2>&1 && apt-get -o DPkg::Lock::Timeout=60 install -y -qq nvtop >/dev/null 2>&1'" >/dev/null 2>&1
RC=$?; set -e
echo "  nvtop step: rc=$RC after $(( $(date +%s) - T0 ))s"
if [ "$RC" = 124 ]; then
  echo "BAD HOST: apt update+install nvtop not done in ${APT_DEADLINE_S}s; destroying instance $ID"
  CONFIRM=yes "$HERE/destroy.sh" "$ID"; exit 5
elif [ "$RC" != 0 ]; then echo "  WARNING: nvtop install failed fast (rc=$RC); not a slowness signal, continuing"; fi
echo "[3/5] installing /workspace/env, /workspace/run_vllm.sh and the TLS pair (pinned self-signed cert for the public port)"
# a re-run after an outbid (2026-10-09 review): on resume vast ran onstart.sh, which started the server on the OLD TLS pair; this step makes
# a new pair, so stop that server first and let step 5 start it on the new one (else the pinned check never passes and READY never comes)
# pkill returns at once; the engine processes (VLLM::EngineCore, VLLM::Worker_TP*) exit only after the API server, and while they hold GPU
# memory a new server fails "Free memory ... less than desired" (review 2026-10-09): wait for them, then force
$SSH 'pkill -f "[r]un_vllm.sh"; pkill -f "[v]llm serve"; for i in $(seq 1 30); do pgrep -f "[v]llm serve|[V]LLM::" > /dev/null || break; sleep 2; done
      pkill -9 -f "[v]llm serve|[V]LLM::"; rm -f /workspace/READY; true' 2>/dev/null
IP=$(echo "$J" | python3 -c 'import json,sys; print(json.load(sys.stdin)["public_ipaddr"])')
APIPORT=$(echo "$J" | python3 -c 'import json,sys; print(json.load(sys.stdin)["ports"]["8000/tcp"][0]["HostPort"])')
TLSD=$HOME/.config/vexorium/vllm_tls; mkdir -p "$TLSD"; chmod 700 "$TLSD"
openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 30 -subj "/CN=lra-a100" -addext "subjectAltName=DNS:lra-a100,IP:$IP" -keyout "$TLSD/key.pem" -out "$TLSD/cert.pem" 2>/dev/null
chmod 600 "$TLSD/key.pem"
$SSH 'mkdir -p /workspace/tls' 2>/dev/null
$SSH 'cat > /workspace/tls/cert.pem' < "$TLSD/cert.pem" 2>/dev/null
$SSH 'cat > /workspace/tls/key.pem && chmod 600 /workspace/tls/key.pem' < "$TLSD/key.pem" 2>/dev/null
printf 'VLLM_API_KEY=%s\nMODEL_REPO=%s\nMODEL_REV=%s\n' "$KEY" "$MODEL_REPO" "$MODEL_REV" | $SSH 'cat > /workspace/env && chmod 600 /workspace/env' 2>/dev/null
$SSH 'cat > /workspace/run_vllm.sh && chmod +x /workspace/run_vllm.sh' < "$HERE/run_vllm.sh" 2>/dev/null
echo "[4/5] checkpoint download (190.8 GB, resumable; progress below)"
$SSH "export HF_HOME=/workspace/hf HF_HUB_ENABLE_HF_TRANSFER=1; (hf download $MODEL_REPO --revision $MODEL_REV 2>&1 || huggingface-cli download $MODEL_REPO --revision $MODEL_REV 2>&1) | tr '\r' '\n' | grep -E --line-buffered 'Fetching|%|Downloading|Error|error' | awk 'NR%20==0 || /Error|error|Fetching 24/' ; du -sh /workspace/hf" 2>/dev/null | grep -v "Welcome\|Have fun"
echo "[5/5] starting the server (log: /workspace/vllm.log on the instance)"
# fully detach (setsid + stdin from /dev/null), otherwise the ssh session never returns while the server runs
$SSH 'setsid nohup /workspace/run_vllm.sh > /workspace/run_vllm.out 2>&1 < /dev/null & sleep 3; cat /workspace/run_vllm.out' 2>/dev/null | grep -v "Welcome\|Have fun" || true
# readiness = infra/vast/server_up.sh (real path: vast record, TCP, pinned-TLS /v1/models, a real 2-token completion), not a log line
for i in $(seq 1 80); do
  V=$("$HERE/server_up.sh" "$ID" 2>&1) && { echo "[$(date +%H:%M:%S)] $V"; echo "server ready"; exit 0; }
  echo "[$(date +%H:%M:%S)] $V"
  case "$V" in *process=dead*|*Traceback*|*"Engine core initialization failed"*|*OutOfMemory*) echo "server failed; read /workspace/vllm.log"; exit 1;; esac
  sleep 30
done
echo "not ready after 40 min"; exit 1
