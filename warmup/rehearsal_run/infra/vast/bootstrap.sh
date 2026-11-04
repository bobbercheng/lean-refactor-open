#!/usr/bin/env bash
# SSH-driven bootstrap of a vast.ai A100 POC instance, run from the GB10 with everything observable:
#   wait for SSH -> check the on-start guard -> install /workspace/env + /workspace/run_vllm.sh -> pre-download the pinned
#   checkpoint with progress -> start the server -> wait until server_up.sh says UP. Re-runnable; each step is skipped if already done.
# Usage: infra/vast/bootstrap.sh <instance_id>
# Exit codes: 0 ready; 3 bad host, destroyed (SSH port never opened, or GPUs occupied: BAD_HOST); 4 SSH login fails (kept); 5 bad host,
# destroyed (apt or the checkpoint download too slow); 6 download failed (kept, server NOT started); 7 destroy of a bad host failed (kept);
# 1 anything else (kept). provision.sh writes the KEPT marker for 4/6/7/1 (review 2026-10-28).
set -eu
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai ssh openssl python3
ID=${1:?instance id}
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd)
KEY=$(cat ~/.config/vexorium/vllm_api_key)
MODEL_REPO=wtdcode/GLM-5.3-Flash-AWQ-W4A16
MODEL_REV=abd7b07719111f137e1de8a0c1b7e01c11b74d1a
drop() {   # bad host: destroy (verified) and exit with the bad-host code; a failed destroy is exit 7 (the instance still bills)
  local code=$1; shift; echo "BAD HOST: $*; destroying instance $ID"
  if CONFIRM=yes "$HERE/destroy.sh" "$ID"; then exit "$code"; else echo "destroy of $ID FAILED: kept, still billing"; exit 7; fi
}
# the port map appears only once the instance is running: wait for it (up to 20 min) instead of failing on the first read
echo "[0/5] waiting for the instance to come up and publish its port map"
for i in $(seq 1 80); do
  J=$(vastai show instance "$ID" --raw 2>/dev/null)
  PORT=$(echo "$J" | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d["ports"]["22/tcp"][0]["HostPort"])' 2>/dev/null) && break
  ST=$(echo "$J" | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d.get("actual_status"), (d.get("status_msg") or "")[:60])' 2>/dev/null)
  echo "  $(date +%H:%M:%S) status=$ST"
  # 2026-10-28 (instance 58149019): a host whose docker cannot create the container sits in status=created forever ("OCI runtime create
  # failed"); that is a bad host, not a slow one: drop it after CREATED_MAX_S (default 300 s) of that error
  case "$ST" in *"OCI runtime"*|*"failed to create"*) CREATED_T=${CREATED_T:-$(date +%s)}; [ $(( $(date +%s) - CREATED_T )) -ge "${CREATED_MAX_S:-300}" ] && drop 3 "container never created on the host (${ST:0:60})";; esac
  sleep 15; [ "$i" = 80 ] && { echo "instance never published a port map"; exit 1; }
done
HOST=$(echo "$J" | python3 -c 'import json,sys; print(json.load(sys.stdin)["public_ipaddr"])')   # direct address, not the shared sshN.vast.ai proxy
# vast reuses ip:port across rentals of one machine (153016 was rented twice): a stale host key makes every login fail, which this
# script reads as "our provisioning bug" (exit 4, instance kept). Once per instance id, forget the address's old key (review 2026-10-28).
if [ ! -e "$ROOT/probe/a100-known-hosts-$ID" ]; then ssh-keygen -R "[$HOST]:$PORT" > /dev/null 2>&1 || true; echo "$HOST:$PORT" > "$ROOT/probe/a100-known-hosts-$ID"; fi
SSH="ssh -i $HOME/.ssh/id_ed25519 -o StrictHostKeyChecking=accept-new -o BatchMode=yes -o ConnectTimeout=20 -o ServerAliveInterval=30 -p $PORT root@$HOST"
# Drop bad hosts early (operator 2026-10-07: "we should drop it immediately if it's not ssh reachable, not wait a long time; the
# principle is to drop the bad instance as early as possible unless our provision script has a bug"):
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
    drop 3 "ssh port not reachable ${SSH_DEADLINE_S}s after running"
  fi
  sleep 10
done
echo "[2/5] host check"
# the verdict of onstart.sh must be READ, not lost behind a pipe (review 2026-10-28: the remote `exit 2` was the first command of a
# pipeline whose status was grep's, so an occupied host went on to the 190 GB download)
HC=$($SSH 'cat /workspace/ONSTART_OK 2>/dev/null; if [ -e /workspace/BAD_HOST ]; then echo BAD_HOST; cat /workspace/BAD_HOST; fi; nvidia-smi --query-gpu=index,name,memory.used,memory.total --format=csv,noheader; df -h /workspace | tail -n 1' 2>/dev/null | grep -v "Welcome\|Have fun" || true)
echo "$HC"
grep -q "^BAD_HOST" <<< "$HC" && drop 3 "GPUs already occupied by another tenant (onstart.sh BAD_HOST)"
grep -q "^onstart:" <<< "$HC" || echo "  WARNING: no ONSTART_OK yet (onstart.sh still running or not run); continuing"
# nvtop is part of the provision AND a cheap end-to-end health probe (operator 2026-10-07: "if it's very slow and time out for the
# provision, just destroy it and ask for new instance"). Runs before the 190 GB download so a bad host costs minutes, not an hour.
#   timeout (apt update+install not done within APT_DEADLINE_S) -> bad host: destroy, exit 5 (provision.sh rents a replacement);
#   fast apt error (lock, missing package) -> not a slowness signal: warn and continue.
APT_DEADLINE_S=${APT_DEADLINE_S:-240}
echo "  installing nvtop (deadline ${APT_DEADLINE_S}s; slow apt = bad host)"
T0=$(date +%s); set +e
timeout $((APT_DEADLINE_S + 60)) $SSH "command -v nvtop >/dev/null && exit 0; export DEBIAN_FRONTEND=noninteractive; timeout $APT_DEADLINE_S bash -c 'apt-get -o DPkg::Lock::Timeout=60 update -qq >/dev/null 2>&1 && apt-get -o DPkg::Lock::Timeout=60 install -y -qq nvtop >/dev/null 2>&1'" >/dev/null 2>&1
RC=$?; set -e
echo "  nvtop step: rc=$RC after $(( $(date +%s) - T0 ))s"
if [ "$RC" = 124 ]; then
  drop 5 "apt update+install nvtop not done in ${APT_DEADLINE_S}s"
elif [ "$RC" != 0 ]; then echo "  WARNING: nvtop install failed fast (rc=$RC); not a slowness signal, continuing"; fi
echo "[3/5] installing /workspace/env, /workspace/run_vllm.sh and the TLS pair (pinned self-signed cert for the public port)"
IP=$(echo "$J" | python3 -c 'import json,sys; print(json.load(sys.stdin)["public_ipaddr"])')
APIPORT=$(echo "$J" | python3 -c 'import json,sys; print(json.load(sys.stdin)["ports"]["8000/tcp"][0]["HostPort"])')
TLSD=$HOME/.config/vexorium/vllm_tls; mkdir -p "$TLSD"; chmod 700 "$TLSD"
# Reuse the pair when the cert is younger than 25 days and already names this IP (review 2026-10-28, finding 16: a re-run after an
# outbid rotated the pair under running sessions, which then failed every handshake for the rest of their connect budget).
REUSE=0
if [ -f "$TLSD/cert.pem" ] && [ -f "$TLSD/key.pem" ] && [ "$(( ( $(date +%s) - $(stat -c %Y "$TLSD/cert.pem") ) / 86400 ))" -lt 25 ] \
   && openssl x509 -in "$TLSD/cert.pem" -noout -text 2>/dev/null | grep -q "IP Address:$IP\b" \
   && [ "$($SSH 'sha256sum /workspace/tls/cert.pem 2>/dev/null | cut -c1-16' 2>/dev/null | grep -v "Welcome\|Have fun" | tail -n 1)" = "$(sha256sum "$TLSD/cert.pem" | cut -c1-16)" ]; then
  REUSE=1; echo "  TLS pair reused (cert on the instance matches; the running server keeps serving it)"
fi
if [ "$REUSE" = 0 ]; then
  # a re-run after an outbid (2026-10-09 review): on resume vast ran onstart.sh, which started the server on the OLD TLS pair; this step makes
  # a new pair, so stop that server first and let step 5 start it on the new one (else the pinned check never passes and READY never comes)
  # pkill returns at once; the engine processes (VLLM::EngineCore, VLLM::Worker_TP*) exit only after the API server, and while they hold GPU
  # memory a new server fails "Free memory ... less than desired" (review 2026-10-09): wait for them, then force
  $SSH 'pkill -f "[r]un_vllm.sh"; pkill -f "[v]llm serve"; for i in $(seq 1 30); do pgrep -f "[v]llm serve|[V]LLM::" > /dev/null || break; sleep 2; done
        pkill -9 -f "[v]llm serve|[V]LLM::"; rm -f /workspace/READY; true' 2>/dev/null
  openssl req -x509 -newkey ec -pkeyopt ec_paramgen_curve:P-256 -nodes -days 30 -subj "/CN=lra-a100" -addext "subjectAltName=DNS:lra-a100,IP:$IP" -keyout "$TLSD/key.pem" -out "$TLSD/cert.pem" 2>/dev/null
  chmod 600 "$TLSD/key.pem"
  $SSH 'mkdir -p /workspace/tls' 2>/dev/null
  $SSH 'cat > /workspace/tls/cert.pem' < "$TLSD/cert.pem" 2>/dev/null
  $SSH 'cat > /workspace/tls/key.pem && chmod 600 /workspace/tls/key.pem' < "$TLSD/key.pem" 2>/dev/null
fi
printf 'VLLM_API_KEY=%s\nMODEL_REPO=%s\nMODEL_REV=%s\n' "$KEY" "$MODEL_REPO" "$MODEL_REV" | $SSH 'cat > /workspace/env && chmod 600 /workspace/env' 2>/dev/null
# the on-instance endpoint (infra/vast/endpoint.sh) reads the key from /root/.config/vexorium/vllm_api_key (review 2026-10-28, finding 5)
$SSH 'mkdir -p /root/.config/vexorium && chmod 700 /root/.config/vexorium && sed -n "s/^VLLM_API_KEY=//p" /workspace/env > /root/.config/vexorium/vllm_api_key && chmod 600 /root/.config/vexorium/vllm_api_key' 2>/dev/null
$SSH 'cat > /workspace/run_vllm.sh && chmod +x /workspace/run_vllm.sh' < "$HERE/run_vllm.sh" 2>/dev/null
if [ "${SKIP_MODEL:-0}" = 1 ]; then   # LeanPool-only rental (2026-10-28, a 309 GB box: the model does not fit; no server is started)
  echo "[4/5] checkpoint download SKIPPED (SKIP_MODEL=1); [5/5] no server"; echo "server ready (SKIP_MODEL=1: no model, no server)"; exit 0
fi
echo "[4/5] checkpoint download (190.8 GB, resumable; deadline ${DL_DEADLINE_S:-5400}s; rate checked after ${DL_RATE_AFTER_S:-300}s, drop below ${DL_MIN_MBS:-50} MB/s)"
# Detached on the instance, polled from here (review 2026-10-28, finding 7: the old pipeline had no deadline and its status was grep's):
# the rate 5 min in (du delta) drops a slow host (exit 5); a failure or the deadline is exit 6 and the server is NOT started.
$SSH "export HF_HOME=/workspace/hf HF_HUB_ENABLE_HF_TRANSFER=1; rm -f /workspace/hf_download.rc
      setsid nohup bash -c '(hf download $MODEL_REPO --revision $MODEL_REV || huggingface-cli download $MODEL_REPO --revision $MODEL_REV) > /workspace/hf_download.log 2>&1; echo \$? > /workspace/hf_download.rc' > /dev/null 2>&1 < /dev/null &" 2>/dev/null
T0=$(date +%s); B0=$($SSH 'du -sb /workspace/hf 2>/dev/null | cut -f1' 2>/dev/null | grep -E '^[0-9]+$' || echo 0); RATE_CHECKED=0; DLRC=""
while :; do
  sleep "${DL_POLL_S:-30}"
  NOW=$(date +%s); EL=$((NOW - T0))
  OUT=$($SSH 'echo rc=$(cat /workspace/hf_download.rc 2>/dev/null); echo bytes=$(du -sb /workspace/hf 2>/dev/null | cut -f1)' 2>/dev/null | grep -v "Welcome\|Have fun" || true)
  DLRC=$(sed -n 's/^rc=//p' <<< "$OUT"); B1=$(sed -n 's/^bytes=//p' <<< "$OUT"); [[ "$B1" =~ ^[0-9]+$ ]] || B1=$B0
  echo "  [$(date +%H:%M:%S)] ${EL}s: $(( B1 / 1000000000 )) GB on disk ($(( (B1 - B0) / 1000000 / (EL > 0 ? EL : 1) )) MB/s since start)"
  [ -n "$DLRC" ] && break
  if [ "$RATE_CHECKED" = 0 ] && [ "$EL" -ge "${DL_RATE_AFTER_S:-300}" ]; then
    RATE_CHECKED=1; MBS=$(( (B1 - B0) / 1000000 / EL ))
    [ "$MBS" -lt "${DL_MIN_MBS:-50}" ] && [ "$B1" -lt 190000000000 ] && { $SSH 'pkill -f "[h]f download|[h]uggingface-cli download"; true' 2>/dev/null; drop 5 "checkpoint download at $MBS MB/s after ${EL}s (minimum ${DL_MIN_MBS:-50})"; }
  fi
  [ "$EL" -ge "${DL_DEADLINE_S:-5400}" ] && { $SSH 'pkill -f "[h]f download|[h]uggingface-cli download"; true' 2>/dev/null; echo "download not finished in ${EL}s: server NOT started"; exit 6; }
done
$SSH 'tail -n 3 /workspace/hf_download.log; du -sh /workspace/hf' 2>/dev/null | grep -v "Welcome\|Have fun" || true
[ "$DLRC" = 0 ] || { echo "download FAILED (rc $DLRC; /workspace/hf_download.log on the instance): server NOT started"; exit 6; }
# 2026-10-31 (docs/a100_throughput_60.md section 6): the recipe's +36% decode needs vLLM's custom all-reduce, which needs NVLink between
# the 4 GPUs (A100 SXM4). On a PCIe box vLLM silently falls back to NCCL: the run works but is ~25% slower. Never fatal, always loud.
nvlink_check() {
  local T C
  T=$($SSH 'nvidia-smi topo -m 2>/dev/null | grep -E "^GPU[0-3]" | head -4' 2>/dev/null | grep -v "Welcome\|Have fun")
  C=$($SSH 'grep -a "all-reduce backends" /workspace/vllm.log | grep -m1 "tp:0"' 2>/dev/null | grep -o "Using \[[^]]*\]")
  if echo "$T" | grep -q "NV[0-9]" && echo "$C" | grep -q "CUSTOM"; then echo "NVLink OK: GPUs linked ($(echo "$T" | grep -o 'NV[0-9]*' | sort -u | tr '\n' ' ')), tp all-reduce $C"
  else echo "WARNING NO-NVLINK: topo [$(echo "$T" | tr '\n' ' ' | cut -c1-160)], tp all-reduce [$C]: expect ~25% slower decode; rent an A100 SXM4 box"; fi
}
echo "[5/5] starting the server (log: /workspace/vllm.log on the instance)"
# fully detach (setsid + stdin from /dev/null), otherwise the ssh session never returns while the server runs
$SSH 'setsid nohup /workspace/run_vllm.sh > /workspace/run_vllm.out 2>&1 < /dev/null & sleep 3; cat /workspace/run_vllm.out' 2>/dev/null | grep -v "Welcome\|Have fun" || true
# readiness = infra/vast/server_up.sh (real path: vast record, TCP, pinned-TLS /v1/models, a real 2-token completion), not a log line
for i in $(seq 1 80); do
  V=$("$HERE/server_up.sh" "$ID" 2>&1) && { echo "[$(date +%H:%M:%S)] $V"; echo "server ready"; nvlink_check; exit 0; }
  echo "[$(date +%H:%M:%S)] $V"
  case "$V" in *process=dead*|*Traceback*|*"Engine core initialization failed"*|*OutOfMemory*) echo "server failed; read /workspace/vllm.log"; exit 1;; esac
  sleep 30
done
echo "not ready after 40 min"; exit 1
