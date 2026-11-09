#!/usr/bin/env bash
# Is the A100 server up? One reliable check used by every script (operator 2026-10-07: "error resistant reliable way to check if
# the server is up"). Walks the real path layer by layer, stops at the first failure and says exactly which layer failed:
#   vast    instance listed as running; ip + mapped API/SSH ports resolved FRESH (never from a cache of another rental)
#   tcp     the mapped API port accepts TCP from here
#   api     GET /v1/models over TLS verified against the pinned cert returns the served model
#   engine  a real 2-token completion succeeds (an API process can answer /v1/models while the engine is dead or still loading)
#   bridge  (only with --bridge) the same completion through the local bridge 127.0.0.1:8000, i.e. the path the harness uses
# On a failure at tcp/api/engine it looks inside over SSH (process alive? READY marker? last error in vllm.log) so the verdict
# is actionable. Output: one line "UP ..." (exit 0) or "DOWN layer=<name>: <reason> [inside: ...]" (exit 1).
# Usage: infra/vast/server_up.sh <instance_id> [--bridge]
set -u
HERE=$(cd "$(dirname "$0")" && pwd); . "$HERE/common.sh"; require vastai curl python3 ssh
ID=${1:?instance id}; BRIDGE=${2:-}
KEY=$(cat ~/.config/vexorium/vllm_api_key); CA=$HOME/.config/vexorium/vllm_tls/cert.pem
SERVED=$(cat "$HERE/../../probe/a100-served-model" 2>/dev/null || echo glm-5.3-flash)   # model trials serve other names (2026-10-08)
BODY='{"model":"'"$SERVED"'","prompt":"1+1=","max_tokens":2,"temperature":0}'
down() { local layer=$1; shift; local why="$*" inside=""
  if [ -n "${SSHP:-}" ] && [ "$layer" != vast ]; then
    inside=$(timeout 40 ssh -i "$HOME/.ssh/id_ed25519" -o BatchMode=yes -o ConnectTimeout=15 -o StrictHostKeyChecking=accept-new -p "$SSHP" "root@$IP" \
      'p=$(pgrep -f "vllm serve" >/dev/null && echo alive || echo dead); r=$([ -e /workspace/READY ] && echo yes || echo no);
       e=$(grep -aE "Traceback|Error|OutOfMemory|Loading safetensors|Capturing|startup complete" /workspace/vllm.log 2>/dev/null | tail -n 1 | cut -c1-120);
       echo "process=$p READY=$r last=[$e]"' 2>/dev/null | grep -v "Welcome\|Have fun" | tail -n 1)
    [ -n "$inside" ] || inside="ssh unreachable"
    inside=" [inside: $inside]"
  fi
  echo "DOWN layer=$layer: $why$inside"; exit 1; }
J=$(timeout 60 vastai show instance "$ID" --raw 2>/dev/null) || down vast "vastai show instance failed"
read -r ST IP APIP SSHP < <(echo "$J" | python3 -c 'import json,sys
d=json.load(sys.stdin); p=d.get("ports") or {}
g=lambda k: (p.get(k) or [{}])[0].get("HostPort","-")
print(d.get("actual_status"), d.get("public_ipaddr") or "-", g("8000/tcp"), g("22/tcp"))' 2>/dev/null) || down vast "unparseable instance record"
[ "${ST:-}" = running ] || down vast "status=${ST:-unknown}"
[ "$APIP" != - ] && [ "$IP" != - ] || down vast "no API port mapped yet"
timeout 8 bash -c "</dev/tcp/$IP/$APIP" 2>/dev/null || down tcp "port $IP:$APIP closed"
M=$(curl -sS --max-time 20 --cacert "$CA" --resolve "lra-a100:$APIP:$IP" -H "Authorization: Bearer $KEY" "https://lra-a100:$APIP/v1/models" 2>&1) \
  || down api "GET /v1/models failed: $(echo "$M" | tail -n 1 | cut -c1-100)"
echo "$M" | grep -q "$SERVED" || down api "model $SERVED not served: $(echo "$M" | cut -c1-100)"
C=$(curl -sS --max-time 90 --cacert "$CA" --resolve "lra-a100:$APIP:$IP" -H "Authorization: Bearer $KEY" -H "Content-Type: application/json" -d "$BODY" "https://lra-a100:$APIP/v1/completions" 2>&1)
if ! echo "$C" | grep -q '"choices"'; then
  # A saturated server (all max-num-seqs slots busy) queues the probe and it times out although the engine is working
  # (2026-10-07 21:04: 16 eval streams, false DOWN). Decide from /metrics: generated-token counter rising = busy, flat = stalled.
  met() { curl -sS --max-time 15 --cacert "$CA" --resolve "lra-a100:$APIP:$IP" -H "Authorization: Bearer $KEY" "https://lra-a100:$APIP/metrics" 2>/dev/null \
          | awk '/^vllm:num_requests_running/{r=$2} /^vllm:num_requests_waiting /{w=$2} /^vllm:num_requests_waiting\{/{if(w=="")w=$2} /^vllm:generation_tokens_total/{g+=$2} END{printf "%d %d %d", r, w, g}'; }
  read -r R1 W1 G1 < <(met); sleep 10; read -r R2 W2 G2 < <(met)
  if [ "${R2:-0}" -gt 0 ] && [ "${G2:-0}" -gt "${G1:-0}" ]; then
    SAT="engine saturated: running $R2, waiting $W2, $(( (G2 - G1) / 10 )) tok/s; probe was queued"
    if [ "$BRIDGE" != --bridge ]; then echo "UP instance=$ID $IP:$APIP (vast, tcp, api ok; $SAT)"; exit 0; fi
  fi
  [ -n "${SAT:-}" ] || down engine "completion failed and no generation progress (running ${R2:-?}, tokens ${G1:-?}->${G2:-?}): $(echo "$C" | tail -n 1 | cut -c1-100)"
fi
if [ "$BRIDGE" = --bridge ] && [ -n "${SAT:-}" ]; then   # saturated: a completion would queue again; prove the bridge path via /metrics
  BM=$(curl -sS --max-time 15 -H "Authorization: Bearer $KEY" http://127.0.0.1:8000/metrics 2>&1 | grep -c "^vllm:generation_tokens_total")
  [ "${BM:-0}" -gt 0 ] || down bridge "server saturated and /metrics not reachable via 127.0.0.1:8000 (systemctl --user status lra-bridge)"
  echo "UP instance=$ID $IP:$APIP (vast, tcp, api ok; $SAT; bridge ok via /metrics)"; exit 0
fi
if [ "$BRIDGE" = --bridge ]; then
  B=$(curl -sS --max-time 90 -H "Authorization: Bearer $KEY" -H "Content-Type: application/json" -d "$BODY" http://127.0.0.1:8000/v1/completions 2>&1)
  if ! echo "$B" | grep -q '"choices"'; then
    # saturated server: the probe queues behind max-num-seqs requests (2026-10-07 21:57 false DOWN). /metrics THROUGH the bridge
    # proves the bridge path; a rising generated-token counter proves the engine is working.
    bm() { curl -sS --max-time 15 -H "Authorization: Bearer $KEY" http://127.0.0.1:8000/metrics 2>/dev/null | awk '/^vllm:num_requests_running/{r=$2} /^vllm:generation_tokens_total/{g+=$2} END{printf "%d %d", r, g}'; }
    read -r BR1 BG1 < <(bm); sleep 10; read -r BR2 BG2 < <(bm)
    if [ "${BR2:-0}" -gt 0 ] && [ "${BG2:-0}" -gt "${BG1:-0}" ]; then
      echo "UP instance=$ID $IP:$APIP (vast, tcp, api, engine ok; bridge ok via /metrics, server saturated: running $BR2, $(( (BG2 - BG1) / 10 )) tok/s; probe was queued)"; exit 0
    fi
    down bridge "server OK directly but not via 127.0.0.1:8000: $(echo "$B" | tail -n 1 | cut -c1-80) (systemctl --user status lra-bridge)"
  fi
fi
echo "UP instance=$ID $IP:$APIP (vast, tcp, api, engine${BRIDGE:+, bridge} ok)"
