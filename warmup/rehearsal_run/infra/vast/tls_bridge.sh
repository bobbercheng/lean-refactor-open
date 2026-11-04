#!/usr/bin/env bash
# Self-healing local bridge 127.0.0.1:8000 -> https://<instance public ip>:<mapped 8000 port>. Replaces the SSH tunnel for good.
#   Usage: infra/vast/tls_bridge.sh <vast instance id>
# Design (operator 2026-10-06: "have error-resistant design for critical components in the beginning"):
#   * no long-lived multiplexed channel: socat forks a fresh TLS connection per client connection, verified against the pinned
#     self-signed certificate (~/.config/vexorium/vllm_tls/cert.pem, CN lra-a100); the bearer key travels inside TLS;
#   * the health probe exercises the REAL path: a ~200 KB POST /tokenize through the bridge every 60 s (the SSH tunnel died on
#     large bodies while tiny GET /v1/models checks kept passing); tokenize costs no GPU time;
#   * on 3 consecutive probe failures the instance address is re-resolved from vastai (a pre-emption resume changes the mapped
#     ports) and socat is restarted; forked children serving in-flight requests are left alone;
#   * the last known address is cached in probe/a100-bridge.addr so the bridge comes up even when the vastai API is down.
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai socat curl python3
ID=${1:?vast instance id}
CA=$HOME/.config/vexorium/vllm_tls/cert.pem
KEY=$(cat ~/.config/vexorium/vllm_api_key)
ADDR_CACHE=probe/a100-bridge.$ID.addr   # per instance: a cache from an earlier rental must never be used
PROBE=$(mktemp); trap 'rm -f "$PROBE"' EXIT; python3 -c 'import json; print(json.dumps({"model":"glm-5.3-flash","prompt":"theorem t : 1 + 1 = 2 := by norm_num\n"*5000}))' > "$PROBE"
log() { echo "[$(date -u +%H:%M:%S)] $*"; }
resolve() {  # prints "ip port"; falls back to the cache
  local r; r=$(timeout 60 vastai show instance "$ID" --raw 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d["public_ipaddr"], d["ports"]["8000/tcp"][0]["HostPort"])' 2>/dev/null)
  if [ -n "$r" ]; then echo "$r" > "$ADDR_CACHE"; echo "$r"; else cat "$ADDR_CACHE" 2>/dev/null; fi
}
start_socat() {
  # outbound TCP: TCP_USER_TIMEOUT 60 s (setsockopt 6:18 = IPPROTO_TCP:TCP_USER_TIMEOUT, ms) aborts a flow whose data goes
  # unacknowledged for 60 s, and keepalives catch a dead peer while a long generation is awaited; without these a single
  # stuck flow sat with 213 KB in Send-Q for 20+ min on 2026-10-07 01:15 while the other three flows (and the probe) were fine.
  socat -d TCP-LISTEN:8000,bind=127.0.0.1,reuseaddr,fork \
    "OPENSSL:$IP:$PORT,cafile=$CA,verify=1,commonname=lra-a100,keepalive,keepidle=30,keepintvl=10,keepcnt=3,setsockopt-int=6:18:60000" >> probe/a100-tls-bridge-socat.log 2>&1 &
  SOCAT=$!; log "socat bridge 127.0.0.1:8000 -> TLS $IP:$PORT (pid $SOCAT)"
}
probe_ok() { curl -sf --max-time 60 -o /dev/null -H "Authorization: Bearer $KEY" -H "Content-Type: application/json" --data-binary @"$PROBE" http://127.0.0.1:8000/tokenize; }
read -r IP PORT < <(resolve); [ -z "${IP:-}" ] && { log "cannot resolve instance $ID address"; exit 1; }
start_socat; FAILS=0; STUCK_PREV=""
while true; do
  sleep 60
  if ! kill -0 "$SOCAT" 2>/dev/null; then log "socat exited"; FAILS=3; fi
  # stuck-flow sweep: a child whose outbound Send-Q stays > 64 KB across two checks (60 s) is holding a dead flow; kill it
  # so the client gets a reset and retries at once instead of waiting out its request timeout.
  STUCK_NOW=$(ss -tnp 2>/dev/null | awk -v ip="$IP" '$5 ~ ip && $3 > 65536' | grep -o 'pid=[0-9]*' | cut -d= -f2 | sort)
  for c in $STUCK_NOW; do if echo "$STUCK_PREV" | grep -qx "$c"; then log "stuck flow in socat child $c (Send-Q > 64 KB for 60 s); killing it"; kill "$c" 2>/dev/null; fi; done
  STUCK_PREV=$STUCK_NOW
  if probe_ok; then FAILS=0; continue; fi
  FAILS=$((FAILS+1)); log "real-path probe failed ($FAILS/3)"
  if [ "$FAILS" -ge 3 ]; then
    read -r NIP NPORT < <(resolve); [ -n "${NIP:-}" ] && { [ "$NIP:$NPORT" != "$IP:$PORT" ] && log "address changed: $IP:$PORT -> $NIP:$NPORT"; IP=$NIP; PORT=$NPORT; }
    kill "$SOCAT" 2>/dev/null; sleep 2; start_socat; FAILS=0
  fi
done
