#!/usr/bin/env bash
# Keep the localhost:8000 -> instance:8000 SSH tunnel alive and unstuck.
# Usage: infra/vast/tunnel_keepalive.sh <ssh_host> <ssh_port> [run_dir_to_watch]
#   Use the instance's DIRECT ssh address (public_ipaddr + 22/tcp HostPort), not the shared sshN.vast.ai proxy: on
#   2026-10-06 the proxy tunnel silently stopped forwarding ~0.5 MB request bodies (100k-token contexts) at 22:15 while small
#   health checks kept passing; the agent's sockets sat in CLOSE-WAIT / full Send-Q and the server had 0 requests running.
# Every 30 s: (a) health check fails and no tunnel process -> start one; (b) stall: the watched run's newest trajectory is
# older than 15 min AND the server reports 0 running requests -> kill and restart the tunnel (stuck client sockets then error
# out and the harness retries).
set -u
H=${1:?ssh host}; P=${2:?ssh port}; RUN_DIR=${3:-}
KEY=$(cat ~/.config/vexorium/vllm_api_key)
start_tunnel() {
  nohup ssh -i ~/.ssh/id_ed25519 -o StrictHostKeyChecking=accept-new -o ServerAliveInterval=15 -o ServerAliveCountMax=4 \
      -o ExitOnForwardFailure=yes -N -L 127.0.0.1:8000:localhost:8000 -p "$P" "root@$H" >> probe/a100-tunnel.log 2>&1 &
  echo "[$(date -u +%H:%M:%S)] tunnel started (pid $!) to $H:$P"
}
tunnel_pids() { pgrep -f "ssh .*-L 127.0.0.1:8000:localhost:8000 -p $P root@$H"; }
LAST_RESTART=$(date +%s)
while true; do
  if ! curl -sf --max-time 10 -H "Authorization: Bearer $KEY" localhost:8000/v1/models >/dev/null 2>&1; then
    if [ -z "$(tunnel_pids)" ]; then echo "[$(date -u +%H:%M:%S)] tunnel down"; start_tunnel; LAST_RESTART=$(date +%s); fi
  elif [ -n "$RUN_DIR" ] && [ -d "$RUN_DIR/trajectories" ]; then
    NEWEST=$(find "$RUN_DIR/trajectories" -type f -printf '%T@\n' 2>/dev/null | sort -n | tail -n 1 | cut -d. -f1)
    AGE=$(( $(date +%s) - ${NEWEST:-$(date +%s)} ))
    RUNNING=$(curl -s --max-time 10 -H "Authorization: Bearer $KEY" localhost:8000/metrics | awk '/^vllm:num_requests_running/{print int($2)}' | head -n 1)
    # cooldown: a restart cannot make the run write a trajectory instantly (workers may sit in a 5-min retry backoff)
    if [ "$AGE" -gt 900 ] && [ "${RUNNING:-1}" = "0" ] && [ $(( $(date +%s) - LAST_RESTART )) -gt 600 ]; then
      echo "[$(date -u +%H:%M:%S)] stall: no trajectory write for ${AGE}s and 0 requests running; restarting tunnel"
      for p in $(tunnel_pids); do kill "$p"; done; sleep 3; start_tunnel; LAST_RESTART=$(date +%s)
    fi
  fi
  sleep 30
done
