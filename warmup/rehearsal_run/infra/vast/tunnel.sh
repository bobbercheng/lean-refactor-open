#!/usr/bin/env bash
# SSH tunnel from the GB10 to the instance's vLLM port: localhost:8000 -> instance:8000. Runs in the foreground; Ctrl-C closes it.
# Usage: infra/vast/tunnel.sh <instance_id>
set -eu
ID=${1:?instance id}
URL=$(vastai ssh-url "$ID")             # ssh://root@host:port
HOST=$(echo "$URL" | sed -E 's#ssh://[^@]+@([^:]+):.*#\1#'); PORT=$(echo "$URL" | sed -E 's#.*:([0-9]+)$#\1#')
echo "tunnel to $HOST:$PORT (local 8000 -> remote 8000); check: curl -s localhost:8000/v1/models"
exec ssh -o StrictHostKeyChecking=accept-new -o ServerAliveInterval=30 -N -L 8000:localhost:8000 -p "$PORT" "root@$HOST"
