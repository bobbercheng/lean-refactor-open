#!/usr/bin/env bash
# ON the Iowa host: gcloud CLI, the status writer and the GCS sidecar for p85b (as aux_host.sh did for p85). The bucket key is deleted before release.
chmod 600 /root/.config/vexorium/gcs_sync_key.json; chmod +x /workspace/tunnel_watch_host.sh
if [ ! -x /opt/google-cloud-sdk/bin/gcloud ]; then (curl -sSfL https://dl.google.com/dl/cloudsdk/channels/rapid/downloads/google-cloud-cli-linux-x86_64.tar.gz | tar -xz -C /opt) > /workspace/setup-gcloud.log 2>&1; fi
/opt/google-cloud-sdk/bin/gcloud --version 2>/dev/null | head -n 1
pgrep -f "[t]unnel_watch_host.sh" > /dev/null || STATUS_ONLY=1 RUN_DIR=/workspace/lra-run-p85b OUT_DIR=/workspace/out-p85b setsid nohup /workspace/tunnel_watch_host.sh > /workspace/tunnel_watch_p85b.log 2>&1 < /dev/null &
pgrep -f "[s]idecar.py --label a100-p85b" > /dev/null || (cd /workspace && PATH=/opt/google-cloud-sdk/bin:$PATH setsid nohup python3 /workspace/infra/sync/sidecar.py --label a100-p85b --key /root/.config/vexorium/gcs_sync_key.json \
  --watch "lra/probe/runs/p85b-*/verified.jsonl" --paths lra/reh/status.json lra-run-p85b out-p85b --snapshot-every 120 > /workspace/sidecar_p85b.log 2>&1 < /dev/null &)
sleep 30
echo "writer $(pgrep -c -f '[t]unnel_watch_host.sh') sidecar $(pgrep -c -f '[s]idecar.py --label a100-p85b')"; tail -n 3 /workspace/sidecar_p85b.log
