#!/usr/bin/env bash
# Minimal on-start script for the vast.ai A100 POC instance (vast runs it inside the container on every start, incl. after a
# bid pre-emption resume). It does only three things, all cheap and all before any money goes into downloads:
#   1. make SSH usable (one host injected /root/.ssh/authorized_keys with bad modes and sshd refused every key);
#   2. refuse hosts whose GPUs are already occupied (/workspace/BAD_HOST; one host had another tenant's 67-70 GB per GPU);
#   3. if the SSH-driven bootstrap (infra/vast/bootstrap.sh) already installed /workspace/run_vllm.sh, relaunch the server —
#      this is what brings the model back after a pre-emption resume without anyone watching.
# Everything else (checkpoint download, server start, readiness) is done by bootstrap.sh over SSH, where it is observable.
set -u
fix_ssh() { mkdir -p /root/.ssh; chown -R root:root /root/.ssh; chmod 700 /root/.ssh; [ -e /root/.ssh/authorized_keys ] && chmod 600 /root/.ssh/authorized_keys; return 0; }
fix_ssh; (for i in $(seq 1 24); do sleep 5; fix_ssh; done) >/dev/null 2>&1 &
mkdir -p /workspace
nvidia-smi --query-gpu=name,memory.total,driver_version --format=csv > /workspace/gpus.txt 2>&1 || true
BAD=0
while read -r used; do [ "${used:-0}" -gt 12000 ] && BAD=1; done < <(nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits 2>/dev/null)
if [ "$BAD" = 1 ]; then nvidia-smi --query-gpu=index,memory.used,memory.total --format=csv > /workspace/BAD_HOST 2>&1; echo "BAD_HOST: GPUs already occupied"; exit 2; fi
rm -f /workspace/BAD_HOST
echo "onstart: ssh fixed, GPUs free ($(date -u +%H:%M:%S))" > /workspace/ONSTART_OK
if [ -x /workspace/run_vllm.sh ]; then echo "onstart: relaunching the installed server"; nohup /workspace/run_vllm.sh > /workspace/run_vllm.out 2>&1 & fi
exit 0
