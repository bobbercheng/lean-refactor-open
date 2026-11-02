#!/usr/bin/env bash
# ON the A100 box: start the gap6 step test (probe/gap6/gap6_host.py) in the driver's environment (the same exports as p85e_ctl.sh envset).
#   gap6_start.sh [END_ISO]     refuses while a gap6 pid is alive; END_ISO (default 2026-11-01T10:30:00Z) -> /workspace/gap6/END_AT
set -u
W=/workspace; G=$W/gap6
p=$(cat $G/gap6.pid 2>/dev/null); if [ -n "$p" ] && [ -r /proc/$p/cmdline ] && tr '\0' ' ' < /proc/$p/cmdline | grep -q "gap6_host[.]py"; then echo "gap6 already running (pid $p)"; exit 1; fi
cd $W/lra || exit 1
grep -q " lra-a100$" /etc/hosts || { echo "no lra-a100 in /etc/hosts: refusing"; exit 1; }
[ -s $W/tls/ca-bundle.pem ] || { echo "no CA bundle: refusing"; exit 1; }
export LRA_API_KEY_FILE="" LRA_NO_GCS=1 LRA_NO_WANDB=1 RUN_DIR=$W/lra-run-p85b REQUESTS_CA_BUNDLE=$W/tls/ca-bundle.pem \
  EP_URL=https://lra-a100:8000/v1 EP_KEY=/root/.config/vexorium/vllm_api_key LRA_API_MODEL=glm-5.3-flash LRA_AGENT_FLAGS=""
echo "${1:-2026-11-01T10:30:00Z} gap6-end" > $G/END_AT
rm -f $G/STOP
BUDGET_S=${BUDGET_S:-2100} PAIRS=${PAIRS:-3} MAX_TOTAL=${MAX_TOTAL:-14} KV_MAX=${KV_MAX:-0.70} \
  setsid nohup python3 $G/gap6_host.py >> $G/gap6.out 2>&1 < /dev/null &
sleep 5; echo "gap6 started: pid $(cat $G/gap6.pid 2>/dev/null)"; tail -3 $G/gap6.log
