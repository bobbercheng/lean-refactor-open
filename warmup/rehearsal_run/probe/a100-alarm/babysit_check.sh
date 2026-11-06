#!/usr/bin/env bash
# One babysit snapshot of a package run on the A100 (2026-10-30): health, errors, per-session turns/checks/best and prompt size vs the
# 524,288-token context window, finished sessions. usage: babysit_check.sh TAG [HOST PORT]
TAG=${1:?tag}; H=${2:-bore.vexorium.net}; P=${3:?bore port}
timeout 150 ssh -i ~/.ssh/id_ed25519 -o BatchMode=yes -o ConnectTimeout=20 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR -p "$P" root@"$H" "TAG=$TAG bash -s" <<'REMOTE'
L=/workspace/lra-run-$TAG/driver.log; O=/workspace/out-$TAG/logs
date -u +%H:%M
echo "driver $(pgrep -c -f '[o]pen_package.py run') agents $(pgrep -c -f '[h]arness/agent.py') gpu $(nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits | tr '\n' ,)"
echo "tool errors $(cat $O/*.log 2>/dev/null | grep -c 'TOOL ERROR') api/connect $(cat $O/*.log 2>/dev/null | grep -ciE 'api_error|connect fail|refused|rate.?limit') forbidden $(cat $O/*.log 2>/dev/null | grep -ci 'forbidden') context_full $(cat $O/*.log 2>/dev/null | grep -ci 'context_full\|context window')"
grep -E "session [0-9]+ done" $L | cut -c1-110
for d in /workspace/lra/probe/runs/$TAG-s*-k*; do f=$(ls $d/trajectories/*.jsonl 2>/dev/null | head -1); [ -n "$f" ] || continue
python3 - "$f" "$(basename $d)" <<'PY'
import json, sys
t = [json.loads(l) for l in open(sys.argv[1]) if '"type": "turn"' in l]
if t:
    last = t[-1]; tin = int(last.get("input_tokens") or 0)
    print(f"{sys.argv[2]} turns {len(t)} checks {last.get('checks_so_far')} best {last.get('best_so_far')} prompt {tin // 1000}k")
PY
done
REMOTE
