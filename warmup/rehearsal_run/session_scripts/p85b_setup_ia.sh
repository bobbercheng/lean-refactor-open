#!/usr/bin/env bash
# GB10 (autonomy rule, after the 10:05 outbid above the cap): put p85's state (the GB10 pull of 09:58) on the new Iowa box and arm the
# tested p85b launcher there. p85 counts as ended at the outbid; its final is measured on the GB10. Run after `rehearsal.sh prep` (PREP DONE).
set -u
cd /home/bobber/source/lra-a100; . infra/vast/common.sh
ID=$(cat "<scratchpad>/new_box_id.txt")
O="-o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o ConnectTimeout=20 -o LogLevel=ERROR"
read IP P <<< "$(vastai show instance $ID --raw 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d["public_ipaddr"], d["ports"]["22/tcp"][0]["HostPort"])')"
echo "$IP $P" > "<scratchpad>/ia_ssh.txt"
L=probe/a100-reh-p85b/setup_ia.log; log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a $L; }
grep -q "PREP DONE" probe/a100-reh-p85b/prep.out || { log "prep not done"; exit 1; }
ssh $O -p $P root@$IP 'mkdir -p /workspace/out /workspace/lra-run /workspace/scale /root/.config/vexorium' 2>/dev/null
rsync -az -e "ssh $O -p $P" probe/a100-reh-p85/out/work probe/a100-reh-p85/out/agent_sessions.jsonl probe/a100-reh-p85/out/clock.json root@$IP:/workspace/out/ || { log "rsync failed"; exit 1; }
scp -q $O -P $P ~/.config/vexorium/vllm_api_key root@$IP:/root/.config/vexorium/vllm_api_key && ssh $O -p $P root@$IP 'chmod 600 /root/.config/vexorium/vllm_api_key' 2>/dev/null
ssh $O -p $P root@$IP 'bash -s' <<'HOST' 2>&1 | grep -v "^Welcome\|^Have fun" | tee -a $L
set -u
W=/workspace
cat > $W/lra-run/RUN_CMD <<'X'
python3 harness/open_package.py run --rows /workspace/lra-run/rows.jsonl --heartbeats /workspace/lra-run/heartbeats.jsonl --out /workspace/out --tag p85 --base-url https://lra-a100:8000/v1 --api-key-file /root/.config/vexorium/vllm_api_key --api-model glm-5.3-flash --started-at 1793401053 --job-seconds 60560 --workers 12 --max-sessions 4 --end-seconds 7200 --end-pipeline on
X
printf 'RUN_DIR=/workspace/lra-run\nOUT=/workspace/out\nEXPORT_ROOT=/workspace/lra\nLRA_BASE_URL=\nLRA_API_KEY_FILE=\n' > $W/lra-run/RUN_ENV
echo '{"note": "p85 ended by the 10:05 UTC outbid of box 58465316 (bid war above the operator cap); state = the GB10 pull of 09:58; p85 final measured on the GB10", "stored_mean": null, "sources": null}' > $W/out/summary.json
echo "$(date -u -Is) scale test NOT run (moved box after the 10:05 outbid)" > $W/scale/scale.log
cat > $W/p85b.conf <<'X'
END_AT="2026-11-01 04:00 UTC"
ROWS_SET=warmup15
MAX_SESSIONS=6
WORKERS=12
SEED_FROM_EXPORT=0
WAIT_UNTIL="2026-11-01 00:00 UTC"
MIN_JOB_S=14400
X
cp $W/lra/infra/vast/p85b_launch_host.sh $W/lra/infra/vast/package_stop_host.sh $W/ 2>/dev/null
ls $W/out/work | wc -l; ls $W/lra-run/
setsid nohup bash $W/p85b_launch_host.sh > $W/p85b_launch.out 2>&1 < /dev/null &
sleep 3; tail -2 $W/p85b_launch.log 2>/dev/null | cut -c1-200
HOST
log "p85b launcher armed on $ID ($IP:$P)"
