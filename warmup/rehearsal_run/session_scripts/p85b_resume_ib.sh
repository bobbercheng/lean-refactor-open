#!/usr/bin/env bash
# GB10 (autonomy rule: box 58520692's host machine went OFFLINE at 12:35 UTC Oct 31, unreachable by SSH / vast): resume p85b on the
# replacement 58533606 (Iowa m153537, same host). Chain: wait SSH -> prep (export 528c9694 + tools + 15 envs from Kaggle) -> restore p85b's
# state (GB10 pull 12:32 merged with the GCS snapshot 12:33: out-p85b, lra-run-p85b incl. RUN_CMD/relaunch.sh, the sessions' run dirs)
# -> aux (GCS key, status writer, sidecar a100-p85b) -> relaunch.sh (waits for vLLM READY, preflight, RUN_CMD unchanged: same job clock,
# rows resume from their banked bests, cut sessions get a new k) -> GB10 side (tunnel file, -ia watch/alarm stopped, -ib watch/alarm via
# p85b_arm_gb10.sh, bridge + health re-pointed) -> scale test re-armed. Bounded waits; log probe/a100-reh-p85b/resume-ib.log.
set -u
cd /home/bobber/source/lra-a100; . infra/vast/common.sh
export XDG_RUNTIME_DIR=/run/user/$(id -u) DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/$(id -u)/bus
S="<scratchpad>"
ID=58533606; R=probe/a100-reh-p85b; L=$R/resume-ib.log; log() { echo "[$(date -u +%H:%M:%S)] $*" >> $L; }
O="-o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o ConnectTimeout=20 -o LogLevel=ERROR"
end=$(( $(date +%s) + 1800 ))
until read IP P <<< "$(vastai show instance $ID --raw 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); print(d["public_ipaddr"], d["ports"]["22/tcp"][0]["HostPort"])' 2>/dev/null)" && [ -n "${P:-}" ] && timeout 30 ssh $O -p $P root@$IP true 2>/dev/null; do
  [ $(date +%s) -gt $end ] && { log "SSH never came up"; exit 1; }; sleep 20; done
echo "$IP $P" > $S/ib_ssh.txt; echo "$IP $P" > probe/a100-tunnels/$ID; log "SSH up $IP:$P (tunnel file written)"
TAG=p85b LRA_FAKE_VAST_BIN= bash infra/vast/rehearsal.sh prep $ID >> $R/prep-ib.out 2>&1
grep -q "PREP DONE on $ID" $R/prep-ib.out || { log "prep failed: $(tail -2 $R/prep-ib.out | tr '\n' ' ')"; exit 1; }
log "prep done"
ssh $O -p $P root@$IP 'mkdir -p /workspace/out-p85b /workspace/lra-run-p85b /workspace/lra/probe/runs /workspace/scale /root/.config/vexorium /workspace/infra/sync && chmod 700 /root/.config/vexorium' 2>/dev/null
rsync -az -e "ssh $O -p $P" $R/restore-ib/out-p85b/ root@$IP:/workspace/out-p85b/ && rsync -az -e "ssh $O -p $P" $R/restore-ib/lra-run-p85b/ root@$IP:/workspace/lra-run-p85b/ \
  && rsync -az -e "ssh $O -p $P" $R/restore-ib/runs/ root@$IP:/workspace/lra/probe/runs/ || { log "state rsync failed"; exit 1; }
scp -q $O -P $P ~/.config/vexorium/vllm_api_key root@$IP:/root/.config/vexorium/vllm_api_key
scp -q $O -P $P ~/.config/vexorium/gcs_sync_key.json root@$IP:/root/.config/vexorium/gcs_sync_key.json
scp -q $O -P $P probe/a100-alarm/tunnel_watch_host.sh root@$IP:/workspace/tunnel_watch_host.sh; scp -q $O -P $P infra/sync/sidecar.py root@$IP:/workspace/infra/sync/sidecar.py
[ -s probe/a100-ntfy-topic ] && scp -q $O -P $P probe/a100-ntfy-topic root@$IP:/workspace/ntfy_topic
scp -q $O -P $P infra/vast/package_stop_host.sh infra/vast/scale_p85b_host.sh infra/vast/vllm_recipe_host.sh $S/aux_p85b_host.sh root@$IP:/workspace/
ssh $O -p $P root@$IP 'chmod 600 /root/.config/vexorium/*; echo "{\"note\": \"restored on 58533606 after 58520692 went offline at 12:35 UTC\"}" > /workspace/lra-run-p85b/RESTORED.json; echo "work $(ls /workspace/out-p85b/work | wc -l) runs $(ls /workspace/lra/probe/runs | wc -l)"' 2>/dev/null >> $L
log "state restored (out-p85b, lra-run-p85b, runs)"
ssh $O -p $P root@$IP 'setsid nohup bash /workspace/aux_p85b_host.sh > /workspace/aux_p85b.out 2>&1 < /dev/null &' 2>/dev/null; log "aux started (detached)"
end=$(( $(date +%s) + 3600 )); until grep -qE "server ready|not ready|failed" probe/a100-bootstrap-$ID.log || [ $(date +%s) -gt $end ]; do sleep 20; done
log "bootstrap: $(tail -1 probe/a100-bootstrap-$ID.log | cut -c1-140)"
grep -q "server ready" probe/a100-bootstrap-$ID.log || { log "vLLM not ready: NOT relaunched"; exit 1; }
ssh $O -p $P root@$IP 'cp -n /workspace/run_vllm.sh /workspace/run_vllm_std.sh 2>/dev/null; cd /workspace/lra && RUN_DIR=/workspace/lra-run-p85b setsid nohup bash /workspace/lra-run-p85b/relaunch.sh >> /workspace/lra-run-p85b/relaunch.out 2>&1 < /dev/null &' 2>/dev/null
end=$(( $(date +%s) + 600 )); until timeout 30 ssh $O -p $P root@$IP 'pgrep -f "[o]pen_package.py run .*--tag p85b"' > /dev/null 2>&1 || [ $(date +%s) -gt $end ]; do sleep 15; done
timeout 30 ssh $O -p $P root@$IP 'pgrep -af "[o]pen_package.py run" | cut -c1-120; tail -3 /workspace/lra-run-p85b/relaunch.out; tail -4 /workspace/lra-run-p85b/driver.log' >> $L 2>&1
timeout 30 ssh $O -p $P root@$IP 'pgrep -f "[o]pen_package.py run .*--tag p85b"' > /dev/null 2>&1 || { log "driver NOT running after relaunch"; exit 1; }
log "p85b DRIVER RUNNING on $ID"
systemctl --user stop lra-a100-watch-p85b-ia lra-a100-alarm-p85b-ia 2>/dev/null; log "stopped -ia watch/alarm (58520692 offline; its sentry/keeper/guard stay until it is destroyed)"
systemctl --user reset-failed lra-a100-p85b-arm-ib 2>/dev/null
systemd-run --user --unit lra-a100-p85b-arm-ib --working-directory=$PWD -E PATH -E HOME -E LRA_FAKE_VAST_BIN= -E LRA_UNIT_SUFFIX=-ib -E "ARM_UNTIL=2026-11-01 01:00 UTC" \
  -p StandardOutput=append:$PWD/$R/arm-ib.out -p StandardError=append:$PWD/$R/arm-ib.out bash infra/vast/p85b_arm_gb10.sh $ID && log "GB10 arm started (suffix -ib)"
systemctl --user stop lra-bridge lra-health 2>/dev/null; systemctl --user reset-failed lra-bridge lra-health 2>/dev/null
systemd-run --user --unit lra-bridge --working-directory=$PWD -E PATH -E HOME bash -c "exec infra/vast/tls_bridge.sh $ID >> probe/a100-tls-bridge.log 2>&1" && log "bridge -> $ID"
systemd-run --user --unit lra-health --working-directory=$PWD -E PATH -E HOME bash -c "exec python3 -u infra/vast/health.py $ID --interval 60 --no-bridge >> probe/a100-health.log 2>&1" && log "health -> $ID"
echo $ID > probe/a100-instance-id
mv probe/a100-hold-keepofficial-58520692 probe/a100-hold-keepofficial-$ID 2>/dev/null && log "keep hold -> $ID"
ssh $O -p $P root@$IP 'cd /workspace && setsid nohup bash /workspace/scale_p85b_host.sh > /workspace/scale_p85b.out 2>&1 < /dev/null &' 2>/dev/null; sleep 5
log "scale test: $(timeout 30 ssh $O -p $P root@$IP 'tail -1 /workspace/scale/scale.log' 2>/dev/null)"
log "aux: $(timeout 30 ssh $O -p $P root@$IP 'tail -3 /workspace/aux_p85b.out | tr "\n" " "' 2>/dev/null)"
log "resume chain done"
