#!/usr/bin/env bash
# onstart variant with an OUTBOUND SSH tunnel (operator 2026-10-30 ~01:08: "make ssh server accessible with tunnel tool, we can also test
# ssh reachable from boot script"). For hosts whose inbound port map never works (UK 151172: direct and sshN.vast.ai proxy both time out).
# 1. start sshd if the image's launcher did not; 2. test port 22 from INSIDE the container; 3. report to a private ntfy.sh topic (no secret on
# the disk; only liveness facts and the tunnel address); 4. bore (github.com/ekzhang/bore v0.5.2) forwards port 22 through bore.pub, the
# address is posted to the topic; key-only SSH as on every host. Then the normal onstart below.
T=${NTFY_TOPIC:-$(cat /workspace/ntfy_topic 2>/dev/null)}   # private push topic: from the env or the box file, never in the repo
note() { curl -fsS -m 20 -d "$*" "https://ntfy.sh/$T" >/dev/null 2>&1 || wget -q -O /dev/null --post-data="$*" "https://ntfy.sh/$T" >/dev/null 2>&1; }
(
  sleep 5
  if ! pgrep -x sshd >/dev/null; then mkdir -p /run/sshd; (service ssh start || /usr/sbin/sshd) >/dev/null 2>&1; fi
  sleep 3
  L22=$(timeout 5 bash -c 'echo > /dev/tcp/127.0.0.1/22' 2>/dev/null && echo open || echo closed)
  note "alive $(hostname) $(date -u +%H:%M:%S) sshd=$(pgrep -c -x sshd) local22=$L22 keys=$(wc -l < /root/.ssh/authorized_keys 2>/dev/null) gpu_used_mib=$(nvidia-smi --query-gpu=memory.used --format=csv,noheader,nounits 2>/dev/null | tr '\n' ,) disk=$(df -h /workspace 2>/dev/null | tail -1 | tr -s ' ' | cut -d' ' -f2,4)"
  cd /tmp && curl -fsSL -m 180 -o bore.tgz https://github.com/ekzhang/bore/releases/download/v0.5.2/bore-v0.5.2-x86_64-unknown-linux-musl.tar.gz && tar xzf bore.tgz && chmod +x bore || note "bore download failed"
  # 2026-10-30 (operator: "use our own bore server bore.vexorium.net"; the bore.pub client hung 08:14 UTC on a dead connection and the run
  # went 4 h without status): our server first, with a WATCHDOG (every 120 s probe our own public port for the SSH banner; 2 misses = kill
  # and restart the client, post the new address) and a status HEARTBEAT every 15 min; bore.pub stays as a second, independent path.
  S=bore.vexorium.net
  ( last_hb=0
    while :; do
      # a FIXED port when the rental sets BORE_PORT (2026-10-30: ntfy.sh dropped the host's port announcements, so a moving port was lost)
      : > /workspace/borev.log; /tmp/bore local 22 --to $S --port ${BORE_PORT:-0} > /workspace/borev.log 2>&1 & BP=$!; port=""
      for i in $(seq 1 30); do port=$(grep -oE "$S:[0-9]+" /workspace/borev.log | tail -1 | cut -d: -f2); [ -n "$port" ] && break; sleep 1; done
      [ -n "$port" ] && note "tunnel $S:$port" || note "tunnel $S: no port after 30 s"
      fails=0
      while kill -0 $BP 2>/dev/null; do
        now=$(date +%s)
        if [ $((now - last_hb)) -ge 900 ]; then last_hb=$now
          R=$(ls -d /workspace/lra-run* 2>/dev/null | head -1)
          note "hb $(date -u +%H:%M) driver=$(pgrep -c -f '[o]pen_package.py run') agents=$(pgrep -c -f '[h]arness/agent.py') vllm=$(pgrep -c -f '[v]llm serve') ready=$([ -e /workspace/READY ] && echo 1 || echo 0) gpu=$(nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits 2>/dev/null | tr '\n' ,) done=$(grep -cE 'session [0-9]+ done' $R/driver.log 2>/dev/null) last=$(grep -E 'session [0-9]+ done' $R/driver.log 2>/dev/null | tail -1 | grep -oE 'mean [0-9.]+')"
        fi
        sleep 120; [ -n "$port" ] || break
        if timeout 10 bash -c "exec 3<>/dev/tcp/$S/$port; head -c 7 <&3" 2>/dev/null | grep -q SSH; then fails=0; else fails=$((fails + 1)); fi
        [ $fails -ge 2 ] && { note "tunnel $S:$port failed 2 checks: restarting bore"; kill $BP 2>/dev/null; break; }
      done
      sleep 5
    done ) &
  while :; do /tmp/bore local 22 --to bore.pub 2>&1 | while read -r l; do echo "$l" >> /workspace/bore.log; case "$l" in *"listening at"*) note "tunnel ${l##*listening at }";; esac; done; note "tunnel dropped, restarting"; sleep 10; done
) >/dev/null 2>&1 &
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
# the package driver after a pre-emption resume (review 2026-10-28): package_run.sh installed RUN_DIR/relaunch.sh; it waits for READY
# and re-runs the saved command when no driver is alive (restartable: open_package.py keeps its clock and per-row state)
for r in /workspace/lra-run*/relaunch.sh; do [ -x "$r" ] && { echo "onstart: scheduling the package relaunch ($r)"; setsid nohup "$r" >> "$(dirname "$r")/relaunch.log" 2>&1 < /dev/null & }; done   # any RUN_DIR (lra-run-<tag>)
exit 0
