#!/usr/bin/env bash
# GB10 side of an outbid during an on-instance chain (2026-10-09). Waits until vast runs the instance again and its SSH answers (the
# direct port can change across a stop, so it is read from vast each time), copies and starts infra/vast/resume_pass_instance.sh there,
# then re-arms the finalize watcher (lra-a100-finalize) with the current port. Log: probe/a100-resume.log.
#   infra/vast/resume_watch.sh INSTANCE_ID PASS LAST          (unit lra-a100-resume)
# Pass 8 run (2026-10-09), so that no stop needs a babysitter:
#   PASS may be auto:FLOOR (resume_pass_instance.sh finishes the pass the chain log shows last, never below FLOOR);
#   LOOP=1 (implies ARM_ON_STOP=1) re-arms after every resume, until finalize stops this unit when it releases the instance;
#   only "exited"/"stopped" count as a stop (vast's "unknown"/"offline" can show while the container runs), and before resuming it asks
#   the instance whether a chain or agent is still alive (then: a false stop, no resume);
#   the bid ladder is the outbid sentry's (infra/vast/outbid_sentry.sh, unit lra-a100-sentry: credit-aware, armed from the rental);
#   PASSES is handed to finalize_a100.sh when it is re-armed (the passes whose run data it uploads and checks).
set -u
cd "$(dirname "$0")/../.." || exit 2
ID=${1:?instance id}; PASS=${2:?pass to finish}; LAST=${3:?last pass}; L=probe/a100-resume.log; LOOP=${LOOP:-0}
[ "$LOOP" = 1 ] && ARM_ON_STOP=1
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
port() { vastai show instance "$ID" --raw 2>/dev/null | python3 -c "
import json, sys; d = json.load(sys.stdin)
p = (d.get('ports') or {}).get('22/tcp') or []
print(d.get('actual_status'), d.get('public_ipaddr'), p[0].get('HostPort') if p else '')" 2>/dev/null; }
SSHO="-i $HOME/.ssh/id_ed25519 -o BatchMode=yes -o ConnectTimeout=20"
arm_finalize() {
  systemctl --user is-active -q lra-a100-finalize && return 0
  systemctl --user reset-failed lra-a100-finalize 2>/dev/null
  systemd-run --user --unit lra-a100-finalize --working-directory="$PWD" -E PATH="$PATH" -E HOME="$HOME" ${PASSES:+-E PASSES="$PASSES"} \
    infra/vast/finalize_a100.sh "$ID" "root@$1" "$2" >> "$L" 2>&1 && log "finalize watcher armed (port $2)"
}
while :; do
  if [ "${ARM_ON_STOP:-0}" = 1 ]; then   # armed while the run is healthy: act only after a stop, never start a second harness beside it
    log "armed on instance $ID: waiting for a stop"
    while read -r st ip pt <<< "$(port)"; [ "$st" != exited ] && [ "$st" != stopped ]; do sleep 60; done
    log "instance $ID stopped (status=$st)"
  fi
  log "waiting for instance $ID to run again"
  n=0
  while true; do
    read -r st ip pt <<< "$(port)"
    if [ "$st" = running ] && [ -n "$pt" ] && ssh $SSHO -p "$pt" "root@$ip" true 2>/dev/null; then break; fi
    n=$((n + 1)); [ $((n % 30)) = 1 ] && log "still stopped or unreachable (status=$st port=${pt:-none})"
    sleep 60
  done
  log "instance running again: ssh root@$ip -p $pt"
  alive=$(ssh $SSHO -p "$pt" "root@$ip" 'pgrep -f "^(/usr/bin/|/bin/)?bash [^ ]*(chain_on_instance|replicate|resume_pass_instance)\.sh|^python3 harness/agent\.py" > /dev/null && echo alive || echo dead' 2>/dev/null | tail -n 1)
  if [ "$alive" = alive ]; then
    log "the chain is still alive on $ID: a false stop, no resume"; arm_finalize "$ip" "$pt"
    [ "$LOOP" = 1 ] && continue || break
  fi
  systemctl --user stop lra-a100-finalize 2>/dev/null; systemctl --user reset-failed lra-a100-finalize 2>/dev/null   # it would block on "chain gone"
  started=0
  for k in 1 2 3; do
    n0=$(ssh $SSHO -p "$pt" "root@$ip" "cat /workspace/lra/probe/a100-80-chain-instance.log 2>/dev/null | wc -l" 2>/dev/null | tail -n 1)
    if [[ "$n0" =~ ^[0-9]+$ ]] && rsync -az -e "ssh $SSHO -p $pt" infra/vast/resume_pass_instance.sh infra/vast/chain_on_instance.sh \
         infra/vast/endpoint.sh "root@$ip:/workspace/lra/infra/vast/" 2>/dev/null; then
      ssh $SSHO -p "$pt" "root@$ip" "cd /workspace/lra; setsid nohup infra/vast/resume_pass_instance.sh $PASS $LAST > /dev/null 2>&1 < /dev/null &" 2>/dev/null
      sleep 20
      o=$(ssh $SSHO -p "$pt" "root@$ip" "tail -n +$((n0 + 1)) /workspace/lra/probe/a100-80-chain-instance.log | tail -n 2" 2>/dev/null | grep -v "^Welcome\|^Have fun")
      echo "$o" | tee -a "$L" > /dev/null
      grep -qE "resume after a vast stop|resume refused" <<< "$o" && { started=1; break; }
    fi
    log "resume launch attempt $k failed (copy, launch or no new chain-log line); retrying in 60 s"; sleep 60
  done
  arm_finalize "$ip" "$pt"   # always re-armed, also after a failed launch (it then reports "chain gone" for a human)
  [ "$started" = 1 ] && log "RESUME STARTED" || log "RESUME FAILED after 3 attempts: babysitter"
  [ "$LOOP" = 1 ] || break
done
