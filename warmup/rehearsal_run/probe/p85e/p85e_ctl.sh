#!/usr/bin/env bash
# ON the A100 box: control of the p85e scheduler (/workspace/p85e/p85e_xloop_host.py). No pgrep -f / pkill -f: the pid file + /proc only.
#   p85e_ctl.sh start [VAR=val ...]    start (refuses while a p85e pid is alive or STOP exists); the VAR=val set is saved in launch.env
#   p85e_ctl.sh start-last             start with the saved launch.env (the GB10 push unit's auto-relaunch after a box restart)
#   p85e_ctl.sh handover [VAR=val ...] v3: replace a running instance WITHOUT stopping its sessions: touch STOP, wait (<= 180 s) until it
#                                      logged "no new sessions (STOP" (it leaves its main loop; v3 also releases xloop.main.lock there),
#                                      rm STOP, start the new one (no args = the saved launch.env). The predecessor keeps draining its
#                                      running sessions (they count against the cap; their lineages stay busy for the successor).
#   p85e_ctl.sh relaunch [VAR=val ...] = handover (v3; the old soft-stop relaunch waited for the drain and failed with sessions running)
#   p85e_ctl.sh stop [now]             touch STOP (now: also STOP_NOW = running sessions get SIGTERM, bests kept); wait <= 300 s (now: 420 s)
#   p85e_ctl.sh dry [VAR=val ...]      one DRY tick against the live driver (prints the candidate list; no lock, no writes)
#   p85e_ctl.sh set-end EPOCH|now|ISO [note]   v3: write /workspace/p85e/END_AT atomically (tmp + mv); prints "END_AT <epoch> <utc>"
#   p85e_ctl.sh get-end                prints "END_AT <epoch> <utc>" (or "END_AT none")
#   p85e_ctl.sh driver                 prints "driver <n of open_package.py run on out-p85b>", "summary real|placeholder|none", "stopper <n>"
#   p85e_ctl.sh end-driver             the p85b driver ended early: /workspace/package_stop_host.sh /workspace/lra-run-p85b 0 (export only),
#                                      detached (refused while a package_stop_host.sh runs); used by the GB10 final in end-driver mode
#   p85e_ctl.sh alive                  prints alive / dead / stopped (STOP present and no pid)
#   p85e_ctl.sh status                 pid, STOP files, END_AT, our sessions, last log lines
# v3 (2026-11-01 ~00:00 UTC): handover, set-end / get-end; envset self-heals a missing lra-a100 hosts line / CA bundle (a container
# restart after the driver exited: nobody else re-sources endpoint.sh then); every start / handover / set-end under flock ctl.lock.
# Test hooks: P85E_W (default /workspace), P85E_PY, P85E_NOENV=1 (no endpoint environment: the local fake-box test only).
set -u
W=${P85E_W:-/workspace}; X=$W/p85e; PY=${P85E_PY:-$X/p85e_xloop_host.py}; PIDF=$X/xloop.pid
mkdir -p $X/logs
alive() { local p; p=$(cat $PIDF 2>/dev/null) || return 1; [ -n "$p" ] && [ -r /proc/$p/cmdline ] && tr '\0' ' ' < /proc/$p/cmdline | grep -q "p85e_xloop_host[.]py"; }
ctl_lock() { exec 7> $X/ctl.lock; flock -w 600 7 || { echo "ctl.lock busy for 600 s: refusing"; exit 1; }; }
envset() {   # the driver's environment (endpoint.sh's exports) + the gates; hosts line / CA bundle only re-created when MISSING
  cd $W/lra || exit 1
  [ "${P85E_NOENV:-0}" = 1 ] && return 0
  if ! grep -q " lra-a100$" /etc/hosts; then echo "127.0.0.1 lra-a100" >> /etc/hosts; echo "[$(date -u +%m-%d\ %H:%M:%S)] ctl: lra-a100 hosts line re-added" >> $X/xloop.log; fi
  if [ ! -s $W/tls/ca-bundle.pem ] && [ -s $W/tls/cert.pem ]; then
    cat "$(python3 -c 'import certifi; print(certifi.where())')" $W/tls/cert.pem > $W/tls/ca-bundle.pem.p85e-tmp && mv $W/tls/ca-bundle.pem.p85e-tmp $W/tls/ca-bundle.pem
    echo "[$(date -u +%m-%d\ %H:%M:%S)] ctl: CA bundle re-created" >> $X/xloop.log
  fi
  grep -q " lra-a100$" /etc/hosts || { echo "no lra-a100 in /etc/hosts: refusing"; exit 1; }
  [ -s $W/tls/ca-bundle.pem ] || { echo "no CA bundle: refusing"; exit 1; }
  export LRA_API_KEY_FILE="" LRA_NO_GCS=1 LRA_NO_WANDB=1 RUN_DIR=$W/lra-run-p85b REQUESTS_CA_BUNDLE=$W/tls/ca-bundle.pem \
    EP_URL=https://lra-a100:8000/v1 EP_KEY=/root/.config/vexorium/vllm_api_key LRA_API_MODEL=glm-5.3-flash LRA_AGENT_FLAGS=""
  export AGENT_EXTRA="--base-url $EP_URL --api-key-file $EP_KEY --api-model $LRA_API_MODEL --serving-tag vllm-a100-awq-w4a16 --max-api-retries 20"
}
launch() {   # no alive / STOP checks (callers do them); the scheduler itself refuses while another main loop holds xloop.main.lock
  envset
  for kv in "$@"; do case "$kv" in *=*) export "$kv";; *) echo "bad arg $kv"; return 1;; esac; done
  printf '%s\n' "$@" > $X/launch.env.p85e-tmp && mv $X/launch.env.p85e-tmp $X/launch.env
  echo "[$(date -u +%m-%d\ %H:%M:%S)] ctl ${VERB:-start}: $*" >> $X/xloop.log
  local old; old=$(cat $PIDF 2>/dev/null)
  setsid nohup python3 $PY >> $X/xloop.out 2>&1 < /dev/null 7>&- &   # 7 = ctl.lock: never inherited by the scheduler
  local w=0; while [ $w -lt 30 ]; do sleep 1; w=$((w + 1)); alive && [ "$(cat $PIDF 2>/dev/null)" != "$old" ] && break; done
  if alive && [ "$(cat $PIDF 2>/dev/null)" != "$old" ]; then echo "started pid $(cat $PIDF)"; else echo "NOT started (pid file unchanged after 30 s):"; tail -n 5 $X/xloop.out; return 1; fi
}
left_main() {   # $1 = pid: that instance logged "no new sessions (" after its own "up pid" line (it only drains now)
  local n; n=$(grep -n "xloop.* up pid $1[: ]" $X/xloop.log 2>/dev/null | tail -n 1 | cut -d: -f1)
  [ -n "$n" ] && tail -n +"$n" $X/xloop.log | grep -q "p85e xloop: no new sessions ("
}
start() {
  alive && { echo "p85e already alive (pid $(cat $PIDF)): use handover"; return 1; }
  [ -e $X/STOP ] || [ -e $X/STOP_NOW ] && { echo "STOP present: use handover"; return 1; }
  launch "$@"
}
handover() {
  local args=("$@")
  if [ ${#args[@]} = 0 ]; then [ -s $X/launch.env ] || { echo "no args and no launch.env"; return 1; }; mapfile -t args < $X/launch.env; fi
  [ -e $X/STOP_NOW ] && { echo "STOP_NOW present (a stop-all is in progress): NOT handed over"; return 1; }
  if alive; then
    local old w=0; old=$(cat $PIDF)
    left_main "$old" || touch $X/STOP
    until left_main "$old"; do
      sleep 5; w=$((w + 5))
      alive || break
      [ $w -lt 180 ] || { echo "old p85e pid $old did not leave its main loop in 180 s: NOT handed over (STOP stays: no new sessions)"; return 1; }
    done
    echo "old p85e pid $old left its main loop after ${w}s (it drains its running sessions)"
  fi
  rm -f $X/STOP
  VERB=handover launch "${args[@]}"
}
stop() {
  touch $X/STOP; [ "${1:-}" = now ] && touch $X/STOP_NOW
  local lim=300; [ "${1:-}" = now ] && lim=420; local w=0
  while alive && [ $w -lt $lim ]; do sleep 5; w=$((w + 5)); done
  alive && { echo "p85e pid $(cat $PIDF) still alive after ${lim}s (sessions still running; STOP stays)"; return 1; }
  echo "p85e stopped (waited ${w}s)"
}
nproc_match() { local n=0 p; for p in /proc/[0-9]*; do { tr '\0' ' ' < $p/cmdline; } 2>/dev/null | grep -qE "$1" && n=$((n + 1)); done; echo $n; }
driver() {
  echo "driver $(nproc_match "harness/open_package[.]py run .*--out $W/out-p85b ")"
  local s=none; [ -f $W/out-p85b/summary.json ] && { if grep -q placeholder $W/out-p85b/summary.json; then s=placeholder; else s=real; fi; }
  echo "summary $s"; echo "stopper $(nproc_match "package_stop_host[.]sh")"
}
getend() { local v; v=$(awk 'NR==1{print $1}' $X/END_AT 2>/dev/null); if [ -n "$v" ]; then echo "END_AT $v $(date -u -d @${v%.*} '+%Y-%m-%dT%H:%M:%SZ' 2>/dev/null)"; else echo "END_AT none"; fi; }
setend() {
  local v=${1:-}; shift || true
  case "$v" in now) v=$(date +%s);; ''|*[!0-9]*) v=$(date -u -d "$v" +%s 2>/dev/null) || { echo "bad END_AT value"; return 1; };; esac
  printf '%s %s %s\n' "$v" "$(date -u -d @$v '+%Y-%m-%dT%H:%M:%SZ')" "${*:-}" > $X/END_AT.p85e-tmp && mv $X/END_AT.p85e-tmp $X/END_AT || return 1
  echo "[$(date -u +%m-%d\ %H:%M:%S)] ctl set-end: $(date -u -d @$v '+%m-%d %H:%M:%S') UTC ${*:-}" >> $X/xloop.log
  getend
}
case "${1:-status}" in
  start) shift; ctl_lock; start "$@";;
  start-last) [ -s $X/launch.env ] || { echo "no launch.env"; exit 1; }; mapfile -t A < $X/launch.env; ctl_lock; start "${A[@]}";;
  handover|relaunch) shift; ctl_lock; handover "$@";;
  stop) stop "${2:-}";;
  dry) shift; envset; for kv in "$@"; do export "$kv"; done; DRY=1 python3 $PY;;
  set-end) shift; ctl_lock; setend "$@";;
  get-end) getend;;
  driver) driver;;
  end-driver) [ "$(nproc_match "package_stop_host[.]sh")" = 0 ] || { echo "a package_stop_host.sh is already running"; exit 0; }
    echo "[$(date -u +%m-%d\ %H:%M:%S)] ctl end-driver: package_stop_host.sh $W/lra-run-p85b 0 (export only)" >> $X/xloop.log
    setsid nohup bash $W/package_stop_host.sh $W/lra-run-p85b 0 >> $W/lra-run-p85b/stop_p85e.out 2>&1 < /dev/null 7>&- &
    echo "scheduled package_stop_host.sh (pid $!)";;
  alive) if alive; then echo alive; elif [ -e $X/STOP ]; then echo stopped; else echo dead; fi;;
  status) if alive; then echo "alive pid $(cat $PIDF)"; else echo "not running"; fi; ls $X/STOP $X/STOP_NOW 2>/dev/null; getend
    echo "p85e processes: $(for p in /proc/[0-9]*; do { tr '\0' ' ' < $p/cmdline; } 2>/dev/null | grep -q "^python3 [^ ]*p85e_xloop_host[.]py" && echo -n "${p#/proc/} "; done)"
    ps -ww -eo pid=,etimes=,args= | grep -E "[h]arness/agent[.]py .*--run-id p85b-[ct][0-9]" | sed -E 's/.*--run-id (p85b-[ct][0-9]+-k[0-9]+).*/\1/' | sort | tr '\n' ' '; echo
    tail -n 12 $X/xloop.log 2>/dev/null;;
  *) echo "usage: $0 start|start-last|handover|relaunch|stop [now]|dry|set-end|get-end|alive|status"; exit 2;;
esac
