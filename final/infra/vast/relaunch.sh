#!/usr/bin/env bash
# Relaunch the package driver after an outbid resume (review 2026-10-28, finding 16/4: onstart.sh brought back only vLLM; the driver died
# with the container and nothing restarted it). Installed by package_run.sh at RUN_DIR/relaunch.sh; run by onstart.sh on every container
# start and by package_watch.sh (GB10) when it finds no driver. Waits for /workspace/READY (bounded by WAIT_READY_S, default 3600: load +
# CUDA graphs), re-sources endpoint.sh (a container restart rewrites /etc/hosts; the ca-bundle is rebuilt), refuses when a driver is
# alive or the run is finished (OUT/summary.json), then runs RUN_CMD unchanged: open_package.py keeps its job clock (clock.json) and
# resumes every row from its saved state (a cut session gets a new k; see open_package.agent_stage).
set -u
RUN_DIR=${RUN_DIR:-$(cd "$(dirname "$0")" && pwd)}
[ -f "$RUN_DIR/RUN_ENV" ] && . "$RUN_DIR/RUN_ENV"
log() { echo "[$(date -u -Is)] relaunch: $*"; }
[ -f "$RUN_DIR/RUN_CMD" ] || { log "no RUN_CMD in $RUN_DIR: nothing to relaunch"; exit 0; }
# one relauncher at a time (verify 2026-10-28: onstart.sh's hook and every watcher poll each started one; all of them waited for READY and
# then every one started a driver): the lock is held until this script exits, a second instance leaves at once
exec 9> "$RUN_DIR/relaunch.lock"
flock -n 9 || { log "another relaunch.sh holds $RUN_DIR/relaunch.lock: leaving"; exit 0; }
[ -f "${OUT:-/workspace/out}/summary.json" ] && { log "run finished (summary.json exists): nothing to relaunch"; exit 0; }
if pgrep -f "[o]pen_package.py run .*--out ${OUT:-/workspace/out} " > /dev/null; then log "driver alive: nothing to do"; exit 0; fi
cd "${EXPORT_ROOT:-/workspace/lra}" || { log "no export root"; exit 1; }
if [ -z "${LRA_BASE_URL:-}" ]; then   # our vast setup: wait for the server (onstart.sh relaunches it; run_vllm.sh touches READY)
  t0=$(date +%s)
  until [ -e /workspace/READY ]; do
    [ $(( $(date +%s) - t0 )) -lt "${WAIT_READY_S:-3600}" ] || { log "server not READY after ${WAIT_READY_S:-3600}s: giving up this time"; exit 1; }
    sleep 20
  done
fi
# the wait above can be long: a driver may have been started meanwhile (the no-driver check is repeated after it)
if pgrep -f "[o]pen_package.py run .*--out ${OUT:-/workspace/out} " > /dev/null; then log "driver alive after the wait: nothing to do"; exit 0; fi
[ -f "${OUT:-/workspace/out}/summary.json" ] && { log "run finished meanwhile: nothing to relaunch"; exit 0; }
export LRA_API_KEY_FILE="${LRA_API_KEY_FILE:-}"
. infra/vast/endpoint.sh
PF=$(preflight); [ "$PF" = ok ] || { log "preflight at $EP_URL: ${PF:-no answer}; not relaunched"; exit 1; }
export LRA_NO_GCS=1 LRA_NO_WANDB=1
CMD=$(cat "$RUN_DIR/RUN_CMD")
log "relaunching: $CMD"
# shellcheck disable=SC2086
setsid nohup $CMD >> "$RUN_DIR/driver.log" 2>&1 < /dev/null &
sleep 3
pgrep -f "[o]pen_package.py run .*--out ${OUT:-/workspace/out} " > /dev/null && { log "driver running again"; exit 0; }
log "driver did not start"; exit 1
