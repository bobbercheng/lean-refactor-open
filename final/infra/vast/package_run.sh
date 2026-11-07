#!/usr/bin/env bash
# Start the open package ON the node, from the release export root (/workspace/lra on the rented A100; docs/a100_rehearsal.md). The only
# launcher of harness/open_package.py for the rehearsal (review 2026-10-28: migrate_harness.sh / launch_line.sh / chain_on_instance.sh /
# resume_watch.sh / finalize_a100.sh are the Oct 6-9 pass line and are never used for the package).
#   infra/vast/package_run.sh                 (environment below; run from the export root)
#   RUN_DIR=/workspace/lra-run    rows.jsonl + heartbeats.jsonl are there (shipped by rehearsal.sh); driver.log, RUN_CMD, relaunch.sh land there
#   OUT=/workspace/out            the package's --out
#   START=<epoch>                 the job clock's start (the rental time: setup counts, as on the organizers' node); JOB=<seconds>
#   TAG=reh  WORKERS=14  MAX_SESSIONS=12  END_SECONDS=7200  END_PIPELINE=on  EXTRA="..."   open_package.py arguments (the defaults = the
#                                 package's own defaults = the official run's recipe, 2026-10-31); RUN_CMD always spells out all four, so a
#                                 relaunch with a newer export resumes the run unchanged (an --end-pipeline in EXTRA is taken as given)
#   LRA_BASE_URL / LRA_API_KEY_FILE          another endpoint (the $0 dry run's fake model); default: endpoint.sh's TLS endpoint on this box
# Refuses to start (exit 1, nothing launched) unless: the endpoint preflight prints `ok` (one real completion through the harness's own
# client), every row's environment and module olean exist (infra/open_package/check_envs.py), /workspace has >= MIN_FREE_GB (40) free,
# and no `open_package.py run` process is alive. Writes RUN_DIR/RUN_CMD (the exact command, for the relaunch after an outbid resume:
# infra/vast/relaunch.sh, hooked by onstart.sh and by package_watch.sh on the GB10) and starts the driver fully detached.
set -u
cd "$(dirname "$0")/../.." || exit 2
RUN_DIR=${RUN_DIR:-/workspace/lra-run}; OUT=${OUT:-/workspace/out}; TAG=${TAG:-reh}
WORKERS=${WORKERS:-11}; MAX_SESSIONS=${MAX_SESSIONS:-12}; END_SECONDS=${END_SECONDS:-7200}; END_PIPELINE=${END_PIPELINE:-on}; EXTRA=${EXTRA:-}
case " $EXTRA " in *" --end-pipeline "*|*" --end-pipeline="*) EPIPE="";; *) EPIPE=" --end-pipeline $END_PIPELINE";; esac   # official.sh / p85b pass it in EXTRA
START=${START:?job start epoch}; JOB=${JOB:?job seconds}
ROWS=${ROWS:-$RUN_DIR/rows.jsonl}; HBS=${HBS:-$RUN_DIR/heartbeats.jsonl}
MIN_FREE_GB=${MIN_FREE_GB:-40}; DF_PATH=${DF_PATH:-/workspace}
log() { echo "[$(date -u -Is)] $*"; }
mkdir -p "$RUN_DIR" "$OUT"
[ -f "$ROWS" ] && [ -f "$HBS" ] || { log "REFUSED: no rows/heartbeats at $ROWS / $HBS"; exit 1; }
if pgrep -f "[o]pen_package.py run .*--out $OUT " > /dev/null; then log "REFUSED: an open_package.py run process on $OUT is alive (never a second driver)"; exit 1; fi
free_gb=$(df --output=avail -BG "$DF_PATH" 2>/dev/null | tail -n 1 | tr -dc 0-9); free_gb=${free_gb:-0}
[ "$free_gb" -ge "$MIN_FREE_GB" ] || { log "REFUSED: $DF_PATH has $free_gb GB free (< $MIN_FREE_GB)"; exit 1; }
python3 infra/open_package/check_envs.py --rows "$ROWS" --root "$PWD" || { log "REFUSED: environments incomplete (above)"; exit 1; }
# the endpoint: endpoint.sh exports EP_URL / EP_KEY (and REQUESTS_CA_BUNDLE + the lra-a100 hosts entry for the pinned TLS cert)
. infra/vast/endpoint.sh
[ -z "${EP_KEY:-}" ] || [ -f "$EP_KEY" ] || { log "REFUSED: key file $EP_KEY missing (bootstrap.sh writes it)"; exit 1; }
PF=$(preflight); [ "$PF" = ok ] || { log "REFUSED: endpoint preflight at $EP_URL: ${PF:-no answer}"; exit 1; }
log "preflight ok at $EP_URL (model $LRA_API_MODEL)"
CMD="python3 harness/open_package.py run --rows $ROWS --heartbeats $HBS --out $OUT --tag $TAG --base-url $EP_URL ${EP_KEY:+--api-key-file $EP_KEY} --api-model $LRA_API_MODEL --started-at $START --job-seconds $JOB --workers $WORKERS --max-sessions $MAX_SESSIONS --end-seconds $END_SECONDS$EPIPE $EXTRA"
printf '%s\n' "$CMD" > "$RUN_DIR/RUN_CMD"
printf 'RUN_DIR=%s\nOUT=%s\nEXPORT_ROOT=%s\nLRA_BASE_URL=%s\nLRA_API_KEY_FILE=%s\n' "$RUN_DIR" "$OUT" "$PWD" "${LRA_BASE_URL:-}" "${LRA_API_KEY_FILE:-}" > "$RUN_DIR/RUN_ENV"
cp infra/vast/relaunch.sh "$RUN_DIR/relaunch.sh" && chmod +x "$RUN_DIR/relaunch.sh"
export LRA_NO_GCS=1 LRA_NO_WANDB=1   # no optional services on the package path (review 2026-10-28, finding 20)
log "starting: $CMD"
# shellcheck disable=SC2086
setsid nohup $CMD >> "$RUN_DIR/driver.log" 2>&1 < /dev/null &
sleep 3
pgrep -f "[o]pen_package.py run .*--out $OUT " > /dev/null && { log "driver running (pid $(pgrep -f "[o]pen_package.py run .*--out $OUT " | head -n 1)); log $RUN_DIR/driver.log"; exit 0; }
log "driver did not start; tail of driver.log:"; tail -n 20 "$RUN_DIR/driver.log"; exit 1
