#!/usr/bin/env bash
# run.sh: the 48 h optimization job (README.md, step 2). Run setup.sh once before. Needs no internet.
#   bash run.sh [ROWS.jsonl HEARTBEATS.jsonl]     the job (default rows: the ones setup.sh prepared; default heartbeats: the file given
#                                                 to setup.sh, else the ones setup measured for those rows, .lra/ref_heartbeats.jsonl)
#   bash run.sh check [ROWS HEARTBEATS]           the preflight only (environments, model files, tools, locks, the GPUs inside the
#                                                 container, the clock it would take); starts nothing; run it once on a GPU node
#   bash run.sh export [ROWS HEARTBEATS]          recovery: write runs/final/proofs.jsonl from whatever the job saved
# What it does: takes the job clock's start FIRST (LRA_START, else the clock of a run being resumed by the SAME scheduler job or with
# LRA_RESUME=1, else the Slurm job's start, else now; a previous run's runs/final is moved aside to runs/final.prev-<start>, never
# resumed by a new job; a clock already over is refused unless LRA_RESUME=1); JOB = min(48 h, the Slurm job's end - start) -
# LRA_SAFETY_S (600), capped at the Slurm end; a preflight (the 4 A100s and NVLink as the container sees them); starts the vLLM server in
# the pinned image (the runtime setup.sh found) on 127.0.0.1:8000, serving the local model snapshot setup.sh verified, and restarts it
# if it dies; waits until it answers (at most LRA_SERVER_WAIT_S, 5400);
# then runs harness/open_package.py run with the package defaults (the official recipe) in the foreground; every LRA_SNAPSHOT_S (3600)
# an interim proofs file (infra/orgserver/snapshot.py); SIGTERM / SIGINT: interim proofs promoted to runs/final/proofs.jsonl if the
# export has not written it, then everything stopped; SIGUSR1: the same promotion, the job goes on. Restart after a crash: the same
# command inside the same scheduler job (the driver resumes from runs/final, on the same clock); in a new job: LRA_RESUME=1.
# A driver that fails with more than 20 min left is restarted on the same clock (at most LRA_DRIVER_RESTARTS, 3), after its processes are gone.
# Knobs: LRA_OUT (runs/final), LRA_START (epoch), LRA_JOB_SECONDS, LRA_SAFETY_S, LRA_RESUME=1, LRA_WORKERS / LRA_COMPILE_SLOTS (default: the package's
# own, unless the allocation is smaller than the node), LRA_EXTRA (more open_package.py flags), LRA_BASE_URL (an already running
# OpenAI-compatible server: no server is started), LRA_FAST_DIR, LRA_VLLM_PORT, LRA_SERVER_WAIT_S, LRA_SNAPSHOT_S, LRA_DRY=1 (print the
# commands, start nothing).
set -u
T_START=$(date +%s)   # first: the job clock never starts later than this line
[ "${BASH_VERSINFO[0]:-0}" -ge 4 ] || { echo "run.sh needs bash 4 or newer (this is ${BASH_VERSION:-not bash})" >&2; exit 2; }
LRA_PKG=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
cd "$LRA_PKG" || exit 2
# shellcheck source=infra/orgserver/lib.sh
. "$LRA_PKG/infra/orgserver/lib.sh"
STATE=$LRA_PKG/.lra
MODE=run
case "${1:-}" in check|export|run) MODE=$1; shift;; esac
[ -f "$STATE/setup.env" ] || lra_die "no $STATE/setup.env: run setup.sh first (README.md)"
# shellcheck disable=SC1091
. "$STATE/setup.env"
LRA_RT=${LRA_RUNTIME:-$LRA_RT}   # another runtime than setup.sh found (its image must have been pulled: LRA_RUNTIME=... bash setup.sh)
ROWS=${1:-${LRA_SETUP_ROWS:-}}; HBS=${2:-}
# b100: without a heartbeats argument, setup's (given or measured) - only for the rows setup prepared
if [ -z "$HBS" ] && { [ -z "${1:-}" ] || [ "$(realpath -m "$1")" = "$(realpath -m "${LRA_SETUP_ROWS:-/nonexistent}")" ]; }; then HBS=${LRA_SETUP_HBS:-}; fi
[ -f "$ROWS" ] && [ -f "$HBS" ] || lra_die "rows / heartbeats file missing: '$ROWS' / '$HBS' (a rows file without its heartbeats file: run setup.sh with that rows file first; it measures them)"
ROWS=$(cd "$(dirname "$ROWS")" && pwd)/$(basename "$ROWS"); HBS=$(cd "$(dirname "$HBS")" && pwd)/$(basename "$HBS")
PY=${LRA_PYTHON:?setup.env has no LRA_PYTHON}
OUT=${LRA_OUT:-$LRA_PKG/runs/final}
case "$OUT" in /*) ;; *) OUT=$LRA_PKG/$OUT;; esac
mkdir -p "$(dirname "$OUT")" || lra_die "cannot create $(dirname "$OUT")"   # OUT itself is created after the clock (it may be set aside)
OUT=$(cd "$(dirname "$OUT")" && pwd)/$(basename "$OUT")
# the PATH of every process of the job: the Python wrapper and ripgrep (.lra), Lean (ELAN_HOME); BASH_ENV puts them back in front in any
# bash whose login profile rebuilt PATH (the model's shell tool runs `bash -lc`; infra/orgserver/bash_env.sh)
export ELAN_HOME LRA_SHELL_PATH_PREPEND="$STATE/pybin:$STATE/bin:$ELAN_HOME/bin" BASH_ENV="$LRA_PKG/infra/orgserver/bash_env.sh"
export PATH="$LRA_SHELL_PATH_PREPEND:$PATH"
export LRA_NO_GCS=1 LRA_NO_WANDB=1 LRA_MEMGATE_CGROUP_V1=1 XDG_CACHE_HOME="$LRA_WS/cache"
DRY=${LRA_DRY:-0}
run() { if [ "$DRY" = 1 ]; then printf 'DRY:'; printf ' %q' "$@"; echo; else "$@"; fi; }
FAILS=""   # run.sh check: everything that would stop the job, reported together at the end
fail() { if [ "$MODE" = check ]; then lra_log "CHECK FAILED: $*"; FAILS="$FAILS; $*"; else lra_die "$*"; fi; }

# ------------------------------------------------------------------------------------------------------------------------- the clock
if [ "$MODE" != export ] && [ "$DRY" != 1 ] && pgrep -f "[o]pen_package.py run .*--out $OUT( |$)" > /dev/null 2>&1; then
  fail "an open_package.py run on $OUT is already running"
fi
LOGD=$OUT/logs   # check and dry runs write nothing into OUT (it may be another run's): their logs go to .lra/logs (rc1: dry too)
{ [ "$MODE" = check ] || [ "$DRY" = 1 ]; } && LOGD=$STATE/logs
if [ "$MODE" = export ]; then
  mkdir -p "$LOGD" || exit 2   # the recovery export reads what the job saved; it takes no clock and moves nothing
else
  # clock.json of OUT is reused only by the same scheduler job (or LRA_RESUME=1); another run's OUT is set aside (run mode only)
  APPLY=(); [ "$MODE" = run ] && [ "$DRY" != 1 ] && APPLY=(--apply)
  CLK=$("$PY" infra/orgserver/orgtools.py clock --out "$OUT" --now "$T_START" --pid "$$" --rows "$ROWS" ${LRA_START:+--start "$LRA_START"} \
        ${LRA_JOB_SECONDS:+--job "$LRA_JOB_SECONDS"} --safety "${LRA_SAFETY_S:-600}" ${APPLY[@]+"${APPLY[@]}"}); CRC=$?
  [ -n "$CLK" ] || lra_die "job clock (orgtools.py clock rc $CRC)"
  eval "$CLK"
  [ -n "${SET_ASIDE:-}" ] && lra_log "job clock: $OUT held another run's state: moved to $SET_ASIDE"
  [ -n "${NOTE:-}" ] && lra_log "job clock: $NOTE"
  if [ "$ACTION" = refuse ]; then fail "job clock: refused (above)"
  else
    lra_log "job clock: start $(date -u -d "@$START" +%Y-%m-%dT%H:%M:%SZ) ($SOURCE), $JOB s, ends $(date -u -d "@$JOB_END" +%Y-%m-%dT%H:%M:%SZ); $ACTION; out $OUT"
  fi
  mkdir -p "$LOGD" || exit 2
fi

# ---------------------------------------------------------------------------------------------------------------------- preflight
FAST=$("$PY" infra/orgserver/orgtools.py fastdir) || lra_die "no node-local directory with working flock (set LRA_FAST_DIR)"
export LRA_MEMGATE_DIR=$FAST LRA_LOCK_DIR=$FAST/locks
"$PY" -c 'import sys, requests; sys.exit(0 if sys.version_info >= (3, 11) else 1)' || lra_die "$PY: Python >= 3.11 with requests is required (setup.sh)"
command -v rg > /dev/null 2>&1 || lra_die "ripgrep (rg) missing on PATH (setup.sh installs it into $STATE/bin)"
"$PY" infra/open_package/check_envs.py --rows "$ROWS" --root "$LRA_PKG" --elan "$ELAN_HOME" > "$LOGD/check_envs.log" 2>&1 \
  || { tail -n 20 "$LOGD/check_envs.log"; lra_die "Lean environments incomplete for $ROWS (setup.sh with this rows file)"; }
if [ -z "${LRA_BASE_URL:-}" ] && [ "$MODE" != export ]; then
  # the model: the local snapshot setup.sh verified (LRA_MODEL_PATH), served as a directory: no hub lookup, offline or not
  MP=$("$PY" infra/orgserver/fetch_model.py --hf-home "$LRA_WS/hf" --repo "$LRA_MODEL_REPO" --rev "$LRA_MODEL_REV" --verify-only --print-path) \
    || fail "model files incomplete under $LRA_WS/hf (setup.sh)"
  if [ -n "${LRA_MODEL_PATH:-}" ] && [ -f "$LRA_MODEL_PATH/config.json" ]; then :
  elif [ -n "$MP" ]; then [ -n "${LRA_MODEL_PATH:-}" ] && lra_log "WARNING: setup.env's LRA_MODEL_PATH $LRA_MODEL_PATH has no config.json: serving $MP"; LRA_MODEL_PATH=$MP
  fi
  export LRA_MODEL_PATH
  lra_log "model: ${LRA_MODEL_PATH:-?} (local snapshot of $LRA_MODEL_REPO @ ${LRA_MODEL_REV:0:12})"
  # the GPUs as the SERVER will see them (inside the image, its runtime flags): 4, A100, NVLink (review 2026-11-01: setup may have run
  # on a node without GPUs, so this is the first look from inside the container on the job's node)
  if [ "$DRY" = 1 ]; then lra_in_image gpu python3 "$LRA_PKG/infra/orgserver/gpu_probe.py"
  elif ! lra_gpu_check "$LOGD/gpu-check.log"; then
    fail "the container sees NO GPU (runtime $LRA_RT; probe log $LOGD/gpu-check.log). run.sh must run on the GPU node, inside the job's allocation, and the runtime needs its GPU option: podman-hpc --gpu, shifter --module=gpu (or LRA_SHIFTER_MODULES), apptainer --nv, docker --gpus all"
  else
    lra_log "GPUs inside the container: $LRA_GPU_N ($LRA_GPU_NAMES), NVLink $([ "$LRA_GPU_NVLINK" = 1 ] && echo yes || echo NO)${LRA_SHIFTER_MODULES:+; shifter --module=$LRA_SHIFTER_MODULES}"
    [ "$LRA_GPU_N" -ge 4 ] || fail "the container sees $LRA_GPU_N GPU(s); the server needs 4 (tensor parallel 4): allocate the node's 4 GPUs (e.g. --gpus=4)"
    [ "$LRA_GPU_A100" -ge 4 ] || lra_log "WARNING: not 4 A100s ($LRA_GPU_NAMES): the image's kernels are built for sm80 (A100); the server may not start"
    [ "$LRA_GPU_NVLINK" = 1 ] || lra_log "WARNING: no NVLink between the first 4 GPUs inside the container: vLLM switches its custom all-reduce off (~25% slower decode)"
  fi
fi
FREE_GB=$(df --output=avail -BG "$OUT" 2> /dev/null | tail -n 1 | tr -dc 0-9); [ "${FREE_GB:-0}" -ge 20 ] || lra_log "WARNING: ${FREE_GB:-?} GB free under $OUT (the run writes ~5-20 GB)"
# the model's shell tool (`bash -lc`, a login shell) must find rg and lake even when a login profile rebuilds PATH
SHP=$(cd "$LRA_WS" && env -u LRA_ORG_JOB bash -lc 'command -v rg; command -v lake' 2> /dev/null)
case "$SHP" in *rg*lake*) ;; *) lra_log "WARNING: a login shell (the model's shell tool) does not find rg and lake (found: ${SHP:-nothing}); BASH_ENV=$BASH_ENV should restore them";; esac
eval "$("$PY" infra/orgserver/orgtools.py sizing)"
SIZING=()
W=${LRA_WORKERS:-$WORKERS}; S=${LRA_COMPILE_SLOTS:-$SLOTS}
[ -n "$W" ] && SIZING+=(--workers "$W")
[ -n "$S" ] && SIZING+=(--compile-slots "$S")
lra_log "preflight: $CPUS CPU(s) usable of $NODE_CPUS, ${MEM_AVAIL_GB} GB available${CGROUP_LIMIT_GB:+, cgroup limit ${CGROUP_LIMIT_GB} GB}; locks in $FAST; ${SIZING[*]:-package default sizing (14 workers, auto compile slots)}"
if [ "$MODE" = check ]; then
  [ -z "$FAILS" ] || lra_die "run.sh check: ${FAILS#; }"
  lra_log "CHECK OK"; exit 0
fi
EXTRA=()
# shellcheck disable=SC2206
[ -n "${LRA_EXTRA:-}" ] && EXTRA=(${LRA_EXTRA})
if [ "$MODE" = export ]; then
  run "$PY" harness/open_package.py export --rows "$ROWS" --heartbeats "$HBS" --out "$OUT" ${SIZING[@]+"${SIZING[@]}"} ${EXTRA[@]+"${EXTRA[@]}"}
  exit $?
fi

# --------------------------------------------------------------------------------------------------------------------------- server
TAG="opk-$START-$$"
SD=$FAST/server; mkdir -p "$SD"; rm -f "$SD/stop"
LOOP=""
if [ -n "${LRA_BASE_URL:-}" ]; then
  BASE=$LRA_BASE_URL
  lra_log "server: using $BASE (LRA_BASE_URL); none started"
else
  lra_server_env
  BASE="http://127.0.0.1:$VLLM_PORT/v1"
  LRA_CONTAINER_NAME="lra-vllm-$(id -u)-$START"
  if "$PY" infra/orgserver/orgtools.py ready "$BASE" --timeout 1 > /dev/null 2>&1; then lra_die "something already answers on $BASE (another server?): stop it or set LRA_VLLM_PORT"; fi
  if [ "$DRY" = 1 ]; then
    lra_in_image gpu bash "$LRA_PKG/infra/orgserver/vllm_entry.sh"   # prints the runtime's command (LRA_DRY=1)
  else
    lra_server_loop "$OUT/logs/server.log" "$SD/stop" "$SD/client.pid" &
    LOOP=$!; echo "$LOOP" > "$SD/loop.pid"
    lra_log "server: starting in $LRA_RT (log $OUT/logs/server.log, vLLM log $LRA_WS/vllm.log)"
  fi
fi
SNAP=""; DRIVER=""
snapshot() { "$PY" infra/orgserver/snapshot.py --rows "$ROWS" --heartbeats "$HBS" --out "$OUT" "$@" -- ${EXTRA[@]+"${EXTRA[@]}"} >> "$OUT/logs/snapshot.log" 2>&1; }
stop_all() {
  [ -n "$SNAP" ] && kill "$SNAP" 2> /dev/null
  [ -n "$DRIVER" ] && kill -TERM "$DRIVER" 2> /dev/null
  "$PY" infra/orgserver/orgtools.py reap "$TAG" --grace 20 > /dev/null 2>&1
  [ -n "$LOOP" ] && lra_server_stop "$SD/stop" "$SD/client.pid" "$LOOP"
}
on_signal() {
  lra_log "signal $1: interim proofs, then stopping (proofs: $OUT/proofs.jsonl)"
  snapshot --promote; tail -n 1 "$OUT/logs/snapshot.log"
  stop_all; exit 143
}
trap 'on_signal TERM' TERM
trap 'on_signal INT' INT
trap 'lra_log "signal USR1: interim proofs"; snapshot --promote; tail -n 1 "$OUT/logs/snapshot.log"' USR1

if [ -n "$LOOP" ]; then
  "$PY" infra/orgserver/orgtools.py ready "$BASE" --timeout "${LRA_SERVER_WAIT_S:-5400}" --pidfile "$SD/loop.pid" &
  RP=$!; wait "$RP"; RRC=$?
  while kill -0 "$RP" 2> /dev/null; do wait "$RP"; RRC=$?; done   # a USR1 trap interrupts wait: wait again
  if [ "$RRC" = 0 ]; then
    lra_log "server: ready after $(( $(date +%s) - T_START )) s"
    if grep -q "Custom allreduce is disabled" "$LRA_WS/vllm.log" 2> /dev/null; then
      lra_log "WARNING: vLLM disabled its custom all-reduce (no NVLink / P2P visible inside the container): decode ~25% slower; check nvidia-smi topo -m in the container"
    fi
  else
    lra_log "WARNING: the server did not answer within ${LRA_SERVER_WAIT_S:-5400} s (see $OUT/logs/server.log, $LRA_WS/vllm.log); the driver starts anyway: its sessions wait for the server, and the model-free end stage still runs"
  fi
fi

# --------------------------------------------------------------------------------------------------------------------------- driver
CMD=("$PY" harness/open_package.py run --rows "$ROWS" --heartbeats "$HBS" --out "$OUT" --base-url "$BASE" --api-model glm-5.3-flash
     --started-at "$START" --job-seconds "$JOB" ${SIZING[@]+"${SIZING[@]}"} ${EXTRA[@]+"${EXTRA[@]}"})
if [ "$DRY" = 1 ]; then run "${CMD[@]}"; exit 0; fi   # a dry run writes nothing into OUT (it may be another run's)
printf '%q ' "${CMD[@]}" > "$OUT/RUN_CMD"; echo >> "$OUT/RUN_CMD"
( while sleep "${LRA_SNAPSHOT_S:-3600}"; do snapshot; done ) &
SNAP=$!
lra_log "driver: $(cat "$OUT/RUN_CMD")"
NRS=0
while :; do
  LRA_ORG_JOB=$TAG "${CMD[@]}" > >(tee -a "$OUT/driver.log") 2>&1 &
  DRIVER=$!
  wait "$DRIVER"; RC=$?
  while kill -0 "$DRIVER" 2> /dev/null; do wait "$DRIVER"; RC=$?; done   # a USR1 trap interrupts wait: wait again
  DRIVER=""
  lra_log "driver exited (rc $RC)"
  LEFT=$((JOB_END - $(date +%s)))
  # a driver that failed with time left is restarted on the same clock (it resumes every row from its saved state), after every process
  # of the failed one is gone (no row ever has two sessions in flight); at most LRA_DRIVER_RESTARTS (3), never in the last 20 min
  if [ "$RC" != 0 ] && [ "$NRS" -lt "${LRA_DRIVER_RESTARTS:-3}" ] && [ "$LEFT" -gt 1200 ]; then
    NRS=$((NRS + 1))
    "$PY" infra/orgserver/orgtools.py reap "$TAG" --grace 20 > /dev/null 2>&1
    lra_log "driver: restart $NRS of ${LRA_DRIVER_RESTARTS:-3} in 30 s (${LEFT} s left on the clock)"
    sleep 30
    continue
  fi
  break
done
[ -f "$OUT/proofs.jsonl" ] || { snapshot --promote; tail -n 1 "$OUT/logs/snapshot.log"; }
stop_all
if [ -f "$OUT/proofs.jsonl" ]; then
  lra_log "DONE: $OUT/proofs.jsonl ($(grep -c . "$OUT/proofs.jsonl") rows); summary $OUT/summary.json"
else
  lra_log "FAILED: no proofs file (logs in $OUT/logs, $OUT/driver.log)"; RC=${RC:-1}; [ "$RC" = 0 ] && RC=1
fi
exit "$RC"
