#!/usr/bin/env bash
# ON the A100 host: stop a package run at any time WITHOUT losing a banked best, and leave it finished (proofs.jsonl + summary.json), so
# neither relaunch.sh (onstart.sh's /workspace/lra-run*/relaunch.sh hook) nor the GB10 watch restarts it (2026-10-31: p85b is stopped this
# way before the official run; docs/open_official_run_runbook.md).
#   bash /workspace/package_stop_host.sh RUN_DIR [END_S]
#     RUN_DIR  the run's directory (RUN_CMD, RUN_ENV: OUT, EXPORT_ROOT), e.g. /workspace/lra-run-p85b
#     END_S    0 (default): export only (each row: the run's valid end-stage / pipeline polish of its CURRENT best, else the agent best, else
#              the seed; normalize records; sorry audit); N > 0: the end stage (R5 clock N s) + normalize + export first
# Steps: (1) a placeholder OUT/summary.json when none exists (relaunch.sh and package_watch.sh read "finished" from it at once); (2) the
# driver frozen (SIGSTOP, by pid) so it starts nothing new; (3) every process the driver's sessions started (environment tag
# LRA_OPK_SESSION=<driver pid>-..., open_package.run_session) gets SIGTERM by process group, SIGKILL after 15 s: agent.py saves a row's best
# on every new best, so the banked bests are in OUT/work/<row>/state.json; (4) the driver killed by pid; (5) open_package.py export (or end)
# with the run's own rows, heartbeats, tag and job clock; its summary.json replaces the placeholder. vLLM, the sidecars and other runs are
# never touched. Idempotent: no driver and a real summary.json = nothing to do (exit 0).
set -u
RUN_DIR=${1:?RUN_DIR}; END_S=${2:-0}
[ -f "$RUN_DIR/RUN_CMD" ] || { echo "no $RUN_DIR/RUN_CMD"; exit 2; }
. "$RUN_DIR/RUN_ENV"; OUT=${OUT:?RUN_ENV without OUT}; EXPORT_ROOT=${EXPORT_ROOT:-/workspace/lra}
L=$RUN_DIR/stop.log; log() { echo "[$(date -u -Is)] stop: $*" | tee -a "$L"; }
CMD=$(cat "$RUN_DIR/RUN_CMD")
arg() { sed -n "s/.*$1 \([^ ]*\).*/\1/p" <<< "$CMD"; }
ROWS=$(arg --rows); HBS=$(arg --heartbeats); TAG=$(arg --tag); ST=$(arg --started-at); JS=$(arg --job-seconds)
D=$(pgrep -f "[o]pen_package.py run .*--out $OUT " | tr '\n' ' ')
if [ -z "$D" ] && [ -f "$OUT/summary.json" ] && ! grep -q '"placeholder"' "$OUT/summary.json"; then log "nothing to do: no driver, $OUT/summary.json exists"; exit 0; fi
[ -f "$OUT/summary.json" ] || { printf '{"placeholder": "stopped by package_stop_host.sh at %s; export pending"}\n' "$(date -u -Is)" > "$OUT/summary.json"; log "placeholder summary.json written (no relaunch from now)"; }
if [ -n "$D" ]; then
  log "driver $D: SIGSTOP"; kill -STOP $D 2>/dev/null
  tagged() { local p d; for p in /proc/[0-9]*; do for d in $D; do grep -qa "LRA_OPK_SESSION=$d-" "$p/environ" 2>/dev/null && { echo "${p#/proc/}"; break; }; done; done; }
  P=$(tagged | tr '\n' ' '); G=$(for p in $P; do ps -o pgid= -p "$p" 2>/dev/null; done | tr -d ' ' | sort -u | tr '\n' ' ')
  log "session processes: $(wc -w <<< "$P") in process group(s) $G: SIGTERM"
  for g in $G; do [ "$g" -gt 1 ] && kill -TERM -- "-$g" 2>/dev/null; done
  sleep 15
  P=$(tagged | tr '\n' ' '); [ -n "$P" ] && { log "still alive after 15 s: $P: SIGKILL"; kill -KILL $P 2>/dev/null; sleep 2; }
  kill -KILL $D 2>/dev/null; sleep 2
  log "after: driver $(pgrep -fc "[o]pen_package.py run .*--out $OUT ") session processes $(tagged | wc -l)"
fi
cd "$EXPORT_ROOT" || { log "no export root $EXPORT_ROOT"; exit 1; }
rm -f "$OUT/summary.json"   # export writes the real one; the placeholder must not survive a failed export unnoticed (re-run this script)
printf '{"placeholder": "export running since %s"}\n' "$(date -u -Is)" > "$OUT/summary.json"
export LRA_NO_GCS=1 LRA_NO_WANDB=1
if [ "$END_S" -gt 0 ] 2>/dev/null; then
  now=$(date +%s); J=$((END_S + 1800 + 900 + 120))
  log "end stage ${END_S}s + normalize + export (job clock restarted: now + ${J}s)"
  python3 harness/open_package.py end --rows "$ROWS" --heartbeats "$HBS" --out "$OUT" --tag "$TAG" --started-at "$now" --job-seconds "$J" --end-seconds "$END_S" >> "$RUN_DIR/driver.log" 2>&1
else
  log "export only"
  python3 harness/open_package.py export --rows "$ROWS" --heartbeats "$HBS" --out "$OUT" --tag "$TAG" ${ST:+--started-at $ST} ${JS:+--job-seconds $JS} >> "$RUN_DIR/driver.log" 2>&1
fi
rc=$?
if [ "$rc" = 0 ] && [ -f "$OUT/proofs.jsonl" ] && ! grep -q '"placeholder"' "$OUT/summary.json"; then
  log "STOPPED + exported: $(python3 -c "import json; d=json.load(open('$OUT/summary.json')); print('rows', d.get('rows'), 'stored mean', d.get('stored_mean'), 'sources', d.get('sources'))")"
else
  log "EXPORT FAILED (rc $rc): the bests are banked in $OUT/work/*/state.json; the placeholder summary.json keeps relaunches off; re-run this script"
  printf '{"placeholder": "export failed rc %s at %s"}\n' "$rc" "$(date -u -Is)" > "$OUT/summary.json"; exit 1
fi
