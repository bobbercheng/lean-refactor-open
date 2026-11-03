#!/usr/bin/env bash
# ON the box, step A of the run-2 switch (team decision 2026-11-01 ~11:10 UTC: install the fixed package, restart vLLM, run again from the seeds).
# Stop run 1 by the package's own stop script (sessions ended by their LRA_OPK_SESSION tag; run 1 exported as a fallback record), then archive
# run 1 so run 2 can reuse every path: out-off -> out-off-run1, lra-run-off -> lra-run-off-run1, probe/runs/off-* -> probe/runs-run1/.
set -u; W=/workspace; log() { echo "[$(date -u +%T)] $*" | tee -a $W/run2_switch.log; }
log "A: stop run 1 (export only)"; bash $W/package_stop_host.sh $W/lra-run-off 0 2>&1 | tail -4 | tee -a $W/run2_switch.log
n=$(pgrep -fc '[h]arness/agent.py'); d=$(pgrep -fc '[o]pen_package.py run '); log "after stop: driver $d agent.py $n; summary: $(head -c 160 $W/out-off/summary.json 2>/dev/null)"
[ "$n" = 0 ] && [ "$d" = 0 ] || { log "ABORT: processes still alive"; exit 2; }
mv $W/out-off $W/out-off-run1 && mv $W/lra-run-off $W/lra-run-off-run1 && mkdir -p $W/lra/probe/runs-run1 && mv $W/lra/probe/runs/off-* $W/lra/probe/runs-run1/ 2>/dev/null
mkdir -p $W/lra-run-off && cp -p $W/lra-run-off-run1/rows.jsonl $W/lra-run-off-run1/heartbeats.jsonl $W/lra-run-off-run1/heartbeats.jsonl.meta.json $W/lra-run-off/ 2>/dev/null
log "archived: $(ls -d $W/out-off-run1 $W/lra-run-off-run1 | tr '\n' ' ') runs-run1 $(ls $W/lra/probe/runs-run1 | wc -l) dirs; new RUN_DIR has $(ls $W/lra-run-off | tr '\n' ' ')"
