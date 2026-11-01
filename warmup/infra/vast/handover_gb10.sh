#!/usr/bin/env bash
# Harness handover, GB10 side. Waits for the GB10 chain to finish
# pass $1, stops the chain within ~2 s (before the next pass's agents do any work), removes that next pass's run entries from the line's
# states (0 attempts, so they cannot count as flat runs), archives its run dir as aborted-*-handover, then stops the GB10 sidecar, whose
# SIGTERM handler pushes a final snapshot to GCS. The instance then restores from the bucket alone and continues.
#   infra/vast/handover_gb10.sh 5
set -u
cd "$(dirname "$0")/../.." || exit 2
P=${1:?pass after which to hand over}; N=$((P + 1)); L=probe/a100-80-chain.log
log() { echo "[$(date -u -Is)] handover: $*" | tee -a probe/a100-handover.log; }
log "waiting for 'after pass $P: assembled' in $L"
until grep -q "after pass $P: assembled [0-9]" "$L"; do
  systemctl --user is-active -q lra-a100-80-chain || { log "chain ended before pass $P finished: $(tail -n 1 "$L")"; exit 1; }
  sleep 2
done
systemctl --user stop lra-a100-80-chain
log "chain stopped right after: $(grep "after pass $P: assembled [0-9]" "$L" | tail -1 | cut -c1-120)"
sleep 3
python3 - "$N" <<'EOF'
import json, pathlib, sys
rid = f"fresh-a100-p{sys.argv[1]}"; n = att = 0
for st in pathlib.Path("harness/work_fresh-a100").glob("*/state.json"):
    s = json.loads(st.read_text()); r0, a0 = len(s.get("runs", [])), len(s.get("attempts", []))
    s["runs"] = [x for x in s.get("runs", []) if (x.get("run_id") if isinstance(x, dict) else x) != rid]
    att += sum(1 for a in s.get("attempts", []) if a.get("run_id") == rid)
    if len(s["runs"]) != r0:
        st.write_text(json.dumps(s, ensure_ascii=False)); n += 1
print(f"removed the {rid} run entry from {n} states ({att} attempts had been recorded)")
EOF
[ -d "probe/runs/fresh-a100-p$N" ] && mv "probe/runs/fresh-a100-p$N" "probe/runs/aborted-fresh-a100-p$N-handover"
[ -f "probe/fresh-a100-p$N.log" ] && mv "probe/fresh-a100-p$N.log" "probe/aborted-fresh-a100-p$N-handover.log"
python3 bank/import_verified.py > /dev/null 2>&1
log "line after pass $P: $(python3 assemble/best.py --include-dev-only --only-run-prefix fresh-a100- | head -1 | cut -c1-40)"
systemctl --user stop lra-sidecar
log "GB10 sidecar stopped (final snapshot pushed): $(tail -n 1 probe/a100-sidecar.log | cut -c1-120)"
log "READY FOR INSTANCE: restore a100-80-dev on the instance and start passes $N-7 there"
