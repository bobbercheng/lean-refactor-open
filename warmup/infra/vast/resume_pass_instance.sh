#!/usr/bin/env bash
# Resume the on-instance chain after vast stopped the instance mid-pass (an outbid, 2026-10-09 ~04:42 during pass 6). A stop kills every
# process (agents, chain, sidecar, W&B updater); on resume vast restarts only the model server. Runs ON the instance from /workspace/lra:
#   1. restarts the GCS sidecar first when its key exists (optional), so whatever was written before the stop is pushed;
#   2. waits until the model answers a real call through the harness's own client (TLS set up as in chain_on_instance.sh);
#   3. finishes pass PASS for every problem whose session did not finish (no `end` record), including sessions a stop cut short
#      (cycle 79, A100 deep dive: cut sessions were the main reason the line stopped at 81.72): same run id and flags as replicate.sh,
#      `--problems` for the subset; the cut session's run entry is removed first (its attempts stay), so it is not a 'flat run';
#   4. logs "after pass PASS" as the chain does, then starts the W&B live updater and hands over to chain_on_instance.sh PASS+1 LAST.
#   setsid nohup infra/vast/resume_pass_instance.sh 6 7 > /dev/null 2>&1 < /dev/null &
# PASS may be "auto" or "auto:FLOOR" (pass 8 run, 2026-10-09): the last pass the chain log shows starting or being finished, never below
# FLOOR, so one armed watcher resumes correctly whichever pass a stop cuts.
set -u
cd "$(dirname "$0")/../.." || exit 2
export PATH="$HOME/.elan/bin:/opt/google-cloud-sdk/bin:$PATH"
PASS=${1:?pass to finish}; LAST=${2:?last pass}; L=probe/a100-80-chain-instance.log
log() { echo "[$(date -u -Is)] $*" >> "$L"; }
# never a second harness beside a live one (2026-10-09 review: a false stop, e.g. vast status "offline" while the container runs, or a
# migrate re-run); checked before the "resume after a vast stop" line so finalize's chain-done counter is not reset
# anchored to "bash <script>": the launching ssh wrapper ("bash -c '... resume_pass_instance.sh ...'") may still be alive for a moment
if pgrep -f "^(/usr/bin/|/bin/)?bash [^ ]*(chain_on_instance|replicate)\.sh|^python3 harness/agent\.py" > /dev/null \
   || pgrep -f "^(/usr/bin/|/bin/)?bash [^ ]*resume_pass_instance\.sh" | grep -vqx "$$"; then
  log "resume refused: a chain or agent is still running on this instance"; exit 0
fi
floor=0
if [ "${PASS%%:*}" = auto ]; then   # auto[:FLOOR]: never below FLOOR (a stop before the chain logged "pass FLOOR starts" must not reopen the closed pass before it)
  [ "$PASS" != auto ] && floor=${PASS#auto:}
  PASS=$( (grep -oE "pass [0-9]+ starts|finishing pass [0-9]+" "$L" 2>/dev/null | grep -oE "[0-9]+"; echo "$floor") | sort -n | tail -n 1)
  [ "${PASS:-0}" -gt 0 ] || { log "STOP: resume with PASS=auto but the chain log names no pass"; exit 1; }
fi
RUN=fresh-a100-p$PASS
num() { python3 assemble/best.py --include-dev-only --only-run-prefix fresh-a100- | head -1 | grep -oE '[0-9]+\.[0-9]+' | head -1; }
log "resume after a vast stop: finishing pass $PASS, then passes $((PASS + 1))-$LAST"
SP=$PASS; [ "$floor" -gt 0 ] && [ "$floor" -lt "$PASS" ] && SP=$floor   # the sidecar keeps every pass of this launch (a stop right after
                                                                       # "pass 9 starts" must not strand pass 8's last writes)
. infra/vast/endpoint.sh
if gcs_on; then
  pgrep -f "[i]nfra/sync/sidecar.py" > /dev/null || setsid nohup python3 -u infra/sync/sidecar.py --label a100-80-dev \
    --watch "probe/runs/fresh-a100-p*/verified.jsonl" --paths $(sidecar_paths "$SP" "$LAST") >> probe/a100-sidecar-instance.log 2>&1 < /dev/null &
else log "resume: GCS backup off (no key; optional)"; fi
pre=""
for i in $(seq 1 60); do   # the server reloads the model after a restart (minutes)
  pre=$(preflight)
  [ "$pre" = ok ] && break; sleep 30
done
[ "$pre" = ok ] || { log "STOP: the model did not answer within 30 min of the resume: $pre"; exit 1; }
log "resume: model answers again (real call); agent flags: ${LRA_AGENT_FLAGS:-none}"
prev=$(num)
todo=$(python3 - "$RUN" <<'EOF'
import gzip, json, pathlib, sys
run = sys.argv[1]; worked = set()
for f in pathlib.Path(f"probe/runs/{run}/trajectories").glob("*.jsonl*"):
    try:
        op = gzip.open if f.suffix == ".gz" else open
        recs = [json.loads(l) for l in op(f, "rt", errors="replace") if l.strip().startswith("{")]
    except Exception:  # noqa: BLE001
        continue
    head = next((r for r in recs if r.get("type") == "header"), {})
    if any(r.get("type") == "end" for r in recs):   # cycle 79: only a finished session counts; a session a stop cut short is re-run
        worked.add(head.get("problem"))
names = [json.loads(l)["name"] for l in open("data/benchmark_warmup.jsonl") if l.strip()]
todo = [n for n in names if n not in worked]
for st in pathlib.Path("harness/work_fresh-a100").glob("*/state.json"):   # drop the cut session's run entry (its attempts stay), so the
    s = json.loads(st.read_text())                                         # re-run is not seen as a second, "flat" run (A100 deep dive)
    if s.get("problem") not in todo:
        continue
    runs = [r for r in s.get("runs", []) if (r.get("run_id") if isinstance(r, dict) else r) != run]
    if len(runs) != len(s.get("runs", [])):
        s["runs"] = runs; st.write_text(json.dumps(s, ensure_ascii=False))
print(" ".join(todo))
EOF
)
if [ -n "$todo" ]; then
  log "resume: pass $PASS for the $(wc -w <<< "$todo") problems that never took a turn in it: $todo"
  python3 harness/agent.py --turns 40 --workers 4 --max-tokens 4000 --model glm-5.3-flash --reasoning-effort low --endpoint openai \
    --quant nvfp4 --work-root harness/work_fresh-a100 --run-id "$RUN" $AGENT_EXTRA --problems $todo >> "probe/$RUN.log" 2>&1
else
  log "resume: every problem had already worked in pass $PASS"
fi
python3 bank/import_verified.py > /dev/null 2>&1
n=$(grep -c ' DONE ' "probe/$RUN.log" 2>/dev/null); sc=$(num)
log "after pass $PASS: assembled $sc (gain $(python3 -c "print(round($sc - $prev, 2))") in the resumed part), $n/15 problems DONE (resumed after a vast stop; the cut-short sessions have no DONE)"
wandb_on && ! pgrep -f "[w]andb_live.sh" > /dev/null && setsid nohup infra/sync/wandb_live.sh $(seq -f "fresh-a100-p%g" "$PASS" "$LAST" | tr '\n' ' ') \
  >> probe/wandb-live-instance.out 2>&1 < /dev/null &
[ "$PASS" -lt "$LAST" ] && exec infra/vast/chain_on_instance.sh "$((PASS + 1))" "$LAST"
log "chain done at $(num); waiting for release from the GB10"
