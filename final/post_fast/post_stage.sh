#!/bin/bash
# post_stage.sh OUT ROWS HEARTBEATS WORK JOB_END: the fast post stage, started by run.sh once vLLM has stopped (POST-HOC 2026-11-06, CHANGE.md).
# It is run_T0.sh, the runner of the measured run T0b, at launch_T0b.sh's values, with the /workspace paths as arguments, this run's picks
# as the input and the stop from the job clock. New here: the guards and the merges into proofs.jsonl, every 5 min and at the end. It always exits 0.
set -u
ulimit -n "$(ulimit -Hn)"
OUT=$1; ROWS=$2; HBS=$3; O=$4; JOB_END=$5
SC=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
cd "$SC" || exit 0
CODE=$(dirname "$SC"); PICKS=$OUT/proofs.picks.jsonl
D=""; STOP=0; trap 'STOP=1; [ -n "$D" ] && kill -TERM "$D" 2> /dev/null' TERM
save() {   # one merge of what the logs hold now; rows only rise, and a failure leaves proofs.jsonl as it is
  E=$O/emit/snapshot_inf.jsonl; rm -f "$E"
  python3 "$SC/snapshot.py" "$PICKS" inf "$O" --adopt-dir --emit "$O/emit" > "$O/emit.json" 2>&1
  [ -s "$E" ] || E=$O/proofs.post.jsonl
  python3 "$SC/merge_post.py" "$E" "$ROWS" "$OUT/proofs.jsonl"
}
[ ! -f "$OUT/proofs.merged.jsonl" ] || python3 "$SC/merge_post.py" "$OUT/proofs.merged.jsonl" "$ROWS" "$OUT/proofs.jsonl"   # a re-run's driver wrote the picks back: the saved gains return first
[ $((JOB_END - 60 - $(date +%s))) -ge 60 ] || { echo "skipped: under 1 min to the stop; proofs.jsonl stays the picks"; exit 0; }
mkdir -p "$O" && cp -f "$OUT/proofs.jsonl" "$PICKS" || exit 0
export LRA_POST_MERGE=1 LRA_FORCE_WARN_SORRY=1 LRA_HG_GATE=1 LRA_HG_PERSIST=1 PF_SPEC_NEXT=1 PF_SPEC_NEXT_AHEAD=1
export LRA_HG_STATE_DIR=$O/hgstate; mkdir -p "$LRA_HG_STATE_DIR"
W=$O/pri.json; python3 -c "import json,math,sys; print(json.dumps({r['name']: math.sqrt((r.get('heartbeats') or 0)*(r.get('tokens') or 0)) for r in map(json.loads, filter(str.strip, open(sys.argv[1])))}))" "$PICKS" > "$W" || echo '{}' > "$W"
export LRA_PREFIX_ROOT=${LRA_PREFIX_ROOT:-$O/prefix-root}; mkdir -p "$LRA_PREFIX_ROOT"
# the prefix servers' driver runs from build/ under that root, and a container's /dev/shm is often noexec (Docker's default): then only build/ moves to the code tree, which run.sh already executes from
cp -f /bin/true "$LRA_PREFIX_ROOT/.x" 2> /dev/null; "$LRA_PREFIX_ROOT/.x" 2> /dev/null || { mkdir -p "$CODE/.lra/prefix-build" && ln -sfn "$CODE/.lra/prefix-build" "$LRA_PREFIX_ROOT/build"; echo "the work dir is noexec: prefix builds in $CODE/.lra/prefix-build"; }
rm -f "$LRA_PREFIX_ROOT/.x"
LRA_PREFIX_MAX_SERVERS=${LRA_PREFIX_MAX_SERVERS:-120} python3 "$SC/pf_svc.py" --sock "$O/svc.sock" --slots 48 --log "$O/svc.log" --ahead-draws --backend "$SC/prefix_backend.py" &
SVC=$!
for i in $(seq 1 60); do [ -S "$O/svc.sock" ] && break; sleep 1; done
[ -S "$O/svc.sock" ] && [ "$STOP" = 0 ] || { kill "$SVC" 2> /dev/null; echo "no compile service, or stopped: proofs.jsonl stays the picks"; exit 0; }
date -u +%FT%TZ > "$O/START"
CAP=$((JOB_END - 60 - $(date +%s)))
timeout -k 5 $((CAP + 35)) python3 "$SC/pf_drive.py" --code "$CODE" --rows "$ROWS" --heartbeats "$HBS" --input "$PICKS" --out "$O" \
  --sock "$O/svc.sock" --worker "$SC/pf_worker.py" --weights "$W" --wall 0 --next-ops --cap "$CAP" &
D=$!
N=0; while kill -0 "$D" 2> /dev/null; do sleep 1; N=$((N + 1)); [ $((N % ${LRA_POST_SAVE_S:-300})) != 0 ] || save; done   # one process: one merge at a time
kill "$SVC" 2> /dev/null
trap '' TERM   # from here on no TERM stops the final merge; its children inherit this
save
mkdir -p "$OUT/logs/post" && timeout 60 cp -f "$O"/*.log "$O"/*.jsonl "$O"/*.json "$E" "$OUT/logs/post/" 2> /dev/null
exit 0
