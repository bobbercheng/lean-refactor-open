#!/usr/bin/env bash
# Finalize the A100-80 line and release the instance (2026-10-09: once the A100 line passes 82, make sure all data is uploaded and
# shut the instance down). Runs on the GB10 as unit lra-a100-finalize. Every 60 s it reads over SSH (control only, never the data path)
# the instance's live line (assemble/live_line.py: the bank plus the running pass's verified records, scored as the chain scores them)
# and the chain log. It finalizes when the line reaches 82.00 (the running pass is stopped at once) or when the chain writes "chain done"
# (its own stop rules, or the last pass; only a "chain done" after the latest chain start or resume counts: the log restored from the bucket
# holds the closed run's "chain done at 81.72", pass 8 run 2026-10-09). An abnormal end (the chain gone without "chain done") blocks instead: the instance is kept for a
# human. Finalize:
#   1. stop the chain and its agents, import the verified records, note the official assembled line in the chain log;
#   2. W&B: stop the live updater, run one full upload (traces, turn table, files artifact) of the instance's runs;
#   3. GCS: stop the sidecar (its SIGTERM pushes a final write-through and snapshot); require "final flush ok";
#   4. restore the bucket on the GB10 alone; require it to match the instance file for file (verified records line for line);
#   5. bring the restored line into the repo, import it into the bank, commit and push;
#   6. only then destroy the instance, require it gone from `vastai show instances`, stop the bridge and health units.
# A failed step logs "FINALIZE BLOCKED at step N" and exits non-zero without destroying anything.
#   infra/vast/finalize_a100.sh INSTANCE_ID root@HOST PORT          (log: probe/a100-finalize.log)
set -u -o pipefail
cd "$(dirname "$0")/../.." || exit 2
ID=${1:?instance id}; H=${2:?ssh target}; P=${3:?ssh port}; LABEL=${LABEL:-a100-80-dev}; TARGET=${TARGET:-82.00}
# PASSES: the passes this instance ran, whose run data is uploaded and checked (pass 8 run, 2026-10-09; a pass that never ran is skipped:
# fingerprint.py and the repo copy skip missing paths, wandb_upload.py --only ignores unknown run ids)
PASSES=${PASSES:-8 9}   # this campaign's passes (6 and 7 are closed and uploaded; uploading them again would duplicate W&B trace points)
PATHS="harness/work_fresh-a100 $(for k in $PASSES; do printf 'probe/runs/fresh-a100-p%s probe/fresh-a100-p%s.log ' "$k" "$k"; done)probe/a100-80-chain-instance.log accounting/replication_fresh-a100.md"
RUNS=$(for k in $PASSES; do printf 'fresh-a100-p%s ' "$k"; done)
L=probe/a100-finalize.log
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
rsh() { ssh -i "$HOME/.ssh/id_ed25519" -o BatchMode=yes -o ConnectTimeout=20 -o ServerAliveInterval=30 -p "$P" "$H" "cd /workspace/lra; $1" 2>/dev/null | grep -v "^Welcome\|^Have fun"; }
block() { log "FINALIZE BLOCKED at step $1: $2 (instance $ID kept)"; exit 1; }

log "watching instance $ID: finalize at a live line >= $TARGET or at 'chain done'"
reason=""; quiet=0
while [ -z "$reason" ]; do
  s=$(rsh 'echo "line=$(python3 assemble/live_line.py fresh-a100-)"; echo "done=$(awk "/start: passes|chain on instance start|resume after a vast stop/{n=0} /chain done/{n++} END{print n+0}" probe/a100-80-chain-instance.log)"; pgrep -f "[c]hain_on_instance.sh|[r]esume_pass_instance.sh" > /dev/null && echo chain=up || echo chain=down')
  line=$(sed -n 's/^line=//p' <<< "$s"); dn=$(sed -n 's/^done=//p' <<< "$s"); ch=$(sed -n 's/^chain=//p' <<< "$s")
  if ! [[ "$line" =~ ^[0-9]+(\.[0-9]+)?$ ]]; then
    quiet=$((quiet + 1)); [ $((quiet % 15)) = 1 ] && log "instance unreachable or no line (outbid, network): waiting"; sleep 60; continue
  fi
  quiet=0
  if python3 -c "import sys; sys.exit(0 if $line >= $TARGET else 1)"; then reason="target: live line $line >= $TARGET"
  elif [ "${dn:-0}" -gt 0 ]; then reason="chain done ($(rsh 'grep -E "STOP|chain done" probe/a100-80-chain-instance.log | tail -n 2 | cut -c28- | tr "\n" " "'))"
  elif [ "$ch" = down ]; then block 0 "the chain is gone without 'chain done' (line $line): $(rsh 'tail -n 1 probe/a100-80-chain-instance.log')"
  else sleep 60
  fi
done
log "finalize: $reason"
[ "${DRY:-0}" = 1 ] && { log "dry run: stopping before step 1"; exit 0; }

# 1. stop the run; import; official line
rsh 'pkill -TERM -f "[c]hain_on_instance.sh|[r]esume_pass_instance.sh"; pkill -TERM -f "[r]eplicate.sh"; pkill -TERM -f "[h]arness/agent.py"
     for i in $(seq 1 45); do pgrep -f "[h]arness/agent.py" > /dev/null || break; sleep 2; done; pkill -KILL -f "[h]arness/agent.py"; true' > /dev/null
off=$(rsh 'python3 bank/import_verified.py > /dev/null && python3 assemble/best.py --include-dev-only --only-run-prefix fresh-a100- | head -1 | grep -oE "[0-9]+\.[0-9]+" | head -1')
[[ "$off" =~ ^[0-9]+\.[0-9]+$ ]] || block 1 "could not compute the official line"
rsh "echo \"[\$(date -u -Is)] finalize: official assembled line $off; run stopped; the GB10 releases the instance after the upload checks\" >> probe/a100-80-chain-instance.log"
log "step 1: run stopped; official assembled line $off"

# 2. W&B: one full upload of the instance's runs
w=$(rsh 'pkill -f "[w]andb_live.sh"; for i in $(seq 1 60); do pgrep -f "^python3 infra/sync/wandb_upload.py" > /dev/null || break; sleep 10; done
         timeout 1800 python3 infra/sync/wandb_upload.py --only '"$RUNS"' 2>&1 | tail -n 4')
grep -q "^done:" <<< "$w" || block 2 "W&B upload: $(tail -n 1 <<< "$w")"
# carry the instance's upload record for these runs into the GB10 manifest, so a later upload from here cannot duplicate trace points
rsh 'cat ~/.cache/vexorium/wandb_uploaded.json' | python3 -c "
import fcntl, json, os, sys
inst = json.load(sys.stdin); path = os.path.expanduser('~/.cache/vexorium/wandb_uploaded.json'); lock = open(path + '.lock', 'w')
fcntl.flock(lock, fcntl.LOCK_EX); man = json.load(open(path)) if os.path.isfile(path) else {}
man.update({k: v for k, v in inst.items() if k.startswith('fresh-a100-p')}); json.dump(man, open(path, 'w'), indent=0)
print(sorted(k for k in inst if k.startswith('fresh-a100-p')))" >> "$L" 2>&1 || block 2 "could not merge the instance's W&B manifest"
log "step 2: W&B full upload: $(grep -E "^(updated|done)" <<< "$w" | tr "\n" " "); manifest merged into the GB10's"

# 3. GCS: final flush
g=$(rsh 'n=$(cat probe/a100-sidecar-instance.log 2>/dev/null | wc -l)
  pgrep -f "[i]nfra/sync/sidecar.py" > /dev/null || { setsid nohup python3 -u infra/sync/sidecar.py --label '"$LABEL"' --watch "probe/runs/fresh-a100-p*/verified.jsonl" \
    --paths '"$PATHS"' accounting >> probe/a100-sidecar-instance.log 2>&1 < /dev/null & sleep 20; }
  pkill -TERM -f "[i]nfra/sync/sidecar.py"; for i in $(seq 1 120); do pgrep -f "[i]nfra/sync/sidecar.py" > /dev/null || break; sleep 2; done
  tail -n +$((n + 1)) probe/a100-sidecar-instance.log | tail -n 2')
grep -q "final flush ok" <<< "$g" || block 3 "sidecar: $(tail -n 1 <<< "$g")"
log "step 3: GCS final flush ok"

# 4. the bucket alone must hold exactly what the instance has
R=$(mktemp -d "${TMPDIR:-/tmp}/a100-final.XXXX")
infra/sync/restore.sh "$LABEL" "$R" > "$R.log" 2>&1 || block 4 "bucket restore failed: $(tail -n 1 "$R.log")"
rsh "python3 infra/sync/fingerprint.py $PATHS && echo FP-END" > "$R.instance.raw"
[ "$(tail -n 1 "$R.instance.raw")" = FP-END ] || block 4 "the instance's fingerprint list came back incomplete"
sed '$d' "$R.instance.raw" | sort > "$R.instance"
(cd "$R" && python3 "$OLDPWD/infra/sync/fingerprint.py" $PATHS) | sort > "$R.bucket"
n=$(wc -l < "$R.instance"); m=$(comm -23 "$R.instance" "$R.bucket" | wc -l)
[ "$n" -gt 0 ] && [ "$m" = 0 ] || block 4 "bucket vs instance: $m of $n instance entries missing or different in the bucket (see $R.instance, $R.bucket)"
# the sidecar never deletes, so the bucket keeps files the instance has since removed (a trajectory .jsonl is gzipped when its problem
# ends): drop them, so the repo gets exactly the instance's file set
comm -13 <(awk '{print $2}' "$R.instance" | sort -u) <(awk '{print $2}' "$R.bucket" | sort -u) | grep -v '#line$' > "$R.stale"
while read -r f; do rm -f "$R/$f"; done < "$R.stale"
log "step 4: the bucket alone holds every instance file and verified record with identical content ($n entries, 0 missing); $(wc -l < "$R.stale") stale bucket files dropped"

# 5. into the repo, the bank, GitHub
for p in $PATHS; do
  if [ -d "$R/$p" ]; then mkdir -p "$p"; rsync -a --delete "$R/$p/" "$p/"; elif [ -f "$R/$p" ]; then cp -p "$R/$p" "$p"; fi
done
python3 bank/import_verified.py > /dev/null || block 5 "bank import failed"
gb=$(python3 assemble/best.py --include-dev-only --only-run-prefix fresh-a100- | head -1 | grep -oE "[0-9]+\.[0-9]+" | head -1)
[ "$gb" = "$off" ] || block 5 "the GB10 assembles $gb from the restored data, the instance $off"
harness/push.sh "A100-80 line final: $off ($reason); data verified in GCS, W&B uploaded; instance $ID to be released" >> "$L" 2>&1 ||
  block 5 "commit/push failed"
log "step 5: repo and bank updated (GB10 assembles $gb), pushed"

# 6. release
vastai destroy instance "$ID" -y 2>&1 | grep -v DEPRECATED >> "$L"
sleep 20
vastai show instances --raw 2>/dev/null | python3 -c "import json, sys; sys.exit(1 if any(i.get('id') == $ID for i in json.load(sys.stdin)) else 0)" ||
  block 6 "instance $ID is still listed after the destroy"
systemctl --user stop lra-bridge lra-health lra-a100-bid lra-a100-sentry
log "step 6: instance $ID destroyed (gone from vastai show instances); lra-bridge, lra-health, lra-a100-bid and lra-a100-sentry stopped"
log "FINALIZE DONE: A100-80 line $off; $reason"
systemctl --user stop lra-a100-resume 2>/dev/null   # last: the looping resume watcher (LOOP=1) has nothing left to watch
