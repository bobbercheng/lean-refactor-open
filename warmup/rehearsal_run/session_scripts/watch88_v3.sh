#!/usr/bin/env bash
# watch88 v3 (2026-10-31 23:50 UTC; operator 23:40 "Keep A100 do warm-up climbing until the board is reset on Nov 1"): the v2 cycle
# unchanged (union pick = probe/a100-upload/pick_union.py over the base runs + the allowlisted verified open-line candidates, base pick as
# the fallback, `launch` of lra-union-measure when winners are pending; one "HH:MM mean" line per cycle in probe/a100-upload/watch88.log,
# read by the W&B tracer), with: THR 87.86 (above the open board's top score at the time, 87.84), END 2026-11-02 00:30 UTC, and a wake on the
# board guard's marker probe/a100-upload/climb/BOARD_RESET (checked every 30 s). Wakes the coordinator by printing ONE line and exiting:
#   REACHED <mean> (>= 87.86)      the stored union pick reached the bar (the coordinator measures + decides; no upload here)
#   BOARD_RESET <evidence>         a board reset was confirmed (lra-climb-guard or lra-warmup-resetwatch; climb_stop.sh board-reset ran)
# v3.1 (2026-11-01 00:45 UTC, review fix): also wakes on probe/p85e/BOARD_RESET (lra-warmup-resetwatch's own marker; it now writes the
# climb marker too), and re-checks both markers right before printing REACHED (a reset during the pick wins: no REACHED after a reset).
#   END <mean>                     the END time passed
# Single instance across versions: flock on the SAME lock as v2 (watch88.lock), waiting up to 15 min for a stopped v2 (its sleep child may
# hold the lock up to 600 s). v2 = watch88.sh.v2 (= watch88.sh), v1 = watch88.sh.v1-base.
cd /home/bobber/source/lra-a100
S="<scratchpad>"
exec 9>$S/watch88.lock; flock -w 900 9 || { echo "watch88 lock still held after 15 min (is v2 task bqkz29a0d still running? pid $(cat $S/watch88.pid 2>/dev/null))"; exit 0; }
echo $$ > $S/watch88.pid
THR=87.86
MARK=probe/a100-upload/climb/BOARD_RESET; MARK2=probe/p85e/BOARD_RESET
reset_seen() { [ -f $MARK ] || [ -f $MARK2 ]; }
END=$(date -d "2026-11-02 00:30 UTC" +%s); mkdir -p probe/a100-reh-p85b-blind/out probe/a100-upload/union
BASE_RUNS="probe/a100-reh-p85/out probe/a100-reh-p85b/out probe/a100-upload/squeeze-out probe/a100-reh-p85b-blind/out"
echo "$(date -u +%H:%M) watch88 v3 start (THR $THR, END 2026-11-02 00:30Z)" >> probe/a100-upload/union/launch.log
why=END
while [ $(date +%s) -lt $END ]; do
  reset_seen && { why=BOARD_RESET; break; }
  read IP P < $S/ia_ssh.txt
  timeout 300 rsync -az --timeout=60 -e "ssh -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o ConnectTimeout=20 -o LogLevel=ERROR -p $P" root@$IP:/workspace/out-blind/work probe/a100-reh-p85b-blind/out/ 2>/dev/null
  m=$(timeout 300 python3 probe/a100-upload/pick_union.py pick --dir probe/a100-upload/watch88 2>>probe/a100-upload/union/pick.err | head -1 | grep -oE "stored mean [0-9.]+" | awk '{print $3}')
  if [ -z "$m" ]; then
    echo "$(date -u +%H:%M) union pick FAILED, base pick used" >> probe/a100-upload/union/pick.err
    m=$(timeout 300 python3 probe/a100/warmup_upload_measure.py pick --runs $BASE_RUNS --dir probe/a100-upload/watch88-base 2>/dev/null | head -1 | grep -oE "stored mean [0-9.]+" | awk '{print $3}')
  else
    timeout 120 python3 probe/a100-upload/pick_union.py launch --dir probe/a100-upload/watch88 2>&1 | tail -1 | sed "s/^/$(date -u +%H:%M) /" >> probe/a100-upload/union/launch.log
  fi
  echo "$(date -u +%H:%M) $m" >> probe/a100-upload/watch88.log
  reset_seen && { why=BOARD_RESET; break; }
  if [ -n "$m" ] && python3 -c "import sys; sys.exit(0 if float('$m') >= $THR else 1)"; then why=REACHED; break; fi
  for i in $(seq 20); do reset_seen && break; [ $(date +%s) -ge $END ] && break; sleep 30; done
done
case $why in
  REACHED) echo "REACHED $m (>= $THR)";;
  BOARD_RESET) echo "BOARD_RESET $( { cat $MARK 2>/dev/null || cat $MARK2 2>/dev/null; } | head -c 400 | tr '\n' ' ')";;
  *) echo "END $m (2026-11-02 00:30 UTC passed)";;
esac
timeout 300 python3 probe/a100-upload/pick_union.py pick --dir probe/a100-upload/watch88 2>&1 | head -17
