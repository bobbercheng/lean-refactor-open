#!/usr/bin/env bash
# GB10 unit lra-p85e-wbpush (p85e phase 1 feed + mirror + guard), v3 (2026-11-01 ~00:00 UTC): every 300 s until END_AT + 5 min (END_AT =
# probe/p85e/END_AT, re-read every round, default and cap 2026-11-02 00:00 UTC; hard end 00:10 Nov 2) or until the final is through
# (probe/p85e/FINAL_DONE; the final also stops this unit):
#   * re-resolve box 58565100 from vastai (NOT from probe/a100-instance-id); exit only when 58565100 is confirmed gone (3 checks 60 s apart);
#   * push probe/p85c/squeeze_best.jsonl to /workspace/p85c/squeeze_best.jsonl (tmp + mv; the box loop merges it every 300 s);
#   * mirror /workspace/p85e into probe/a100-reh-p85e/ (pick root probe/a100-reh-p85e/twin) and pull OUT/work + run dirs p85b-c* / p85b-t*
#     into probe/a100-reh-p85b (the watch stops pulling once the driver's summary.json exists and it blocks on the hold);
#   * v3: the box's /workspace/p85e/END_AT is synced to the GB10 END_AT when they differ (heals a missed push / a restored disk);
#   * if p85e is dead (no pid, no STOP) while END_AT is more than 30 min away and no final is triggered: start it again with its saved
#     launch.env (a box restart / outbid), at most 6 times in total (count in probe/p85e/relaunch.count, which v2 started; v3 adds 3).
# Single instance: flock /tmp/p85e-wbpush.lock. RuntimeMaxSec from the absolute end by the launcher (p85e_units_v3.sh).
set -u
. "${P85E_DIR:-/home/bobber/source/lra-a100/probe/p85e}/p85e_common.sh"
PLOG=$ROOT/probe/p85e/wbpush.log
exec 9> "$LOCKDIR/p85e-wbpush.lock"; flock -n 9 || { plog "another wbpush holds $LOCKDIR/p85e-wbpush.lock: exit"; exit 0; }
HARD=${P85E_WB_HARD:-$((CAP_EPOCH + 600))}; ROUND_S=${P85E_ROUND_S:-300}; GONE_S=${P85E_GONE_S:-60}; MAXREL=${P85E_MAXREL:-6}
RCF=$ROOT/probe/p85e/relaunch.count; relaunches=$(cat "$RCF" 2>/dev/null); case "$relaunches" in (*[!0-9]*|"") relaunches=0;; esac
wb_end() { local e; e=$(( $(end_at) + 300 )); [ $e -gt "$HARD" ] && e=$HARD; echo $e; }
gone=0
mkdir -p "$MIR" "$REH/out/work" "$REH/runs"
plog "wbpush v3 up (end END_AT+5min = $(hm "$(wb_end)") UTC, hard $(hm "$HARD"); auto-relaunches used $relaunches/$MAXREL)"
while [ "$(date +%s)" -lt "$(wb_end)" ] && [ ! -e "$FINAL_DONE" ]; do
  resolve; rc=$?
  if [ $rc = 2 ]; then
    gone=$((gone + 1)); plog "instance $ID0 not in vastai's instance list ($gone/3)"
    [ $gone -ge 3 ] && { plog "instance $ID0 gone (destroyed): wbpush exits"; exit 0; }
    sleep "$GONE_S"; continue
  fi
  gone=0
  if [ $rc != 0 ]; then plog "box not reachable ($ST $IP:$PT): skip this round"; sleep "$ROUND_S"; continue; fi
  if timeout 90 scp $SOPT -P "$PT" -q probe/p85c/squeeze_best.jsonl "root@$IP:/workspace/p85c/squeeze_best.jsonl.p85e-new" 2>/dev/null \
     && bsh "mv /workspace/p85c/squeeze_best.jsonl.p85e-new /workspace/p85c/squeeze_best.jsonl && echo ok" 60 | grep -q ok; then
    push_="pushed $(wc -l < probe/p85c/squeeze_best.jsonl) bests"
  else push_="PUSH FAILED (old file kept on the box)"; fi
  pull_p85e; prc=$?
  late=$(pull_late)
  r=$(bsh "bash /workspace/p85e/p85e_ctl.sh alive; bash /workspace/p85e/p85e_ctl.sh get-end" 60)
  st=$(head -n 1 <<< "$r"); be=$(awk '/^END_AT/{print $2}' <<< "$r"); ge=$(end_at); sync_=""
  if [ -n "$r" ] && [ "${be:-none}" != "$ge" ]; then sync_="; END_AT box ${be:-none} -> $(push_end "$ge" wbpush-sync | awk '{print $2}')"; fi
  now=$(date +%s)
  if [ "$st" = dead ] && [ $((ge - now)) -gt 1800 ] && [ ! -e "$FINAL_NOW" ] && [ "$relaunches" -lt "$MAXREL" ]; then
    relaunches=$((relaunches + 1)); echo "$relaunches" > "$RCF"; out=$(bsh "bash /workspace/p85e/p85e_ctl.sh start-last" 120 | tail -n 1)
    plog "p85e was DEAD (no pid, no STOP): auto-relaunch $relaunches/$MAXREL with launch.env: $out"
  fi
  plog "$push_; mirror rc $prc; late pull $late; p85e $st$sync_; last: $(tail -n 1 "$MIR/xloop.log" 2>/dev/null | cut -c1-160)"
  w=0; while [ $w -lt "$ROUND_S" ] && [ ! -e "$FINAL_DONE" ]; do sleep 10; w=$((w + 10)); done
done
plog "wbpush end ($( [ -e "$FINAL_DONE" ] && echo 'final done' || echo "END_AT+5min $(hm "$(wb_end)")")): exits"
