#!/usr/bin/env bash
# ON the NC box: p85b relaunch after the 16:40 outbid (the onstart hook failed: relaunch.sh lost its exec bit in the GCS restore).
# Operator 2026-10-31 ~16:57 UTC "take all possible solutions ... reach 90": with no driver alive, raise --workers 12 -> 15 (every row
# at once) and --max-sessions 6 -> 12 (rows near the cap) in RUN_CMD; job clock unchanged (agent deadline 01:15, end 04:00).
set -u
R=/workspace/lra-run-p85b
pgrep -f "[o]pen_package.py run" > /dev/null && { echo "a driver is alive: not touching RUN_CMD"; exit 1; }
cp $R/RUN_CMD $R/RUN_CMD.before-w15-$(date -u +%H%M)
sed -i -e 's/--workers 12/--workers 15/' -e 's/--max-sessions 6/--max-sessions 12/' $R/RUN_CMD
grep -oE -- "--(workers|max-sessions) [0-9]+" $R/RUN_CMD | tr '\n' ' '; echo
chmod +x $R/relaunch.sh
cd /workspace/lra && RUN_DIR=$R setsid nohup bash $R/relaunch.sh >> $R/relaunch.out 2>&1 < /dev/null &
echo "relaunch started (waits for READY)"
