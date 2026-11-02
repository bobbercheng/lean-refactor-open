#!/usr/bin/env bash
# GB10 fail-safe of the b104 box A/B (unit lra-b104-ab-revert): waits (bounded) until REVERT_AT (epoch) or probe/p85e/RELEASE_SEEN
# (release: ab/STOP on the box first = running pairs stop now, bests banked), then, only if the running p85e is the v3.2-ab variant
# (/workspace/p85e/ab/p85e_xloop_host.py in its cmdline), hands p85e back to v3.1 through p85e_ctl.sh handover with the saved args
# (/workspace/p85e/ab/launch.env.v31; no P85E_PY = the untouched v3.1 file). Logs to probe/b104/ab_revert.log + docs/a100_80_babysit.md.
set -u
REVERT_AT=${1:?epoch}
. /home/bobber/source/lra-a100/probe/p85e/p85e_common.sh
PLOG=/home/bobber/source/lra-f44-turncap/probe/b104/ab_revert.log
BAB=/home/bobber/source/lean-refactor/docs/a100_80_babysit.md
RS=/home/bobber/source/lra-a100/probe/p85e/RELEASE_SEEN
why="REVERT_AT $(hm "$REVERT_AT")"
plog "ab_revert armed: REVERT_AT $(hm "$REVERT_AT") UTC or $RS"
while [ "$(date +%s)" -lt "$REVERT_AT" ]; do
  [ -e "$RS" ] && { why="release (RELEASE_SEEN)"; break; }
  sleep 30
done
for try in 1 2 3 4 5 6; do resolve && break; plog "box not resolvable ($ST): retry $try"; sleep 60; done
[ "${ST:-}" = running ] || { plog "box not running ($ST): nothing to revert"; exit 0; }
if [ "$why" = "release (RELEASE_SEEN)" ]; then bsh "mkdir -p /workspace/p85e/ab && touch /workspace/p85e/ab/STOP && echo stop-ok" 60 | grep -q stop-ok && plog "ab/STOP touched (release)"; sleep 40; fi
pid=$(bsh "cat /workspace/p85e/xloop.pid 2>/dev/null" 60 | tr -d '\r' | tail -n 1)
cmd=$(bsh "tr '\\0' ' ' < /proc/$pid/cmdline 2>/dev/null" 60 | tail -n 1)
if ! grep -q "/workspace/p85e/ab/p85e_xloop_host" <<< "$cmd"; then plog "running p85e pid ${pid:-none} is not the AB variant ($cmd): nothing to revert"; exit 0; fi
out=$(bsh 'cd /workspace/p85e && mapfile -t A < ab/launch.env.v31 && bash p85e_ctl.sh handover "${A[@]}" 2>&1 | tail -n 3; md5sum p85e_xloop_host.py; cat launch.env | tr "\n" " "' 420)
plog "revert ($why): $out"
( flock -w 120 9 || exit 0; echo "- $(date -u +%H:%M) UTC b104 box A/B revert (unit lra-b104-ab-revert, $why): p85e handed back to v3.1 with the saved args: $(tr '\n' ' ' <<< "$out" | cut -c1-400)" >> "$BAB" ) 9>/tmp/babysit.lock
