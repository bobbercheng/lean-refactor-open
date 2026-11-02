#!/usr/bin/env bash
# Full builds of every project module at the OLDER official pins (2026-10-11, set #3 build approved by the operator). The
# 2026-10-08 full builds covered only each repository's newest pin; the older pins had 14-50% of their modules built, so most
# theorems could not be compiled there (one reason sealed set #2 is 5% multi-pin against 58% for the official rows). Nov 1 needs
# these builds anyway. Runs inside a memory-capped systemd unit (lake builds in parallel; MemoryHigh throttles before MemoryMax).
export PATH="$HOME/.elan/bin:$PATH"; cd "$(dirname "$0")"
for d in cslib-v4.32.0 cslib-v4.31.0 cslib-v4.30.0 arklib-v4.30.0 arklib-v4.29.0 arklib-v4.28.0 strata-v4.27.0 strata-v4.26.0; do
  echo "[$(date -u -Is)] full build $d"
  ( cd $d && nice -n 15 lake build ) > logs/fullbuild-$d.log 2>&1
  rc=$?; top=$(case ${d%%-*} in cslib) echo Cslib;; physlib) echo Physlib;; strata) echo Strata;; arklib) echo ArkLib;; esac)
  echo "[$(date -u -Is)] $d exit=$rc built=$(find $d/.lake/build/lib/lean/$top -name '*.olean' | wc -l)/$(find $d/$top -name '*.lean' | wc -l) $(tail -1 logs/fullbuild-$d.log | cut -c1-120)"
done; echo "[$(date -u -Is)] DONE"
