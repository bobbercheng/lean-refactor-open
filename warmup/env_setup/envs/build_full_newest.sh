#!/usr/bin/env bash
# Full builds of every project module at each repository's newest local pin (2026-10-08). The original builds compiled only the
# warm-up modules (17-40% of each repo), so most theorems in these repos could not be compiled locally: a Nov 1 readiness gap and
# the reason sealed set #2 could not be drawn from whole repositories. Runs at low CPU priority so experiments keep precedence.
export PATH="$HOME/.elan/bin:$PATH"; cd "$(dirname "$0")"
for d in cslib-v4.33.0-rc2 strata-v4.29.1 arklib-v4.31.0 physlib-v4.32.0; do
  echo "[$(date -Is)] full build $d"
  ( cd $d && nice -n 15 lake build ) > logs/fullbuild-$d.log 2>&1
  rc=$?; top=$(case ${d%%-*} in cslib) echo Cslib;; physlib) echo Physlib;; strata) echo Strata;; arklib) echo ArkLib;; esac)
  echo "[$(date -Is)] $d exit=$rc built=$(find $d/.lake/build/lib/lean/$top -name '*.olean' | wc -l)/$(find $d/$top -name '*.lean' | wc -l) $(tail -1 logs/fullbuild-$d.log | cut -c1-120)"
done; echo DONE
