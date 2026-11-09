#!/usr/bin/env bash
# start lra-climb-guard (GB10): the board-reset / hard-cap guard of the warm-up climb (climb_guard.py; RuntimeMaxSec to 2026-11-02 00:05 UTC)
set -euo pipefail
export XDG_RUNTIME_DIR=/run/user/$(id -u) DBUS_SESSION_BUS_ADDRESS=unix:path=/run/user/$(id -u)/bus
C=/home/bobber/source/lra-a100/probe/a100-upload/climb
[ -f $C/STOPPED ] && { echo "STOPPED present: not starting"; exit 1; }
RT=$(( $(date -u -d '2026-11-02 00:05:00' +%s) - $(date -u +%s) ))
systemd-run --user --unit lra-climb-guard --collect -p CPUWeight=10 -p Nice=10 -p MemoryMax=512M -p RuntimeMaxSec=$RT --working-directory=$C \
  -E PATH=$HOME/miniconda3/bin:/usr/local/bin:/usr/bin:/bin -E HOME=$HOME -E PYTHONUNBUFFERED=1 \
  -p StandardOutput=append:$C/guard.log -p StandardError=append:$C/guard.log $HOME/miniconda3/bin/python3 -u $C/climb_guard.py
echo "started lra-climb-guard (RuntimeMaxSec $RT); log $C/guard.log"
