#!/usr/bin/env bash
# LeanPool env (sixth library, organizer note 2026-10-24): envs/leanpool.git-main (blobless clone of
# https://github.com/LeanPool/lean-pool) + one worktree per pinned commit, envs/leanpool-<toolchain>.
# Usage: build_leanpool.sh [cache|projects <P1 P2 ...>|full] — run inside a 48G unit; lake 5 (v4.35) has no --jobs flag: its job count is Lean's task-manager thread count, bounded here with LEAN_NUM_THREADS=${LRA_LAKE_JOBS:-2}.
# `cache` pulls the Mathlib oleans (lake exe cache get) + builds the TauCeti dependency; `projects` builds the named
# LeanPool.<P> aggregates (minutes each; projects are independent); `full` is `lake build LeanPool` (resumable: rerun until exit 0).
set -u
export PATH="$HOME/.elan/bin:$PATH"; cd "$(dirname "$0")"
V=${LRA_LEANPOOL_V:-v4.35.0-rc3}; d=leanpool-$V; J=${LRA_LAKE_JOBS:-2}; mkdir -p logs
case "${1:-cache}" in
  cache)
    echo "[$(date -Is)] cache $d"; ( cd $d && lake exe cache get ) > logs/cache-$d.log 2>&1; echo "[$(date -Is)] cache exit=$? $(tail -1 logs/cache-$d.log)"
    echo "[$(date -Is)] deps $d"; ( cd $d && LEAN_NUM_THREADS=$J lake build TauCeti ) > logs/deps-$d.log 2>&1; echo "[$(date -Is)] deps exit=$? $(tail -1 logs/deps-$d.log)" ;;
  projects)
    shift; for P in "$@"; do
      echo "[$(date -Is)] build $d LeanPool.$P"; ( cd $d && LEAN_NUM_THREADS=$J lake build LeanPool.$P ) > logs/build-$d-$P.log 2>&1
      echo "[$(date -Is)] LeanPool.$P exit=$? $(tail -1 logs/build-$d-$P.log)"
    done ;;
  full)
    echo "[$(date -Is)] full build $d (resumable)"; ( cd $d && LEAN_NUM_THREADS=$J lake build LeanPool ) > logs/fullbuild-$d.log 2>&1
    echo "[$(date -Is)] full exit=$? $(tail -1 logs/fullbuild-$d.log)" ;;
esac
du -sh $d/.lake 2>/dev/null; echo DONE
