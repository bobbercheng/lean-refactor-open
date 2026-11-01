#!/usr/bin/env bash
# Build Mathlib environments for the PutnamBench toolchains (mathlib4 commits from version_info).
set -u
export PATH="$HOME/.elan/bin:$PATH"
ROOT="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT"
declare -A COMMITS=( [v4.25.0]=1ccd71f89cbbd82ae7d097723ce1722ca7b01c33 [v4.26.0]=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67 [v4.27.0]=a3a10db0e9d66acbebf76c5e6a135066525ac900 )
if [ ! -d mathlib4/.git ]; then
  echo "[$(date -Is)] cloning mathlib4 (blobless)"; git clone --filter=blob:none https://github.com/leanprover-community/mathlib4 mathlib4 || exit 1
fi
for v in v4.27.0 v4.26.0 v4.25.0; do
  c=${COMMITS[$v]}; d="mathlib-$v"
  if [ ! -d "$d" ]; then
    echo "[$(date -Is)] worktree $d @ $c"; (cd mathlib4 && git fetch -q origin "$c" && git worktree add -q "../$d" "$c") || { echo "worktree failed $v"; continue; }
  fi
  echo "[$(date -Is)] toolchain: $(cat $d/lean-toolchain)"
  (cd "$d" && time lake exe cache get) > "logs/cache-$v.log" 2>&1
  echo "[$(date -Is)] cache get $v exit=$? ; tail: $(tail -1 logs/cache-$v.log)"
  (cd "$d" && du -sh .lake 2>/dev/null)
done
echo "[$(date -Is)] DONE"
