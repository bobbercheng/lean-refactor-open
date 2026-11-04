#!/usr/bin/env bash
# Clone the four project repos (blobless) and create a worktree per pinned commit. No builds yet.
set -u
export PATH="$HOME/.elan/bin:$PATH"
cd "$(dirname "$0")"
mkdir -p logs
declare -A URL=( [strata]=https://github.com/strata-org/Strata [cslib]=https://github.com/leanprover/cslib [physlib]=https://github.com/leanprover-community/physlib [arklib]=https://github.com/Verified-zkEVM/ArkLib )
declare -A COMMITS=(
  [strata]="v4.26.0:451e5f047bafa010d178856db76c00029bfa4d7f v4.27.0:4348c65a93a3b57b1a4541991ed2d2fcdd9fa35d v4.29.1:384e22374e0872095ad9c6f74c5998c09cfd93a9"
  [cslib]="v4.33.0-rc2:3aa9d4416c185e0b9faeb72bbd65abe85b95dbcc v4.32.0:197a7be621263b84c67ca4f803f69205b36d06df v4.31.0:8ea71c8df91acd63285515a04da952b23b78d266 v4.30.0:c7944a9fb44c3298f1a960a5e574ab23a6ab8ed5"
  [physlib]="v4.32.0:c48433678e8fb6306ebcd48453300c8e16058a62"
  [arklib]="v4.31.0:c1712f6c496d0aef04f09bae42aec13811b3273f v4.30.0:e6d77b18ca1334a91faf4d1ccf9f96d854d58ba4 v4.29.0:de71a9dfd2f5a343e8895517b7efe857d9f1ce5c v4.28.0:673fa440714eb1949b8b50a28f2a4f52b1837e9b"
)
for p in strata cslib physlib arklib; do
  if [ ! -d "$p.git-main/.git" ]; then
    echo "[$(date -Is)] clone $p"; git clone -q --filter=blob:none "${URL[$p]}" "$p.git-main" || { echo "clone failed $p"; continue; }
  fi
  for vc in ${COMMITS[$p]}; do
    v=${vc%%:*}; c=${vc##*:}; d="$p-$v"
    if [ ! -d "$d" ]; then
      (cd "$p.git-main" && git fetch -q origin "$c" 2>/dev/null; git worktree add -q "../$d" "$c") || { echo "worktree failed $d"; continue; }
    fi
    echo "== $d  toolchain=$(cat $d/lean-toolchain 2>/dev/null)  mathlib=$(python3 -c "
import json,sys
try:
  m=json.load(open('$d/lake-manifest.json'))
  pk=[x for x in m.get('packages',[]) if x.get('name')=='mathlib']
  print(pk[0].get('rev','?')[:12] if pk else 'none')
except Exception as e: print('no-manifest')
")  pkgs=$(python3 -c "
import json
try: print(','.join(x['name'] for x in json.load(open('$d/lake-manifest.json')).get('packages',[])))
except Exception: print('?')
")"
  done
done
echo "[$(date -Is)] DONE"; du -sh . 2>/dev/null
