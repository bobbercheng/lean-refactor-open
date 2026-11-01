#!/usr/bin/env bash
# Pin the upstream clones envs/<repo>.git-main to the HEADs a given A100 pass saw (recorded in its trajectories as "upstream HEAD
# (<hash> <date>)"). Their HEAD drives the "UPSTREAM" digest in the opening message (harness/leantools.py upstream_digest) and what the
# model sees via git log/show. Passes 1-3 had no digest. Passes 6-8 ran on clones made on the A100 instance; only short hashes were
# recorded, so they are resolved after a fetch.   usage: envs/pin_upstream.sh 4-5|6-8
set -euo pipefail
cd "$(dirname "$0")"
case "${1:-}" in
  4-5) declare -A PIN=([strata]=02f873ed7a89099aacae18e7b78e74ca5d4ef8db [cslib]=ea16de32af9cd93796505668672297df9c422052
                       [physlib]=bae4db68ef61fc01a190fd232f82d2ad6508164e [arklib]=35ddcaa83f683011f944f58904be779495a5709a) ;;
  6-8) declare -A PIN=([strata]=d1fc3a083 [cslib]=a3da622f [physlib]=a7b32c82 [arklib]=db7005f84) ;;   # arklib db7005f84 recorded for passes 6-7
  *) echo "usage: $0 4-5|6-8"; exit 2 ;;
esac
for r in "${!PIN[@]}"; do
  d="$r.git-main"; [ -d "$d" ] || { echo "missing $d (run harness_setup.sh / setup_projects.sh first)"; exit 1; }
  git -C "$d" cat-file -e "${PIN[$r]}^{commit}" 2>/dev/null || git -C "$d" fetch -q origin
  git -C "$d" checkout -q --detach "${PIN[$r]}" && echo "$r pinned at ${PIN[$r]}"
done
