#!/usr/bin/env bash
# Pack the Lean toolchains and environments for public Kaggle datasets (operator 2026-10-09: "use Kaggle public dataset for lean env
# instead of gcp bucket as it's free for Kaggle public dataset"). Runs ON the instance, in the repo root, beside a live run (lowest CPU and
# IO priority). One folder per dataset under OUT: the toolchains, then one per project repo holding its envs (worktrees with their .lake
# builds) and its git clone; one tar.zst per toolchain / env / clone; GNU tar's index of each archive goes to OUT/index/.
# Never public: the harness's candidate files. Every LRAScratch/ is excluded, and the audit fails the pack if an archive lists LRAScratch
# or a .lean file outside .lake/ that git does not track there. Publish with infra/sync/publish_envs_kaggle.sh (on the GB10).
#   infra/sync/pack_envs.sh [OUT=/workspace/envpack]        last line of OUT/PACK.log: "PACK DONE ..." or "PACK FAILED ..."
# Subsets (review 2026-10-28, findings 4/18: publishing one new env must not re-pack 35 GB nor re-version every dataset):
#   ENVS_JSON=<file>       the environment list to pack (default infra/vast/harness_envs.json; a leanpool-only file packs just LeanPool)
#   ONLY_TOOLCHAINS="a b"  pack only these ~/.elan/toolchains entries (default: every one present); ONLY_TOOLCHAINS=none packs no toolchain and
#                          no elan-home; ONLY_ENVS="e f" packs only these envs/clones of the plan; DATASET=<name> overrides the env dataset name
#                          (all env archives into one folder, e.g. lean-env-leanpool-x86-64 is the default for repo leanpool anyway).
set -u -o pipefail
cd "$(dirname "$0")/../.." || exit 2
OUT=${1:-/workspace/envpack}; A=${ARCH:-$(uname -m | tr _ -)}; T0=$(date +%s); BAD=0   # ARCH: tests only (the GB10 is aarch64; its packs are never published)
ENVS_JSON=${ENVS_JSON:-infra/vast/harness_envs.json}; export ENVS_JSON; ONLY_TOOLCHAINS=${ONLY_TOOLCHAINS:-}; ONLY_ENVS=${ONLY_ENVS:-}; DATASET=${DATASET:-}
wanted() { [ -z "$2" ] || grep -qx "$1" <<< "$(tr ' ' '\n' <<< "$2")"; }
mkdir -p "$OUT/index"; M=$OUT/MANIFEST.tsv; printf 'dataset\tfile\traw_bytes\tpacked_bytes\tseconds\n' > "$M"
exec > >(tee -a "$OUT/PACK.log") 2>&1
pack() {   # dataset, archive name, parent dir, entry, [extra tar args]
  local ds=$1 name=$2 dir=$3 entry=$4 t; t=$(date +%s); shift 4; mkdir -p "$OUT/$ds" "$OUT/index/$ds"
  if nice -n 19 ionice -c3 tar -C "$dir" --exclude=LRAScratch "$@" --totals --index-file="$OUT/index/$ds/$name.index" -cvf - "$entry" \
       2> "$OUT/index/$ds/$name.err" | nice -n 19 zstd -T16 -6 -q > "$OUT/$ds/$name.tar.zst"; then   # raw = tar stream bytes, so exclusions count
    printf '%s\t%s\t%s\t%s\t%s\n' "$ds" "$name.tar.zst" "$(grep -oP 'Total bytes written: \K[0-9]+' "$OUT/index/$ds/$name.err")" "$(stat -c %s "$OUT/$ds/$name.tar.zst")" "$(( $(date +%s) - t ))" >> "$M"
    echo "packed $ds/$name ($(( $(date +%s) - t ))s)"
  else echo "pack $ds/$name FAILED"; BAD=$((BAD + 1)); fi
}
TC=lean4-toolchains-$A
if [ "$ONLY_TOOLCHAINS" != none ]; then
  [ -n "$ONLY_TOOLCHAINS" ] || pack "$TC" elan-home "$HOME" .elan --exclude=.elan/toolchains --exclude=.elan/tmp --exclude=.elan/downloads
  for d in "$HOME"/.elan/toolchains/*/; do wanted "$(basename "$d")" "$ONLY_TOOLCHAINS" && pack "$TC" "$(basename "$d")" "$HOME/.elan/toolchains" "$(basename "$d")"; done
fi
python3 - > "$OUT/index/plan.txt" <<'EOF'
import json, os
d = json.load(open(os.environ["ENVS_JSON"]))
only = set(os.environ.get("ONLY_ENVS", "").split())
for r in sorted({v["repo"] for v in d.values()}):
    g = "mathlib" if r == "mathlib4" else r
    for e in ["mathlib4" if r == "mathlib4" else f"{r}.git-main"] + sorted(k for k, v in d.items() if v["repo"] == r):
        if not only or e in only:
            print(g, e)
EOF
while read -r g e; do pack "${DATASET:-lean-env-$g-$A}" "$e" envs "$e"; done < "$OUT/index/plan.txt"
# audit: what went into the archives, not what was meant to
while read -r g e; do
  idx=$OUT/index/${DATASET:-lean-env-$g-$A}/$e.index
  grep -q LRAScratch "$idx" && { echo "AUDIT: LRAScratch inside $e"; BAD=$((BAD + 1)); }
  extra=$(comm -23 <(grep '\.lean$' "$idx" | grep -v '/\.lake/' | sed "s|^$e/||" | sort) <(git -C "envs/$e" ls-files '*.lean' | sort) | head -n 5)
  [ -n "$extra" ] && { echo "AUDIT: .lean files git does not track in $e: $extra"; BAD=$((BAD + 1)); }
done < "$OUT/index/plan.txt"
[ -d "$OUT/index/$TC" ] && grep -l LRAScratch "$OUT/index/$TC"/*.index && BAD=$((BAD + 1))
(cd "$OUT" && find . -name '*.tar.zst' -printf '%P\n' | sort | xargs -P 8 -n 1 sha256sum) > "$OUT/SHA256SUMS.tmp" && sort -k 2 "$OUT/SHA256SUMS.tmp" > "$OUT/SHA256SUMS"; rm -f "$OUT/SHA256SUMS.tmp"
RAW=$(awk -F'\t' 'NR>1{s+=$3} END{printf "%.1f", s/1e9}' "$M"); PK=$(awk -F'\t' 'NR>1{s+=$4} END{printf "%.1f", s/1e9}' "$M")
N=$(( $(wc -l < "$M") - 1 ))
if [ "$BAD" = 0 ]; then echo "PACK DONE: $N archives, $RAW GB raw -> $PK GB packed, $(( $(date +%s) - T0 ))s"
else echo "PACK FAILED: $BAD problems (see above); $N archives, $(( $(date +%s) - T0 ))s"; fi
