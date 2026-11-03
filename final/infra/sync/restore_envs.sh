#!/usr/bin/env bash
# Restore the Lean toolchains and environments from the public Kaggle datasets instead of building them (pairs with pack_envs.sh and
# publish_envs_kaggle.sh; operator 2026-10-09). No credentials: public dataset files download anonymously over HTTPS and arrive as the
# raw .tar.zst. Every file in infra/vast/envs_kaggle.tsv is fetched (PAR at a time), checked against its sha256 and unpacked: elan-home
# into ~, toolchains into ~/.elan/toolchains, envs and git clones into envs/. Worktree links are repaired when the repo root is not
# /workspace/lra, where the envs were built. Then `lake build --no-build` proves every env's modules are up to date (nothing to rebuild).
#   infra/sync/restore_envs.sh [PAR=8]        from the repo root; last line "RESTORE DONE ..." or "RESTORE FAILED ..."
# ENVS_JSON (default infra/vast/harness_envs.json): the environments the up-to-date check proves; TSV (default infra/vast/envs_kaggle.tsv):
# the archive list; ONLY_DATASETS="a b": restore only these datasets' rows (e.g. the new LeanPool dataset on a box that has the rest);
# KAGGLE_DL_BASE: another download base (the $0 dry run serves the archives from a local directory). Review 2026-10-28.
set -u -o pipefail
cd "$(dirname "$0")/../.." || exit 2
PAR=${1:-8}; T0=$(date +%s); export ROOT=$PWD DL=$PWD/.envs-download OWNER=${KAGGLE_OWNER:-bobber}
export ENVS_JSON=${ENVS_JSON:-infra/vast/harness_envs.json} TSV=${TSV:-infra/vast/envs_kaggle.tsv} ONLY_DATASETS=${ONLY_DATASETS:-} KAGGLE_DL_BASE=${KAGGLE_DL_BASE:-https://www.kaggle.com/api/v1/datasets/download}
mkdir -p envs "$HOME/.elan/toolchains" "$DL"
missing=""; for b in curl tar sha256sum zstd; do command -v "$b" > /dev/null || missing="$missing $b"; done   # 2026-10-09: the vLLM image has no zstd
# b94b (2026-10-31): wait up to APT_LOCK_S (300) for the dpkg lock instead of failing at once (a fresh box's unattended-upgrades holds it)
AL="-o DPkg::Lock::Timeout=${APT_LOCK_S:-300}"
[ -n "$missing" ] && { DEBIAN_FRONTEND=noninteractive apt-get $AL install -y -qq $missing || { DEBIAN_FRONTEND=noninteractive apt-get $AL update -qq && DEBIAN_FRONTEND=noninteractive apt-get $AL install -y -qq $missing; }; } > /dev/null 2>&1
command -v zstd > /dev/null || { echo "RESTORE FAILED: zstd missing and could not be installed"; exit 1; }
fetch() {   # dataset file sha256
  local ds=$1 f=$2 sum=$3 t dest ok=0; t=$(date +%s)
  case "$f" in elan-home.*) dest=$HOME ;; leanprover--*) dest=$HOME/.elan/toolchains ;; *) dest=$ROOT/envs ;; esac
  for a in 1 2 3; do
    [ -f "$DL/$f" ] && echo "$sum  $DL/$f" | sha256sum -c --quiet - 2>/dev/null && { ok=1; break; }   # already downloaded and intact
    curl -sSfL --retry 3 -o "$DL/$f" "$KAGGLE_DL_BASE/$OWNER/$ds/$f" &&
      echo "$sum  $DL/$f" | sha256sum -c --quiet - && { ok=1; break; }
    echo "retry $a: $f"; sleep 5
  done
  [ "$ok" = 1 ] && zstd -dc -T0 -q "$DL/$f" | tar -xf - -C "$dest" && rm -f "$DL/$f" && echo "restored $f ($(( $(date +%s) - t ))s)" || echo "FAILED $f"
}
export -f fetch
# refuse BEFORE any download when an environment of ENVS_JSON is neither on disk nor listed in the tsv (verify 2026-10-28: the old script
# downloaded everything and failed only at the up-to-date check; e.g. a LeanPool env before its dataset is published)
[ -f "$TSV" ] || { echo "RESTORE FAILED: no archive list $TSV"; exit 1; }
for env in $(python3 -c "import json, os; print(' '.join(sorted(json.load(open(os.environ['ENVS_JSON'])))))"); do
  [ -d "envs/$env/.lake" ] || grep -q "	$env.tar.zst	" "$TSV" || { echo "RESTORE FAILED: $env (in $ENVS_JSON) is neither in envs/ nor listed in $TSV; publish it first (infra/sync/publish_envs_kaggle.sh)"; exit 1; }
done
tail -n +2 "$TSV" | { if [ -n "$ONLY_DATASETS" ]; then grep -E "^($(tr ' ' '|' <<< "$ONLY_DATASETS"))	"; else cat; fi; } > "$DL/list.tsv"
xargs -P "$PAR" -L 1 bash -c 'fetch "$0" "$1" "$3"' < "$DL/list.tsv" | tee "$DL/restore.log"
T1=$(date +%s); BAD=$(grep -c "^FAILED" "$DL/restore.log")
export PATH="$HOME/.elan/bin:$PATH"
python3 - <<'EOF' > "$DL/plan.txt"
import json, os
for k, v in sorted(json.load(open(os.environ["ENVS_JSON"])).items()):
    print(k, "mathlib4" if v["repo"] == "mathlib4" else f"{v['repo']}.git-main", " ".join(v["modules"]))
EOF
while read -r env clone mods; do
  [ "$ROOT" != /workspace/lra ] && git -C "envs/$clone" worktree repair "$ROOT/envs/$env" > /dev/null 2>&1
  if [ -n "$mods" ]; then (cd "envs/$env" && lake build --no-build $mods > /dev/null 2>&1); else (cd "envs/$env" && lake env true > /dev/null 2>&1); fi ||
    { echo "NOT UP TO DATE: $env"; BAD=$((BAD + 1)); }
done < "$DL/plan.txt"
echo "download+unpack $(( T1 - T0 ))s, check $(( $(date +%s) - T1 ))s"
[ "$BAD" = 0 ] && echo "RESTORE DONE: $(wc -l < "$DL/list.tsv") archives, $(( $(date +%s) - T0 ))s" || echo "RESTORE FAILED: $BAD problems, $(( $(date +%s) - T0 ))s"
