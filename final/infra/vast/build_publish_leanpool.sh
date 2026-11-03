#!/usr/bin/env bash
# Build and pack the missing LeanPool environment ON the x86-64 instance (docs/a100_rehearsal.md; operator 2026-10-28: "our Kaggle
# dataset only have 5 lean env, we also need to add 1 new env"; the GB10 build is aarch64 and can never be uploaded). From the export
# root (/workspace/lra), after infra/sync/restore_envs.sh put the 15 warm-up envs and the 10 toolchains in place:
#   build    ENVS_JSON (default infra/vast/harness_envs.leanpool.json, from infra/open_package/rehearsal_rows.py): elan installs
#            leanprover/lean4:v4.35.0-rc3 on first use; harness_setup.sh clones leanpool blobless into envs/leanpool.git-main, adds the
#            worktree envs/leanpool-v4.35.0-rc3 at the pinned commit, pulls Mathlib's cache and builds the rows' modules; then
#            LEANPOOL_BUILD=full (default) runs envs/build_leanpool.sh full (`lake build LeanPool`, resumable, up to BUILD_ROUNDS x
#            BUILD_MAX_S) so the published env serves ANY LeanPool row of the final; LEANPOOL_BUILD=modules stops after the rows' modules.
#            Proof: `lake build --no-build <modules>` exits 0 and infra/open_package/check_envs.py passes on ROWS.
#   pack     ENVS_JSON + ONLY_TOOLCHAINS=leanprover--lean4---v4.35.0-rc3 through infra/sync/pack_envs.sh into OUT (/workspace/envpack):
#            two dataset folders, lean-env-leanpool-x86-64 (NEW: leanpool.git-main + leanpool-v4.35.0-rc3) and lean4-toolchains-x86-64
#            (the one new toolchain; publish adds the 10 existing files back before versioning, KEEP_EXISTING). Ends "PACK DONE".
#   all      build, then pack. The PUBLISH step is NOT here: the Kaggle key is piped from the GB10 over SSH into publish_envs_kaggle.sh's
#            environment (infra/vast/rehearsal.sh leanpool), never written on this disk.
# Disk: refuses to build or pack with less than MIN_FREE_GB (60) free on /workspace (review 2026-10-28, finding 10). Logs: envs/logs/.
#   infra/vast/build_publish_leanpool.sh build|pack|all        last line "LEANPOOL BUILD DONE" / "PACK DONE ..." or "... FAILED"
set -u
cd "$(dirname "$0")/../.." || exit 2
export PATH="$HOME/.elan/bin:$PATH"
STEP=${1:-all}
ENVS_JSON=${ENVS_JSON:-infra/vast/harness_envs.leanpool.json}; export ENVS_JSON
OUT=${OUT:-/workspace/envpack}; MIN_FREE_GB=${MIN_FREE_GB:-60}; DF_PATH=${DF_PATH:-/workspace}
LEANPOOL_BUILD=${LEANPOOL_BUILD:-full}; BUILD_ROUNDS=${BUILD_ROUNDS:-3}; BUILD_MAX_S=${BUILD_MAX_S:-5400}
TC=${LEANPOOL_TOOLCHAIN:-v4.35.0-rc3}; ENV=leanpool-$TC
log() { echo "[$(date -u -Is)] $*"; }
free_ok() { local g; g=$(df --output=avail -BG "$DF_PATH" 2>/dev/null | tail -n 1 | tr -dc 0-9); g=${g:-0}
  [ "$g" -ge "$MIN_FREE_GB" ] && return 0; log "REFUSED ($1): $DF_PATH has $g GB free (< $MIN_FREE_GB)"; return 1; }
mods() { python3 -c "import json,os; d=json.load(open(os.environ['ENVS_JSON'])); print(' '.join(d['$ENV']['modules']))"; }
build() {
  [ -f "$ENVS_JSON" ] || { log "LEANPOOL BUILD FAILED: no $ENVS_JSON (infra/open_package/rehearsal_rows.py writes it)"; return 1; }
  free_ok build || { log "LEANPOOL BUILD FAILED: disk"; return 1; }
  command -v elan > /dev/null || { log "elan missing (restore_envs.sh unpacks elan-home); installing"; curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none > envs/logs/setup-elan.log 2>&1; }
  mkdir -p envs/logs
  log "toolchain leanprover/lean4:$TC"; elan toolchain install "leanprover/lean4:$TC" > "envs/logs/toolchain-$TC.log" 2>&1 || log "elan toolchain install rc $? (lake fetches it on first use)"
  log "harness_setup.sh with ENVS_JSON=$ENVS_JSON (clone, worktree, cache, the rows' modules)"
  SKIP_ENVS=0 LRA_WITH_KAGGLE=1 bash infra/vast/harness_setup.sh > "envs/logs/leanpool-setup.log" 2>&1
  tail -n 1 "envs/logs/leanpool-setup.log"
  grep -q "SETUP DONE ok=1 failed=0" "envs/logs/leanpool-setup.log" || { log "LEANPOOL BUILD FAILED: harness_setup.sh ($(tail -n 1 envs/logs/leanpool-setup.log))"; return 1; }
  if [ "$LEANPOOL_BUILD" = full ]; then
    local r rc=1
    for r in $(seq 1 "$BUILD_ROUNDS"); do
      free_ok "full build round $r" || { log "LEANPOOL BUILD FAILED: disk"; return 1; }
      log "full build round $r/$BUILD_ROUNDS (lake build LeanPool, at most ${BUILD_MAX_S}s)"
      LRA_LEANPOOL_V=$TC LRA_LAKE_JOBS=${LRA_LAKE_JOBS:-$(nproc)} timeout "$BUILD_MAX_S" bash envs/build_leanpool.sh full > "envs/logs/leanpool-full-$r.log" 2>&1; rc=$?
      tail -n 2 "envs/logs/leanpool-full-$r.log"
      grep -q "full exit=0" "envs/logs/leanpool-full-$r.log" && { rc=0; break; }
      rc=1
    done
    [ "$rc" = 0 ] || log "WARNING: the full build did not finish in $BUILD_ROUNDS rounds; the rows' modules are built, the pack goes on with a partial pool (resumable later)"
  fi
  (cd "envs/$ENV" && lake build --no-build $(mods) > /dev/null 2>&1) || { log "LEANPOOL BUILD FAILED: lake build --no-build $(mods)"; return 1; }
  if [ -n "${ROWS:-}" ]; then python3 infra/open_package/check_envs.py --rows "$ROWS" --root "$PWD" || { log "LEANPOOL BUILD FAILED: check_envs"; return 1; }; fi
  log "LEANPOOL BUILD DONE: envs/$ENV $(du -sh "envs/$ENV/.lake" 2>/dev/null | cut -f1) .lake, clone $(du -sh envs/leanpool.git-main 2>/dev/null | cut -f1)"
}
pack() {
  free_ok pack || { log "PACK FAILED: disk"; return 1; }
  [ -d "envs/$ENV/.lake" ] || { log "PACK FAILED: no envs/$ENV/.lake"; return 1; }
  rm -rf "$OUT"
  ONLY_TOOLCHAINS="leanprover--lean4---$TC" bash infra/sync/pack_envs.sh "$OUT"
  tail -n 1 "$OUT/PACK.log"
  grep -q "^PACK DONE" <<< "$(tail -n 1 "$OUT/PACK.log")" && ls -la "$OUT"/lean-env-leanpool-*/ "$OUT"/lean4-toolchains-*/ 2>/dev/null
  grep -q "^PACK DONE" <<< "$(tail -n 1 "$OUT/PACK.log")"
}
case "$STEP" in
  build) build;;
  pack) pack;;
  all) build && pack;;
  *) echo "usage: $0 build|pack|all"; exit 2;;
esac
