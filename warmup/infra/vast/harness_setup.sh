#!/usr/bin/env bash
# Harness-on-A100 setup. Runs ON the instance, in the copied repo root
# (/workspace/lra). Builds exactly the Lean environments the 15 warm-up problems need (infra/vast/harness_envs.json, derived from
# data/benchmark_warmup.jsonl): full clones of the project repos (envs/<repo>.git-main: worktree source and the upstream digest's history),
# a worktree per pinned commit, Mathlib's prebuilt cache, and `lake build` of the problems' modules. Repos run in parallel, the envs of one
# repo in sequence. Installs elan, ripgrep, zstd and `requests`; the optional tools (gcloud, wandb, anthropic) only when wanted.
# Logs: envs/logs/setup-*.log; ends with a line "SETUP DONE ok=<n> failed=<m>".
set -u
cd "$(dirname "$0")/../.." || exit 2
ROOT=$PWD; export PATH="$HOME/.elan/bin:/opt/google-cloud-sdk/bin:$PATH"
mkdir -p envs/logs
log() { echo "[$(date -u -Is)] $*"; }

# Python: the run path needs only `requests` (OpenAI-compatible client). Optional, never needed to replicate: wandb (live traces) when a W&B
# credential exists, anthropic (z.ai / OpenRouter endpoints) with LRA_WITH_ANTHROPIC=1, the gcloud CLI (GCS backup) when our bucket key exists.
PKGS="requests"; { [ -n "${WANDB_API_KEY:-}" ] || grep -qs api.wandb.ai "$HOME/.netrc"; } && PKGS="$PKGS wandb"; [ "${LRA_WITH_ANTHROPIC:-0}" = 1 ] && PKGS="$PKGS anthropic"
log "python packages: $PKGS"; python3 -m pip install -q --break-system-packages $PKGS > envs/logs/setup-pip.log 2>&1 || python3 -m pip install -q $PKGS >> envs/logs/setup-pip.log 2>&1
GCS=0; [ -f "$HOME/.config/vexorium/gcs_sync_key.json" ] && GCS=1
# ripgrep: harness/leantools.py and lemma search shell out to `rg`, and the model greps sources with it; jq for parity with the GB10.
# 2026-10-09: missing on the first harness instance, so pass 6 ran without lemma search (16 failures) and with 12 failed `rg` calls.
{ command -v rg && command -v jq && command -v zstd; } > /dev/null || { log "ripgrep, jq, zstd"; (apt-get install -y -qq ripgrep jq zstd || { apt-get update -qq && apt-get install -y -qq ripgrep jq zstd; }) > envs/logs/setup-apt.log 2>&1; }
command -v rg > /dev/null || log "WARNING: ripgrep missing; lemma search will fail"
if [ "${SKIP_ENVS:-0}" = 1 ]; then   # envs and ~/.elan come from the Kaggle datasets (infra/sync/restore_envs.sh) instead of a build
  [ "$GCS" = 0 ] || [ -x /opt/google-cloud-sdk/bin/gcloud ] || { log "gcloud CLI"; (curl -sSfL https://dl.google.com/dl/cloudsdk/channels/rapid/downloads/google-cloud-cli-linux-x86_64.tar.gz | tar -xz -C /opt) > envs/logs/setup-gcloud.log 2>&1; }
  log "SETUP DONE (tools only; SKIP_ENVS=1)"; exit 0
fi
if [ ! -x "$HOME/.elan/bin/elan" ]; then
  log "elan"; curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none > envs/logs/setup-elan.log 2>&1
fi
if [ "$GCS" = 1 ] && [ ! -x /opt/google-cloud-sdk/bin/gcloud ]; then   # optional: GCS backup
  log "gcloud CLI"; (curl -sSfL https://dl.google.com/dl/cloudsdk/channels/rapid/downloads/google-cloud-cli-linux-x86_64.tar.gz | tar -xz -C /opt) > envs/logs/setup-gcloud.log 2>&1
fi

build_repo() {   # $1 = repo key in harness_envs.json
  local repo=$1 url clone
  url=$(python3 -c "import json,sys; d=json.load(open('infra/vast/harness_envs.json')); print(next(v['url'] for v in d.values() if v['repo']==sys.argv[1]))" "$repo")
  if [ "$repo" = mathlib4 ]; then clone=envs/mathlib4; else clone=envs/$repo.git-main; fi
  if [ ! -d "$clone/.git" ]; then
    log "clone $repo"
    if [ "$repo" = mathlib4 ]; then git clone -q --filter=blob:none "$url" "$clone"; else git clone -q "$url" "$clone"; fi || { log "clone $repo FAILED"; return 1; }
  fi
  python3 -c "import json,sys; d=json.load(open('infra/vast/harness_envs.json')); [print(k, v['commit'], int(v['cache']), ' '.join(v['modules'])) for k, v in sorted(d.items()) if v['repo']==sys.argv[1]]" "$repo" |
  while read -r env commit cache mods; do
    L=envs/logs/setup-$env.log
    if grep -q "^ENV OK $env" envs/logs/setup-repo-*.log 2>/dev/null; then echo "ENV OK $env"; continue; fi   # re-runs skip finished envs
    { log "env $env @ $commit"
      [ -d "envs/$env" ] || (cd "$clone" && git fetch -q origin "$commit" 2>/dev/null; git worktree add -q -f "$ROOT/envs/$env" "$commit") || { log "worktree FAILED"; echo "ENV FAILED $env"; continue; }
      if [ "$cache" = 1 ]; then   # one cache download at a time: parallel `cache get`s race on ~/.cache/mathlib/curl.cfg (2026-10-09: ArkLib fell back to a source build of Mathlib)
        mkdir -p "$HOME/.cache"; for t in 1 2 3; do (cd "envs/$env" && flock "$HOME/.cache/mathlib-cache.lock" lake exe cache get) && break; log "cache get attempt $t failed"; sleep 15; done
      fi
      if [ -n "$mods" ]; then (cd "envs/$env" && lake build $mods); rc=$?; else (cd "envs/$env" && lake env true); rc=$?; fi
      [ $rc = 0 ] && echo "ENV OK $env" || echo "ENV FAILED $env (rc=$rc)"; } >> "$L" 2>&1
    tail -n 1 "$L"
  done
}
export -f build_repo log; export ROOT
log "building environments"
for repo in $(python3 -c "import json; print(' '.join(sorted({v['repo'] for v in json.load(open('infra/vast/harness_envs.json')).values()})))"); do
  build_repo "$repo" > "envs/logs/setup-repo-$repo.log" 2>&1 &
done
wait
OK=$(cat envs/logs/setup-repo-*.log | grep -c "^ENV OK"); BAD=$(cat envs/logs/setup-repo-*.log | grep -c "^ENV FAILED")
log "SETUP DONE ok=$OK failed=$BAD"; df -h / | tail -1
