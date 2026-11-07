#!/usr/bin/env bash
# Harness-on-A100 setup (operator 2026-10-09: "have A100 take over the harness"). Runs ON the instance, in the copied repo root
# (/workspace/lra). Builds exactly the Lean environments the 15 warm-up problems need (infra/vast/harness_envs.json, derived from
# data/benchmark_warmup.jsonl): full clones of the project repos (envs/<repo>.git-main: worktree source and the upstream digest's history),
# a worktree per pinned commit, Mathlib's prebuilt cache, and `lake build` of the problems' modules. Repos run in parallel, the envs of one
# repo in sequence. Installs elan, ripgrep, zstd and `requests`; the optional tools (gcloud, wandb, anthropic) only when wanted.
# Logs: envs/logs/setup-*.log; ends with a line "SETUP DONE ok=<n> failed=<m>".
# ENVS_JSON (review 2026-10-28): another environment list (default infra/vast/harness_envs.json), e.g. a leanpool-only file so a build on a
# box whose other envs were restored from Kaggle does not re-run their cache/build steps. LEAN_NUM_THREADS bounds lake 5 (no --jobs flag).
set -u
cd "$(dirname "$0")/../.." || exit 2
ROOT=$PWD; export PATH="${ELAN_HOME:-$HOME/.elan}/bin:/opt/google-cloud-sdk/bin:$PATH"   # ELAN_HOME: the organizers' toolchains (setup.sh)
ENVS_JSON=${ENVS_JSON:-infra/vast/harness_envs.json}; export ENVS_JSON
[ -z "${LEAN_NUM_THREADS:-}" ] || export LEAN_NUM_THREADS
mkdir -p envs/logs
log() { echo "[$(date -u -Is)] $*"; }
# 2026-11-02 (open run 3 box: envs restored from the public datasets are owned by another user than the one running setup, e.g. ubuntu vs
# root; git then refuses "dubious ownership" and the worktree step failed): safe.directory=* for THIS process tree only, through
# GIT_CONFIG_COUNT (git >= 2.31), the same way harness/open_package.py passes it to lake; the user's global git config is not touched.
_gc=${GIT_CONFIG_COUNT:-0}; export "GIT_CONFIG_KEY_${_gc}=safe.directory" "GIT_CONFIG_VALUE_${_gc}=*" "GIT_CONFIG_COUNT=$((_gc + 1))"

# Python: the run path needs only `requests` (OpenAI-compatible client). Optional, never needed to replicate: wandb (live traces) when a W&B
# credential exists, anthropic (z.ai / OpenRouter endpoints) with LRA_WITH_ANTHROPIC=1, the gcloud CLI (GCS backup) when our bucket key exists.
PKGS="requests"; { [ -n "${WANDB_API_KEY:-}" ] || grep -qs api.wandb.ai "$HOME/.netrc"; } && PKGS="$PKGS wandb"; [ "${LRA_WITH_ANTHROPIC:-0}" = 1 ] && PKGS="$PKGS anthropic"
[ "${LRA_WITH_KAGGLE:-0}" = 1 ] && PKGS="$PKGS kaggle==2.2.5"   # publish_envs_kaggle.sh needs the CLI (review 2026-10-28: it was never installed)
log "python packages: $PKGS"; python3 -m pip install -q --break-system-packages $PKGS > envs/logs/setup-pip.log 2>&1 || python3 -m pip install -q $PKGS >> envs/logs/setup-pip.log 2>&1
GCS=0; [ -f "$HOME/.config/vexorium/gcs_sync_key.json" ] && GCS=1
# ripgrep: harness/leantools.py and lemma search shell out to `rg`, and the model greps sources with it; jq for parity with the GB10.
# 2026-10-09: missing on the first harness instance, so pass 6 ran without lemma search (16 failures) and with 12 failed `rg` calls.
# 2026-10-31 (b94b; a fresh box's unattended-upgrades held the dpkg lock and the install failed at once): every apt call waits up to
# APT_LOCK_S (300) for the dpkg / apt locks (-o DPkg::Lock::Timeout) instead of failing, and a failed install is retried after `apt-get update`.
# apt only as root (b97; the organizers' server, 2026-11-01: no root there; setup.sh installs ripgrep itself, jq / zstd are optional)
APT_LOCK_S=${APT_LOCK_S:-300}
apt_q() { DEBIAN_FRONTEND=noninteractive apt-get -o DPkg::Lock::Timeout="$APT_LOCK_S" "$@"; }
apt_install() { apt_q install -y -qq "$@" || { log "apt-get install $* failed: apt-get update, then one retry"; apt_q update -qq && apt_q install -y -qq "$@"; }; }
{ command -v rg && command -v jq && command -v zstd; } > /dev/null || [ "$(id -u)" != 0 ] || { log "ripgrep, jq, zstd"; apt_install ripgrep jq zstd > envs/logs/setup-apt.log 2>&1 || log "WARNING: apt-get install ripgrep jq zstd failed (envs/logs/setup-apt.log)"; }
command -v rg > /dev/null || log "WARNING: ripgrep missing; lemma search will fail"
if [ "${SKIP_ENVS:-0}" = 1 ]; then   # envs and ~/.elan come from the Kaggle datasets (infra/sync/restore_envs.sh) instead of a build
  [ "$GCS" = 0 ] || [ -x /opt/google-cloud-sdk/bin/gcloud ] || { log "gcloud CLI"; (curl -sSfL https://dl.google.com/dl/cloudsdk/channels/rapid/downloads/google-cloud-cli-linux-x86_64.tar.gz | tar -xz -C /opt) > envs/logs/setup-gcloud.log 2>&1; }
  log "SETUP DONE (tools only; SKIP_ENVS=1)"; exit 0
fi
if [ ! -x "${ELAN_HOME:-$HOME/.elan}/bin/elan" ]; then
  log "elan"; curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none > envs/logs/setup-elan.log 2>&1
fi
if [ "$GCS" = 1 ] && [ ! -x /opt/google-cloud-sdk/bin/gcloud ]; then   # optional: GCS backup
  log "gcloud CLI"; (curl -sSfL https://dl.google.com/dl/cloudsdk/channels/rapid/downloads/google-cloud-cli-linux-x86_64.tar.gz | tar -xz -C /opt) > envs/logs/setup-gcloud.log 2>&1
fi

# cache_lock LOCKFILE CMD...: CMD under one exclusive lock. flock(1) when it is installed and works on LOCKFILE's filesystem (our boxes);
# else (2026-11-01: no flock binary, or a Lustre / NFS mount without flock) a mkdir lock beside it, stale after 2 h, waited for at most
# 1 h; then CMD runs anyway (a parallel `cache get` race costs a source build of Mathlib, a skipped `cache get` costs the same for sure)
cache_lock() {
  local lk=$1 d; shift
  if command -v flock > /dev/null 2>&1 && flock -w 3600 "$lk" true 2> /dev/null; then flock "$lk" "$@"; return $?; fi
  d=$lk.d
  for _ in $(seq 1 720); do
    mkdir "$d" 2> /dev/null && { echo "$$" > "$d/pid"; "$@"; local rc=$?; rm -f "$d/pid"; rmdir "$d" 2> /dev/null; return $rc; }
    [ -n "$(find "$d" -maxdepth 0 -mmin +120 2> /dev/null)" ] && { rm -f "$d/pid"; rmdir "$d" 2> /dev/null; continue; }
    sleep 5
  done
  log "cache lock $d still held after 1 h: running without it"; "$@"
}

build_repo() {   # $1 = repo key in harness_envs.json
  local repo=$1 url clone
  url=$(python3 -c "import json,sys,os; d=json.load(open(os.environ['ENVS_JSON'])); print(next(v['url'] for v in d.values() if v['repo']==sys.argv[1]))" "$repo")
  if [ "$repo" = mathlib4 ]; then clone=envs/mathlib4; else clone=envs/$repo.git-main; fi
  if [ ! -d "$clone/.git" ]; then
    log "clone $repo"
    case "$repo" in mathlib4|leanpool) git clone -q --filter=blob:none "$url" "$clone";; *) git clone -q "$url" "$clone";; esac || { log "clone $repo FAILED"; return 1; }   # blobless: the 11.9M-line pool
  fi
  python3 -c "import json,sys,os; d=json.load(open(os.environ['ENVS_JSON'])); [print(k, v['commit'], int(v['cache']), ' '.join(v['modules'])) for k, v in sorted(d.items()) if v['repo']==sys.argv[1]]" "$repo" |
  while read -r env commit cache mods; do
    L=envs/logs/setup-$env.log
    if grep -q "^ENV OK $env" envs/logs/setup-repo-*.log 2>/dev/null; then echo "ENV OK $env"; continue; fi   # re-runs skip finished envs
    ( log "env $env @ $commit"
      [ -d "envs/$env" ] || (cd "$clone" && git fetch -q origin "$commit" 2>/dev/null; git worktree add -q -f "$ROOT/envs/$env" "$commit") || { log "worktree FAILED"; echo "ENV FAILED $env (worktree)"; exit 0; }
      if [ "$cache" = 1 ]; then   # one cache download at a time: parallel `cache get`s race on ~/.cache/mathlib/curl.cfg (2026-10-09: ArkLib fell back to a source build of Mathlib)
        CD=${XDG_CACHE_HOME:-$HOME/.cache}; mkdir -p "$CD"   # setup.sh: XDG_CACHE_HOME = <work dir>/cache (Mathlib's cache lives there too)
        for t in 1 2 3; do (cd "envs/$env" && cache_lock "$CD/mathlib-cache.lock" lake exe cache get) && break; log "cache get attempt $t failed"; sleep 15; done
      fi
      if [ -n "$mods" ]; then (cd "envs/$env" && lake build $mods); rc=$?; else (cd "envs/$env" && lake env true); rc=$?; fi
      [ $rc = 0 ] && echo "ENV OK $env" || echo "ENV FAILED $env (rc=$rc)" ) >> "$L" 2>&1
    tail -n 1 "$L"
  done
}
export -f build_repo cache_lock log; export ROOT
log "building environments"
for repo in $(python3 -c "import json,os; print(' '.join(sorted({v['repo'] for v in json.load(open(os.environ['ENVS_JSON'])).values()})))"); do
  build_repo "$repo" > "envs/logs/setup-repo-$repo.log" 2>&1 &
done
wait
OK=$(cat envs/logs/setup-repo-*.log | grep -c "^ENV OK"); BAD=$(cat envs/logs/setup-repo-*.log | grep -c "^ENV FAILED")   # across every ENVS_JSON built here
# 2026-11-02: an env of THIS ENVS_JSON with no "ENV OK" line (its clone or worktree failed, or nothing was logged) is a failure too
NOREP=$(python3 -c "import json,os,glob,re; want=set(json.load(open(os.environ['ENVS_JSON']))); ok={m.group(1) for f in glob.glob('envs/logs/setup-repo-*.log') for m in re.finditer(r'^ENV OK (\S+)', open(f).read(), re.M)}; print(' '.join(sorted(want-ok)))")
[ -n "$NOREP" ] && log "NOT BUILT: $NOREP"
NB=$(echo $NOREP | wc -w); [ "$NB" -gt "$BAD" ] && BAD=$NB
log "SETUP DONE ok=$OK failed=$BAD"; df -h / | tail -1
