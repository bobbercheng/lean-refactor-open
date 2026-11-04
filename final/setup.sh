#!/usr/bin/env bash
# setup.sh: the one-time preparation BEFORE the 48 h job (README.md, step 1). Needs the internet (GitHub, the Mathlib cache, Hugging
# Face, Docker Hub); the job itself (run.sh) needs none. Re-runnable: finished work is kept and skipped.
#   bash setup.sh [ROWS.jsonl [HEARTBEATS.jsonl]]     default rows: data/official/rows.jsonl; without it and without an argument, setup
#                                                     STOPS (2026-11-01: it used to fall back to the 15 warm-up rows silently, and a 48 h job
#                                                     on the wrong rows would follow); the warm-up rows only on purpose, by path
# A heartbeats file you pass (or data/official/heartbeats.jsonl beside data/official/rows.jsonl) is used as is. Without one (b100,
# 2026-11-01: the final's reference heartbeats are not public), the refhb step measures them after the envs step.
# Steps (LRA_SKIP="image model ..." skips some):
#   tools  Python >= 3.11 with `requests` (a venv under the work directory when the system Python is older or lacks it; uv, pinned, as
#          the last resort), ripgrep (the pinned static build into .lra/bin when `rg` is missing), git and curl present
#   lean   ELAN_HOME: the provided Lean toolchains. The first of LRA_ELAN_HOME, ELAN_HOME, ~/.elan, the home of an `elan` on PATH with a
#          toolchains/ directory; used as is when writable, else (and for bare toolchain directories, LRA_TOOLCHAINS=dir1:dir2) its
#          toolchains are linked into a user elan in the work directory (elan installed there when needed): nothing is ever written
#          into a read-only installation; toolchains still missing are downloaded by elan during the build below
#   image  the container runtime (LRA_RUNTIME, else the first of podman-hpc, shifter, apptainer, singularity, docker; none = a `vllm`
#          on PATH) and the pinned vLLM image pulled (digest-checked where the runtime reports it); then a check that the image runs,
#          sees the package and the work directory, holds the pinned vLLM build (version + RECORD hash), and the GPUs when this node
#          has them (a node without GPUs: run `bash run.sh check` on a GPU node before the job)
#   model  the pinned checkpoint (191 GB) into <work dir>/hf with the image's own huggingface_hub; verified file by file; its local
#          snapshot directory is what the job serves (LRA_MODEL_PATH in .lra/setup.env)
#   envs   the Lean project environments of the rows, from public sources into envs/ (git clone at the pinned commits, Mathlib's cache,
#          `lake build` of the rows' modules: infra/vast/harness_setup.sh); infra/open_package/check_envs.py must print "envs ok"
#   envfix every row's reference proof through the measured compile on its newest toolchain; a row that fails because of a
#          `set_option / omit / include / unseal / variable ... in` chain directly above its declaration (the chain attaches to the
#          heartbeat-measuring command, 5 rows of the final) gets that chain's trailing ` in` stripped in the environment's copy of its
#          file, every pin, and is checked again (undone when it still fails): infra/refhb/envfix.py. Each edited environment gets an
#          untracked marker envs/<env>/.lra_envfix.json; the envs step restores the marked files before it builds. Runs with or
#          without a heartbeats file
#   refhb  only when no heartbeats file is given: each row's reference proof (`src`) compiled on its newest toolchain with the package's
#          own direct meter (infra/refhb/make_ref_heartbeats.py: direct path + 2; warm-up rows reuse the published warm-up values) ->
#          .lra/ref_heartbeats.jsonl, which run.sh then uses (LRA_SETUP_HBS); every row must be covered; LRA_REFHB_JOBS (8) at once.
#          LRA_REFHB_ALLOW_MISSING=1: a row whose reference cannot be measured gets a flagged placeholder instead of stopping setup
#          (logged as PLACEHOLDER; the next setup run measures such rows again)
#   check  one seed compiled through the package's own compile path (cold and warm), an rg timing, flock on the lock directory
#   warm   when the container sees 4 GPUs (LRA_WARM_SERVER=auto, the default; 1: required, 0 or LRA_SKIP=warm: never): one server start
#          exactly as the job starts it (offline, from the local snapshot), which fills the compile caches in the work directory and
#          proves the offline start on this node; then stopped. A start that does not answer fails setup.
# Knobs: LRA_WS (work directory, default <package>/ws; ~200 GB), LRA_RUNTIME, LRA_PYTHON, LRA_ELAN_HOME, LRA_TOOLCHAINS,
# LRA_ENV_URLS="source=git-url ..." (a library the rows file does not name a repository for), LEAN_NUM_THREADS, LRA_WARM_SERVER,
# LRA_DRY=1 (print what each step would run; nothing is downloaded, built or written but the logs).
# Ends with "SETUP OK" and writes .lra/setup.env (read by run.sh). Logs: .lra/logs/setup-*.log, envs/logs/.
set -u
set -o pipefail
[ "${BASH_VERSINFO[0]:-0}" -ge 4 ] || { echo "setup.sh needs bash 4 or newer (this is ${BASH_VERSION:-not bash})" >&2; exit 2; }
LRA_PKG=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
cd "$LRA_PKG" || exit 2
# shellcheck source=infra/orgserver/lib.sh
. "$LRA_PKG/infra/orgserver/lib.sh"
STATE=$LRA_PKG/.lra
LRA_WS=${LRA_WS:-$LRA_PKG/ws}
mkdir -p "$STATE/bin" "$STATE/pybin" "$STATE/logs" "$LRA_WS" || exit 2
LRA_WS=$(cd "$LRA_WS" && pwd)
ROWS=${1:-}; HBS=${2:-}
if [ -z "$ROWS" ]; then
  if [ -f data/official/rows.jsonl ]; then ROWS=data/official/rows.jsonl; [ -n "$HBS" ] || [ ! -f data/official/heartbeats.jsonl ] || HBS=data/official/heartbeats.jsonl
  else lra_die "no benchmark rows: data/official/rows.jsonl is missing and no rows file was given. Put the benchmark rows there (README.md, step 0) or pass them: bash setup.sh ROWS.jsonl [HEARTBEATS.jsonl]. The 15 warm-up rows only on purpose: bash setup.sh data/benchmark_warmup.jsonl data/benchmark_heartbeats.jsonl"; fi
fi
[ -f "$ROWS" ] || lra_die "rows file missing: $ROWS"
[ -z "$HBS" ] || [ -f "$HBS" ] || lra_die "heartbeats file missing: $HBS"
ROWS=$(cd "$(dirname "$ROWS")" && pwd)/$(basename "$ROWS")
REFHB=0   # b100: no heartbeats file given -> the refhb step measures them (a given file is used as is)
if [ -n "$HBS" ]; then HBS=$(cd "$(dirname "$HBS")" && pwd)/$(basename "$HBS"); else REFHB=1; fi
ARCH=$(uname -m)
DRY=${LRA_DRY:-0}
skip() { case " ${LRA_SKIP:-} " in *" $1 "*) return 0;; esac; return 1; }
x() { _lra_x "$@"; }   # a step's command: printed with LRA_DRY=1, else run
[ "$DRY" = 1 ] && lra_log "setup: LRA_DRY=1: each step prints its commands (DRY: ...); nothing is downloaded, built or installed, and setup.env is not written"
lra_log "setup: package $LRA_PKG, work directory $LRA_WS, rows $ROWS ($(grep -c . "$ROWS") rows), arch $ARCH"
if [ "$ARCH" != x86_64 ]; then lra_log "WARNING: the vLLM image is linux/amd64 only; on $ARCH only the Lean side can be prepared (test hosts)"; fi

fetch_pinned() {   # URL SHA256 DEST
  curl -sSfL --retry 3 --connect-timeout 30 -o "$3.part" "$1" || return 1
  echo "$2  $3.part" | sha256sum -c --quiet - || { rm -f "$3.part"; lra_log "checksum mismatch: $1"; return 1; }
  mv -f "$3.part" "$3"
}

# ------------------------------------------------------------------------------------------------------------------------------- tools
for t in git curl tar sha256sum; do command -v "$t" > /dev/null 2>&1 || lra_die "'$t' is required on the host"; done
py_ok() { "$1" -c 'import sys; sys.exit(0 if sys.version_info >= (3, 11) else 1)' > /dev/null 2>&1; }
PY=""
for c in ${LRA_PYTHON:-} python3.13 python3.12 python3.11 python3; do
  if command -v "$c" > /dev/null 2>&1 && py_ok "$c"; then PY=$(command -v "$c"); break; fi
done
if [ -n "$PY" ] && ! "$PY" -c "import requests" > /dev/null 2>&1; then
  x "$PY" -m pip install --user -q requests >> "$STATE/logs/setup-pip.log" 2>&1 || true
fi
if [ "$DRY" = 1 ] && { [ -z "$PY" ] || ! "$PY" -c "import requests" > /dev/null 2>&1; }; then
  lra_log "tools: DRY: no Python >= 3.11 with requests here: setup would create $LRA_WS/venv (uv $UV_VERSION as the last resort)"
  PY=${PY:-python3}
elif [ -z "$PY" ] || ! "$PY" -c "import requests" > /dev/null 2>&1; then
  VENV=$LRA_WS/venv
  if [ -x "$VENV/bin/python" ] && py_ok "$VENV/bin/python" && "$VENV/bin/python" -c "import requests" > /dev/null 2>&1; then PY=$VENV/bin/python
  elif [ -n "$PY" ] && "$PY" -m venv "$VENV" >> "$STATE/logs/setup-pip.log" 2>&1 && "$VENV/bin/python" -m pip install -q requests >> "$STATE/logs/setup-pip.log" 2>&1; then
    PY=$VENV/bin/python
  else   # no usable Python 3.11+: a uv-managed CPython 3.12 venv (uv pinned by sha256)
    lra_log "tools: no Python >= 3.11 with requests; installing a CPython 3.12 venv with uv $UV_VERSION"
    sha_var=UV_SHA256_$ARCH
    if [ ! -x "$STATE/bin/uv" ]; then
      fetch_pinned "https://github.com/astral-sh/uv/releases/download/$UV_VERSION/uv-$ARCH-unknown-linux-musl.tar.gz" "${!sha_var:-none}" "$STATE/uv.tgz" || lra_die "uv download"
      tar -xzf "$STATE/uv.tgz" -C "$STATE" && mv -f "$STATE/uv-$ARCH-unknown-linux-musl/uv" "$STATE/bin/uv" && rm -rf "$STATE/uv.tgz" "$STATE/uv-$ARCH-unknown-linux-musl"
    fi
    export UV_PYTHON_INSTALL_DIR=$LRA_WS/python UV_CACHE_DIR=$LRA_WS/cache/uv
    "$STATE/bin/uv" venv -q --python 3.12 "$VENV" >> "$STATE/logs/setup-pip.log" 2>&1 && "$STATE/bin/uv" pip install -q --python "$VENV/bin/python" requests >> "$STATE/logs/setup-pip.log" 2>&1 || lra_die "Python venv (see $STATE/logs/setup-pip.log)"
    PY=$VENV/bin/python
  fi
fi
[ "$DRY" = 1 ] || { printf '#!/bin/sh\nexec %q "$@"\n' "$PY" > "$STATE/pybin/python3"; chmod +x "$STATE/pybin/python3"; }
lra_log "tools: python $PY ($("$PY" -c 'import sys; print(sys.version.split()[0])' 2> /dev/null))"
if command -v rg > /dev/null 2>&1; then RG=$(command -v rg)
elif [ -x "$STATE/bin/rg" ]; then RG=$STATE/bin/rg
elif [ "$DRY" = 1 ]; then RG=true; lra_log "tools: DRY: would install ripgrep $RG_VERSION (sha256-pinned) into $STATE/bin"
else
  case "$ARCH" in x86_64) rgt=x86_64-unknown-linux-musl;; aarch64) rgt=aarch64-unknown-linux-gnu;; *) lra_die "no ripgrep build for $ARCH";; esac
  sha_var=RG_SHA256_$ARCH
  fetch_pinned "https://github.com/BurntSushi/ripgrep/releases/download/$RG_VERSION/ripgrep-$RG_VERSION-$rgt.tar.gz" "${!sha_var}" "$STATE/rg.tgz" || lra_die "ripgrep download"
  tar -xzf "$STATE/rg.tgz" -C "$STATE" && mv -f "$STATE/ripgrep-$RG_VERSION-$rgt/rg" "$STATE/bin/rg" && rm -rf "$STATE/rg.tgz" "$STATE/ripgrep-$RG_VERSION-$rgt"
  RG=$STATE/bin/rg
fi
"$RG" --version > /dev/null 2>&1 || lra_die "ripgrep at $RG does not run"
[ "$RG" = true ] || lra_log "tools: $("$RG" --version | head -n 1) ($RG)"
export PATH="$STATE/pybin:$STATE/bin:$PATH"

# -------------------------------------------------------------------------------------------------------------------------------- lean
# the elan installation: LRA_ELAN_HOME, ELAN_HOME, ~/.elan, then the home of an `elan` on PATH when it has toolchains/ (a system elan in
# /usr/bin keeps its toolchains in ~/.elan, not /usr). Used as is only when writable (elan writes toolchains/, tmp/, update-hashes/);
# else its toolchains are linked into $LRA_WS/elan and elan is installed there: never a write into a read-only prefix (review 2026-11-01)
writable_elan() { [ -d "$1" ] && [ -w "$1" ] && { [ ! -e "$1/toolchains" ] || [ -w "$1/toolchains" ]; }; }
EH="" EH_FROM=""
if [ -n "${LRA_ELAN_HOME:-}" ]; then EH=$LRA_ELAN_HOME EH_FROM=LRA_ELAN_HOME
elif [ -n "${ELAN_HOME:-}" ]; then EH=$ELAN_HOME EH_FROM=ELAN_HOME
elif [ -e "$HOME/.elan/bin/elan" ] || [ -d "$HOME/.elan/toolchains" ]; then EH=$HOME/.elan EH_FROM="\$HOME/.elan"
elif command -v elan > /dev/null 2>&1; then
  c=$(dirname "$(dirname "$(readlink -f "$(command -v elan)")")")
  [ -d "$c/toolchains" ] && EH=$c EH_FROM="elan on PATH"
fi
# an explicitly named ELAN_HOME that does not exist yet is created when its parent is writable
if [ -n "$EH" ] && [ ! -e "$EH" ] && [ "$DRY" != 1 ] && [ "$EH_FROM" != "\$HOME/.elan" ] && [ "$EH_FROM" != "elan on PATH" ]; then mkdir -p "$EH" 2> /dev/null; fi
PROVIDED=""
if [ -z "$EH" ] || ! writable_elan "$EH" || { [ "$EH_FROM" = "\$HOME/.elan" ] && [ ! -x "$EH/bin/elan" ]; }; then
  # read-only (a site installation), or ~/.elan holding toolchains without elan itself: link, do not install into it
  [ -n "$EH" ] && PROVIDED=$EH/toolchains && lra_log "lean: $EH ($EH_FROM) is read-only or has no elan: its toolchains are linked into $LRA_WS/elan"
  EH=$LRA_WS/elan
fi
if [ ! -x "$EH/bin/elan" ]; then
  lra_log "lean: installing elan into $EH"
  if [ "$DRY" = 1 ]; then echo "DRY: curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | ELAN_HOME=$EH sh -s -- -y --no-modify-path --default-toolchain none"
  else curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | ELAN_HOME=$EH sh -s -- -y --no-modify-path --default-toolchain none > "$STATE/logs/setup-elan.log" 2>&1 || lra_die "elan install (see $STATE/logs/setup-elan.log)"; fi
fi
export ELAN_HOME=$EH PATH="$EH/bin:$PATH"
TCS=${LRA_TOOLCHAINS:-}; LINK_DIRS="$PROVIDED ${TCS//:/ }"
# shellcheck disable=SC2086
[ -n "${LINK_DIRS// /}" ] && x "$PY" infra/orgserver/orgtools.py elan-link "$EH" $LINK_DIRS
lra_log "lean: ELAN_HOME=$EH ($(ls "$EH/toolchains" 2> /dev/null | wc -l) toolchain(s) present${EH_FROM:+; found via $EH_FROM})"

write_env() {
  {
    printf '# written by setup.sh %s; read by run.sh\n' "$(date -u +%Y-%m-%dT%H:%M:%SZ)"
    for v in LRA_WS LRA_RT LRA_PYTHON ELAN_HOME LRA_SHIFTER_VOLUMES LRA_SHIFTER_MODULES LRA_SETUP_ROWS LRA_SETUP_HBS LRA_MODEL_PATH LRA_SETUP_GPUS; do
      printf '%s=%q\n' "$v" "${!v:-}"
    done
  } > "$STATE/setup.env.tmp" && mv -f "$STATE/setup.env.tmp" "$STATE/setup.env"
}
[ "$DRY" = 1 ] && write_env() { :; }   # a dry run writes no state
LRA_MODEL_PATH=${LRA_MODEL_PATH:-} LRA_SETUP_GPUS=""
if [ -f "$STATE/setup.env" ]; then   # a re-run keeps what an earlier run found (a skipped step does not erase it)
  # shellcheck disable=SC1091
  LRA_MODEL_PATH=${LRA_MODEL_PATH:-$(. "$STATE/setup.env"; echo "${LRA_MODEL_PATH:-}")}
fi
# shellcheck disable=SC2034
LRA_PYTHON=$PY LRA_SETUP_ROWS=$ROWS LRA_SETUP_HBS=$HBS
LRA_SHIFTER_VOLUMES=${LRA_SHIFTER_VOLUMES:-0}; LRA_SHIFTER_MODULES=${LRA_SHIFTER_MODULES-gpu}

# ------------------------------------------------------------------------------------------------------------------------------- image
LRA_RT=$(lra_detect_runtime)
lra_log "image: runtime $LRA_RT"
write_env
NO_GPU_HINT="this node shows no GPU, so the container's GPU access was NOT checked: before the 48 h job, run \`bash run.sh check\` once on a GPU node (in an allocation like the job's). It checks that the container sees the 4 A100s and NVLink"
GPU_HOST=0; command -v nvidia-smi > /dev/null 2>&1 && nvidia-smi -L 2> /dev/null | grep -q '^GPU [0-9]' && GPU_HOST=1
if ! skip image; then
  if [ "$DRY" = 1 ]; then lra_pull_image
  else
    lra_pull_image > "$STATE/logs/setup-image.log" 2>&1 || { tail -n 20 "$STATE/logs/setup-image.log"; lra_die "image pull with $LRA_RT (see $STATE/logs/setup-image.log)"; }
    grep -E "WARNING|shifterimg lookup id" "$STATE/logs/setup-image.log" || true   # the digest checks' verdicts
  fi
  if [ "$LRA_RT" != none ]; then
    # the image runs, sees the package (read-only) and the work directory (written), and holds the pinned vLLM build: its version and the
    # sha256 of its installed RECORD (the hash of every file of the wheel); on every runtime, so a re-tagged image is caught here
    see() { lra_in_image nogpu bash -c 'test -r "$0/infra/orgserver/vllm_entry.sh" && touch "$1/.lra-write-test" && rm -f "$1/.lra-write-test" && python3 -c "
import hashlib, importlib.metadata as m, sys, vllm
try:
    rec = hashlib.sha256(m.distribution(\"vllm\").read_text(\"RECORD\").encode()).hexdigest()
except Exception as e:
    rec = \"unreadable:\" + type(e).__name__
print(\"vllm\", vllm.__version__, \"record\", rec, \"python\", sys.version.split()[0])"' "$LRA_PKG" "$LRA_WS"; }
    if [ "$DRY" = 1 ]; then see
    elif ! see >> "$STATE/logs/setup-image.log" 2>&1; then
      if [ "$LRA_RT" = shifter ] && [ "$LRA_SHIFTER_VOLUMES" = 0 ]; then LRA_SHIFTER_VOLUMES=1; see >> "$STATE/logs/setup-image.log" 2>&1 || lra_die "the image cannot see $LRA_PKG / $LRA_WS (see $STATE/logs/setup-image.log)"
      else tail -n 20 "$STATE/logs/setup-image.log"; lra_die "the image does not run, or cannot see / write $LRA_PKG / $LRA_WS (see $STATE/logs/setup-image.log)"; fi
    fi
    if [ "$DRY" != 1 ]; then
      IMGL=$(grep '^vllm ' "$STATE/logs/setup-image.log" | tail -n 1)
      lra_log "image: $IMGL"
      read -r _ IV _ IR _ <<< "$IMGL"
      if [ "${IV:-}" != "$LRA_IMAGE_VLLM_VERSION" ] && [ "${IV#"$LRA_IMAGE_VLLM_VERSION"}" = "${IV:-}" ]; then
        [ "${LRA_IMAGE_UNPINNED:-0}" = 1 ] || lra_die "the image's vLLM is ${IV:-?}, not the pinned $LRA_IMAGE_VLLM_VERSION (another image under the tag?); LRA_IMAGE_UNPINNED=1 accepts it"
      fi
      if [ "${IR:-}" = "$LRA_IMAGE_VLLM_RECORD" ]; then lra_log "image: vLLM RECORD hash matches the pinned build"
      elif [ "${IR#unreadable}" != "${IR:-}" ]; then lra_log "WARNING: the image's vLLM RECORD is unreadable ($IR): only the version was checked"
      else [ "${LRA_IMAGE_UNPINNED:-0}" = 1 ] || lra_die "the image's vLLM RECORD hash ${IR:-?} is not the pinned build's $LRA_IMAGE_VLLM_RECORD (another image under the tag?); LRA_IMAGE_UNPINNED=1 accepts it"; fi
    fi
  fi
  if [ "$GPU_HOST" = 1 ] && [ "$DRY" != 1 ]; then
    lra_gpu_check "$STATE/logs/setup-gpus.log" || lra_die "the container does not see the GPUs with $LRA_RT (see $STATE/logs/setup-gpus.log; $([ "$LRA_RT" = shifter ] && echo 'tried --module=gpu, nvidia and none; set LRA_SHIFTER_MODULES' || echo 'the runtime needs its GPU support: podman-hpc --gpu, apptainer --nv, docker --gpus all'))"
    LRA_SETUP_GPUS="$LRA_GPU_N GPU(s): $LRA_GPU_NAMES; NVLink $([ "$LRA_GPU_NVLINK" = 1 ] && echo yes || echo no)"
    lra_log "image: inside the container: $LRA_SETUP_GPUS${LRA_SHIFTER_MODULES:+ (shifter --module=$LRA_SHIFTER_MODULES)}"
    [ "$LRA_GPU_N" -ge 4 ] || lra_log "WARNING: the container sees $LRA_GPU_N GPU(s); the server needs 4 (tensor parallel 4): the job must run where 4 are visible"
    [ "$LRA_GPU_A100" -ge 4 ] || lra_log "WARNING: fewer than 4 A100s visible ($LRA_GPU_NAMES): the image's kernels are built for sm80 (A100)"
    [ "$LRA_GPU_NVLINK" = 1 ] || lra_log "WARNING: no NVLink between the GPUs inside the container: vLLM's custom all-reduce will be off (~25% slower decode)"
  elif [ "$DRY" = 1 ]; then lra_in_image gpu python3 "$LRA_PKG/infra/orgserver/gpu_probe.py"
  else lra_log "WARNING: $NO_GPU_HINT"; fi
  write_env
fi

# ------------------------------------------------------------------------------------------------------------------------------- model
FM=(infra/orgserver/fetch_model.py --hf-home "$LRA_WS/hf" --repo "$LRA_MODEL_REPO" --rev "$LRA_MODEL_REV")
if ! skip model; then
  lra_log "model: $LRA_MODEL_REPO @ $LRA_MODEL_REV into $LRA_WS/hf (191 GB; resumable)"
  if [ "$DRY" = 1 ]; then
    if [ "$LRA_RT" = none ]; then x "$PY" "${FM[@]}"; else lra_in_image nogpu python3 "$LRA_PKG/${FM[0]}" "${FM[@]:1}"; fi
  else
    mkdir -p "$LRA_WS/hf"
    if ! "$PY" "${FM[@]}" --verify-only > /dev/null 2>&1; then
      ( while sleep 120; do lra_log "model: $(du -sh "$LRA_WS/hf" 2> /dev/null | cut -f1) on disk"; done ) &
      PROG=$!
      if [ "$LRA_RT" = none ]; then
        "$PY" -c "import huggingface_hub" > /dev/null 2>&1 || "$PY" -m pip install -q "huggingface_hub[hf_transfer]" >> "$STATE/logs/setup-pip.log" 2>&1 || "$PY" -m pip install --user -q "huggingface_hub[hf_transfer]" >> "$STATE/logs/setup-pip.log" 2>&1
        "$PY" "${FM[@]}" > "$STATE/logs/setup-model.log" 2>&1
      else
        lra_in_image nogpu python3 "$LRA_PKG/${FM[0]}" "${FM[@]:1}" > "$STATE/logs/setup-model.log" 2>&1
      fi
      kill "$PROG" 2> /dev/null; wait "$PROG" 2> /dev/null
    fi
    "$PY" "${FM[@]}" --verify-only || lra_die "model incomplete (see $STATE/logs/setup-model.log)"
    # the job serves this directory (run.sh: LRA_MODEL_PATH), so the server never resolves the repository id, offline or not
    LRA_MODEL_PATH=$("$PY" "${FM[@]}" --verify-only --print-path 2> /dev/null) || lra_die "model snapshot path"
    lra_log "model: served from $LRA_MODEL_PATH"
    write_env
  fi
fi

# -------------------------------------------------------------------------------------------------------------------------------- envs
export XDG_CACHE_HOME=$LRA_WS/cache   # Mathlib's cache (`lake exe cache get`) and the other tool caches in the work directory, not $HOME
mkdir -p "$XDG_CACHE_HOME"
if ! skip envs; then
  URLS=(); for u in ${LRA_ENV_URLS:-}; do URLS+=(--url "$u"); done
  if [ "$DRY" = 1 ]; then
    x "$PY" infra/open_package/envs_from_rows.py --rows "$ROWS" --out "$STATE/harness_envs.json" ${URLS[@]+"${URLS[@]}"}
    x env ENVS_JSON="$STATE/harness_envs.json" bash infra/vast/harness_setup.sh
    x "$PY" infra/open_package/check_envs.py --rows "$ROWS" --root "$LRA_PKG" --elan "$ELAN_HOME"
  else
  "$PY" infra/open_package/envs_from_rows.py --rows "$ROWS" --out "$STATE/harness_envs.json" ${URLS[@]+"${URLS[@]}"} || lra_die "environment list (a library without a repository URL: LRA_ENV_URLS=\"source=https://...\")"
  lra_log "envs: building $(grep -c '"repo"' "$STATE/harness_envs.json") environment(s) into envs/ (logs envs/logs/; ~40-60 min, more for new Mathlib versions)"
  # envfix markers from an earlier setup run: restore the edited files first, so `lake build` sees each library as released (the envfix
  # step below edits them again)
  for m in envs/*/.lra_envfix.json; do
    [ -f "$m" ] || continue; d=$(dirname "$m")
    "$PY" -c 'import json,sys; print("\n".join(json.load(open(sys.argv[1]))))' "$m" | while IFS= read -r f; do
      [ -n "$f" ] && git -C "$d" checkout -- "$f" 2> /dev/null && lra_log "envs: restored $d/$f (envfix marker)"; done
    rm -f "$m"
  done
  ENVS_JSON=$STATE/harness_envs.json bash infra/vast/harness_setup.sh 2>&1 | tee "$STATE/logs/setup-envs.log" | grep -E "SETUP DONE|ENV (OK|FAILED)|WARNING" || true
  CE=$("$PY" infra/open_package/check_envs.py --rows "$ROWS" --root "$LRA_PKG" --elan "$ELAN_HOME"); rc=$?
  echo "$CE" | tail -n 30
  [ "$rc" = 0 ] || lra_die "Lean environments incomplete (above; build logs in envs/logs/)"
  fi
fi

# ------------------------------------------------------------------------------------------------------------------------------ envfix
# open run 3: rows whose reference proof fails the measured compile because of a `... in` chain above the declaration (header, envfix)
if ! skip envfix; then
  if [ "$DRY" = 1 ]; then
    x "$PY" infra/refhb/envfix.py --rows "$ROWS" --jobs "${LRA_REFHB_JOBS:-8}" --backup "$STATE/envfix_backup"
  else
    FAST=$("$PY" infra/orgserver/orgtools.py fastdir) || lra_die "no node-local directory with working flock (set LRA_FAST_DIR)"
    LRA_MEMGATE_DIR=$FAST LRA_LOCK_DIR=$FAST/locks "$PY" infra/refhb/envfix.py --rows "$ROWS" --jobs "${LRA_REFHB_JOBS:-8}" --backup "$STATE/envfix_backup" > "$STATE/logs/setup-envfix.log" 2>&1 \
      || { tail -n 8 "$STATE/logs/setup-envfix.log"; lra_die "envfix: failed (above; $STATE/logs/setup-envfix.log); LRA_SKIP=envfix skips it"; }
    lra_log "envfix: $(grep 'ENVFIX DONE' "$STATE/logs/setup-envfix.log" | tail -n 1 | sed 's/^\[envfix [0-9:]*\] //' | cut -c1-200)"
    grep -E "chain edit on|still failing|timed out" "$STATE/logs/setup-envfix.log" | sed 's/^\[envfix [0-9:]*\] /envfix: /' | cut -c1-200 | while IFS= read -r l; do lra_log "$l"; done
  fi
fi

# ------------------------------------------------------------------------------------------------------------------------------- refhb
# b100: the reference heartbeats when no file was given: measured on the environments just built, through the package's own direct
# meter (the same Lean invocation its end stage measures candidates with), plus 2 (on the warm-up rows the official values are within
# 0.71 % of this reading); kept for a re-run with the same rows file
if [ "$REFHB" = 1 ]; then
  skip refhb && lra_die "no heartbeats file given and the refhb step is skipped: pass it (bash setup.sh ROWS.jsonl HEARTBEATS.jsonl) or drop refhb from LRA_SKIP"
  REF=$STATE/ref_heartbeats.jsonl; RSHA=$(sha256sum "$ROWS" | cut -c1-64)
  if [ "$DRY" = 1 ]; then
    x "$PY" infra/refhb/make_ref_heartbeats.py --rows "$ROWS" --out "$REF" --jobs "${LRA_REFHB_JOBS:-8}" --resume
  elif [ -s "$REF" ] && [ "$(cat "$STATE/ref_heartbeats.rows.sha256" 2> /dev/null)" = "$RSHA" ]; then
    lra_log "refhb: measured earlier for these rows ($REF)"
  else
    "$PY" infra/open_package/check_envs.py --rows "$ROWS" --root "$LRA_PKG" --elan "$ELAN_HOME" > "$STATE/logs/setup-refhb-envs.log" 2>&1 \
      || lra_die "refhb: the reference heartbeats are measured on the rows' environments, which are incomplete ($STATE/logs/setup-refhb-envs.log; the envs step builds them)"
    FAST=$("$PY" infra/orgserver/orgtools.py fastdir) || lra_die "no node-local directory with working flock (set LRA_FAST_DIR)"
    lra_log "refhb: no heartbeats file given: measuring each row's reference proof on its newest toolchain (log $STATE/logs/setup-refhb.log; a few minutes)"
    AM=(); [ "${LRA_REFHB_ALLOW_MISSING:-0}" = 1 ] && AM=(--allow-missing)
    LRA_MEMGATE_DIR=$FAST LRA_LOCK_DIR=$FAST/locks "$PY" infra/refhb/make_ref_heartbeats.py --rows "$ROWS" --out "$REF" --jobs "${LRA_REFHB_JOBS:-8}" --resume ${AM[@]+"${AM[@]}"} > "$STATE/logs/setup-refhb.log" 2>&1 \
      || { grep -E "REFHB|FAILED" "$STATE/logs/setup-refhb.log" | tail -n 8; lra_die "refhb: reference heartbeats incomplete (above; $STATE/logs/setup-refhb.log). Fix the rows' environments and re-run setup (it resumes), pass the heartbeats file, or re-run with LRA_REFHB_ALLOW_MISSING=1 (flagged placeholders for those rows)"; }
    if grep -q "REFHB PLACEHOLDERS" "$STATE/logs/setup-refhb.log"; then   # kept for the job, measured again by the next setup run
      lra_log "refhb: WARNING $(grep 'REFHB PLACEHOLDERS' "$STATE/logs/setup-refhb.log" | tail -n 1 | sed 's/^\[refhb [0-9:]*\] //' | cut -c1-300)"
      rm -f "$STATE/ref_heartbeats.rows.sha256"
    else
      echo "$RSHA" > "$STATE/ref_heartbeats.rows.sha256"
    fi
    lra_log "refhb: $(grep 'REFHB OK' "$STATE/logs/setup-refhb.log" | tail -n 1 | sed 's/^\[refhb [0-9:]*\] //')"
  fi
  HBS=$REF; LRA_SETUP_HBS=$HBS; write_env
fi

# ------------------------------------------------------------------------------------------------------------------------------- check
if ! skip check && [ "$DRY" = 1 ]; then
  x "$PY" infra/orgserver/orgtools.py selfcheck --rows "$ROWS" --n "${LRA_SELFCHECK_ROWS:-1}"
elif ! skip check; then
  FAST=$("$PY" infra/orgserver/orgtools.py fastdir) || lra_die "no node-local directory with working flock (set LRA_FAST_DIR)"
  lra_log "check: lock directory $FAST (flock ok)"
  "$PY" infra/orgserver/orgtools.py flocktest "$LRA_PKG/.lra" || lra_log "note: no flock on the package filesystem; run.sh keeps every lock in $FAST"
  LRA_MEMGATE_DIR=$FAST LRA_LOCK_DIR=$FAST/locks LRA_FORCE_WARN_SORRY=1 "$PY" infra/orgserver/orgtools.py selfcheck --rows "$ROWS" --n "${LRA_SELFCHECK_ROWS:-1}" || lra_die "a seed does not compile through the package's compile path (above)"
fi

# -------------------------------------------------------------------------------------------------------------------------------- warm
# one server start exactly as run.sh starts it (offline, the local snapshot, the image's runtime flags): proves the offline start on this
# node while setup still has the internet to fix things, and leaves torch.compile / Triton caches in the work directory for the job
WARM=${LRA_WARM_SERVER:-auto}
if skip warm || skip image || skip model || [ "$WARM" = 0 ]; then WARM=0
elif [ "$WARM" = auto ] && [ "$DRY" = 1 ]; then WARM=1; lra_log "warm: DRY: runs when the container sees 4 GPUs:"
elif [ "$WARM" = auto ]; then
  WARM=0; [ "${LRA_GPU_N:-0}" -ge 4 ] && WARM=1
  [ "$WARM" = 1 ] || lra_log "warm: skipped (the container sees ${LRA_GPU_N:-0} GPU(s); LRA_WARM_SERVER=1 forces it)"
fi
if [ "$WARM" = 1 ] && [ "$DRY" = 1 ]; then
  lra_server_env; LRA_MODEL_PATH=${LRA_MODEL_PATH:-$LRA_WS/hf/hub/models--${LRA_MODEL_REPO//\//--}/snapshots/$LRA_MODEL_REV}; export LRA_MODEL_PATH
  lra_in_image gpu bash "$LRA_PKG/infra/orgserver/vllm_entry.sh"
elif [ "$WARM" = 1 ]; then
  [ -n "$LRA_MODEL_PATH" ] || lra_die "warm: no local model snapshot (the model step)"
  lra_server_env
  BASE_W="http://127.0.0.1:$VLLM_PORT/v1"
  "$PY" infra/orgserver/orgtools.py ready "$BASE_W" --timeout 1 > /dev/null 2>&1 && lra_die "warm: something already answers on $BASE_W (LRA_VLLM_PORT, or LRA_SKIP=warm)"
  LRA_CONTAINER_NAME=lra-vllm-warm-$(id -u)-$$
  SD=$STATE/warm; mkdir -p "$SD"; rm -f "$SD/stop"
  lra_log "warm: one offline server start from $LRA_MODEL_PATH (about 16 min; log $STATE/logs/setup-warm.log, $LRA_WS/vllm.log)"
  LRA_SERVER_RESTARTS=0 lra_server_loop "$STATE/logs/setup-warm.log" "$SD/stop" "$SD/client.pid" &
  WPID=$!; echo "$WPID" > "$SD/loop.pid"
  if "$PY" infra/orgserver/orgtools.py ready "$BASE_W" --timeout "${LRA_SERVER_WAIT_S:-5400}" --pidfile "$SD/loop.pid"; then
    WOK=1; lra_log "warm: the server answered offline from the local snapshot; compile caches in $LRA_WS/cache"
    grep -q "Custom allreduce is disabled" "$LRA_WS/vllm.log" 2> /dev/null && lra_log "WARNING: vLLM disabled its custom all-reduce (no NVLink / P2P inside the container): ~25% slower decode"
  else WOK=0; cp -f "$LRA_WS/vllm.log" "$STATE/logs/setup-warm-vllm.log" 2> /dev/null; fi
  lra_server_stop "$SD/stop" "$SD/client.pid" "$WPID"
  [ "$WOK" = 1 ] || { tail -n 30 "$STATE/logs/setup-warm-vllm.log" 2> /dev/null; lra_die "warm: the server did not answer when started offline as the job will start it (logs: $STATE/logs/setup-warm.log, $STATE/logs/setup-warm-vllm.log). Fix it before the job; LRA_SKIP=warm skips this check"; }
fi

write_env
[ "$DRY" = 1 ] && { lra_log "SETUP DRY RUN done (nothing was changed)"; exit 0; }
[ "$GPU_HOST" = 1 ] || skip image || lra_log "REMINDER: $NO_GPU_HINT"
lra_log "SETUP OK: next, the job: bash run.sh${1:+ $ROWS $HBS}   (settings in $STATE/setup.env)"
