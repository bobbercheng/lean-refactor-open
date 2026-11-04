# shellcheck shell=bash disable=SC2034
# Shared by setup.sh and run.sh on the organizers' server (2026-10-31; README.md). Sourced, never run. Container runtimes: podman-hpc,
# shifter, apptainer / singularity, docker, or none (a `vllm` executable on the host). The same absolute paths inside and outside the
# container: the package directory (read-only) and the work directory LRA_WS (model cache, server log, caches).

# rc3 (2026-11-01): Lake runs git inside the env checkouts, and git refuses a repository owned by another user ("detected dubious
# ownership"): with uid-mapped containers or shared storage every lake build / compile would fail. safe.directory=* for setup.sh, run.sh
# and every child through git's GIT_CONFIG_COUNT variables (git >= 2.31), appended after any pairs already set; no config file is written.
lra_git_trust() {
  local n=${GIT_CONFIG_COUNT:-0} i k v
  for ((i = 0; i < n; i++)); do
    k=GIT_CONFIG_KEY_$i; v=GIT_CONFIG_VALUE_$i
    [ "${!k:-}" = safe.directory ] && [ "${!v:-}" = "*" ] && return 0
  done
  export "GIT_CONFIG_KEY_$n=safe.directory" "GIT_CONFIG_VALUE_$n=*" "GIT_CONFIG_COUNT=$((n + 1))"
}
lra_git_trust

LRA_MODEL_REPO=${LRA_MODEL_REPO:-wtdcode/GLM-5.3-Flash-AWQ-W4A16}
LRA_MODEL_REV=${LRA_MODEL_REV:-abd7b07719111f137e1de8a0c1b7e01c11b74d1a}
# The image (overridable, e.g. a mirror of the same digest: LRA_IMAGE_NAME=myregistry/vllm-backport; README.md, "The image")
LRA_IMAGE_NAME=${LRA_IMAGE_NAME:-lazymio/vllm-backport}
LRA_IMAGE_TAG=${LRA_IMAGE_TAG:-v0.13.1-sm80}
LRA_IMAGE_DIGEST=${LRA_IMAGE_DIGEST:-sha256:8094fcbab905a04a480b327f2761255e3d17cd8d39470cac9d76450bbb567f7e}                # the tag's linux/amd64 manifest
LRA_IMAGE_INDEX_DIGEST=${LRA_IMAGE_INDEX_DIGEST:-sha256:0fc33cd7d2be777bf6faaee9b02adf781dc6d0bc44b9a09ce4865089f67e9cba}    # the tag's OCI index (2026-10-31)
LRA_IMAGE_CONFIG_DIGEST=${LRA_IMAGE_CONFIG_DIGEST:-sha256:671aa3aadb9e536a89ecda894d93eb15870a4bd5c1d24b588ab5a06e2ca8ea8f}  # its config = the image ID
# inside the image (any runtime, digest or not): vLLM's version and the sha256 of its installed RECORD (every file's hash of the wheel)
LRA_IMAGE_VLLM_VERSION=${LRA_IMAGE_VLLM_VERSION:-0.13.1}
LRA_IMAGE_VLLM_RECORD=${LRA_IMAGE_VLLM_RECORD:-73938aeb7b66cc4419c6cf91a560d565403443c4cf4c2e21e1a3ba893d1bc467}
LRA_IMAGE_PATH=/usr/local/cuda/bin:/usr/local/nvidia/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
# variables handed to every process in the image (when set, non-empty, on the host)
LRA_IMAGE_ENV="HF_HUB_OFFLINE HF_HUB_DISABLE_TELEMETRY VLLM_WORKSPACE VLLM_HOST VLLM_PORT VLLM_NO_USAGE_STATS DO_NOT_TRACK VLLM_CACHE_ROOT TRITON_CACHE_DIR TORCHINDUCTOR_CACHE_DIR XDG_CACHE_HOME LRA_MODEL_PATH"
# host variables never handed in (Shifter / Apptainer / none pass the host environment): the job's shell rc (run.sh, BASH_ENV) is the host's
LRA_IMAGE_UNSET="PYTHONPATH PYTHONHOME PYTHONSTARTUP PYTHONUSERBASE VIRTUAL_ENV CONDA_PREFIX BASH_ENV ENV LRA_SHELL_PATH_PREPEND"
RG_VERSION=14.1.1
RG_SHA256_x86_64=4cf9f2741e6c465ffdb7c26f38056a59e2a2544b51f7cc128ef28337eeae4d8e    # ripgrep-14.1.1-x86_64-unknown-linux-musl.tar.gz
RG_SHA256_aarch64=c827481c4ff4ea10c9dc7a4022c8de5db34a5737cb74484d62eb94a95841ab2f   # ripgrep-14.1.1-aarch64-unknown-linux-gnu.tar.gz
UV_VERSION=0.6.14
UV_SHA256_x86_64=0cac4df0cb3457b154f2039ae471e89cd4e15f3bd790bbb3cb0b8b40d940b93e    # uv-x86_64-unknown-linux-musl.tar.gz
UV_SHA256_aarch64=94e22c4be44d205def456427639ca5ca1c1a9e29acc31808a7b28fdd5dcf7f17   # uv-aarch64-unknown-linux-musl.tar.gz

lra_log() { echo "[$(date -u +%Y-%m-%dT%H:%M:%SZ)] $*"; }
lra_die() { lra_log "FAILED: $*" >&2; exit 1; }

# the container runtime: $LRA_RUNTIME, else the first one present
lra_detect_runtime() {
  if [ -n "${LRA_RUNTIME:-}" ]; then echo "$LRA_RUNTIME"; return 0; fi
  local r
  for r in podman-hpc shifter apptainer singularity; do command -v "$r" > /dev/null 2>&1 && { echo "$r"; return 0; }; done
  command -v docker > /dev/null 2>&1 && docker info > /dev/null 2>&1 && { echo docker; return 0; }
  echo none
}

# the image reference a runtime runs (after lra_pull_image)
lra_image_ref() {
  case "$1" in
    podman-hpc) echo "docker.io/$LRA_IMAGE_NAME:$LRA_IMAGE_TAG";;   # pulled by tag, digest checked after the pull
    docker) echo "docker.io/$LRA_IMAGE_NAME@$LRA_IMAGE_DIGEST";;
    shifter) echo "docker:$LRA_IMAGE_NAME:$LRA_IMAGE_TAG";;
    apptainer|singularity) echo "$LRA_WS/image/vllm-backport_$LRA_IMAGE_TAG.sif";;
    none) echo "${VLLM_BIN:-vllm}";;
    *) return 1;;
  esac
}

lra_pull_image() {
  local ref; ref=$(lra_image_ref "$LRA_RT") || lra_die "unknown runtime '$LRA_RT' (LRA_RUNTIME: podman-hpc, shifter, apptainer, singularity, docker, none)"
  if [ "${LRA_DRY:-0}" = 1 ]; then   # the pull commands only
    case "$LRA_RT" in
      podman-hpc) _lra_x podman-hpc pull "$ref"; _lra_x podman-hpc image inspect --format '{{.Digest}} {{.RepoDigests}}' "$ref";;
      docker) _lra_x docker pull "$ref";;
      shifter) _lra_x shifterimg -v pull "$ref"; _lra_x shifterimg lookup "$ref";;
      apptainer|singularity) _lra_x "$LRA_RT" pull --force "$ref.part" "docker://$LRA_IMAGE_NAME@$LRA_IMAGE_DIGEST";;
      none) _lra_x command -v "$ref";;
    esac
    return 0
  fi
  case "$LRA_RT" in
    podman-hpc)
      podman-hpc pull "$ref" || return 1
      local dg; dg=$(podman-hpc image inspect --format '{{.Digest}} {{.RepoDigests}}' "$ref" 2> /dev/null)
      if [ -z "$dg" ]; then lra_log "WARNING: could not read the pulled image's digest (podman-hpc image inspect)"
      elif [[ "$dg" != *"$LRA_IMAGE_DIGEST"* && "$dg" != *"$LRA_IMAGE_INDEX_DIGEST"* ]]; then
        [ "${LRA_IMAGE_UNPINNED:-0}" = 1 ] || { lra_log "image digest mismatch: $dg (expected $LRA_IMAGE_DIGEST); LRA_IMAGE_UNPINNED=1 accepts it"; return 1; }
      fi;;
    docker) docker pull "$ref" || return 1;;
    shifter) shifterimg -v pull "$ref" || return 1; lra_shifter_verify "$ref";;
    apptainer|singularity)
      [ -s "$ref" ] && return 0
      mkdir -p "$LRA_WS/image" "$LRA_WS/tmp" "$LRA_WS/cache/apptainer"
      APPTAINER_TMPDIR="$LRA_WS/tmp" APPTAINER_CACHEDIR="$LRA_WS/cache/apptainer" SINGULARITY_TMPDIR="$LRA_WS/tmp" \
        SINGULARITY_CACHEDIR="$LRA_WS/cache/apptainer" "$LRA_RT" pull --force "$ref.part" "docker://$LRA_IMAGE_NAME@$LRA_IMAGE_DIGEST" || return 1
      mv -f "$ref.part" "$ref";;
    none) command -v "$ref" > /dev/null 2>&1 || { lra_log "no '$ref' on PATH: LRA_RUNTIME=none needs the vllm-backport build installed (README.md, 'No container runtime')"; return 1; };;
  esac
}

# Shifter pulls by tag (no digest pull): compare the image id `shifterimg lookup` reports with the pinned manifest, index and config
# digests. A mismatch, or no id, is a warning only (Shifter versions differ in what the id is); the in-image check of setup.sh (vLLM's
# version and RECORD hash) is the binding one on every runtime.
lra_shifter_verify() {
  local id h ok=0
  id=$(shifterimg lookup "$1" 2> /dev/null | tail -n 1 | tr -d '[:space:]'); id=${id#sha256:}
  if [ -z "$id" ]; then lra_log "WARNING: shifterimg lookup $1 printed no image id: the image is pinned by tag here (the in-image check decides)"; return 0; fi
  for h in "$LRA_IMAGE_DIGEST" "$LRA_IMAGE_INDEX_DIGEST" "$LRA_IMAGE_CONFIG_DIGEST"; do
    h=${h#sha256:}; [ "${#id}" -ge 12 ] && [ "${h#"$id"}" != "$h" ] && ok=1
  done
  if [ "$ok" = 1 ]; then lra_log "image: shifterimg lookup id $id matches the pinned digests"
  else lra_log "WARNING: shifterimg lookup id $id is none of the pinned digests (manifest ${LRA_IMAGE_DIGEST#sha256:}, config ${LRA_IMAGE_CONFIG_DIGEST#sha256:}); the in-image check decides"; fi
  return 0
}

# run a command, print it with LRA_DRY=1, or exec it with LRA_EXEC=1 (the server loop: the runtime's own process is the one it signals)
_lra_x() { if [ "${LRA_DRY:-0}" = 1 ]; then printf 'DRY:'; printf ' %q' "$@"; echo; elif [ "${LRA_EXEC:-0}" = 1 ]; then exec "$@"; else "$@"; fi; }

# lra_in_image gpu|nogpu CMD ARGS...: CMD in the pinned image, in the foreground, with this file's environment (LRA_IMAGE_ENV) and no
# host Python settings (Shifter and Apptainer pass the host environment in; PYTHONNOUSERSITE keeps ~/.local packages out)
lra_in_image() {
  local gpu=$1; shift
  local envs=() v
  for v in $LRA_IMAGE_UNSET; do envs+=(-u "$v"); done
  envs+=(PYTHONNOUSERSITE=1 "PATH=$LRA_IMAGE_PATH")
  for v in $LRA_IMAGE_ENV; do [ -n "${!v:-}" ] && envs+=("$v=${!v}"); done
  local ref; ref=$(lra_image_ref "$LRA_RT") || lra_die "unknown runtime '$LRA_RT'"
  case "$LRA_RT" in
    podman-hpc|docker)
      local args=(run --rm --net=host --ipc=host -v "$LRA_PKG:$LRA_PKG:ro" -v "$LRA_WS:$LRA_WS" -w "$LRA_WS" --entrypoint /usr/bin/env)
      [ -n "${LRA_CONTAINER_NAME:-}" ] && args+=(--name "$LRA_CONTAINER_NAME")
      if [ "$gpu" = gpu ]; then if [ "$LRA_RT" = podman-hpc ]; then args+=(--gpu); else args+=(--gpus all); fi; fi
      # shellcheck disable=SC2086
      _lra_x "$LRA_RT" "${args[@]}" ${LRA_RUNTIME_ARGS:-} "$ref" "${envs[@]}" "$@";;
    shifter)
      local args=("--image=$ref")
      [ "$gpu" = gpu ] && [ -n "${LRA_SHIFTER_MODULES:-}" ] && args+=("--module=$LRA_SHIFTER_MODULES")
      [ "${LRA_SHIFTER_VOLUMES:-0}" = 1 ] && args+=("--volume=$LRA_PKG:$LRA_PKG" "--volume=$LRA_WS:$LRA_WS")
      # shellcheck disable=SC2086
      _lra_x shifter "${args[@]}" ${LRA_RUNTIME_ARGS:-} /usr/bin/env "${envs[@]}" "$@";;
    apptainer|singularity)
      local args=(exec --bind "$LRA_PKG:$LRA_PKG:ro" --bind "$LRA_WS:$LRA_WS")
      [ "$gpu" = gpu ] && args+=(--nv)
      # shellcheck disable=SC2086
      _lra_x "$LRA_RT" "${args[@]}" ${LRA_RUNTIME_ARGS:-} "$ref" /usr/bin/env "${envs[@]}" "$@";;
    none)   # the host's own vllm (its Python environment untouched)
      local henv=(-u BASH_ENV -u ENV -u LRA_SHELL_PATH_PREPEND); for v in $LRA_IMAGE_ENV; do [ -n "${!v:-}" ] && henv+=("$v=${!v}"); done
      _lra_x env "${henv[@]}" "$@";;
  esac
}

# stop a server started by lra_server_loop: the container by name (podman-hpc / docker), else SIGTERM to vllm_entry.sh itself (it
# writes LRA_WS/entry.pid; under Shifter / Apptainer / none it is a host process), then to the runtime's process; SIGKILL after 60 s
lra_stop_container() {
  local pid=$1 epid="" i
  case "$LRA_RT" in
    podman-hpc|docker) [ -n "${LRA_CONTAINER_NAME:-}" ] && timeout 120 "$LRA_RT" rm -f "$LRA_CONTAINER_NAME" > /dev/null 2>&1;;
    *) epid=$(cat "$LRA_WS/entry.pid" 2> /dev/null); [ -n "$epid" ] && kill -TERM "$epid" 2> /dev/null;;
  esac
  [ -n "$pid" ] && kill -TERM "$pid" 2> /dev/null
  for i in $(seq 1 60); do
    { [ -z "$pid" ] || ! kill -0 "$pid" 2> /dev/null; } && { [ -z "$epid" ] || ! kill -0 "$epid" 2> /dev/null; } && return 0
    sleep 1
  done
  [ -n "$pid" ] && kill -KILL "$pid" 2> /dev/null
  [ -n "$epid" ] && kill -KILL "$epid" 2> /dev/null
  return 0
}

# ------------------------------------------------------------------------------------------------------------------------------- gpus
# lra_gpu_check LOG: the GPUs the SERVER will see: infra/orgserver/gpu_probe.py inside the image with the server's own runtime flags
# (podman-hpc --gpu, shifter --module, apptainer --nv, docker --gpus all) and environment; NVML as vLLM uses it, else nvidia-smi.
# Under Shifter the first module that shows GPUs wins ($LRA_SHIFTER_MODULES, gpu, nvidia, none) and stays in LRA_SHIFTER_MODULES.
# Sets LRA_GPU_N, LRA_GPU_A100 (how many of them are A100s), LRA_GPU_NVLINK (1: the first 4 all connected by NVLink) and
# LRA_GPU_NAMES. Returns 1 when the container sees no GPU at all. The probe's output is appended to LOG.
lra_gpu_check() {
  local log=$1 m out gl mods=("${LRA_SHIFTER_MODULES:-}")
  LRA_GPU_N=0 LRA_GPU_A100=0 LRA_GPU_NVLINK=0 LRA_GPU_NAMES=""
  [ "$LRA_RT" = shifter ] && mods+=(gpu nvidia "")
  for m in "${mods[@]}"; do
    LRA_SHIFTER_MODULES=$m
    [ "$LRA_RT" = shifter ] && echo "== shifter --module=${m:-<none>}" >> "$log"
    out=$(lra_in_image gpu python3 "$LRA_PKG/infra/orgserver/gpu_probe.py" 2>> "$log"); echo "$out" >> "$log"
    # one line per GPU index (rc1 review of b97: a probe that printed its NVML lines and then the nvidia-smi fallback's must not count twice)
    gl=$(printf '%s\n' "$out" | grep '^GPU [0-9][0-9]*:' | sort -t: -k1,1 -u)
    LRA_GPU_N=$(printf '%s\n' "$gl" | grep -c '^GPU [0-9]')
    [ "$LRA_GPU_N" -gt 0 ] && break
  done
  [ "$LRA_GPU_N" -gt 0 ] || return 1
  LRA_GPU_A100=$(printf '%s\n' "$gl" | grep -c 'A100')
  LRA_GPU_NAMES=$(printf '%s\n' "$gl" | sed 's/^GPU [0-9]*: //' | sort | uniq -c | sed 's/^ *//' | paste -sd, -)
  printf '%s\n' "$out" | grep -q '^NVLINK 1' && LRA_GPU_NVLINK=1
  return 0
}

# ------------------------------------------------------------------------------------------------------------------------------ server
# the server's environment (run.sh, setup.sh's warm start): 127.0.0.1:8000 without key or TLS, the model cache offline, no telemetry,
# every cache in the work directory (not $HOME)
lra_server_env() {
  export VLLM_WORKSPACE="$LRA_WS" VLLM_HOST="${LRA_VLLM_HOST:-127.0.0.1}" VLLM_PORT="${LRA_VLLM_PORT:-8000}"
  export HF_HUB_OFFLINE="${LRA_HF_OFFLINE:-1}" HF_HUB_DISABLE_TELEMETRY=1 VLLM_NO_USAGE_STATS=1 DO_NOT_TRACK=1
  # LRA_MODEL_PATH (setup.sh: the verified local snapshot of the pinned revision): run_vllm.sh serves that directory, so no model, config
  # or tokenizer lookup can reach the hub (2026-11-01); unset: the repository id at the pinned revision, as on our rentals
  [ -n "${LRA_MODEL_PATH:-}" ] && export LRA_MODEL_PATH
  export VLLM_CACHE_ROOT="$LRA_WS/cache/vllm" TRITON_CACHE_DIR="$LRA_WS/cache/triton" TORCHINDUCTOR_CACHE_DIR="$LRA_WS/cache/inductor"
  export XDG_CACHE_HOME="$LRA_WS/cache"
  mkdir -p "$LRA_WS/cache"
}

# lra_server_loop LOG STOPFILE PIDFILE: (run in the background) start the server and restart it when it exits, until STOPFILE exists;
# at most LRA_SERVER_RESTARTS (5) restarts, 60 s apart; PIDFILE holds the running runtime client's pid; vllm.log of a server that
# exited is kept as vllm.log.<n>
lra_server_loop() {
  local log=$1 stop=$2 pidf=$3 n=0 rc
  while [ ! -f "$stop" ]; do
    case "$LRA_RT" in podman-hpc|docker) [ -n "${LRA_CONTAINER_NAME:-}" ] && timeout 120 "$LRA_RT" rm -f "$LRA_CONTAINER_NAME" > /dev/null 2>&1;; esac
    lra_log "server start $n: runtime $LRA_RT, image $(lra_image_ref "$LRA_RT"), model ${LRA_MODEL_PATH:-$LRA_MODEL_REPO@$LRA_MODEL_REV}, http://$VLLM_HOST:$VLLM_PORT/v1" >> "$log"
    ( export LRA_EXEC=1; lra_in_image gpu bash "$LRA_PKG/infra/orgserver/vllm_entry.sh" ) >> "$log" 2>&1 &
    echo "$!" > "$pidf"
    wait "$!"; rc=$?
    lra_log "server exited (rc $rc)" >> "$log"
    [ -f "$stop" ] && break
    [ -f "$LRA_WS/vllm.log" ] && mv -f "$LRA_WS/vllm.log" "$LRA_WS/vllm.log.$n"
    n=$((n + 1))
    if [ "$n" -gt "${LRA_SERVER_RESTARTS:-5}" ]; then lra_log "server: $n starts failed, no more restarts" >> "$log"; break; fi
    sleep 60
  done
}

# lra_server_stop STOPFILE PIDFILE LOOP_PID
lra_server_stop() {
  touch "$1"
  lra_stop_container "$(cat "$2" 2> /dev/null)"
  [ -n "${3:-}" ] && { kill -TERM "$3" 2> /dev/null; wait "$3" 2> /dev/null; }
  return 0
}
