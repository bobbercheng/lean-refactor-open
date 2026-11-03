#!/usr/bin/env bash
# The vLLM server of a run on the organizers' server (2026-10-31; README.md). run.sh starts this inside the pinned image (or on the host
# with LRA_RUNTIME=none): infra/vast/run_vllm.sh, the measured recipe with its flags unchanged, on VLLM_WORKSPACE (model cache hf/,
# vllm.log, vllm.pid, READY) bound to VLLM_HOST:VLLM_PORT (run.sh: 127.0.0.1:8000, no key, no TLS), in its own process group; then this
# script stays in the foreground while the server lives, so the container (or the srun / shifter step) lasts exactly as long as the
# server. SIGTERM / SIGINT stop the server's whole process group (API server, engine, the 4 GPU workers: SIGTERM, SIGKILL after 30 s).
# Exits 1 when the server is gone (run.sh restarts it).
set -u
W=${VLLM_WORKSPACE:?VLLM_WORKSPACE (the work directory) is required}
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
mkdir -p "$W/cache"
URL="http://127.0.0.1:${VLLM_PORT:-8000}/v1/models"
pgid_of() { sed 's/.*) //' "/proc/$1/stat" 2> /dev/null | awk '{print $3}'; }
up() { if command -v curl > /dev/null 2>&1; then curl -sf -o /dev/null "$URL"; else python3 -c "import urllib.request,sys; urllib.request.urlopen(sys.argv[1], timeout=5)" "$URL" 2> /dev/null; fi; }
PID=""; RV=""
stop() {
  local g
  [ -n "$PID" ] || PID=$(cat "$W/vllm.pid" 2> /dev/null)
  [ -n "$PID" ] && g=$(pgid_of "$PID")
  if [ -n "${g:-}" ] && [ "$g" != "$(pgid_of $$)" ]; then
    kill -TERM -- "-$g" 2> /dev/null
    for _ in $(seq 1 30); do kill -0 -- "-$g" 2> /dev/null || break; sleep 1; done
    kill -KILL -- "-$g" 2> /dev/null
  elif [ -n "$PID" ]; then
    kill -TERM "$PID" 2> /dev/null; sleep 10; kill -KILL "$PID" 2> /dev/null
  fi
  [ -n "$RV" ] && kill -TERM "$RV" 2> /dev/null
  echo "[vllm_entry] server stopped"; exit 143
}
trap stop TERM INT
echo "$$" > "$W/entry.pid"   # run.sh signals this process to stop the server (lra_stop_container)
rm -f "$W/vllm.pid"
# run_vllm.sh in a session of its own (setsid --wait: this script waits for it; `vllm serve` and its workers keep that process group)
if command -v setsid > /dev/null 2>&1 && setsid --help 2>&1 | grep -q -- "--wait"; then
  setsid --wait bash "$HERE/infra/vast/run_vllm.sh" &
else
  bash "$HERE/infra/vast/run_vllm.sh" &
fi
RV=$!
wait "$RV"
echo "[vllm_entry] run_vllm.sh returned $?"
PID=$(cat "$W/vllm.pid" 2> /dev/null)
while :; do
  if [ -n "$PID" ] && kill -0 "$PID" 2> /dev/null; then :; elif up; then :; else break; fi
  sleep 10 & wait $!
done
echo "[vllm_entry] the server (pid ${PID:-?}) is gone; see $W/vllm.log"
exit 1
