#!/usr/bin/env bash
# Runs ON the A100 host (started over SSH, detached). 2026-10-30, after the 08:14 UTC bore.pub tunnel loss (the client hung on a dead
# connection, no timeout, the boot loop restarts it only on exit, and the run had no other status path):
#  1. tunnel port 22 through OUR bore server (operator: "use our own bore server bore.vexorium.net"), post "tunnel HOST:PORT" to ntfy;
#  2. watchdog: every 120 s connect to our own public port and expect the SSH banner; 2 misses in a row = kill the client, restart, post;
#  3. heartbeat: every 15 min post one status line (driver / agents / vLLM / GPU / sessions done / mean): status never depends on SSH.
# The boot script's bore.pub loop keeps running beside it as a second path. No secret in any message.
T=$(cat /workspace/ntfy_topic 2>/dev/null); S=bore.vexorium.net; RUN_DIR=${RUN_DIR:-/workspace/lra-run-pkg1}; export OUT_DIR=${OUT_DIR:-/workspace/out-pkg1}
n() { python3 -c "import sys,urllib.request; urllib.request.urlopen(urllib.request.Request('https://ntfy.sh/'+sys.argv[1], data=' '.join(sys.argv[2:]).encode()), timeout=20)" "$T" "$@" 2>/dev/null; }
B=/tmp/bore; [ -x $B ] || { cd /tmp && python3 -c "import urllib.request; urllib.request.urlretrieve('https://github.com/ekzhang/bore/releases/download/v0.5.2/bore-v0.5.2-x86_64-unknown-linux-musl.tar.gz', '/tmp/b.tgz')" && tar xzf b.tgz && chmod +x bore; }
hb() {
  L=$RUN_DIR/driver.log
  n "hb $(date -u +%H:%M) driver=$(pgrep -c -f '[o]pen_package.py run') agents=$(pgrep -c -f '[h]arness/agent.py') vllm=$(pgrep -c -f '[v]llm serve') ready=$([ -e /workspace/READY ] && echo 1 || echo 0) gpu=$(nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits 2>/dev/null | tr '\n' ',' ) done=$(grep -cE 'session [0-9]+ done' $L 2>/dev/null) last=$(grep -E 'session [0-9]+ done' $L 2>/dev/null | tail -1 | grep -oE 'mean [0-9.]+') summary=$([ -f ${OUT_DIR:-/workspace/out-pkg1}/summary.json ] && echo yes || echo no)"
}
st() {   # status file for the GCS sidecar (operator: the A100 must sync its status to the bucket; read it from the GB10)
  L=$RUN_DIR/driver.log; mkdir -p /workspace/lra/reh
  python3 - "$L" > /workspace/lra/reh/status.json.tmp 2>/dev/null <<'PY' && mv /workspace/lra/reh/status.json.tmp /workspace/lra/reh/status.json
import json, os, re, subprocess, sys, time
L = sys.argv[1]
def c(p):
    return int(subprocess.run(["pgrep", "-c", "-f", p], capture_output=True, text=True).stdout.strip() or 0)
txt = open(L, errors="replace").read() if os.path.exists(L) else ""
done = re.findall(r"row#(\d+) session (\d+) done \(rc (\d+)\): ([0-9.]+) -> ([0-9.]+) in (\d+) s; .*?mean ([0-9.]+)", txt)
try:
    gpu = subprocess.run(["nvidia-smi", "--query-gpu=utilization.gpu", "--format=csv,noheader,nounits"], capture_output=True, text=True, timeout=20).stdout.split()
except Exception:
    gpu = []
print(json.dumps({"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "epoch": int(time.time()), "driver": c("[o]pen_package.py run"),
                  "agents": c("[h]arness/agent.py"), "vllm": c("[v]llm serve"), "ready": os.path.exists("/workspace/READY"), "gpu": gpu,
                  "sessions_done": len(done), "mean": float(done[-1][6]) if done else None,
                  "last": [{"row": int(r), "k": int(k), "rc": int(rc), "from": float(a), "to": float(b), "s": int(s)} for r, k, rc, a, b, s, _ in done[-5:]],
                  "summary": os.path.exists(os.environ.get("OUT_DIR", "/workspace/out-pkg1") + "/summary.json"),
                  "agent_stage_done": os.path.exists(os.environ.get("OUT_DIR", "/workspace/out-pkg1") + "/agent_stage.json"), "run_dir": os.path.dirname(L)}))
PY
}
last_hb=0
# STATUS_ONLY=1 (2026-10-30, rental p85): the boot script's own bore client already holds the fixed port and runs its watchdog, so this
# process only writes the status file for the GCS sidecar every 120 s and posts the 15-min heartbeat; it never starts a tunnel
if [ "${STATUS_ONLY:-0}" = 1 ]; then
  while :; do st; now=$(date +%s); [ $((now - last_hb)) -ge 900 ] && { hb; last_hb=$now; }; sleep 120; done
fi
while :; do
  : > /tmp/borev.log
  # a FIXED port on our server (2026-10-30: ntfy.sh dropped the host's port announcements, so the GB10 kept a dead address; a fixed port
  # needs no announcement); a random port only if the fixed one is refused
  $B local 22 --to $S --port ${BORE_PORT:?set BORE_PORT} > /tmp/borev.log 2>&1 &
  sleep 3; grep -q "listening at" /tmp/borev.log || { kill $! 2>/dev/null; $B local 22 --to $S > /tmp/borev.log 2>&1 & }
  BP=$!; port=""
  for i in $(seq 1 30); do port=$(grep -oE "$S:[0-9]+" /tmp/borev.log | tail -1 | cut -d: -f2); [ -n "$port" ] && break; sleep 1; done
  if [ -n "$port" ]; then n "tunnel $S:$port"; else n "tunnel $S: no port after 30 s ($(tail -1 /tmp/borev.log | cut -c1-120))"; fi
  fails=0
  while kill -0 $BP 2>/dev/null; do
    st; now=$(date +%s); [ $((now - last_hb)) -ge 900 ] && { hb; last_hb=$now; }
    sleep 120
    [ -n "$port" ] || break
    if timeout 10 bash -c "exec 3<>/dev/tcp/$S/$port; head -c 7 <&3" 2>/dev/null | grep -q SSH; then fails=0; else fails=$((fails + 1)); fi
    [ $fails -ge 2 ] && { n "tunnel $S:$port failed 2 checks: restarting bore"; kill $BP 2>/dev/null; break; }
  done
  sleep 5
done
