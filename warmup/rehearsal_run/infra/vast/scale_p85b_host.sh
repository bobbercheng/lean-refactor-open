#!/usr/bin/env bash
# ON the A100 host (Iowa 58520692): the worker-scaling test (operator 2026-10-31 ~06:45 UTC: "yes, please"), moved from p85's end-stage
# window (lost to the 10:05 outbid) to p85b's (agent deadline Nov 1 01:15 UTC; the end stage is CPU only, 256 cores). (1) wait for
# p85b's "end stage:" line and no agent.py (bounded: not started by Nov 1 02:00 UTC -> NOT run); (2) vLLM -> std32 (--max-num-seqs 32,
# graphs to 32) via vllm_recipe_host.sh (FORCE=1: p85b's driver is alive but its end stage never calls the server); (3) phases of 12 and
# 16 workers, 20 min each, fresh sessions from the seed on p85's 18 rows (out-scale<N>, --max-sessions 1, nice 10), a sample every 15 s;
# (4) summary + the runbook rule (16 only if gen >= 1.10 x p12, kv_max <= 0.60, waiting 0) -> /workspace/lra-run-p85b/WORKERS_WHY;
# vLLM back to std unless 16 won. ABORT at any point (own sessions stopped) on /workspace/scale.abort or a package driver other than
# p85b's (= the official run started).
set -u
W=/workspace; S=$W/scale; mkdir -p $S; ts() { date -u +%H:%M:%S; }; log() { echo "[$(ts)] $*" | tee -a $S/scale.log; }
K=$(cat /root/.config/vexorium/vllm_api_key)
END=$(date -d "2026-11-01 02:00 UTC" +%s)
aborted() { [ -e $W/scale.abort ] && return 0; pgrep -af "[o]pen_package.py run" | grep -v -- "--tag p85b " | grep -q .; }
stop_phase() {  # $1 = workers, $2 = driver pid
  kill -STOP $2 2>/dev/null
  for g in $(ps -eo pgid,args | grep -E "[h]arness/agent.py .*--run-id scale$1-" | awk '{print $1}' | sort -u); do kill -TERM -- -$g 2>/dev/null; done
  sleep 10
  for g in $(ps -eo pgid,args | grep -E "[h]arness/agent.py .*--run-id scale$1-" | awk '{print $1}' | sort -u); do kill -KILL -- -$g 2>/dev/null; done
  kill -KILL $2 2>/dev/null; sleep 3
  log "phase $1 workers: stopped (agents left $(pgrep -fc "[h]arness/agent.py .*--run-id scale$1-"))"
}
log "p85b scale test armed: waiting for p85b's end stage"
until grep -q "end stage: " $W/lra-run-p85b/driver.log 2>/dev/null && ! pgrep -f "[h]arness/agent.py" > /dev/null; do
  aborted && { log "ABORT before start (official run or scale.abort): test NOT run"; exit 1; }
  [ $(date +%s) -gt $END ] && { log "p85b agent stage not over by 02:00: test NOT run"; exit 1; }; sleep 30; done
log "p85b agent stage over: $(grep 'end stage: ' $W/lra-run-p85b/driver.log | tail -1 | cut -c1-120)"
aborted && { log "ABORT before vLLM restart: test NOT run"; exit 1; }
[ -f $W/run_vllm_std.sh ] || cp $W/run_vllm.sh $W/run_vllm_std.sh
FORCE=1 bash $W/vllm_recipe_host.sh std32 2>&1 | tee -a $S/scale.log | tail -1 | grep -q "VLLM OK std32" || { log "std32 not up: test NOT run"; exit 1; }
cd $W/lra || exit 1
export LRA_API_KEY_FILE=""; . infra/vast/endpoint.sh; export LRA_NO_GCS=1 LRA_NO_WANDB=1
sample() {
  m=$(curl -sk --max-time 10 -H "Authorization: Bearer $K" https://localhost:8000/metrics)
  g() { echo "$m" | grep -E "^vllm:$1\{" | awk '{s+=$2} END {print s+0}'; }
  gpu=$(nvidia-smi --query-gpu=utilization.memory,power.draw --format=csv,noheader,nounits | awk -F', ' '{u+=$1; p+=$2} END {printf "%.1f,%.1f", u/NR, p/NR}')
  echo "$1,$(date +%s),$(g num_requests_running),$(g num_requests_waiting),$(g kv_cache_usage_perc),$(g generation_tokens_total),$(g prompt_tokens_total),$gpu" >> $S/samples.csv
}
AB=0
for NW in 12 16; do
  O=$W/out-scale$NW; mkdir -p $O
  log "phase $NW workers: start"
  nice -n 10 python3 harness/open_package.py agent --rows $W/lra-run/rows.jsonl --heartbeats $W/lra-run/heartbeats.jsonl --out $O \
    --tag scale$NW --base-url https://lra-a100:8000/v1 --api-key-file /root/.config/vexorium/vllm_api_key --api-model glm-5.3-flash \
    --started-at $(date +%s) --job-seconds 4800 --end-seconds 60 --workers $NW --max-sessions 1 > $S/driver$NW.log 2>&1 &
  DP=$!
  T0=$(date +%s); while [ $(( $(date +%s) - T0 )) -lt 1200 ]; do aborted && { AB=1; break; }; sample p$NW; sleep 15; done
  stop_phase $NW $DP
  [ $AB = 1 ] && { log "ABORT in phase $NW (official run or scale.abort): own sessions stopped; vLLM left to official.sh's vllm phase"; exit 1; }
done
python3 - $S <<'PY' | tee -a $S/scale.log
import csv, json, sys
S = sys.argv[1]; rows = list(csv.reader(open(f"{S}/samples.csv")))
out = {}
for ph in sorted({r[0] for r in rows}, key=lambda p: int(p[1:])):
    R = [r for r in rows if r[0] == ph][12:]          # the first 3 min are warm-up
    if len(R) < 4: continue
    t = [float(r[1]) for r in R]; gen = [float(r[5]) for r in R]
    run = [float(r[2]) for r in R]
    out[ph] = {"samples": len(R), "gen_tok_s": round((gen[-1] - gen[0]) / (t[-1] - t[0]), 1), "running_mean": round(sum(run) / len(run), 2),
               "per_stream_tok_s": round((gen[-1] - gen[0]) / (t[-1] - t[0]) / max(0.1, sum(run) / len(run)), 1),
               "waiting_mean": round(sum(float(r[3]) for r in R) / len(R), 2), "kv_mean": round(sum(float(r[4]) for r in R) / len(R), 3),
               "kv_max": round(max(float(r[4]) for r in R), 3), "gpu_mem_util_mean": round(sum(float(r[7]) for r in R) / len(R), 1),
               "gpu_power_mean_w": round(sum(float(r[8]) for r in R) / len(R), 1)}
p12, p16 = out.get("p12"), out.get("p16")
ok = bool(p12 and p16 and p16["gen_tok_s"] >= 1.10 * p12["gen_tok_s"] and p16["kv_max"] <= 0.60 and p16["waiting_mean"] == 0)
why = (f"WORKERS={16 if ok else 12}: p16 gen {p16 and p16['gen_tok_s']} vs 1.10 x p12 {p12 and round(1.10 * p12['gen_tok_s'], 1)}, "
       f"p16 kv_max {p16 and p16['kv_max']} (<= 0.60), p16 waiting {p16 and p16['waiting_mean']} (== 0)")
out["decision"] = why
json.dump(out, open(f"{S}/summary.json", "w"), indent=1); open("/workspace/lra-run-p85b/WORKERS_WHY", "w").write(why + "\n"); print(json.dumps(out))
PY
grep -q "^WORKERS=16" $W/lra-run-p85b/WORKERS_WHY || { log "16 not adopted: vLLM back to std"; FORCE=1 bash $W/vllm_recipe_host.sh std 2>&1 | tee -a $S/scale.log | tail -1; }
log "scale test done"
