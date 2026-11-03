#!/usr/bin/env bash
# ON the NC box (operator 2026-10-31 ~18:15 UTC, "close the 90 gap ... nothing to lose"): a SECOND, blind-start lineage for each stuck
# row (SKI, CCS, Inits: ~0 gain per session in the main lineage), beside the p85b driver, never touching its state: own work root
# /workspace/out-blind/work, own run ids p85b-blind-<i>-k<k>; first session --fresh --blind-start (statement + facts sheet, no original),
# later sessions continue the blind lineage's own best; same server/flags/card as the driver's sessions; until the agent deadline.
set -u
W=/workspace; OB=$W/out-blind; mkdir -p $OB/work $OB/logs; L=$OB/lineages.log; log() { echo "[$(date -u +%H:%M:%S)] $*" >> $L; }
DEADLINE=$(date -d "2026-11-01 09:15 UTC" +%s)
cd $W/lra || exit 1
. infra/vast/endpoint.sh 2>/dev/null
run_row() {   # $1 = index, $2 = row name
  local i=$1 n=$2 k=1
  while [ $(date +%s) -lt $((DEADLINE - 1200)) ] && [ ! -e $OB/STOP ]; do
    local extra=""; [ $k = 1 ] && extra="--fresh --blind-start"
    log "row $i ($n) blind lineage session k$k starts $extra"
    timeout $((DEADLINE - $(date +%s))) python3 harness/agent.py --open-package --endpoint openai --base-url https://lra-a100:8000/v1 \
      --model glm-5.3-flash --api-model glm-5.3-flash --serving-tag vllm-a100-awq-w4a16 --problems "$n" --workers 1 --turns 60 \
      --max-tokens 6000 --reasoning-effort default --work-root $OB/work --run-id p85b-blind-$i-k$k --rows $W/lra-run-p85b/rows.jsonl \
      --heartbeats $W/lra-run-p85b/heartbeats.jsonl --max-api-retries 20 --api-key-file /root/.config/vexorium/vllm_api_key \
      --adaptive-low-turns 90 --compact-tool-json --skeleton-combinator-holes --open-card=$W/p85c/open_card_dialect.md $extra \
      > $OB/logs/b$i.k$k.log 2>&1
    log "row $i session k$k rc $? best $(python3 -c "import json,re,sys; print(json.load(open('$OB/work/'+re.sub(r'[^A-Za-z0-9_.-]','_','$n')+'/state.json'))['best']['score'])" 2>/dev/null)"
    k=$((k + 1)); sleep 5
  done
}
run_row 07 "Cslib.SKI.parallelReduction_diamond" &
run_row 08 "Cslib.CCS.bisimilarity_congr_choice" &
run_row 02 "Core.InitsUpdatesComm" &
log "3 blind lineages started (SKI, CCS, Inits); stop: touch $OB/STOP"
wait
