#!/usr/bin/env bash
# DEV ONLY: the $0 dry run of the open package (docs/open_package_readme.md "Dry run"): harness/open_package.py run end to end on two
# NON-benchmark rows (data/abpool: one strata row, one arklib row with three pins) against probe/open_package/fake_model.py (scripted,
# no model). Real Lean: run it only inside a capped unit:
#   systemd-run --user --collect -u lra-opk-dry -p MemoryMax=48G -p OOMPolicy=continue -p RuntimeMaxSec=7200 \
#     -p WorkingDirectory=$PWD -E PATH -E HOME /bin/bash probe/open_package/dry_run.sh [OUT]
# CMD=agent (env): the agent stage + prompt audit, then the export, without the end stage (it does not touch the model-facing path);
# TAG (env): the run-id prefix (default opkdry; a new dry run takes a new one so probe/runs/<tag>-* of earlier runs stay).
# FAKE_DELAY=S (env, 2026-10-28, audit section P, P3): the fake model starts S seconds AFTER the driver, so the first sessions' first calls
# meet a refused connection (a vLLM server still loading) and must wait for it without using an attempt (--max-api-retries 2 here).
# EXTRA (env): more open_package.py arguments (e.g. "--schedule room").
# PICK=name1,name2 (env, 2026-10-29): other data/abpool rows (e.g. a PhysLib row for the section S sorry-guard check);
# LRA_FAKE_SORRY_PROOFS=1 (env): the fake model also offers `stop` / `impossible` bodies (probe/open_package/fake_model.py).
# KNOBS (env, 2026-10-31): the run-size flags, default "--workers 2 --max-sessions 2 --end-seconds 1500" (2 rows on the shared dev box);
# KNOBS="" runs on the package's own defaults (--workers 14 --max-sessions 12 --end-seconds 7200 --end-pipeline on); JOB_S (env, default
# 5400) is --job-seconds: with the default 7,200 s end share it must exceed 7,200 + 1,800 (normalize) + 300 (margin) + 300 (min session).
# PICK_N=N (env): the first N data/abpool rows by name with ONE pin (never a benchmark row), instead of PICK / the two default rows.
set -u
cd "$(dirname "$0")/../.." || exit 2
OUT="${1:-$HOME/source/lra-ab/opk/dry}"
PORT="${PORT:-18471}"
mkdir -p "$OUT"
python3 - "$OUT" <<'PY' || { echo "[dry_run] FAILED: could not prepare the dry-run rows"; exit 1; }
import json, os, sys
out = sys.argv[1]
pick = ["CallElimCorrect.normalizeOldExprInVars", "Code.closeToWord_iff_exists_agreementCols"]
if os.environ.get("PICK"):   # PICK=name1,name2 (env): other data/abpool rows (still never a benchmark row)
    pick = [x for x in os.environ["PICK"].split(",") if x]
rows = {json.loads(l)["name"]: l for l in open("data/abpool/abpool.jsonl") if l.strip()}
if os.environ.get("PICK_N"):   # PICK_N=N (env): the first N one-pin rows by name
    pick = sorted(n for n, l in rows.items() if len(json.loads(l)["version_info"]) == 1)[: int(os.environ["PICK_N"])]
hbs = {json.loads(l)["name"]: l for l in open("data/abpool/heartbeats.jsonl") if l.strip()}
warm = {json.loads(l)["name"] for l in open("data/benchmark_warmup.jsonl") if l.strip()}
assert not (set(pick) & warm), "a dry-run row is a benchmark row"
open(f"{out}/rows.jsonl", "w").write("".join(rows[n].rstrip("\n") + "\n" for n in pick))
open(f"{out}/heartbeats.jsonl", "w").write("".join(hbs[n].rstrip("\n") + "\n" for n in pick))
PY
FAKE_DELAY="${FAKE_DELAY:-0}"
(sleep "$FAKE_DELAY"; echo "[dry_run] fake model starts on port $PORT ($(date -u +%H:%M:%S))"
 exec python3 probe/open_package/fake_model.py --port "$PORT" --log "$OUT/fake_requests.jsonl") &
FAKE=$!
trap 'kill $FAKE 2>/dev/null' EXIT
if [ "$FAKE_DELAY" = 0 ]; then
  for i in $(seq 1 50); do curl -s "http://127.0.0.1:$PORT/v1/models" > /dev/null && break; sleep 0.2; done
fi
CMD="${CMD:-run}"
# shellcheck disable=SC2086
python3 harness/open_package.py "$CMD" --rows "$OUT/rows.jsonl" --heartbeats "$OUT/heartbeats.jsonl" --out "$OUT" --tag "${TAG:-opkdry}" \
  --base-url "http://127.0.0.1:$PORT/v1" ${KNOBS---workers 2 --max-sessions 2 --end-seconds 1500} --turns 9 --no-adaptive-turns --max-api-retries 2 \
  --job-seconds "${JOB_S:-5400}" --export-margin 300 --min-session-seconds 300 --compile-slots 3 --end-jobs 2 ${EXTRA:-}
rc=$?
if [ "$CMD" = agent ]; then
  python3 harness/open_package.py export --rows "$OUT/rows.jsonl" --heartbeats "$OUT/heartbeats.jsonl" --out "$OUT"; rc=$((rc + $?))
fi
echo "rc=$rc"
