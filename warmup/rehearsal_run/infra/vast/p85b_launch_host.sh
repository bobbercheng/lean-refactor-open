#!/usr/bin/env bash
# ON the A100 host: the p85b CONTINUATION launcher (operator 2026-10-31 07:15 UTC: after p85, continue toward 85 on the warm-up 15 from p85's
# own state, same package, from-seed lineage; docs/open_official_run_runbook.md section 1). Armed detached; executes by itself:
#  1. waits, bounded by WAIT_UNTIL (default 2026-10-31 18:00 UTC; past it: NOT launched, ntfy push), until
#     p85 is DONE  (W/out/summary.json exists and no `open_package.py run ... --out W/out ` process) AND
#     the scaling test is DONE  (W/scale/scale.log says "scale test done" or "NOT run", or no scale_test_host.sh process) AND no scale-test
#     session is left (an orphan after an abnormal exit is stopped by pid after 10 min) AND W/READY (vLLM up);
#  2. picks the workers from W/scale/summary.json: 16 only if p16 gen_tok_s >= 1.10 x p12's AND p16 kv_max <= 0.60 AND p16 waiting_mean == 0,
#     else 12; the reason goes to RUN_DIR/WORKERS_WHY and the log;
#  3. RUN_DIR = W/lra-run-p85b: rows.jsonl = p85's rows (ROWS_SET=warmup15: the 15 warm-up rows, LeanPool dropped; all18 keeps them),
#     heartbeats.jsonl = p85's; OUT = W/out-p85b: work/<row>/ copied from p85's W/out/work/<row>/ (state.json = best + attempts + runs + ledger,
#     notes.md, the workspace files) so every row RESUMES from p85's banked best (open_package.py: --fresh only when the row has no
#     state.json); NOT copied: agent_sessions.jsonl (the session count and the room schedule start fresh under the new tag), end-pipe/,
#     end/, normalize (p85b polishes its own bests; p85's export stays in W/out/proofs.jsonl for the measurement);
#     SEED_FROM_EXPORT=1 (off by default): a row whose p85 export (end / normalize) scored above its agent best starts from that proof;
#  4. starts the driver with W/lra/infra/vast/package_run.sh, exactly the way p85 was started (endpoint preflight, envs check, disk check;
#     writes RUN_DIR/RUN_CMD, RUN_ENV, relaunch.sh; onstart.sh's /workspace/lra-run*/relaunch.sh hook and the GB10 watch cover an outbid
#     resume): TAG=p85b, START=now, JOB=END_AT-now, WORKERS=W, MAX_SESSIONS=6, END_SECONDS=7200, EXTRA="--end-pipeline on" (no --style-rw,
#     no --blind-start); RUN_CMD is diffed against p85's in the log;
#  5. the host status writer follows p85b (tunnel_watch_host.sh STATUS_ONLY, restarted by its pid), a GCS sidecar labelled a100-p85b, a push.
# Config, read when it fires (edit it before then; shell assignments): W/p85b.conf
#   END_AT="2026-11-01 04:00 UTC"  ROWS_SET=warmup15  MAX_SESSIONS=6  WORKERS=  (empty = from the scaling test)  SEED_FROM_EXPORT=0
#   WAIT_UNTIL="2026-10-31 18:00 UTC"  MIN_JOB_S=14400 (refuse a job shorter than this)
# Disarm: touch W/p85b.disarm (checked every poll) or kill the pid in W/p85b_launch.pid. Stop p85b later (bests kept, export written): W/package_stop_host.sh W/lra-run-p85b [END_S].
# Idempotent: one launcher at a time (flock W/p85b_launch.lock); RUN_DIR/RUN_CMD present = already launched (relaunch.sh owns restarts).
# Dry run (probe/a100/p85b_dry_run.sh): W=<scratch>/workspace, LRA_BASE_URL=<fake model>, SKIP_AUX=1, DRY_EXTRA="<driver flags>",
# DF_PATH / MIN_FREE_GB passed to package_run.sh, POLL_S short.
set -u
W=${W:-/workspace}; CONF=${CONF:-$W/p85b.conf}; L=${L:-$W/p85b_launch.log}
P85_RUN=$W/lra-run; P85_OUT=$W/out; RUN_DIR=$W/lra-run-p85b; OUT=$W/out-p85b; TAG=p85b; EXPORT_ROOT=${EXPORT_ROOT:-$W/lra}; S=$W/scale
END_AT="2026-11-01 04:00 UTC"; ROWS_SET=warmup15; MAX_SESSIONS=6; WORKERS=""; SEED_FROM_EXPORT=0; WAIT_UNTIL="2026-10-31 18:00 UTC"; MIN_JOB_S=14400
END_SECONDS=${END_SECONDS:-7200}; POLL_S=${POLL_S:-60}
log() { echo "[$(date -u -Is)] p85b: $*" | tee -a "$L"; }
push() { local t; t=$(cat "$W/ntfy_topic" 2>/dev/null); [ -n "$t" ] && [ "${SKIP_AUX:-0}" != 1 ] && curl -fsS -m 20 -H "Title: A100 p85b" -d "$*" "https://ntfy.sh/$t" > /dev/null 2>&1; true; }
exec 9> "$W/p85b_launch.lock"; flock -n 9 || { echo "another p85b launcher holds $W/p85b_launch.lock: leaving"; exit 0; }
echo $$ > "$W/p85b_launch.pid"
[ -f "$CONF" ] && . "$CONF"
[ -f "$RUN_DIR/RUN_CMD" ] && { log "already launched ($RUN_DIR/RUN_CMD exists): relaunch.sh / the GB10 watch own restarts; leaving"; exit 0; }
deadline=$(date -u -d "$WAIT_UNTIL" +%s) || { log "bad WAIT_UNTIL '$WAIT_UNTIL'"; exit 2; }
log "armed: waits for p85 done + scaling test done + READY until $WAIT_UNTIL; config $( [ -f "$CONF" ] && echo "$CONF" || echo defaults): END_AT='$END_AT' ROWS_SET=$ROWS_SET MAX_SESSIONS=$MAX_SESSIONS WORKERS='${WORKERS:-auto}' SEED_FROM_EXPORT=$SEED_FROM_EXPORT"
p85_alive() { pgrep -f "[o]pen_package.py run .*--out $P85_OUT " > /dev/null; }
scale_done() {
  grep -qE "scale test done|NOT run" "$S/scale.log" 2>/dev/null && return 0
  pgrep -f "[s]cale_test_host.sh" > /dev/null && return 1
  return 0
}
scale_agents() { pgrep -f "[h]arness/agent.py .*--run-id scale[0-9]+-" | tr '\n' ' '; }
orphan_since=0; said=""
while :; do
  [ -e "$W/p85b.disarm" ] && { log "disarmed ($W/p85b.disarm): NOT launched"; push "p85b launcher disarmed: not launched"; exit 0; }
  [ -f "$CONF" ] && . "$CONF"   # a config edit before the launch counts
  deadline=$(date -u -d "$WAIT_UNTIL" +%s 2>/dev/null) || deadline=$(date -u -d "2026-10-31 18:00 UTC" +%s)
  now=$(date +%s)
  why=""
  { [ -f "$P85_OUT/summary.json" ] && ! p85_alive; } || why="p85 not done (summary $( [ -f "$P85_OUT/summary.json" ] && echo yes || echo no), driver $(p85_alive && echo alive || echo gone))"
  [ -z "$why" ] && { scale_done || why="scaling test still running"; }
  if [ -z "$why" ]; then
    sa=$(scale_agents)
    if [ -n "$sa" ]; then
      [ "$orphan_since" = 0 ] && orphan_since=$now
      if [ $((now - orphan_since)) -ge 600 ]; then
        log "WARN scale-test session(s) left 10 min after the test ended: stopping pids $sa (TERM, then KILL)"; kill -TERM $sa 2>/dev/null; sleep 15
        sa=$(scale_agents); [ -n "$sa" ] && kill -KILL $sa 2>/dev/null
      else why="scale-test sessions still running ($sa)"; fi
    fi
  fi
  [ -z "$why" ] && { [ -e "$W/READY" ] || [ -n "${LRA_BASE_URL:-}" ] || why="vLLM not READY"; }
  [ -z "$why" ] && break
  [ "$why" != "$said" ] && { log "waiting: $why"; said=$why; }
  [ "$now" -ge "$deadline" ] && { log "NOT launched: still '$why' at $WAIT_UNTIL"; push "p85b NOT launched: $why at $WAIT_UNTIL (operator: launch by hand, docs/open_official_run_runbook.md 1.4)"; exit 1; }
  sleep "$POLL_S"
done
log "conditions met: p85 done ($(python3 -c "import json; d=json.load(open('$P85_OUT/summary.json')); print('stored mean', d.get('stored_mean'), 'sources', d.get('sources'))" 2>/dev/null)); scaling test: $(tail -n 1 "$S/scale.log" 2>/dev/null | cut -c1-120)"
# ---- 2. workers
if [ -n "${WORKERS:-}" ]; then NW=$WORKERS; WHY="config override WORKERS=$WORKERS"
else
  read -r NW WHY < <(python3 - "$S/summary.json" <<'PY'
import json, sys
try:
    d = json.load(open(sys.argv[1]))
    a, b = d["p12"], d["p16"]
    g12, g16 = float(a["gen_tok_s"]), float(b["gen_tok_s"]); kv, wt = float(b["kv_max"]), float(b["waiting_mean"])
except Exception as e:  # noqa: BLE001
    print(12, f"no usable scaling summary ({type(e).__name__}: {str(e)[:80]}): 12 (p85's worker count)"); sys.exit()
r = g16 / g12 if g12 > 0 else 0.0
ok = r >= 1.10 and kv <= 0.60 and wt == 0
print(16 if ok else 12, f"p16/p12 total gen {g16:.1f}/{g12:.1f} = {r:.3f} ({'>=' if r >= 1.10 else '<'} 1.10), p16 kv_max {kv:.3f} "
      f"({'<=' if kv <= 0.60 else '>'} 0.60), p16 waiting_mean {wt:g} ({'none' if wt == 0 else 'waiting'}): {16 if ok else 12}")
PY
)
fi
[ -n "${NW:-}" ] || { NW=12; WHY="worker pick failed: 12"; }
log "workers $NW: $WHY"
# ---- 3. run dir, rows, per-row state
now=$(date +%s); END_EPOCH=$(date -u -d "$END_AT" +%s) || { log "NOT launched: bad END_AT '$END_AT'"; push "p85b NOT launched: bad END_AT"; exit 2; }
JOB=$((END_EPOCH - now))
[ "$JOB" -ge "$MIN_JOB_S" ] || { log "NOT launched: END_AT $END_AT leaves ${JOB}s (< MIN_JOB_S $MIN_JOB_S)"; push "p85b NOT launched: END_AT too close"; exit 1; }
mkdir -p "$RUN_DIR" "$OUT/work"; printf '%s\n' "$WHY" > "$RUN_DIR/WORKERS_WHY"
python3 - "$P85_RUN" "$P85_OUT" "$RUN_DIR" "$OUT" "$ROWS_SET" "$SEED_FROM_EXPORT" <<'PY' | tee -a "$L"
import json, re, shutil, sys, time
from pathlib import Path
p85_run, p85_out, run_dir, out, rows_set, seed = Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]), Path(sys.argv[4]), sys.argv[5], sys.argv[6] == "1"
safe = lambda n: re.sub(r"[^A-Za-z0-9_.-]", "_", n)   # open_package.safe = agent.py's workspace directory name
lines = [l for l in (p85_run / "rows.jsonl").read_text().splitlines() if l.strip()]
rows = [json.loads(l) for l in lines]
if rows_set == "warmup15":
    keep = [i for i, r in enumerate(rows) if r["source"] != "leanpool"]
    if len(keep) != 15:
        raise SystemExit(f"ROWS_SET=warmup15: {len(keep)} non-LeanPool rows in {p85_run}/rows.jsonl, expected 15")
elif rows_set == "all18":
    keep = list(range(len(rows)))
else:
    raise SystemExit(f"ROWS_SET {rows_set!r}: warmup15 or all18")
(run_dir / "rows.jsonl").write_text("".join(lines[i] + "\n" for i in keep))          # p85's lines, byte for byte, in p85's order
shutil.copyfile(p85_run / "heartbeats.jsonl", run_dir / "heartbeats.jsonl")
exp = {}
if (p85_out / "proofs.jsonl").exists():
    for l in (p85_out / "proofs.jsonl").read_text().splitlines():
        try:
            r = json.loads(l); exp[r["name"]] = r
        except (ValueError, KeyError):
            pass
rep = {"at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "rows_set": rows_set, "seed_from_export": seed, "rows": {}}
for i in keep:
    r = rows[i]; n = r["name"]; src = p85_out / "work" / safe(n); dst = out / "work" / safe(n)
    if dst.exists():
        shutil.rmtree(dst)   # a half copy of an earlier attempt (RUN_CMD was never written): copy again
    if not (src / "state.json").exists():
        rep["rows"][n] = {"state": "none: the row starts --fresh"}; print(f"  {n[:60]}: no p85 state (fresh)"); continue
    tmp = out / "work" / (safe(n) + ".copying"); shutil.rmtree(tmp, ignore_errors=True)
    shutil.copytree(src, tmp, symlinks=True); tmp.rename(dst)
    st = json.loads((dst / "state.json").read_text()); b = st.get("best") or {}
    rec = {"best": b.get("score"), "runs": len(st.get("runs") or []), "attempts": len(st.get("attempts") or [])}
    e = exp.get(n)
    if e:
        rec["p85_export"] = {"source": e.get("source"), "stored_score": e.get("stored_score")}
    if seed and e and e.get("source") in ("end", "normalize") and float(e.get("stored_score") or 0) > float(b.get("score") or 0) \
            and r["statement"].strip() in (e.get("proof") or ""):
        st["best"] = {"score": e["stored_score"], "proof": e["proof"].rstrip() + "\n", "tokens": e.get("tokens"), "heartbeats": e.get("heartbeats"),
                      "seed": f"p85 export ({e['source']})"}
        (dst / "state.json").write_text(json.dumps(st, ensure_ascii=False, indent=1)); (dst / "best.lean").write_text(st["best"]["proof"])
        rec["seeded_from_export"] = e["stored_score"]
    rep["rows"][n] = rec
    print(f"  {n[:60]}: best {rec['best']} ({rec['runs']} earlier runs)" + (f"; p85 export {e.get('source')} {e.get('stored_score')}" if e else "")
          + (f"; SEEDED from the export {rec['seeded_from_export']}" if "seeded_from_export" in rec else ""))
(run_dir / "SEED.json").write_text(json.dumps(rep, indent=1, ensure_ascii=False))
print(f"  {len(keep)} row(s) -> {run_dir}/rows.jsonl; state copied for {sum(1 for v in rep['rows'].values() if 'best' in v)}")
PY
[ "${PIPESTATUS[0]}" = 0 ] || { log "NOT launched: the state copy failed (above)"; push "p85b NOT launched: state copy failed"; exit 1; }
# ---- 4. start the driver the way p85 was started
log "starting: TAG=$TAG START=$now JOB=$JOB (end $(date -u -d @$END_EPOCH +%Y-%m-%dT%H:%MZ)) WORKERS=$NW MAX_SESSIONS=$MAX_SESSIONS END_SECONDS=$END_SECONDS"
( cd "$EXPORT_ROOT" && RUN_DIR=$RUN_DIR OUT=$OUT TAG=$TAG START=$now JOB=$JOB WORKERS=$NW MAX_SESSIONS=$MAX_SESSIONS END_SECONDS=$END_SECONDS \
    EXTRA="--end-pipeline on${DRY_EXTRA:+ $DRY_EXTRA}" MIN_FREE_GB=${MIN_FREE_GB:-20} DF_PATH=${DF_PATH:-$W} bash infra/vast/package_run.sh 9>&- ) 2>&1 | tee -a "$L" | grep -q "driver running" \
  || { log "NOT launched: package_run.sh refused or failed (above); RUN_DIR kept for a manual retry (rm $RUN_DIR/RUN_CMD first if it exists)"; push "p85b NOT launched: package_run.sh refused (see $L)"; exit 1; }
log "RUN_CMD vs p85's (words only in p85 / only in p85b): $(python3 -c "
import sys; a = open('$P85_RUN/RUN_CMD').read().split(); b = open('$RUN_DIR/RUN_CMD').read().split()
print('-', ' '.join(x for x in a if x not in b), '| +', ' '.join(x for x in b if x not in a))" 2>/dev/null)"
# ---- 5. host status + GCS sidecar follow p85b (not in the dry run)
if [ "${SKIP_AUX:-0}" != 1 ]; then
  for p in $(pgrep -f "[t]unnel_watch_host.sh"); do grep -qa "STATUS_ONLY=1" "/proc/$p/environ" 2>/dev/null && { log "status writer $p (p85) stopped by pid"; kill -TERM "$p"; }; done
  sleep 2; STATUS_ONLY=1 RUN_DIR=$RUN_DIR OUT_DIR=$OUT setsid nohup bash "$W/tunnel_watch_host.sh" > "$W/tunnel_watch_p85b.log" 2>&1 < /dev/null 9>&- &
  if ! pgrep -f "[s]idecar.py --label a100-p85b" > /dev/null && [ -f /root/.config/vexorium/gcs_sync_key.json ]; then
    (cd "$W" && PATH=/opt/google-cloud-sdk/bin:$PATH setsid nohup python3 "$W/infra/sync/sidecar.py" --label a100-p85b --key /root/.config/vexorium/gcs_sync_key.json \
       --watch "lra/probe/runs/p85b-*/verified.jsonl" --paths lra/reh/status.json lra-run-p85b out-p85b --snapshot-every 120 > "$W/sidecar_p85b.log" 2>&1 < /dev/null 9>&- &)
  fi
  sleep 5; log "status writer $(pgrep -f '[t]unnel_watch_host.sh' | tr '\n' ' ')/ sidecar a100-p85b $(pgrep -f '[s]idecar.py --label a100-p85b' | tr '\n' ' ')"
fi
printf '{"launched_at": %s, "workers": %s, "workers_why": %s, "end_at": %s, "job_seconds": %s, "rows_set": "%s", "max_sessions": %s, "seed_from_export": %s}\n' \
  "$now" "$NW" "$(python3 -c 'import json,sys; print(json.dumps(sys.argv[1]))' "$WHY")" "$END_EPOCH" "$JOB" "$ROWS_SET" "$MAX_SESSIONS" "$SEED_FROM_EXPORT" > "$RUN_DIR/LAUNCHED.json"
log "LAUNCHED p85b: workers $NW, max-sessions $MAX_SESSIONS, end $(date -u -d @$END_EPOCH +%Y-%m-%dT%H:%MZ), rows $ROWS_SET; driver log $RUN_DIR/driver.log"
push "p85b LAUNCHED: $NW workers ($WHY), max-sessions $MAX_SESSIONS, end $(date -u -d @$END_EPOCH +%m-%dT%H:%MZ), rows $ROWS_SET"
exit 0
