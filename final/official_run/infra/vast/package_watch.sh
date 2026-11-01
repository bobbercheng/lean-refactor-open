#!/usr/bin/env bash
# GB10-side watcher of a package run on a rented instance (unit lra-a100-watch; docs/a100_rehearsal.md). Control plane only (SSH, rsync):
# the model path stays on the instance. Every POLL_S (60 s):
#   * instance running + SSH ok: if no `open_package.py run` process is alive and OUT/summary.json does not exist, run RUN_DIR/relaunch.sh
#     there (the resume after an outbid; a container restart ran onstart.sh's hook too, this is the belt to its braces);
#   * every PULL_EVERY_S (300 s): rsync-pull OUT/ (logs, work, agent_sessions.jsonl, end stage, normalize, proofs, summary, token report)
#     and the sessions' probe/runs/<TAG>-*/ into LOCAL (probe/a100-reh-<TAG>/);
#   * no-progress watchdog (review 2026-10-28, finding 8): while a driver is alive and the agent stage is on, no file under OUT/logs or
#     probe/runs/<TAG>-* changed for STALL_MIN (20) minutes -> CRITICAL line + KEPT marker (spend_guard.sh destroys after its grace unless
#     probe/a100-ack-<id>); a later change clears the marker;
#   * done (OUT/summary.json pulled and no driver alive) -> final pull, accounting line, release: destroy.sh (CONFIRM=yes FORCE=yes after a
#     hold of at most HOLD_MAX_S = 1800 s if a probe/a100-hold*-<id> file exists), units stopped; exits.
#   infra/vast/package_watch.sh ID [pull|once|loop]      loop is the default; `pull` = one pull (the spend guard's PRE_DESTROY hook)
# Environment: TAG=reh RUN_DIR=/workspace/lra-run OUT=/workspace/out EXPORT_ROOT=/workspace/lra LOCAL=probe/a100-reh-$TAG
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3 ssh rsync
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd); cd "$ROOT" || exit 2
ID=${1:?instance id}; MODE=${2:-loop}
TAG=${TAG:-reh}; RUN_DIR=${RUN_DIR:-/workspace/lra-run}; OUT=${OUT:-/workspace/out}; EXPORT_ROOT=${EXPORT_ROOT:-/workspace/lra}
LOCAL=${LOCAL:-probe/a100-reh-$TAG}; L=$LOCAL/watch.log; ACC=accounting/a100_poc.md
POLL_S=${POLL_S:-60}; PULL_EVERY_S=${PULL_EVERY_S:-300}; STALL_MIN=${STALL_MIN:-20}; HOLD_MAX_S=${HOLD_MAX_S:-1800}; SSH_TIMEOUT=${SSH_TIMEOUT:-40}
mkdir -p "$LOCAL/out" "$LOCAL/runs"
log() { echo "[$(date -u -Is)] $*" | tee -a "$L"; }
addr() { vastai show instance "$ID" --raw 2>/dev/null | python3 -c "import json, sys; d = json.load(sys.stdin); p = (d.get('ports') or {}).get('22/tcp') or [{}]; print(d.get('actual_status') or '?', d.get('public_ipaddr') or '-', p[0].get('HostPort') or '-', float(d.get('dph_total') or 0))" 2>/dev/null; }
# REH_LOCAL_DIR (the $0 dry run): the "instance" is a local directory; commands run here, pulls are local copies
rsh() { if [ -n "${REH_LOCAL_DIR:-}" ]; then (cd "$REH_LOCAL_DIR" && timeout "$SSH_TIMEOUT" bash -c "$1"); else timeout "$SSH_TIMEOUT" ssh -i "$HOME/.ssh/id_ed25519" -o BatchMode=yes -o ConnectTimeout=15 -o StrictHostKeyChecking=accept-new -p "$PT" "root@$IP" "$1" 2>/dev/null | grep -v "^Welcome\|^Have fun"; fi; }
pull() {   # bounded rsync of OUT and the sessions' run dirs
  if [ -n "${REH_LOCAL_DIR:-}" ]; then
    rsync -a --timeout=120 "$OUT/" "$LOCAL/out/" 2>/dev/null; rsync -a --timeout=120 --include="$TAG-*/" --include="$TAG-*/**" --exclude='*' "$EXPORT_ROOT/probe/runs/" "$LOCAL/runs/" 2>/dev/null   # local mode: OUT / EXPORT_ROOT are the local paths
  else
    local e="ssh -i $HOME/.ssh/id_ed25519 -o BatchMode=yes -o ConnectTimeout=15 -o StrictHostKeyChecking=accept-new -p $PT"
    timeout 900 rsync -az --timeout=120 -e "$e" "root@$IP:$OUT/" "$LOCAL/out/" 2>/dev/null
    timeout 900 rsync -az --timeout=120 -e "$e" --include="$TAG-*/" --include="$TAG-*/**" --exclude='*' "root@$IP:$EXPORT_ROOT/probe/runs/" "$LOCAL/runs/" 2>/dev/null
  fi
  log "pulled: $(ls "$LOCAL/out" 2>/dev/null | wc -l) entries in out/, $(ls -d "$LOCAL"/runs/* 2>/dev/null | wc -l) run dir(s)$( [ -f "$LOCAL/out/summary.json" ] && echo '; summary.json present')"
}
release() {   # $1 = reason
  local h waited=0
  for h in probe/a100-hold*-"$ID"; do [ -e "$h" ] || continue
    log "hold file $h ($(cat "$h")): waiting at most ${HOLD_MAX_S}s before the release"
    while [ -e "$h" ] && [ "$waited" -lt "$HOLD_MAX_S" ]; do sleep 30; waited=$((waited + 30)); done
  done
  touch "probe/a100-pause-$ID"
  if CONFIRM=yes FORCE=yes "$HERE/destroy.sh" "$ID" >> "$L" 2>&1; then log "released $ID ($1)"; else log "DESTROY FAILED for $ID ($1): the spend guard retries; act by hand (vastai destroy instance $ID -y)"; fi
  systemctl --user stop "lra-a100-sentry$U" "lra-a100-bid$U" "lra-bridge$U" "lra-health$U" 2>/dev/null; true
}
read -r ST IP PT DPH <<< "$(addr)"
[ -n "${REH_LOCAL_DIR:-}" ] && { ST=running; IP=local; PT=0; DPH=${DPH:-0}; }
if [ "$MODE" = pull ]; then [ "$ST" = running ] || { log "pull: instance $ST; nothing pulled"; exit 1; }; pull; exit 0; fi
log "watch $ID: tag $TAG, poll ${POLL_S}s, pull every ${PULL_EVERY_S}s, stall ${STALL_MIN} min, local $LOCAL"
last_pull=0; last_change=$(date +%s); stall_said=0; gone=0; T0=$(date +%s)
while :; do
  read -r ST IP PT DPH <<< "$(addr)"
  [ -n "${REH_LOCAL_DIR:-}" ] && { ST=running; IP=local; PT=0; }
  if [ -z "$ST" ] || [ "$ST" = "?" ]; then gone=$((gone + 1)); [ "$gone" -ge 5 ] && { log "instance $ID not listed for 5 polls: watch exits (released elsewhere?)"; exit 0; }; sleep "$POLL_S"; continue; fi
  gone=0
  if [ "$ST" != running ] || [ "$PT" = - ]; then log "instance $ST (the sentry's ladder fights for it; the relaunch comes on the next running poll)"; sleep "$POLL_S"; continue; fi
  st=$(rsh "pgrep -f '[o]pen_package.py run .*--out $OUT ' > /dev/null && echo alive || echo dead; [ -f $OUT/summary.json ] && echo done; [ -f $OUT/agent_stage.json ] && echo agent-done; pgrep -f '[r]elaunch.sh' > /dev/null && echo relaunching
            f=\$( { find $OUT/logs -type f -newer $RUN_DIR/RUN_CMD -printf '%T@\n'; find $EXPORT_ROOT/probe/runs -mindepth 2 -maxdepth 2 -path '*/$TAG-*' -newer $RUN_DIR/RUN_CMD -printf '%T@\n'; } 2>/dev/null | sort -n | tail -n 1); echo newest=\${f%.*}")
  [ -n "$st" ] || { log "ssh to $IP:$PT failed this poll"; sleep "$POLL_S"; continue; }
  alive=$(grep -cx alive <<< "$st"); done_=$(grep -cx done <<< "$st"); agent_done=$(grep -cx agent-done <<< "$st"); newest=$(sed -n 's/^newest=//p' <<< "$st"); relaunching=$(grep -cx relaunching <<< "$st")
  now=$(date +%s)
  if [ "$done_" = 1 ] && [ "$alive" = 0 ]; then
    pull; log "run finished: $(python3 -c "import json; print(json.load(open('$LOCAL/out/summary.json')))" 2>/dev/null | cut -c1-200)"
    T0=$(python3 -c "import json; print(int(json.load(open('$LOCAL/out/clock.json'))['started_at']))" 2>/dev/null || echo "$T0")   # the job clock's start (the rental time)
    printf -- "- %s UTC package run %s on %s finished %s s after the job clock's start: %s\n" "$(date -u +%Y-%m-%dT%H:%M)" "$TAG" "$ID" "$((now - T0))" "$(python3 -c "import json; d=json.load(open('$LOCAL/out/summary.json')); print('rows', d.get('rows'), 'stored mean', d.get('stored_mean'), 'sources', d.get('sources'))" 2>/dev/null)" >> "$ACC"
    release "run finished"; exit 0
  fi
  if [ "$alive" = 0 ] && [ "$done_" = 0 ] && [ "$relaunching" = 1 ]; then
    log "no driver alive: a relaunch.sh is already waiting for the server (onstart.sh's hook or an earlier poll)"; last_change=$now
  elif [ "$alive" = 0 ] && [ "$done_" = 0 ]; then
    log "no driver alive and no summary.json: relaunching ($RUN_DIR/relaunch.sh)"
    rsh "RUN_DIR=$RUN_DIR setsid nohup bash $RUN_DIR/relaunch.sh >> $RUN_DIR/relaunch.log 2>&1 < /dev/null & sleep 1; echo scheduled" | tail -n 1 | tee -a "$L"
    last_change=$now
  fi
  if [ "$alive" = 1 ] && [ "$agent_done" = 0 ]; then
    if [ -n "$newest" ] && [ "${newest%%.*}" -gt "$last_change" ] 2>/dev/null; then last_change=${newest%%.*}; fi
    if [ $(( (now - last_change) / 60 )) -ge "$STALL_MIN" ]; then
      [ "$stall_said" = 1 ] || { log "CRITICAL no-progress: no session log or trajectory changed for $(( (now - last_change) / 60 )) min while the driver runs (KEPT marker written; ack with probe/a100-ack-$ID to keep it)"; kept "$ID" "package no-progress ${STALL_MIN} min" >> "$L"; stall_said=1; }
    elif [ "$stall_said" = 1 ]; then log "progress again: KEPT marker cleared"; rm -f "probe/a100-kept-$ID"; stall_said=0; fi
  fi
  if [ $((now - last_pull)) -ge "$PULL_EVERY_S" ]; then pull; last_pull=$now; fi
  sleep "$POLL_S"
done
