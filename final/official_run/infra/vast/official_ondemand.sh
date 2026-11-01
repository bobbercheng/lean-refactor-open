#!/usr/bin/env bash
# The OFFICIAL open-track run on a FRESH ON-DEMAND 4x A100 80 GB SXM4 box rented AT THE RELEASE (operator 2026-10-31 ~20:40 UTC: "For Nov 1
# run, I decide to use on-demand rent instead of bid but it should rent the instance once the questions is released"). Nothing is rented
# before the release; the 48 h clock starts at `start` (DECISIONS.env CLOCK_START=launch, operator 2026-11-01: vLLM up and setup done, as the
# organizers' run.sh after their setup step; CLOCK_START=release = at RELEASE_AT, setup inside); the setup runs in parallel where safe.
# Runbook: docs/open_official_ondemand.md. Reuses infra/vast/official.sh (rows, export, envs, ship, vllm, start, status, upload: ID passed
# explicitly), create.sh (ONDEMAND=1), bootstrap.sh, spend_guard.sh (scoped to this box by infra/vast/scoped_vastai), package_watch.sh,
# probe/a100-alarm/alarm.py, infra/sync/restore_envs.sh, harness_setup.sh. No sentry, no bid ladder, no bid keeper: an on-demand box
# cannot be outbid (a stop is a host event or the credit; the alarm reports it).
#
# Never touches the p85b rehearsal: its box (probe/a100-instance-id, read only), its -ms2 units and its hold file stay as they are. This
# script's state: OFF=probe/a100-official/ (instance-id, ssh.txt, official.log, DECISIONS.env, rental-<id>.json, state/), units
# lra-a100-{go,bootstrap,prep,spendguard,watch,alarm}-off (LRA_UNIT_SUFFIX, default -off).
#
# Phases (each idempotent; ID defaults to OFF/instance-id, NEVER probe/a100-instance-id):
#   plan [RELEASE_AT]       $0, search only: decisions, the offer it would rent (filters below), price, credit hours + run-out time
#                           (first line: CREDIT WARNING when the credit does not cover HOURS + SETUP_H), guard cap, units, the phase list
#   go RELEASE_AT [R [H]]   THE release command: runs go-fg detached in unit lra-a100-go-off (log OFF/go.out); R H = the released rows +
#                           heartbeats jsonl (or later: `rows R [H]`); returns at once. b100: H is optional (the final's references are
#                           private): without it the refhb phase measures them on the box after ENVS OK; a given H is used as is
#   go-fg RELEASE_AT [R [H]] the same in the foreground: RELEASE_AT -> DECISIONS.env; credit math; rows + export in the background; rent ->
#                           (prep -> envs) || bootstrap -> vllm -> start -> arm (ARM_TRIES x ARM_RETRY_S, else STOP + push); a bad host
#                           (a PARSED no-NVLink verdict, bootstrap 3/5/1/6, rc 1 before SSH) is destroyed, its machine blacklisted, the
#                           next offer rented (at most MAX_RENTALS creates in all); re-running it resumes from the done markers
#   gates (go, go-fg)       RELEASE_AT not > 10 min ahead (EARLY_OK=1), not > LATE_MAX_H (6) h old unless it is the recorded one (LATE_OK=1);
#                           another active spend guard (GUARD_GLOB, e.g. p85b's lra-a100-spendguard-ms2) refuses unless OTHER_GUARD_OK=1
#   rows R [H]              official.sh rows (validate, env list) + OFF/rows/ROWS_OK (the envs phase waits for it, ROWS_WAIT_S); no H:
#                           OFF/rows/HB_MEASURE (b100)
#   export                  official.sh export of FINAL_COMMIT (skipped when OFF/export already holds that commit)
#   rent                    CONFIRM=yes: one on-demand rental + scoped spend guard + bootstrap unit + SSH + early NVLink topology check
#                           (refused unless DECISIONS.env holds a RELEASE_AT that has come: rent at the release)
#   prep [ID]               on the box: apt (lock wait) + tools, ship (official.sh ship), aux (bucket-only GCS key, status writer, sidecar),
#                           Kaggle env restore (public, no key) after the bootstrap's download-rate check
#   envs [ID]               waits for ROWS_OK; official.sh envs plan -> build (only the missing envs) -> check until ENVS OK
#   refhb [ID]              b100: official.sh refhb: a provided heartbeats file is used as is; else (HB_MEASURE) the reference proofs measured
#                           on the box (infra/refhb/make_ref_heartbeats.py, direct path + 2, REFHB_JOBS 8) -> RUN_DIR + OFF/rows/heartbeats.jsonl.
#                           The prep unit runs prep -> envs -> refhb; start needs it (package_run.sh refuses without the file).
#                           One row without a reading stops the chain (rc 1, pushed) unless REFHB_ALLOW_MISSING=1 (set it before `go`): that
#                           row then gets a flagged placeholder (OFF/rows/REFHB_PLACEHOLDERS, pushed) and the chain goes on to vllm and start
#   vllm [ID]               waits for the bootstrap (READY + "NVLink OK", else a re-check: topology + vLLM's tp:0 all-reduce); run_vllm_std.sh;
#                           official.sh vllm (recipe std)
#   start [ID]              official.sh start: package_run.sh, START = now (CLOCK_START=launch; recorded in OFF/clock_start.json and reused on a
#                           resume) or RELEASE_AT (CLOCK_START=release), JOB 172800, decided WORKERS / MAX_SESSIONS / END_SECONDS
#   arm [ID]                guard re-armed with the box's dph (cap HOURS x dph + GUARD_EXTRA + p85b overlap), hold file (OFF_HOLD_MAX_S),
#                           lra-a100-watch-off, lra-a100-alarm-off, accounting; read-only WARN lines about the p85b side
#   status [ID] | ssh [ID] | topo [ID] | upload [ID] | stop-go   (topo: the NVLink check alone; stop-go stops the orchestrator units, never the box)
# Offer filters (rent): on-demand, 4x A100 SXM4 80 GB, verified, reliability >= REL_MIN (0.98), cpu_cores_effective >= CPU_MIN (64),
#   disk >= DISK (500), inet_down >= MIN_DOWN (500 Mb/s), dph_total (incl. the DISK storage) <= ONDEMAND_CAP (6.50; ONDEMAND_CAP_MAX, when
#   set, after 2 empty searches, with a push), the offer's end_date beyond HOURS + SETUP_H + 6 h, machine not in bad_machines.txt and not a
#   machine our own instances run on (an on-demand rental there would evict our p85b bid box). Rank: offers listing bw_nvlink > 0 first
#   (bw_nvlink 0 / missing is kept but ranked after them: the early topology check decides), then dph x (HOURS + SETUP_H) + traffic
#   (DL_GB down, UL_GB up) + CPU_PENALTY_H x hours when cpu_cores_effective < PREFER_CPU (128).
# NVLink verdicts: only a PARSED negative drops a box (a PIX/PXB/PHB/NODE/SYS link, a wrong or missing GPU, GPU memory in use at the early
#   check, or vLLM's tp:0 all-reduce without CUSTOM when the topology cannot be read); an unreadable read is retried TOPO_TRIES (3) x
#   TOPO_RETRY_S (30 s) and then KEPT with a push. Every vast CLI call here is bounded (VAST_TIMEOUT_S 120; create.sh CREATE_TIMEOUT_S 240,
#   a lost create reply is adopted by its label lra-a100-off; destroy.sh DESTROY_TIMEOUT_S 600).
# Local dry run ($0; probe/a100/ondemand_dry_run.sh): REH_LOCAL_DIR = the "box", LRA_FAKE_VAST_BIN, BOOTSTRAP_SH, TOPO_CMD, LRA_UNIT_SUFFIX.
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3 ssh scp rsync systemd-run
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$(cd "$HERE/../.." && pwd); cd "$ROOT" || exit 2; SELF=$HERE/$(basename "$0")
PHASE=${1:-help}; shift || true
export XDG_RUNTIME_DIR=${XDG_RUNTIME_DIR:-/run/user/$(id -u)} DBUS_SESSION_BUS_ADDRESS=${DBUS_SESSION_BUS_ADDRESS:-unix:path=/run/user/$(id -u)/bus}
export OFF=${OFF:-probe/a100-official}; mkdir -p "$OFF/state" "$OFF/rows"
L=$OFF/official.log; D=$OFF/DECISIONS.env; IDF=$OFF/instance-id; SSHF=$OFF/ssh.txt; STD=$OFF/state
export LRA_UNIT_SUFFIX=${LRA_UNIT_SUFFIX:--off}; U=$LRA_UNIT_SUFFIX
OFFICIAL=$HERE/official.sh; BOOTSTRAP_SH=${BOOTSTRAP_SH:-$HERE/bootstrap.sh}; BAD=$HERE/bad_machines.txt; touch "$BAD"
CAP=${ONDEMAND_CAP:-6.50}; DISK=${DISK:-500}; REL_MIN=${REL_MIN:-0.98}; CPU_MIN=${CPU_MIN:-64}; PREFER_CPU=${PREFER_CPU:-128}
CPU_PENALTY_H=${CPU_PENALTY_H:-0.50}; MIN_DOWN=${MIN_DOWN:-500}; HOURS=${HOURS:-48}; SETUP_H=${SETUP_H:-2}; GUARD_EXTRA=${GUARD_EXTRA:-25}
CREDIT_FLOOR=${CREDIT_FLOOR:-5}; MAX_RENTALS=${MAX_RENTALS:-${MAX_RENTS:-5}}; RENT_TRIES=${RENT_TRIES:-4}; OFF_HOLD_MAX_S=${OFF_HOLD_MAX_S:-14400}
CAP_MAX=${ONDEMAND_CAP_MAX:-}; LATE_MAX_H=${LATE_MAX_H:-6}; GUARD_GLOB=${GUARD_GLOB:-lra-a100-spendguard*}; VAST_T=${VAST_TIMEOUT_S:-120}
TOPO_TRIES=${TOPO_TRIES:-3}; TOPO_RETRY_S=${TOPO_RETRY_S:-30}; ARM_TRIES=${ARM_TRIES:-5}; ARM_RETRY_S=${ARM_RETRY_S:-60}
RESTORE_PAR=${RESTORE_PAR:-16}; DL_GB=${DL_GB:-240}; UL_GB=${UL_GB:-10}; NVLINK_REQUIRED=${NVLINK_REQUIRED:-1}; POLL=${POLL_S:-15}
P85B_END=${P85B_END:-2026-11-01 12:00 UTC}; ROWS_WAIT_S=${ROWS_WAIT_S:-21600}; ENVS_MAX_S=${ENVS_MAX_S:-10800}; BOOT_MAX_S=${BOOT_MAX_S:-9600}
export LRA_TLS_DIR=${LRA_TLS_DIR:-$HOME/.config/vexorium/vllm_tls_off}   # this box's own pinned pair (bootstrap.sh / server_up.sh, b96)
ACC=${ACC:-accounting/a100_poc.md}; TAG=off
WS=/workspace; EXPORT_ROOT=/workspace/lra; RUN_DIR=/workspace/lra-run-off; OUT=/workspace/out-off
if [ -n "${REH_LOCAL_DIR:-}" ]; then WS=$REH_LOCAL_DIR/workspace; EXPORT_ROOT=$REH_LOCAL_DIR$EXPORT_ROOT; RUN_DIR=$REH_LOCAL_DIR$RUN_DIR; OUT=$REH_LOCAL_DIR$OUT; fi
log() { echo "[$(date -u -Is)] ondemand: $*" | tee -a "$L"; }
# a local dry run must never reach the real vast CLI (it would rent): REH_LOCAL_DIR without the fake vastai is refused
[ -n "${REH_LOCAL_DIR:-}" ] && [ -z "${LRA_FAKE_VAST_BIN:-}" ] && { echo "REFUSED: REH_LOCAL_DIR (dry run) without LRA_FAKE_VAST_BIN"; exit 2; }
# variables the orchestrator hands to its own units (go, prep): the production knobs and the dry run's
PASSVARS="OFF ONDEMAND_CAP DISK REL_MIN CPU_MIN PREFER_CPU CPU_PENALTY_H MIN_DOWN HOURS SETUP_H GUARD_EXTRA CREDIT_FLOOR MAX_RENTS MAX_RENTALS RENT_TRIES OFF_HOLD_MAX_S ONDEMAND_CAP_MAX
  RESTORE_PAR P85B_END NVLINK_REQUIRED LRA_TLS_DIR VERIFIED ROWS_WAIT_S ENVS_MAX_S BOOT_MAX_S BUSY_CHECK KEPT_GRACE_MIN STALE_S IDLE_GPU IDLE_CPU REMIND_MIN
  LOG_EVERY DL_MIN_MBS DL_DEADLINE_S DL_GB UL_GB SSH_WAIT_S PREP_WAIT_S RATE_WAIT_S DL_RATE_AFTER_S STALL_MIN EXTRA_URLS REFHB_JOBS REFHB_MAX_S REFHB_POLL_S REFHB_ALLOW_MISSING
  LRA_FAKE_VAST_BIN LRA_UNIT_SUFFIX REH_LOCAL_DIR ENVS_SRC BOOTSTRAP_SH TOPO_CMD LRA_BASE_URL LRA_API_KEY_FILE NO_PUSH NO_ALARM_LIVE POLL_S GUARD_POLL_S
  WATCH_POLL_S PULL_EVERY_S DESTROY_WAIT_S IDLE_MIN RESTORE_EARLY_MBS EARLY_OK MIN_LEFT_S MIN_FREE_GB DF_PATH MARGIN_GB KEEP_ROWS DRY_EXTRA ACC FAKE_BOOTSTRAP_RCS_FILE
  OTHER_GUARD_OK LATE_OK LATE_MAX_H GUARD_GLOB VAST_TIMEOUT_S CREATE_TIMEOUT_S DESTROY_TIMEOUT_S TOPO_TRIES TOPO_RETRY_S ARM_TRIES ARM_RETRY_S
  GONE_READS GONE_GAP_S NO_OFFER_SLEEP_S LOST_CREATE_WAIT_S"
push() { [ -n "${NO_PUSH:-}" ] && return 0; local t; t=$(cat probe/a100-ntfy-topic 2>/dev/null); [ -n "$t" ] && curl -fsS -m 20 -H "Title: A100 official on-demand" -H "Priority: high" -d "$*" "https://ntfy.sh/$t" > /dev/null 2>&1; true; }
die() { log "STOP: $*"; push "official on-demand run STOPPED: $*"; exit 1; }
[ -f "$D" ] || "$OFFICIAL" init > /dev/null 2>&1   # official.sh writes DECISIONS.env with its defaults on any call (the unknown phase exits 2)
[ -f "$D" ] || { echo "no $D"; exit 2; }
. "$D"; REC_RELEASE_AT=${RELEASE_AT:-}   # the recorded release (a resume may pass it however old it is)
cur_id() { cat "$IDF" 2>/dev/null; }
need_id() { ID=${1:-$(cur_id)}; [ -n "$ID" ] || { echo "no instance id (none given, $IDF empty)" >&2; exit 2; }; }
envargs() {   # fills ENVA with -E NAME=VALUE for every set variable named (values may hold spaces)
  ENVA=(); local v; for v in "$@"; do [ -n "${!v+x}" ] && ENVA+=(-E "$v=${!v}"); done; true; }
vast() { timeout "$VAST_T" vastai "$@"; }   # every vast CLI call bounded (review b96)
SSHO="-i $HOME/.ssh/id_ed25519 -o BatchMode=yes -o ConnectTimeout=20 -o ServerAliveInterval=30 -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR"
inst() {   # ID -> "status ip sshport dph machine" (gone when not listed)
  vast show instances --raw 2>/dev/null | python3 -c "
import json, sys
try: rows = json.load(sys.stdin)
except Exception: print('? - - 0 -'); sys.exit()
i = next((r for r in rows if str(r.get('id')) == '$1'), None)
if i is None: print('gone - - 0 -'); sys.exit()
p = ((i.get('ports') or {}).get('22/tcp') or [{}])[0].get('HostPort') or '-'
print(i.get('actual_status') or '?', i.get('public_ipaddr') or '-', p, float(i.get('dph_total') or 0), i.get('machine_id') or '-')" 2>/dev/null; }
connect() {   # sets IP PT DPH MACH for $1
  if [ -n "${REH_LOCAL_DIR:-}" ]; then IP=local; PT=0; read -r _ _ _ DPH MACH <<< "$(inst "$1")"; return 0; fi
  local s; read -r s IP PT DPH MACH <<< "$(inst "$1")"; [ "$s" = running ] && [ "$PT" != - ] && [ "$IP" != - ]; }
rsh() {   # ID CMD [timeout]
  local t=${3:-600}
  if [ -n "${REH_LOCAL_DIR:-}" ]; then timeout "$t" bash -c "cd '$EXPORT_ROOT' 2>/dev/null || cd '$WS'; $2"; return; fi
  connect "$1" || return 1
  timeout "$t" ssh $SSHO -p "$PT" "root@$IP" "cd $EXPORT_ROOT 2>/dev/null; $2" 2>/dev/null | grep -v "^Welcome\|^Have fun"; return "${PIPESTATUS[0]}"; }
rcp() {   # ID SRC DST
  if [ -n "${REH_LOCAL_DIR:-}" ]; then mkdir -p "$(dirname "$3")"; cp "$2" "$3"; return; fi
  connect "$1" || return 1; timeout 1800 scp -q $SSHO -P "$PT" "$2" "root@$IP:$3"; }
credit_raw() { vast show user --raw 2>/dev/null | python3 -c "import json, sys; d = json.load(sys.stdin); print('%.2f %s' % (float(d['credit']), 'yes' if d.get('can_pay') else 'no')) if isinstance(d, dict) and d.get('credit') is not None else None" 2>/dev/null; }
others_dph() {   # sum dph_total of OUR other running instances (p85b's box: billed beside the official one until it is released) + their machines
  vast show instances --raw 2>/dev/null | python3 -c "
import json, sys
try: rows = json.load(sys.stdin)
except Exception: print('0 -'); sys.exit()
o = [r for r in rows if str(r.get('id')) != '${1:-x}']
print('%.3f' % sum(float(r.get('dph_total') or 0) for r in o if r.get('actual_status') == 'running'), ','.join(str(r.get('machine_id')) for r in o) or '-')" 2>/dev/null; }
rel_epoch() { date -u -d "${RELEASE_AT:-now}" +%s 2>/dev/null || date +%s; }
set_decision() {   # KEY VALUE: rewrite KEY= in DECISIONS.env (the comment records who set it)
  python3 - "$D" "$1" "$2" <<'PY'
import re, sys, time
p, k, v = sys.argv[1:4]
s = open(p).read(); line = f'{k}="{v}"   # set by official_ondemand.sh at {time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}'
s, n = re.subn(rf"^{k}=.*$", line.replace("\\", "\\\\"), s, flags=re.M)
open(p, "w").write(s if n else s.rstrip("\n") + "\n" + line + "\n")
PY
}
units_on() { systemctl --user list-units --plain --no-legend 'lra-a100*' 2>/dev/null | awk '{print $1}' | tr '\n' ' '; }
done_mark() { echo "$(date -u -Is) $2" > "$STD/$1.ok"; }
is_done() { [ -f "$STD/$1.ok" ]; }

# ---------------------------------------------------------------- offers and money
offers() {   # ranked acceptable on-demand offers, one JSON per line (best first); rejection counts on stderr
  local q="num_gpus=4 gpu_ram>=80 gpu_name=A100_SXM4 cpu_cores_effective>=$CPU_MIN disk_space>=$DISK inet_down>=$MIN_DOWN${VERIFIED:+ verified=$VERIFIED}"
  vast search offers "$q" --type on-demand --storage "$DISK" -o dph_total --limit 64 --raw 2>/dev/null | \
  OWN_MACH="$(others_dph x | awk '{print $2}')" SKIP="${SKIP_OFFERS:-}" python3 -c '
import json, os, sys, time
E = os.environ; bad = set(open(sys.argv[1]).read().split()); own = set(E["OWN_MACH"].split(",")) - {"-", ""}; skip = set(E["SKIP"].split())
cap, rel, cpu, disk, down = float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]), float(sys.argv[5]), float(sys.argv[6])
hours, pcpu, pen, dl, ul, anyv = float(sys.argv[7]), float(sys.argv[8]), float(sys.argv[9]), float(sys.argv[10]), float(sys.argv[11]), sys.argv[12] == "any"
try: offers = json.load(sys.stdin)
except Exception: print("search failed or unreadable", file=sys.stderr); sys.exit(1)
why = {}; ok = []
def no(o, r): why[r] = why.get(r, 0) + 1
for o in offers:
    f = lambda k, d=0: (o.get(k) if o.get(k) is not None else d)
    if str(o.get("id")) in skip: no(o, "create failed earlier"); continue
    if str(o.get("machine_id")) in bad: no(o, "bad_machines.txt"); continue
    if str(o.get("machine_id")) in own: no(o, "machine of our own instance (would evict it)"); continue
    if int(f("num_gpus")) != 4 or "A100" not in str(f("gpu_name", "")) or "SXM" not in str(f("gpu_name", "")) or float(f("gpu_ram")) < 80000: no(o, "not 4x A100 SXM4 80GB"); continue
    if not anyv and o.get("verification") not in (None, "verified"): no(o, "not verified"); continue
    if float(f("reliability2", f("reliability"))) < rel: no(o, f"reliability < {rel}"); continue
    if float(f("cpu_cores_effective")) < cpu: no(o, f"vCPU < {cpu:.0f}"); continue
    if float(f("disk_space")) < disk: no(o, f"disk < {disk:.0f}"); continue
    if float(f("inet_down")) < down: no(o, f"inet_down < {down:.0f}"); continue
    if float(f("dph_total")) > cap + 1e-9: no(o, f"dph_total > cap {cap}"); continue
    if f("end_date") and float(f("end_date")) < time.time() + (hours + 6) * 3600: no(o, "offer ends too soon"); continue
    if o.get("rentable") is False: no(o, "not rentable"); continue
    c = float(f("cpu_cores_effective"))
    o["_nv"] = 0 if float(f("bw_nvlink")) > 0 else 1   # bw_nvlink 0 / missing: kept, ranked after every listed-NVLink offer (the topology check decides)
    o["_cost"] = float(f("dph_total")) * hours + float(f("inet_down_cost")) * dl + float(f("inet_up_cost")) * ul + (pen * hours if c < pcpu else 0)
    ok.append(o)
ok.sort(key=lambda o: (o["_nv"], o["_cost"]))
nv0 = sum(o["_nv"] for o in ok); nv0 = f" ({nv0} with bw_nvlink 0/missing, ranked last)" if nv0 else ""
print(f"offers: {len(offers)} listed, {len(ok)} acceptable{nv0}; rejected: " + (", ".join(f"{k} {v}" for k, v in sorted(why.items())) or "none"), file=sys.stderr)
for o in ok:
    print(json.dumps({k: o.get(k) for k in ("id", "machine_id", "dph_total", "cpu_cores_effective", "reliability2", "inet_down", "inet_down_cost",
                                           "inet_up_cost", "disk_space", "geolocation", "bw_nvlink", "end_date", "_cost", "_nv")}))' \
    "$BAD" "$CAP" "$REL_MIN" "$CPU_MIN" "$DISK" "$MIN_DOWN" "$((HOURS + SETUP_H))" "$PREFER_CPU" "$CPU_PENALTY_H" "$DL_GB" "$UL_GB" "${VERIFIED:-}"
}
money() {   # DPH DCOST [exclude-id]: credit math; first line CREDIT WARNING when short; sets GUARD_CAP, CREDIT, OVERLAP
  local dph=$1 dcost=$2 cr can od om
  read -r cr can <<< "$(credit_raw)"; CREDIT=${cr:-}
  read -r od om <<< "$(others_dph "${3:-x}")"
  python3 - "${cr:-0}" "$dph" "$dcost" "$od" "$(date -u -d "$P85B_END" +%s 2>/dev/null || echo 0)" "$HOURS" "$SETUP_H" "$DL_GB" "$GUARD_EXTRA" "$CREDIT_FLOOR" "$(rel_epoch)" "${cr:+ok}" <<'PY'
import sys, time, datetime as dt
c, dph, dcost, od, p85_end, hours, setup, dl, extra, floor, rel = map(float, sys.argv[1:12]); readable = sys.argv[12] == "ok"
now = time.time(); ts = lambda e: dt.datetime.fromtimestamp(e, dt.timezone.utc).strftime("%Y-%m-%d %H:%M UTC")
ov_h = max(0.0, (p85_end - now) / 3600); overlap = od * ov_h
need = dph * (hours + setup) + dcost * dl + overlap + floor
# run-out: both boxes until P85B_END, then the official box alone (vast stops every instance at $0)
t, left = now, c - dcost * dl
if od > 0 and ov_h > 0:
    burn = dph + od; h = min(ov_h, max(0, left) / burn); t += h * 3600; left -= h * burn
t += max(0, left) / dph * 3600 if dph > 0 else 0
end_need = max(now, rel) + hours * 3600 + 3600
cap = hours * dph + extra + overlap
if not readable:
    print("CREDIT WARNING: vast credit unreadable now: cannot check the coverage (renting anyway; check `vastai show user`)")
elif c < need:
    print(f"CREDIT WARNING: credit ${c:.2f} covers ~{c / dph:.1f} h of this box alone at ${dph:.2f}/h (need {hours + setup:.0f} h: ${need:.2f} incl. "
          f"${dcost * dl:.2f} traffic, ${overlap:.2f} for our other boxes at ${od:.2f}/h until P85B_END, ${floor:.0f} floor); it runs out ~{ts(t)} "
          f"({'BEFORE' if t < end_need else 'after'} the run's end + 1 h at {ts(end_need)}): TOP UP >= ${need - c:.0f} now (vast stops the box at $0); renting anyway")
else:
    print(f"credit OK: ${c:.2f} >= ${need:.2f} needed ({hours + setup:.0f} h at ${dph:.2f}/h + traffic + other boxes ${overlap:.2f} + floor); runs out ~{ts(t)}")
print(f"MONEY credit={c:.2f} dph={dph:.3f} hours_covered={c / dph if dph else 0:.1f} runout={ts(t)} need={need:.2f} topup={max(0, need - c):.0f} "
      f"guard_cap={cap:.2f} overlap={overlap:.2f} other_dph={od:.3f}")
PY
}

# ---------------------------------------------------------------- box checks
topo_check() {   # ID [resume] -> 0 "NVLINK OK": 4 A100 80GB GPUs (free, unless resume: vLLM may be up), pairwise NV links; 1 "NVLINK BAD": a PARSED
  # negative (a PIX/PXB/PHB/NODE/SYS link, a wrong or missing GPU, GPU memory in use); 2 "NVLINK UNREADABLE": the read failed (listing, SSH or
  # nvidia-smi rc != 0, no GPU lines, no topo rows, an unknown cell): never a reason to drop a box (review b96: an empty read parsed as "0 GPUs")
  local raw rc
  if [ -n "${TOPO_CMD:-}" ]; then raw=$(timeout 120 bash -c "$TOPO_CMD" 2>&1); rc=$?
  else raw=$(rsh "$1" "nvidia-smi --query-gpu=name,memory.total,memory.used --format=csv,noheader,nounits && echo --- && nvidia-smi topo -m" 120); rc=$?; fi
  printf '%s\n' "$raw" | RESUME="${2:-}" RC="$rc" python3 -c '
import os, re, sys
t = sys.stdin.read(); g, sep, topo = t.partition("---")
NEG = {"PIX", "PXB", "PHB", "NODE", "SYS", "SOC"}
bad, unk = [], []
gpus = [l.split(",") for l in g.strip().splitlines() if l.count(",") >= 2] if sep else []   # the separator follows a COMPLETE GPU query
if not gpus: unk.append("no GPU lines")
elif len(gpus) != 4: bad.append("%d GPUs" % len(gpus))
for x in gpus:
    try: n, tot, used = x[0].strip(), float(x[1]), float(x[2])
    except ValueError: unk.append("GPU line " + ",".join(x)[:40]); continue
    if "A100" not in n or tot < 80000: bad.append("GPU %s %.0f MiB" % (n, tot))
    if used > 12000 and not os.environ.get("RESUME"): bad.append("GPU memory in use (%.0f MiB)" % used)
rows = {int(m.group(1)): l.split()[1:5] for l in topo.splitlines() if (m := re.match(r"^GPU(\d)\s", l))}
links = set()
if not rows: unk.append("no topo rows")
else:
    for i in range(4):
        r = rows.get(i)
        if not r or len(r) < 4: unk.append("no topo row GPU%d" % i); continue
        for j in range(4):
            if j == i: continue
            if re.match(r"^NV\d+$", r[j]): links.add(r[j])
            elif r[j] in NEG: bad.append("GPU%d-GPU%d %s" % (i, j, r[j]))
            else: unk.append("GPU%d-GPU%d %r" % (i, j, r[j][:8]))
if os.environ.get("RC", "0") != "0": unk.insert(0, "read rc " + os.environ.get("RC", "?"))
if bad: print("NVLINK BAD: " + "; ".join(bad[:6])); sys.exit(1)
if unk: print("NVLINK UNREADABLE: " + "; ".join(unk[:4])); sys.exit(2)
print("NVLINK OK " + " ".join(sorted(links)))'
}
topo_verdict() {   # ID [resume]: topo_check, re-read up to TOPO_TRIES times TOPO_RETRY_S apart while UNREADABLE; prints the last verdict, returns its rc
  local i v r=2
  for i in $(seq 1 "$TOPO_TRIES"); do
    v=$(topo_check "$1" "${2:-}"); r=$?
    [ "$r" = 2 ] || break
    [ "$i" -lt "$TOPO_TRIES" ] && { echo "[$(date -u -Is)] ondemand: topology read $i/$TOPO_TRIES on $1: $v (re-read in ${TOPO_RETRY_S}s)" >> "$L"; sleep "$TOPO_RETRY_S"; }
  done; echo "$v"; return "$r"
}
late_nvlink() {   # ID (vLLM READY) -> 0 NVLink confirmed; 1 a PARSED negative (topology BAD, or the tp:0 all-reduce without CUSTOM while the
  # topology is unreadable); 2 still unreadable after TOPO_TRIES reads (review b96: bootstrap prints NO-NVLINK when its two SSH reads fail)
  local i v t c
  for i in $(seq 1 "$TOPO_TRIES"); do
    v=$(topo_check "$1" resume); t=$?
    c=$(rsh "$1" "grep -a 'all-reduce backends' $WS/vllm.log 2>/dev/null | grep -a 'tp:0' | tail -n 1 | grep -o 'Using \[[^]]*\]'" 60)
    case "$t:$c" in
      1:*) echo "$v (tp:0 all-reduce ${c:-unread})"; return 1;;
      0:*CUSTOM*|2:*CUSTOM*) echo "NVLINK OK ($v; tp:0 all-reduce $c)"; return 0;;
      0:*) echo "$v (tp:0 all-reduce ${c:-line not found}: the topology is NVLink; check the recipe's all-reduce in vllm.log)"; return 0;;
      2:Using*) echo "$v; tp:0 all-reduce $c without CUSTOM: no NVLink"; return 1;;
    esac
    [ "$i" -lt "$TOPO_TRIES" ] && { echo "[$(date -u -Is)] ondemand: late NVLink read $i/$TOPO_TRIES on $1: $v, all-reduce unread (re-read in ${TOPO_RETRY_S}s)" >> "$L"; sleep "$TOPO_RETRY_S"; }
  done; echo "$v; tp:0 all-reduce unread"; return 2
}
wait_ssh() {   # ID -> 0 when SSH answers (writes ssh.txt + the alarm's tunnel file); 2 when the bootstrap ended first (bad host); 1 timeout
  local id=$1 t0; t0=$(date +%s)
  if [ -n "${REH_LOCAL_DIR:-}" ]; then   # the dry run: "SSH up" = the (fake) bootstrap reached its host check [2/5]; an rc before that = no SSH
    while [ $(( $(date +%s) - t0 )) -lt "${SSH_WAIT_S:-1500}" ]; do
      [ -f "$STD/bootstrap.$id.rc" ] && [ "$(cat "$STD/bootstrap.$id.rc")" != 0 ] && return 2
      grep -q '^\[2/5\]' "probe/a100-bootstrap-$id.log" 2>/dev/null && { echo "127.0.0.1 22" > "$SSHF"; mkdir -p probe/a100-tunnels; echo "127.0.0.1 22" > "probe/a100-tunnels/$id"; return 0; }
      sleep 1; done; return 1; fi
  while [ $(( $(date +%s) - t0 )) -lt "${SSH_WAIT_S:-1500}" ]; do
    [ -f "$STD/bootstrap.$id.rc" ] && [ "$(cat "$STD/bootstrap.$id.rc")" != 0 ] && return 2
    if connect "$id" && timeout 40 ssh $SSHO -p "$PT" "root@$IP" true 2>/dev/null; then
      echo "$IP $PT" > "$SSHF"; mkdir -p probe/a100-tunnels; echo "$IP $PT" > "probe/a100-tunnels/$id"; return 0; fi
    sleep "$POLL"
  done; return 1
}
start_bootstrap() {   # ID: bootstrap.sh in its own unit (survives this script); rc -> state/bootstrap.<id>.rc
  local id=$1 u="lra-a100-bootstrap$U"
  systemctl --user is-active -q "$u" && { log "bootstrap unit $u already running"; return 0; }
  systemctl --user reset-failed "$u" 2>/dev/null; rm -f "$STD/bootstrap.$id.rc"
  systemd-run --user --unit "$u" --collect --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" -E LRA_FAKE_VAST_BIN="${LRA_FAKE_VAST_BIN:-}" \
    -E LRA_UNIT_SUFFIX="$U" -E LRA_TLS_DIR="$LRA_TLS_DIR" -E DL_MIN_MBS="${DL_MIN_MBS:-50}" -E DL_DEADLINE_S="${DL_DEADLINE_S:-5400}" \
    -E FAKE_BOOTSTRAP_RCS_FILE="${FAKE_BOOTSTRAP_RCS_FILE:-}" \
    bash -c "'$BOOTSTRAP_SH' $id >> probe/a100-bootstrap-$id.log 2>&1; echo \$? > '$STD/bootstrap.$id.rc'" > /dev/null 2>&1 \
    && log "bootstrap started: unit $u, log probe/a100-bootstrap-$id.log (model 190.8 GB + vLLM; TLS pair $LRA_TLS_DIR)"
}
boot_rc() { cat "$STD/bootstrap.$1.rc" 2>/dev/null; }
boot_wait() {   # ID PATTERN MAX_S: 0 when the bootstrap log matches PATTERN (or the bootstrap ended 0); 1 when it ended non-zero; 2 timeout
  local t0; t0=$(date +%s)
  while [ $(( $(date +%s) - t0 )) -lt "$3" ]; do
    grep -qE "$2" "probe/a100-bootstrap-$1.log" 2>/dev/null && return 0
    case "$(boot_rc "$1")" in 0) return 0;; "") ;; *) return 1;; esac
    sleep "$POLL"
  done; return 2
}
rate_checked() {   # ID: safe to start the Kaggle restore beside the model download: the link is fast (>= RESTORE_EARLY_MBS after 60 s, so sharing it
  # cannot push the download under the bootstrap's DL_MIN_MBS drop line), or the bootstrap's one rate check is behind it, or the download is over
  local last el mbs; last=$(grep -E '^ +\[[0-9:]+\] [0-9]+s: [0-9]+ GB on disk \([0-9-]+ MB/s' "probe/a100-bootstrap-$1.log" 2>/dev/null | tail -n 1)
  el=$(sed -nE 's/^ +\[[0-9:]+\] ([0-9]+)s: .*/\1/p' <<< "$last"); mbs=$(sed -nE 's/.*\(([0-9]+) MB\/s.*/\1/p' <<< "$last")
  [ "${el:-0}" -ge 60 ] && [ "${mbs:-0}" -ge "${RESTORE_EARLY_MBS:-150}" ] && return 0
  [ "${el:-0}" -ge $(( ${DL_RATE_AFTER_S:-300} + 30 )) ] || grep -qE '^\[5/5\]|server ready|SKIPPED' "probe/a100-bootstrap-$1.log" 2>/dev/null || [ -n "$(boot_rc "$1")" ]; }
drop_box() {   # ID REASON: stop its bootstrap / prep units, destroy (verified), blacklist the machine; 0 = gone
  local id=$1 m; m=$(python3 -c "import json; print(json.load(open('$OFF/rental-$id.json')).get('machine', ''))" 2>/dev/null)
  log "DROP $id (machine ${m:-?}): $2"
  systemctl --user stop "lra-a100-bootstrap$U" "lra-a100-prep$U" 2>/dev/null
  echo "$id" >> "$STD/dropped-ids"
  if CONFIRM=yes timeout "${DESTROY_TIMEOUT_S:-600}" "$HERE/destroy.sh" "$id" >> "$L" 2>&1; then
    [ -n "$m" ] && echo "$m" >> "$BAD"; rm -f "$IDF"
    printf -- "- %s UTC official on-demand: instance %s dropped (%s); machine %s blacklisted\n" "$(date -u +%Y-%m-%dT%H:%M)" "$id" "$2" "${m:-?}" >> "$ACC"
    log "dropped $id (verified gone; machine ${m:-?} blacklisted)"; return 0
  fi
  kept "$id" "official on-demand drop failed ($2): still billing" >> "$L"; return 1
}
arm_guard() {   # ID DPH: spend_guard.sh scoped to this box (cap HOURS x dph + GUARD_EXTRA + the overlap with our other boxes), ask-first
  local id=$1 dph=$2 c cap ov u="lra-a100-spendguard$U"
  read -r c _ <<< "$(credit_raw)"; [ -n "$c" ] || { log "guard NOT armed: vast credit unreadable (retry: $0 arm $id)"; return 1; }
  read -r ov _ <<< "$(others_dph "$id")"
  cap=$(python3 -c "import time, sys; e = float(sys.argv[3]); print('%.2f' % ($HOURS * float(sys.argv[1]) + $GUARD_EXTRA + float(sys.argv[2]) * max(0, (e - time.time()) / 3600)))" "$dph" "${ov:-0}" "$(date -u -d "$P85B_END" +%s 2>/dev/null || echo 0)")
  systemctl --user stop "$u" 2>/dev/null; systemctl --user reset-failed "$u" 2>/dev/null
  systemd-run --user --unit "$u" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" \
    -E LRA_FAKE_VAST_BIN="$HERE/scoped_vastai${LRA_FAKE_VAST_BIN:+:$LRA_FAKE_VAST_BIN}" -E LRA_SCOPE_ID="$id" -E LRA_UNIT_SUFFIX="$U" \
    -E SPEND_CAP="$cap" -E CREDIT_FLOOR="$CREDIT_FLOOR" -E KEPT_GRACE_MIN="${KEPT_GRACE_MIN:-45}" -E GUARD_POLL_S="${GUARD_POLL_S:-60}" -E STALE_S="${STALE_S:-1800}" \
    -E IDLE_MIN="${IDLE_MIN:-30}" -E IDLE_GPU="${IDLE_GPU:-5}" -E IDLE_CPU="${IDLE_CPU:-5}" -E REMIND_MIN="${REMIND_MIN:-30}" -E LOG_EVERY="${LOG_EVERY:-10}" \
    -E BUSY_CHECK="${BUSY_CHECK-python3 probe/a100-alarm/run_busy.py --label a100-off}" -E GUARD_NTFY="$( [ -n "${NO_PUSH:-}" ] || cat probe/a100-ntfy-topic 2>/dev/null)" \
    -E PRE_DESTROY="TAG=$TAG LOCAL=probe/a100-reh-$TAG RUN_DIR=$RUN_DIR OUT=$OUT EXPORT_ROOT=$EXPORT_ROOT infra/vast/package_watch.sh {ID} pull" -E PRE_DESTROY_MAX_S=900 \
    -E TAG=$TAG -E REH_LOCAL_DIR="${REH_LOCAL_DIR:-}" -E DESTROY_WAIT_S="${DESTROY_WAIT_S:-10}" \
    bash -c "infra/vast/spend_guard.sh $id $c 2>> probe/a100-spend-guard-off.err > /dev/null" > /dev/null 2>&1 \
    && { log "spend guard armed: $u on $id ONLY (scoped vastai), cap \$$cap from credit \$$c (= $HOURS h x \$$dph + \$$GUARD_EXTRA + other boxes until P85B_END), floor \$$CREDIT_FLOOR, ask-first"; echo "$cap" > "$STD/guard.$id.cap"; } \
    || { log "guard NOT armed: systemd-run $u failed (retry: $0 arm $id)"; return 1; }
}
other_guards() {   # active spend-guard units of OTHER rentals (GUARD_GLOB), never this run's own
  systemctl --user list-units --plain --no-legend --state=active "$GUARD_GLOB" 2>/dev/null | awk '{print $1}' | grep -vx "lra-a100-spendguard$U.service"; }
other_guard_warn() {   # one WARN line per other active guard; 0 = at least one (review b96: p85b's -ms2 guard is account-wide and unscoped, past its
  # $40 cap from ~05:00 UTC Nov 1; once p85b reports idle after 12:00 UTC, any 30 min in which the official box also looks idle by vast's
  # gpu/cpu utilisation (e.g. vLLM READY while the envs wait for rows) makes it destroy EVERY listed instance with FORCE)
  local g env any=1
  for g in $(other_guards); do
    env=$(systemctl --user show "$g" -p Environment 2>/dev/null)
    echo "WARN OTHER SPEND GUARD ${g%.service} is active (SPEND_CAP \$$(grep -oE 'SPEND_CAP=[0-9.]+' <<< "$env" | cut -d= -f2), IDLE_MIN $(grep -oE 'IDLE_MIN=[0-9]+' <<< "$env" | cut -d= -f2), account-wide, NOT scoped): past its cap it destroys EVERY listed instance (FORCE, holds ignored) once all look idle, the official box included. Stop it right after p85b's final pull ($P85B_END), and BEFORE go when the release is later: systemctl --user stop ${g%.service}"
    any=0
  done; return $any; }
release_check() {   # REL -> 0 acceptable; else prints why (review b96: a far-past typo silently cut the 48 h clock)
  local e now rec; e=$(date -u -d "$1" +%s 2>/dev/null) || { echo "bad RELEASE_AT '$1'"; return 2; }; now=$(date +%s)
  [ "$e" -le $((now + 600)) ] || [ "${EARLY_OK:-0}" = 1 ] || { echo "REFUSED: RELEASE_AT $1 is in the future: the operator's rule is to rent at the release (EARLY_OK=1 overrides)"; return 2; }
  { [ "$e" -ge $((now - LATE_MAX_H * 3600)) ] || [ "${LATE_OK:-0}" = 1 ]; } && return 0
  rec=$(date -u -d "${REC_RELEASE_AT:-x}" +%s 2>/dev/null); [ -n "$rec" ] && [ "$rec" = "$e" ] && return 0   # a resume of the recorded release
  echo "REFUSED: RELEASE_AT $1 is $(( (now - e) / 3600 )) h old (> LATE_MAX_H $LATE_MAX_H h) and not the recorded release (${REC_RELEASE_AT:-none}): a typo would cut the 48 h clock (LATE_OK=1 overrides)"; return 2; }
money_now() {   # [exclude-id] -> $STD/money.out (first line = the credit verdict, then MONEY) for the best offer now; offers' stderr -> $STD/offers.now.err
  local first; first=$(offers 2> "$STD/offers.now.err" | head -n 1)
  [ -n "$first" ] || { echo "CREDIT/OFFER WARNING: no acceptable on-demand offer right now (cap \$$CAP${CAP_MAX:+, ONDEMAND_CAP_MAX \$$CAP_MAX after 2 empty searches}; rent re-searches every ${NO_OFFER_SLEEP_S:-60} s)" > "$STD/money.out"; return 1; }
  money "$(python3 -c "import json, sys; print(json.loads(sys.argv[1])['dph_total'])" "$first")" "$(python3 -c "import json, sys; print(json.loads(sys.argv[1]).get('inet_down_cost') or 0)" "$first")" "${1:-x}" > "$STD/money.out"; }
rentals() { cat "$STD/rentals.count" 2>/dev/null || echo 0; }
confirmed_gone() {   # ID -> 0 only when GONE_READS (3) listings, GONE_GAP_S (10 s) apart, all parse and lack it (review b96: one read re-rented)
  local i s n=${GONE_READS:-3}
  for i in $(seq 1 "$n"); do read -r s _ <<< "$(inst "$1")"; [ "$s" = gone ] || return 1; [ "$i" -lt "$n" ] && sleep "${GONE_GAP_S:-10}"; done; return 0; }
lost_create() {   # create.sh gave no id: an instance labelled lra-a100-off that vast lists (not one we dropped) is that create's (reply lost / timed out)
  sleep "${LOST_CREATE_WAIT_S:-5}"
  vast show instances --raw 2>/dev/null | python3 -c '
import json, os, sys
try: rows = json.load(sys.stdin)
except Exception: sys.exit()
gone = set(open(sys.argv[1]).read().split()) if os.path.exists(sys.argv[1]) else set()
for r in (rows if isinstance(rows, list) else []):
    if r.get("label") == "lra-a100-off" and str(r.get("id")) not in gone: print(r.get("id")); break' "$STD/dropped-ids" 2>/dev/null; }

# ---------------------------------------------------------------- phases
rows_known() { [ -f "$OFF/rows/ROWS_OK" ] && [ -f "$OFF/rows/rows.jsonl" ] && [ -f "$OFF/rows/harness_envs.official.json" ]; }
ph_rows() {
  "$OFFICIAL" rows "$1" "${2:-}" > "$STD/rows.out" 2>&1; local rc=$?; tail -n 4 "$STD/rows.out"
  [ "$rc" = 0 ] && grep -q "ROWS OK" "$STD/rows.out" && { date +%s > "$OFF/rows/ROWS_OK"; log "rows OK: $(grep -E '^rows:' "$STD/rows.out" | cut -c1-160)"; return 0; }
  log "rows FAILED (rc $rc; $STD/rows.out): fix and re-run: $0 rows R [H]"; return 1
}
ph_export() {
  local want have; want=$(git rev-parse --short=8 "${FINAL_COMMIT:-x}^{commit}" 2>/dev/null || echo "${FINAL_COMMIT:-}")
  have=$(cat "$OFF/export/HARNESS_COMMIT" 2>/dev/null)
  if [ -n "$have" ] && [ -f "$OFF/export.tar.gz" ] && [ -n "$want" ] && { [ "${want#"$have"}" != "$want" ] || [ "${have#"$want"}" != "$have" ]; }; then
    log "export: $OFF/export.tar.gz already holds $have (FINAL_COMMIT $FINAL_COMMIT)"; done_mark export "$have"; return 0; fi
  rm -f "$STD/export.ok"; "$OFFICIAL" export > "$STD/export.out" 2>&1; tail -n 2 "$STD/export.out"
  grep -q "EXPORT OK" "$STD/export.out" && [ -f "$OFF/export.tar.gz" ] && { done_mark export "$(cat "$OFF/export/HARNESS_COMMIT")"; return 0; }
  log "export FAILED ($STD/export.out)"; return 1
}
ph_rent() {   # one on-demand rental with its guard, bootstrap unit, SSH and the early NVLink check; prints the id last
  [ "${CONFIRM:-}" = yes ] || { log "rent: set CONFIRM=yes (spends money); \`$0 plan\` shows the pick"; return 2; }
  [ -e probe/a100-stop-now ] && { log "rent refused: probe/a100-stop-now exists (the spend guards' manual kill switch)"; return 2; }
  # operator 2026-10-31: rent at the release, not before (review b96: the `rent` phase bypassed that gate): a recorded RELEASE_AT that has come
  [ -n "${RELEASE_AT:-}" ] || { log "rent refused: no RELEASE_AT in $D (rent at the release: \`$0 go RELEASE_AT\` records it)"; return 2; }
  local re; re=$(date -u -d "$RELEASE_AT" +%s 2>/dev/null) || { log "rent refused: RELEASE_AT '$RELEASE_AT' in $D does not parse"; return 2; }
  [ "$re" -le $(( $(date +%s) + 600 )) ] || [ "${EARLY_OK:-0}" = 1 ] || { log "rent refused: RELEASE_AT $RELEASE_AT is in the future (rent at the release; EARLY_OK=1 overrides)"; return 2; }
  local id s; id=$(cur_id)
  if [ -n "$id" ]; then
    read -r s _ <<< "$(inst "$id")"
    case "$s" in
      gone) confirmed_gone "$id" || { log "rent: $id read gone once but not ${GONE_READS:-3} times: not renting another"; echo "$id"; return 0; }
            log "rent: the recorded official box $id is gone (${GONE_READS:-3} reads)"; rm -f "$IDF";;
      "?"|"") log "rent refused: the vast listing is unreadable and $id may still be live: not renting a second box (re-run later)"; return 1;;
      *) log "rent: $id ($s) is already the official box: not renting another (drop it first)"; echo "$id"; return 0;;
    esac
  fi
  local a o cr can raised=""
  for a in $(seq 1 "$RENT_TRIES"); do
    [ "$(rentals)" -lt "$MAX_RENTALS" ] || { log "rent refused: $(rentals) rentals made for this release already (MAX_RENTALS $MAX_RENTALS, $STD/rentals.count): read the drops in $L, then MAX_RENTALS=N to allow more"; push "official on-demand: rental limit $MAX_RENTALS reached, no healthy box"; return 1; }
    read -r cr can <<< "$(credit_raw)"
    [ "${can:-}" = no ] && { log "rent refused: vast says can_pay=no (credit \$${cr:-?}): top up"; return 2; }
    python3 -c "import sys; sys.exit(0 if float('${cr:-0}') > $CREDIT_FLOOR + 1 else 1)" 2>/dev/null || [ -z "$cr" ] || { log "rent refused: credit \$$cr <= floor \$$CREDIT_FLOOR + 1: top up"; return 2; }
    o=$(offers 2>> "$L" | head -n 1)
    if [ -z "$o" ]; then
      if [ -n "$CAP_MAX" ] && [ -z "$raised" ] && [ "$a" -ge 2 ] && python3 -c "import sys; sys.exit(0 if float('$CAP_MAX') > float('$CAP') else 1)" 2>/dev/null; then
        log "rent: no acceptable offer under \$$CAP after $a searches: raising the cap to ONDEMAND_CAP_MAX \$$CAP_MAX (time over money)"
        push "official on-demand: no offer under \$$CAP; cap raised to ONDEMAND_CAP_MAX \$$CAP_MAX"; CAP=$CAP_MAX; raised=1; continue; fi
      log "rent: no acceptable on-demand offer (cap \$$CAP, rel >= $REL_MIN, vCPU >= $CPU_MIN, disk >= $DISK, down >= $MIN_DOWN; raise ONDEMAND_CAP or set ONDEMAND_CAP_MAX?); search $a/$RENT_TRIES"
      [ "$a" -lt "$RENT_TRIES" ] && sleep "${NO_OFFER_SLEEP_S:-60}"; continue; fi
    read -r OFFER MACH ODPH OCPU OREL ODOWN ODC GEO ONV <<< "$(python3 -c "import json, sys; o = json.loads(sys.argv[1]); print(o['id'], o['machine_id'], '%.3f' % o['dph_total'], int(o['cpu_cores_effective']), '%.4f' % float(o.get('reliability2') or 0), int(o['inet_down']), '%.4f' % float(o.get('inet_down_cost') or 0), (o.get('geolocation') or '?').replace(' ', '_'), o.get('bw_nvlink'))" "$o")"
    log "[rent $a/$RENT_TRIES, rental $(( $(rentals) + 1 ))/$MAX_RENTALS] offer $OFFER machine $MACH ($GEO) on-demand \$$ODPH/h, $OCPU vCPU, rel $OREL, down $ODOWN Mb/s at \$$ODC/GB, disk $DISK GB, bw_nvlink $ONV"
    money "$ODPH" "$ODC" | tee -a "$L" | grep -v '^MONEY' | head -n 1
    local outc; outc=$(CONFIRM=yes ONDEMAND=1 DISK="$DISK" LABEL=lra-a100-off timeout "${CREATE_TIMEOUT_S:-240}" "$HERE/create.sh" "$OFFER" "$ODPH" 2>&1)
    id=$(printf '%s' "$outc" | python3 -c 'import json,sys,re; t=sys.stdin.read(); m=re.search(r"\{.*\}", t, re.S); print(json.loads(m.group(0)).get("new_contract",""))' 2>/dev/null)
    if [ -z "$id" ]; then
      id=$(lost_create)
      if [ -n "$id" ]; then log "create.sh gave no id for offer $OFFER, but vast lists instance $id labelled lra-a100-off: adopting it (no second rental)"
      else log "create failed for offer $OFFER: $(printf '%s' "$outc" | grep -o '"msg": *"[^"]*"' | head -n 1 | cut -c1-160); skipping that listing"; SKIP_OFFERS="${SKIP_OFFERS:-} $OFFER"; export SKIP_OFFERS; continue; fi
    fi
    echo $(( $(rentals) + 1 )) > "$STD/rentals.count"
    echo "$id" > "$IDF"
    python3 -c "import json, sys, time; json.dump({'id': sys.argv[1], 'offer': sys.argv[2], 'machine': sys.argv[3], 'dph_offer': float(sys.argv[4]), 'geo': sys.argv[5], 'cpu': int(sys.argv[6]), 'rented_at': time.time(), 'credit_at_rental': sys.argv[7], 'release_at': sys.argv[8], 'disk': int(sys.argv[9])}, open(sys.argv[10], 'w'))" \
      "$id" "$OFFER" "$MACH" "$ODPH" "$GEO" "$OCPU" "${cr:-?}" "${RELEASE_AT:-}" "$DISK" "$OFF/rental-$id.json"
    printf -- "- %s UTC official on-demand rental: instance %s (offer %s, machine %s, %s, \$%s/h on-demand, %s vCPU, disk %s GB, down %s Mb/s at \$%s/GB; credit \$%s)\n" \
      "$(date -u +%Y-%m-%dT%H:%M)" "$id" "$OFFER" "$MACH" "$GEO" "$ODPH" "$OCPU" "$DISK" "$ODOWN" "$ODC" "${cr:-?}" >> "$ACC"
    log "RENTED $id (offer $OFFER, machine $MACH, \$$ODPH/h): id -> $IDF"
    arm_guard "$id" "$ODPH" || log "rent: WARN the guard is not armed yet on $id (arm re-arms it)"
    start_bootstrap "$id"
    wait_ssh "$id"; local w=$?
    if [ "$w" = 0 ]; then
      log "SSH up: $(cat "$SSHF") (-> $SSHF, probe/a100-tunnels/$id)"
      local v r; v=$(topo_verdict "$id"); r=$?; log "topology: $v"; echo "$v" > "$STD/topo.$id"
      case "$r" in
        0) done_mark "rent.$id" "$OFFER $MACH $ODPH"; echo "$id"; return 0;;
        2) log "rent: WARN the early NVLink read failed $TOPO_TRIES times on $id ($v): KEEPING it; the late check (bootstrap + vLLM all-reduce) decides"
           push "official on-demand $id: early NVLink check unreadable ($TOPO_TRIES reads); box kept, the late check decides"
           done_mark "rent.$id" "$OFFER $MACH $ODPH topo-unreadable"; echo "$id"; return 0;;
      esac
      drop_box "$id" "early check: $v" || return 1; continue
    fi
    if [ "$w" = 2 ]; then   # the bootstrap ended before SSH: 3/5 = a bad host it destroyed itself; 1 after its [0/5] = a host that never came up
      local rc; rc=$(boot_rc "$id")
      case "$rc" in
        3|5) read -r s _ <<< "$(inst "$id")"; [ "$s" = gone ] && { echo "$MACH" >> "$BAD"; echo "$id" >> "$STD/dropped-ids"; rm -f "$IDF"; log "bad host $id (bootstrap rc $rc, destroyed): machine $MACH blacklisted"; continue; };;
        1) if grep -q '^\[0/5\]' "probe/a100-bootstrap-$id.log" 2>/dev/null; then   # review b96: e.g. "instance never published a port map"
             drop_box "$id" "bootstrap rc 1 before SSH ($(tail -n 1 "probe/a100-bootstrap-$id.log" | cut -c1-100))" || return 1; continue; fi;;
      esac
      kept "$id" "official on-demand: bootstrap rc $rc before SSH" >> "$L"; log "rent: bootstrap rc $rc on $id before SSH (KEPT; see probe/a100-bootstrap-$id.log)"; return 1
    fi
    drop_box "$id" "SSH not up within ${SSH_WAIT_S:-1500}s" || return 1
  done
  log "rent: no healthy box after $RENT_TRIES tries"; return 1
}
ph_prep() {   # ID: tools, ship, aux, Kaggle envs (in this order; the restore only after the bootstrap's download-rate check)
  local id=$1; is_done "prep.$id" && { log "prep $id: done earlier"; return 0; }
  boot_wait "$id" '^\[3/5\]|^\[4/5\]' "${PREP_WAIT_S:-1200}"; case $? in 1) log "prep $id: bootstrap ended rc $(boot_rc "$id")"; return 1;; 2) log "prep $id: bootstrap not past its apt step in ${PREP_WAIT_S:-1200}s; continuing";; esac
  if [ -z "${REH_LOCAL_DIR:-}" ]; then
    log "prep $id: apt tools (waits up to 300 s for the boot-time dpkg lock; 2026-10-31 18:25 'tools missing')"
    rsh "$id" "export DEBIAN_FRONTEND=noninteractive; for i in 1 2 3; do apt-get -o DPkg::Lock::Timeout=300 update -qq > /dev/null 2>&1; apt-get -o DPkg::Lock::Timeout=300 install -y -qq ripgrep jq zstd curl > /dev/null 2>&1 && break; sleep 10; done; command -v rg jq zstd | wc -l" 1500 | tail -n 1 | grep -qx 3 \
      || log "prep $id: WARN apt tools not all present yet (harness_setup.sh retries)"
  fi
  for i in $(seq 1 80); do [ -f "$OFF/export.tar.gz" ] && is_done export && break; [ "$i" = 1 ] && log "prep $id: waiting for the export (FINAL_COMMIT $FINAL_COMMIT)"; sleep "$POLL"; done
  is_done export || { log "prep $id: no export after $((80 * POLL)) s"; return 1; }
  "$OFFICIAL" ship "$id" > "$STD/ship.out" 2>&1; tail -n 1 "$STD/ship.out"; grep -q "SHIP OK" "$STD/ship.out" || { log "prep $id: ship failed ($STD/ship.out)"; return 1; }
  if [ -z "${REH_LOCAL_DIR:-}" ]; then
    log "prep $id: aux (bucket-only GCS key, vLLM key dir, status writer, sidecar, ntfy topic; the Kaggle key never leaves the GB10)"
    rsh "$id" "mkdir -p /root/.config/vexorium /workspace/infra/sync && chmod 700 /root/.config/vexorium" 60 > /dev/null
    [ -f "$HOME/.config/vexorium/gcs_sync_key.json" ] && rcp "$id" "$HOME/.config/vexorium/gcs_sync_key.json" /root/.config/vexorium/gcs_sync_key.json
    rcp "$id" probe/a100-alarm/tunnel_watch_host.sh /workspace/tunnel_watch_host.sh; rcp "$id" infra/sync/sidecar.py /workspace/infra/sync/sidecar.py
    [ -s probe/a100-ntfy-topic ] && rcp "$id" probe/a100-ntfy-topic /workspace/ntfy_topic
    rcp "$id" "$HERE/vllm_recipe_host.sh" /workspace/vllm_recipe_host.sh; rcp "$id" "$HERE/package_stop_host.sh" /workspace/package_stop_host.sh
    rsh "$id" "chmod 600 /root/.config/vexorium/* 2>/dev/null; chmod +x /workspace/tunnel_watch_host.sh; mkdir -p envs/logs && APT_LOCK_S=300 SKIP_ENVS=1 LRA_WITH_KAGGLE=0 bash infra/vast/harness_setup.sh 2>&1 | tail -n 1" 1800 | tee -a "$L"
    rsh "$id" "command -v rg > /dev/null && command -v zstd > /dev/null && command -v jq > /dev/null && echo tools-ok" 60 | grep -q tools-ok || { log "prep $id: tools missing (rg/zstd/jq) after harness_setup.sh"; return 1; }
  fi
  local t0; t0=$(date +%s); until rate_checked "$id"; do
    [ $(( $(date +%s) - t0 )) -ge "${RATE_WAIT_S:-1500}" ] && { log "prep $id: the bootstrap's rate check not seen in ${RATE_WAIT_S:-1500}s; restoring anyway"; break; }
    sleep "$POLL"; done
  case "$(boot_rc "$id")" in ""|0) ;; *) log "prep $id: bootstrap ended rc $(boot_rc "$id"): no env restore"; return 1;; esac
  local only=""
  if rows_known && ! grep -q '"source": *"leanpool"' "$OFF/rows/rows.jsonl"; then
    only=$(awk -F'\t' 'NR > 1 && $1 != "lean-env-leanpool-x86-64" {print $1}' infra/vast/envs_kaggle.tsv | sort -u | tr '\n' ' ')
    log "prep $id: no leanpool row: the LeanPool dataset (74 GB unpacked) is skipped"
  fi
  if [ -n "${REH_LOCAL_DIR:-}" ]; then
    log "prep $id: local mode: linking the dev box's environments (${ENVS_SRC:-$ROOT/envs})"
    rsh "$id" "mkdir -p envs; for e in ${ENVS_SRC:-$ROOT/envs}/*; do b=\$(basename \$e); [ -e envs/\$b ] || ln -s \$e envs/\$b; done; ls envs | wc -l" 60 | tee -a "$L"
  else
    log "prep $id: Kaggle env restore (public datasets, PAR $RESTORE_PAR${only:+, only: $only})"
    rsh "$id" "ONLY_DATASETS='$only' infra/sync/restore_envs.sh $RESTORE_PAR > envs/logs/restore.log 2>&1; tail -n 2 envs/logs/restore.log" 5400 | tee -a "$L" | grep -q "^RESTORE DONE" \
      || { log "prep $id: restore failed (envs/logs/restore.log on the box)"; return 1; }
  fi
  done_mark "prep.$id" ok; log "PREP DONE on $id"; return 0
}
ph_envs() {   # ID: waits for the rows; plan -> build -> check (bounded)
  local id=$1 t0; is_done "envs.$id" && { log "envs $id: done earlier"; return 0; }
  t0=$(date +%s); until rows_known; do
    [ $(( $(date +%s) - t0 )) -ge "$ROWS_WAIT_S" ] && { log "envs $id: no rows after ${ROWS_WAIT_S}s"; return 1; }
    [ $(( ($(date +%s) - t0) % 300 )) -lt "$POLL" ] && log "envs $id: waiting for the released rows: run \`$0 rows ROWS.jsonl [HEARTBEATS.jsonl]\`"
    sleep "$POLL"; done
  "$OFFICIAL" envs "$id" plan > "$STD/envs_plan.out" 2>&1; local p; p=$(grep -E "^PLAN " "$STD/envs_plan.out" | tail -n 1); log "envs $id: ${p:-no PLAN line ($STD/envs_plan.out)}"
  case "$p" in "PLAN ok missing=0"*) ;;
    "PLAN ok"*) "$OFFICIAL" envs "$id" build > "$STD/envs_build.out" 2>&1; log "envs $id: build started: $(grep -E 'building|nothing missing|already running' "$STD/envs_build.out" | tail -n 1 | cut -c1-200)";;
    *) log "envs $id: CRITICAL the plan is not ok (NEED-PRUNE / UNKNOWN-SOURCE: runbook 3.3; operator decision); fix, then re-run: $0 envs $id"; push "official envs plan NOT ok: $p"; return 1;; esac
  t0=$(date +%s); while :; do
    "$OFFICIAL" envs "$id" check > "$STD/envs_check.out" 2>&1
    grep -q "ENVS OK" "$STD/envs_check.out" && { done_mark "envs.$id" ok; log "ENVS OK on $id"; return 0; }
    local s; s=$(rsh "$id" "tail -n 1 envs/logs/official_setup.log 2>/dev/null" 60)
    case "$s" in *"SETUP DONE"*"failed=0"*) ;; *"SETUP DONE"*) log "envs $id: CRITICAL $s (envs/logs/official_setup.log on the box)"; push "official env build failed: $s"; return 1;; esac
    [ $(( $(date +%s) - t0 )) -ge "$ENVS_MAX_S" ] && { log "envs $id: not ENVS OK after ${ENVS_MAX_S}s ($s)"; return 1; }
    sleep $(( POLL * 4 )); done
}
ph_refhb() {   # ID (b100): the reference heartbeats: a provided file as is; else measured on the box after ENVS OK (official.sh refhb, idempotent)
  local id=$1 rc
  "$OFFICIAL" refhb "$id" > "$STD/refhb.out" 2>&1; rc=$?; tail -n 3 "$STD/refhb.out"
  if [ "$rc" = 0 ] && grep -q "REFHB OK" "$STD/refhb.out"; then done_mark "refhb.$id" ok; log "refhb $id: $(grep 'REFHB OK' "$STD/refhb.out" | tail -n 1 | sed 's/^\[[^]]*\] //' | cut -c1-220)"
    grep -q "PLACEHOLDER" "$STD/refhb.out" && log "refhb $id: $(grep 'REFHB OK WITH' "$STD/refhb.out" | tail -n 1 | sed 's/^\[[^]]*\] //' | cut -c1-260) (official.sh pushed the alert)"
    return 0; fi
  log "refhb $id: FAILED (rc $rc; $STD/refhb.out): fix, then \`$0 refhb $id\` (it resumes) or \`$0 rows R H\` with a heartbeats file, and re-run the release command"
  push "official refhb FAILED on $id: $(tail -n 1 "$STD/refhb.out" | cut -c1-200)"; return 1
}
ph_vllm() {   # ID -> 0 ready; 3 = re-rent (bad host / no NVLink, box dropped); 1 = stop
  local id=$1 rc; is_done "vllm.$id" && { log "vllm $id: done earlier"; return 0; }
  boot_wait "$id" '^server ready' "$BOOT_MAX_S"; rc=$(boot_rc "$id")
  if ! grep -q "^server ready" "probe/a100-bootstrap-$id.log" 2>/dev/null; then
    case "$rc" in
      3|5) read -r s _ <<< "$(inst "$id")"; if [ "$s" = gone ]; then local m; m=$(python3 -c "import json; print(json.load(open('$OFF/rental-$id.json'))['machine'])" 2>/dev/null)
             [ -n "$m" ] && echo "$m" >> "$BAD"; echo "$id" >> "$STD/dropped-ids"; rm -f "$IDF"; log "bad host $id (bootstrap rc $rc: $(grep 'BAD HOST' "probe/a100-bootstrap-$id.log" | tail -n 1 | cut -c1-140)): destroyed, machine ${m:-?} blacklisted"; return 3; fi;;
      1|6) drop_box "$id" "bootstrap rc $rc ($(tail -n 1 "probe/a100-bootstrap-$id.log" | cut -c1-120))" && return 3; return 1;;
      "") drop_box "$id" "bootstrap not done in ${BOOT_MAX_S}s" && return 3; return 1;;
    esac
    kept "$id" "official on-demand: bootstrap rc $rc" >> "$L"; log "vllm $id: bootstrap rc $rc (KEPT for the operator: probe/a100-bootstrap-$id.log)"; return 1
  fi
  local nv; nv=$(grep -E "^NVLink OK|^WARNING NO-NVLINK" "probe/a100-bootstrap-$id.log" | tail -n 1); log "vllm $id: server ready; ${nv:-no NVLink line}"
  if [ "${nv#NVLink OK}" = "$nv" ]; then
    # review b96: bootstrap's NO-NVLINK is also what two failed SSH reads print ("topo [], tp all-reduce []"); a READY box (~25 min of download
    # and load) is dropped only on a PARSED negative of a re-check: the topology (resume mode) + vLLM's tp:0 all-reduce choice
    local lv lr; lv=$(late_nvlink "$id"); lr=$?; log "vllm $id: late NVLink re-check (early check: $(cat "$STD/topo.$id" 2>/dev/null || echo none)): $lv"
    case "$lr" in
      0) ;;
      1) if [ "$NVLINK_REQUIRED" = 1 ]; then drop_box "$id" "late check: $lv" && return 3; return 1; fi
         log "vllm $id: WARN no NVLink (NVLINK_REQUIRED=0: kept)";;
      *) log "vllm $id: WARN NVLink not confirmed (unreadable after $TOPO_TRIES reads): KEEPING the READY box"; push "official $id: NVLink unconfirmed after the load (unreadable); READY box kept";;
    esac
  fi
  rsh "$id" "[ -f $WS/run_vllm_std.sh ] || cp $WS/run_vllm.sh $WS/run_vllm_std.sh 2>/dev/null; true" 60 > /dev/null
  "$OFFICIAL" vllm "$id" > "$STD/vllm.out" 2>&1; tail -n 1 "$STD/vllm.out"
  grep -qE "VLLM OK|local mode has no vLLM" "$STD/vllm.out" || { log "vllm $id: recipe step failed ($STD/vllm.out)"; return 1; }
  done_mark "vllm.$id" ok; return 0
}
ph_start() {
  local id=$1; is_done "start.$id" && { log "start $id: done earlier"; return 0; }
  "$OFFICIAL" start "$id" > "$STD/start.out" 2>&1; tail -n 3 "$STD/start.out"
  grep -q "STARTED official run" "$STD/start.out" && { done_mark "start.$id" ok; log "STARTED on $id (RUN_CMD: $(rsh "$id" "cat $RUN_DIR/RUN_CMD" 60 | grep -oE -- '--started-at [0-9]+ --job-seconds [0-9]+ --workers [0-9]+ --max-sessions [0-9]+ --end-seconds [0-9]+.*' | cut -c1-160))"; push "official run STARTED on $id"; return 0; }
  log "start $id: FAILED ($STD/start.out)"; return 1
}
arm_units_up() { systemctl --user is-active -q "lra-a100-spendguard$U" && systemctl --user is-active -q "lra-a100-watch$U" && systemctl --user is-active -q "lra-a100-alarm$U"; }
ph_arm() {   # ID: guard (exact dph), hold, watch, alarm (each verified active); read-only WARNs about the p85b side; 1 = not armed (go_fg retries)
  local id=$1 dph; rm -f "$STD/arm.$id.ok"; read -r _ _ _ dph _ <<< "$(inst "$id")"
  [ "${dph:-0}" != 0 ] || dph=$(python3 -c "import json; print(json.load(open('$OFF/rental-$id.json'))['dph_offer'])" 2>/dev/null)
  arm_guard "$id" "$dph" || return 1
  echo "official on-demand run $id (b96): keep through the final pull; the watch releases it at most OFF_HOLD_MAX_S ($OFF_HOLD_MAX_S s) after the run; remove this file to release at once" > "probe/a100-hold-keepofficial-$id"
  local w="lra-a100-watch$U" a="lra-a100-alarm$U"; mkdir -p "probe/a100-reh-$TAG"
  python3 -c "import json; json.dump({'id': '$id', 'run_dir': '$RUN_DIR', 'out': '$OUT', 'tag': '$TAG', 'ondemand': True}, open('probe/a100-reh-$TAG/rental.json', 'w'))"
  systemctl --user stop "$w" 2>/dev/null; systemctl --user reset-failed "$w" 2>/dev/null
  systemd-run --user --unit "$w" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" -E LRA_FAKE_VAST_BIN="${LRA_FAKE_VAST_BIN:-}" -E LRA_UNIT_SUFFIX="$U" \
    -E TAG=$TAG -E RUN_DIR="$RUN_DIR" -E OUT="$OUT" -E EXPORT_ROOT="$EXPORT_ROOT" -E REH_LOCAL_DIR="${REH_LOCAL_DIR:-}" -E LOCAL="probe/a100-reh-$TAG" \
    -E POLL_S="${WATCH_POLL_S:-60}" -E PULL_EVERY_S="${PULL_EVERY_S:-300}" -E STALL_MIN="${STALL_MIN:-20}" -E HOLD_MAX_S="$OFF_HOLD_MAX_S" -E DESTROY_WAIT_S="${DESTROY_WAIT_S:-10}" \
    bash -c "infra/vast/package_watch.sh $id >> probe/a100-reh-$TAG/watch.out 2>&1" > /dev/null 2>&1 \
    && log "watch armed: $w (pull every ${PULL_EVERY_S:-300}s, relaunch, stall alarm, release ${OFF_HOLD_MAX_S}s after the final pull)" \
    || { log "arm $id: FAILED to start the watch unit $w (no pulls, relaunch or stall alarm)"; return 1; }
  systemctl --user stop "$a" 2>/dev/null; systemctl --user reset-failed "$a" 2>/dev/null
  systemd-run --user --unit "$a" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" \
    python3 probe/a100-alarm/alarm.py --reh "probe/a100-reh-$TAG" --id "$id" --run-dir "$RUN_DIR" --out-dir "$OUT" ${NO_ALARM_LIVE:+--no-live --no-push} > /dev/null 2>&1 \
    && log "alarm armed: $a (session errors, driver/vLLM/GPU/disk, stop / unreachable box -> ntfy)" \
    || { log "arm $id: FAILED to start the alarm unit $a"; return 1; }
  sleep "${ARM_SETTLE_S:-3}"
  local x; for x in "lra-a100-spendguard$U" "$w" "$a"; do
    systemctl --user is-active -q "$x" || { log "arm $id: $x is not active ${ARM_SETTLE_S:-3}s after its start ($(systemctl --user show "$x" -p Result --value 2>/dev/null))"; return 1; }
  done
  printf -- "- %s UTC official on-demand run on %s armed: guard cap \$%s (ask-first, scoped), watch hold %s s, alarm\n" "$(date -u +%Y-%m-%dT%H:%M)" "$id" "$(cat "$STD/guard.$id.cap" 2>/dev/null)" "$OFF_HOLD_MAX_S" >> "$ACC"
  local l; while IFS= read -r l; do [ -n "$l" ] && log "$l"; done <<< "$(other_guard_warn)"
  local p; p=$(cat probe/a100-instance-id 2>/dev/null); [ -n "$p" ] && [ "$p" != "$id" ] && ls probe/a100-hold*-"$p" > /dev/null 2>&1 && \
    log "WARN probe/a100-hold*-$p keeps the p85b box billing up to its watch's HOLD_MAX_S after p85b ends (the old kept-box plan); remove it after p85b's final pull unless that box is still wanted"
  done_mark "arm.$id" ok; log "ARMED official on-demand run on $id"
}
plan_print() {
  local id; id=$(cur_id)
  [ -n "${1:-}" ] && RELEASE_AT=$1
  local o; o=$(offers 2> "$STD/offers.err"); local first; first=$(head -n 1 <<< "$o")
  if [ -n "$first" ]; then
    read -r OFFER MACH ODPH OCPU OREL ODOWN ODC GEO ONV <<< "$(python3 -c "import json, sys; o = json.loads(sys.argv[1]); print(o['id'], o['machine_id'], '%.3f' % o['dph_total'], int(o['cpu_cores_effective']), '%.4f' % float(o.get('reliability2') or 0), int(o['inet_down']), '%.4f' % float(o.get('inet_down_cost') or 0), (o.get('geolocation') or '?').replace(' ', '_'), o.get('bw_nvlink'))" "$first")"
    money "$ODPH" "$ODC" "$id" > "$STD/money.out"; grep -v '^MONEY' "$STD/money.out" | head -n 1 | tee -a "$L"   # FIRST line
  else echo "CREDIT/OFFER WARNING: no acceptable on-demand offer now (cap \$$CAP${CAP_MAX:+, ONDEMAND_CAP_MAX \$$CAP_MAX}): credit not checked" | tee -a "$L"; fi
  other_guard_warn && echo "  -> go REFUSES while another spend guard is active: stop it (command above), or OTHER_GUARD_OK=1 when it must run beside the official run"   # next FIRST lines (review b96)
  local why; [ -n "${1:-}" ] && { why=$(release_check "$1") || echo "NOTE go would refuse RELEASE_AT '$1' now: $why"; }
  echo "== official on-demand plan $(date -u '+%Y-%m-%d %H:%M UTC') (\$0: search only, nothing rented)"
  if [ -n "$first" ]; then
    echo "WOULD RENT: offer $OFFER machine $MACH ($GEO), on-demand \$$ODPH/h incl. $DISK GB storage, $OCPU vCPU, reliability $OREL, down $ODOWN Mb/s at \$$ODC/GB, bw_nvlink $ONV"
    grep '^MONEY' "$STD/money.out"
  else echo "WOULD RENT: nothing: no acceptable on-demand offer now"; fi
  cat "$STD/offers.err"
  echo "acceptable offers (best first; bw_nvlink > 0 first, then rank = dph x $((HOURS + SETUP_H)) h + traffic + vCPU penalty):"
  head -n "${PLAN_TOP:-5}" <<< "$o" | python3 -c '
import json, sys
for l in sys.stdin:
    if l.strip():
        o = json.loads(l); g = o.get; dc = float(g("inet_down_cost") or 0); rl = float(g("reliability2") or 0)
        print("  offer %s machine %s %s: $%.3f/h, %d vCPU, rel %.3f, down %d Mb/s at $%.4f/GB, bw_nvlink %s%s, rank $%.0f" % (g("id"), g("machine_id"), g("geolocation"),
              g("dph_total"), int(g("cpu_cores_effective")), rl, int(g("inet_down")), dc, g("bw_nvlink"), " (ranked last: the topology check decides)" if g("_nv") else "", g("_cost")))'
  echo "filters: on-demand, 4x A100 SXM4 80 GB, verified${VERIFIED:+ ($VERIFIED)}, rel >= $REL_MIN, vCPU >= $CPU_MIN (prefer >= $PREFER_CPU: +\$$CPU_PENALTY_H/h below), disk >= $DISK GB, down >= $MIN_DOWN Mb/s, dph_total <= \$$CAP (ONDEMAND_CAP_MAX ${CAP_MAX:-off}), bw_nvlink > 0 first, not in bad_machines.txt ($(wc -l < "$BAD") machines), not our own machines ($(others_dph "${id:-x}" | awk '{print $2}'))"
  echo "decisions ($D):"; grep -E '^[A-Z_]+=' "$D" | grep -E '^(RELEASE_AT|FINAL_COMMIT|WORKERS|MAX_SESSIONS|VLLM_RECIPE|END_SECONDS|AUTO_BRIEF)=' | sed 's/^/    /'
  [ -n "${1:-}" ] && echo "    RELEASE_AT (this plan) = $1 -> job clock start $(date -u -d "$1" +%s 2>/dev/null || echo BAD)"
  [ -n "${FINAL_COMMIT:-}" ] || echo "    WARN FINAL_COMMIT is empty: go would export HEAD of $(git rev-parse --abbrev-ref HEAD 2>/dev/null) = $(git rev-parse --short=8 HEAD 2>/dev/null)"
  echo "rows: $(rows_known && echo "ready ($(wc -l < "$OFF/rows/rows.jsonl") rows)" || echo "not yet (go waits for \`$0 rows R [H]\` up to ${ROWS_WAIT_S}s)")"
  echo "export: $(cat "$OFF/export/HARNESS_COMMIT" 2>/dev/null || echo none) in $OFF/export.tar.gz"
  echo "current official box: ${id:-none} ($( [ -n "$id" ] && inst "$id" || echo -))"
  echo "p85b (read only): probe/a100-instance-id = $(cat probe/a100-instance-id 2>/dev/null) ($(inst "$(cat probe/a100-instance-id 2>/dev/null)" | cut -d' ' -f1)); its units: $(systemctl --user list-units --plain --no-legend 'lra-a100*-ms2*' 2>/dev/null | awk '{print $1}' | tr '\n' ' ')"
  echo "units now: $(units_on)"
  echo "bounds: at most MAX_RENTALS $MAX_RENTALS creates for this release ($(rentals) so far), $RENT_TRIES searches per rent call; NVLink: only a parsed negative drops a box ($TOPO_TRIES reads, ${TOPO_RETRY_S}s apart)"
  echo "go would run: RELEASE_AT -> $D; rows + export (background); CONFIRM=yes rent (create.sh ONDEMAND=1 DISK=$DISK; guard lra-a100-spendguard$U scoped;"
  echo "  bootstrap unit lra-a100-bootstrap$U; SSH; NVLink topology); prep unit lra-a100-prep$U (apt, ship, aux, restore PAR $RESTORE_PAR) then envs (plan/build/check)"
  echo "  then refhb (the given heartbeats file, else the references measured on the box: $( [ -f "$OFF/rows/HB_MEASURE" ] && echo 'to measure' || echo 'file given or rows not yet in'));"
  echo "  vllm (bootstrap READY + NVLink OK; recipe ${VLLM_RECIPE:-std}); official.sh start (RUN_DIR $RUN_DIR, OUT $OUT, TAG off, START per CLOCK_START=${CLOCK_START:-launch}, JOB 172800,"
  echo "  WORKERS ${WORKERS:-?} MAX_SESSIONS ${MAX_SESSIONS:-?} END_SECONDS ${END_SECONDS:-?} --end-pipeline on${AUTO_BRIEF:+ AUTO_BRIEF=$AUTO_BRIEF}); arm (guard re-armed, hold ${OFF_HOLD_MAX_S}s,"
  echo "  lra-a100-watch$U, lra-a100-alarm$U). NOT run: no sentry, no bid ladder, no bid keeper, no p85b stop, no -ms2 unit touched."
}
go_fg() {
  local rel=${1:?RELEASE_AT}; local R=${2:-} H=${3:-} why
  why=$(release_check "$rel") || { log "go $why"; exit 2; }   # operator 2026-10-31: rent once the questions are released, not before
  RELEASE_AT=$rel
  # the money line FIRST in official.log (operator: rent anyway, but say when the credit runs out); the offers' summary after it
  money_now "$(cur_id)"; log "$(head -n 1 "$STD/money.out")"; grep '^MONEY' "$STD/money.out" >> "$L"; cat "$STD/offers.now.err" >> "$L" 2>/dev/null
  grep -q "^CREDIT WARNING" "$STD/money.out" && { cp "$STD/money.out" "$OFF/CREDIT_WARNING"; push "$(head -n 1 "$STD/money.out" | cut -c1-280)"; }
  local og l; if og=$(other_guard_warn); then   # review b96: p85b's account-wide guard would destroy the official box too
    while IFS= read -r l; do log "$l"; done <<< "$og"; push "$(head -n 1 <<< "$og" | cut -c1-300)"
    [ "${OTHER_GUARD_OK:-0}" = 1 ] || die "another spend guard is active (WARN above): stop it, or re-run with OTHER_GUARD_OK=1"
    log "OTHER_GUARD_OK=1: going on beside it (stop it right after p85b's final pull)"
  fi
  set_decision RELEASE_AT "$rel"
  [ -n "${FINAL_COMMIT:-}" ] || { local h; h=$(git rev-parse --short=8 HEAD 2>/dev/null); log "WARN FINAL_COMMIT empty in $D: using HEAD $h ($(git rev-parse --abbrev-ref HEAD 2>/dev/null))"; set_decision FINAL_COMMIT "$h"; }
  . "$D"
  log "GO: official on-demand run, RELEASE_AT $RELEASE_AT ($(rel_epoch)), FINAL_COMMIT $FINAL_COMMIT, WORKERS $WORKERS, MAX_SESSIONS $MAX_SESSIONS, VLLM_RECIPE $VLLM_RECIPE, END_SECONDS $END_SECONDS, AUTO_BRIEF $AUTO_BRIEF"
  if [ -n "$R" ]; then ph_rows "$R" "$H" &
  elif [ -f "$OFF/rows/ROWS_OK" ] && [ "$(cat "$OFF/rows/ROWS_OK")" -lt $(( $(rel_epoch) - 43200 )) ]; then mv "$OFF/rows/ROWS_OK" "$OFF/rows/ROWS_OK.stale-$(date +%s)"; log "go: rows older than RELEASE_AT - 12 h set aside: run \`$0 rows R H\`"; fi
  rm -f "$STD/export.ok"; ph_export > /dev/null &
  local rents=0 id rc s v r
  while :; do
    id=$(cur_id)
    if [ -n "$id" ]; then read -r s _ <<< "$(inst "$id")"   # review b96: one "gone" read is not enough to rent a second box
      if [ "$s" = gone ] && confirmed_gone "$id"; then log "go: $id is gone (${GONE_READS:-3} reads): renting a new box"; rm -f "$IDF"; id=""; fi; fi
    if [ -z "$id" ]; then
      rents=$((rents + 1)); [ "$rents" -le "$MAX_RENTALS" ] || die "no healthy on-demand box after $MAX_RENTALS rent calls"
      CONFIRM=yes ph_rent > "$STD/rent.$rents.out" 2>&1; cat "$STD/rent.$rents.out"; id=$(tail -n 1 "$STD/rent.$rents.out")
      [ -n "$id" ] && [ "$id" = "$(cur_id)" ] || die "rent failed (see $L)"
    else
      log "go: resuming on the official box $id"
      if ! is_done "rent.$id"; then
        wait_ssh "$id" || die "resumed box $id: SSH not up"
        v=$(topo_verdict "$id" resume); r=$?; log "topology: $v"; echo "$v" > "$STD/topo.$id"
        [ "$r" = 1 ] && die "resumed box $id: $v (drop it: CONFIRM=yes infra/vast/destroy.sh $id; then re-run go)"
        done_mark "rent.$id" "resumed$( [ "$r" = 2 ] && echo ' topo-unreadable')"
      fi
      [ -n "$(boot_rc "$id")" ] || systemctl --user is-active -q "lra-a100-bootstrap$U" || start_bootstrap "$id"
    fi
    systemctl --user stop "lra-a100-prep$U" 2>/dev/null; systemctl --user reset-failed "lra-a100-prep$U" 2>/dev/null; rm -f "$STD/prep.$id.rc"
    envargs $PASSVARS
    systemd-run --user --unit "lra-a100-prep$U" --collect --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" "${ENVA[@]}" \
      bash -c "bash '$SELF' prep $id && bash '$SELF' envs $id && bash '$SELF' refhb $id; echo \$? > '$STD/prep.$id.rc'" > /dev/null 2>&1 && log "prep + envs + refhb started: unit lra-a100-prep$U (log $L)"
    ph_vllm "$id"; rc=$?
    [ "$rc" = 3 ] && { systemctl --user stop "lra-a100-prep$U" 2>/dev/null; log "go: re-renting (box $id dropped)"; continue; }
    [ "$rc" = 0 ] || die "vLLM not ready on $id"
    local t0; t0=$(date +%s); until [ -f "$STD/prep.$id.rc" ]; do [ $(( $(date +%s) - t0 )) -ge $((ROWS_WAIT_S + ENVS_MAX_S + 7200)) ] && die "prep/envs not done"; sleep "$POLL"; done
    [ "$(cat "$STD/prep.$id.rc")" = 0 ] || die "prep/envs/refhb failed on $id (rc $(cat "$STD/prep.$id.rc"); $L); fix, then re-run the release command (it resumes)"
    break
  done
  # operator 2026-11-01 ~06:55 UTC (option B): rent + prepare at the release, hold the start for the ~09:30 decision. OFF/HOLD_START present:
  # stop here with the box ready (vLLM up, ENVS OK, refhb done); rm the file and re-run the release command (it resumes into start + arm)
  if [ -f "$OFF/HOLD_START" ]; then
    log "HELD before start ($OFF/HOLD_START): official box $id READY (vLLM up, envs ok, refhb done); to start: rm $OFF/HOLD_START, then re-run go (resumes into start + arm)"
    exit 0
  fi
  ph_start "$id" || die "start failed on $id"
  # review b96: a failed arm (credit unreadable, a unit that did not start) left a 48 h run with no watch / alarm while the log said GO DONE
  local ai; for ai in $(seq 1 "$ARM_TRIES"); do
    if is_done "arm.$id" && arm_units_up; then log "arm $id: done earlier; guard, watch and alarm active"; break; fi
    ph_arm "$id" && break
    [ "$ai" -lt "$ARM_TRIES" ] && { log "arm $id: attempt $ai/$ARM_TRIES failed: retry in ${ARM_RETRY_S}s"; sleep "$ARM_RETRY_S"; }
  done
  { is_done "arm.$id" && arm_units_up; } || die "arm failed on $id after $ARM_TRIES tries: the run is LIVE without its guard / watch / alarm: run \`$0 arm $id\` now"
  log "GO DONE: official run on $id since $(date -u -d "@$(rel_epoch)" '+%H:%M') UTC (release) - setup took $(( ($(date +%s) - $(rel_epoch)) / 60 )) min ($( [ "${CLOCK_START:-launch}" = release ] && echo 'inside' || echo 'outside') the 48 h clock: CLOCK_START=${CLOCK_START:-launch}); ssh $(cat "$SSHF" 2>/dev/null)"
}

case "$PHASE" in
plan) plan_print "${1:-}";;
go)
  [ -n "${1:-}" ] || { echo "usage: $0 go \"RELEASE_AT\" [ROWS.jsonl [HEARTBEATS.jsonl]]"; exit 2; }
  why=$(release_check "$1") || { echo "$why"; exit 2; }
  u="lra-a100-go$U"; systemctl --user is-active -q "$u" && { echo "$u is already running (log $OFF/go.out); stop-go first to restart it"; exit 1; }
  # review b96: the credit verdict in THIS terminal (it used to reach only go.out / official.log / ntfy), then any other spend guard
  RELEASE_AT=$1; money_now "$(cur_id)"; head -n 1 "$STD/money.out"; grep '^MONEY' "$STD/money.out"
  if og=$(other_guard_warn); then echo "$og"
    [ "${OTHER_GUARD_OK:-0}" = 1 ] || { echo "REFUSED: another spend guard is active (above): stop it, or re-run with OTHER_GUARD_OK=1 to run beside it"; push "official go REFUSED: $(head -n 1 <<< "$og" | cut -c1-240)"; exit 2; }
  fi
  systemctl --user reset-failed "$u" 2>/dev/null
  R=${2:+$(realpath "$2")}; H=${3:+$(realpath "$3")}
  envargs $PASSVARS
  systemd-run --user --unit "$u" --working-directory="$ROOT" -E PATH="$PATH" -E HOME="$HOME" -p RuntimeMaxSec=$((ROWS_WAIT_S + ENVS_MAX_S + BOOT_MAX_S + 14400)) "${ENVA[@]}" \
    bash -c "bash '$SELF' go-fg '$1' '${R}' '${H}' >> '$OFF/go.out' 2>&1" > /dev/null || { echo "could not start $u"; exit 1; }
  echo "started $u: release $1; log $OFF/go.out + $L; status: $0 status; stop the orchestrator: $0 stop-go";;
go-fg) go_fg "$@";;
rows) [ -n "${1:-}" ] || { echo "usage: $0 rows ROWS.jsonl [HEARTBEATS.jsonl]   (no heartbeats file: measured by the refhb phase)"; exit 2; }; ph_rows "$1" "${2:-}";;
export) ph_export;;
rent) ph_rent;;
prep) need_id "${1:-}"; ph_prep "$ID";;
envs) need_id "${1:-}"; ph_envs "$ID";;
refhb) need_id "${1:-}"; ph_refhb "$ID";;
vllm) need_id "${1:-}"; ph_vllm "$ID";;
start) need_id "${1:-}"; ph_start "$ID";;
arm) need_id "${1:-}"; ph_arm "$ID";;
status) need_id "${1:-}"; id=$ID; echo "official box $id: $(inst "$id") | ssh $(cat "$SSHF" 2>/dev/null) | units: $(units_on)"
  echo "done: $(ls "$STD" 2>/dev/null | grep -E "\.$id\.ok$|^export\.ok$" | tr '\n' ' ') | bootstrap rc $(boot_rc "$id") | prep rc $(cat "$STD/prep.$id.rc" 2>/dev/null)"
  tail -n 2 "probe/a100-bootstrap-$id.log" 2>/dev/null | sed 's/^/  bootstrap: /'
  is_done "start.$id" && "$OFFICIAL" status "$id"; true;;
topo) need_id "${1:-}"; topo_verdict "$ID" "${2:-}";;
ssh) need_id "${1:-}"; id=$ID; read -r h p < "$SSHF"; echo "ssh -i ~/.ssh/id_ed25519 -p $p root@$h   # official box $id";;
upload) need_id "${1:-}"; "$OFFICIAL" upload "$ID";;
stop-go) for u in "lra-a100-go$U" "lra-a100-prep$U" "lra-a100-bootstrap$U"; do systemctl --user is-active -q "$u" && { systemctl --user stop "$u"; log "stopped $u (the box, guard, watch and alarm are untouched)"; }; done; true;;
*) sed -n '2,48p' "$SELF"; exit 2;;
esac
