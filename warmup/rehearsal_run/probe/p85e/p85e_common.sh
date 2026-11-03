# sourced by the GB10-side p85e scripts (lra-a100 probe/p85e): box address re-resolved on every call, bounded ssh / scp / rsync.
# v2 (2026-10-31 ~22:45 UTC, fixer): resolve() no longer reads probe/a100-instance-id (provision.sh rewrites it when the release box is
# rented): it asks vastai about 58565100 itself and reports "gone" (2) only when vastai's instance list was read fine and 58565100 is not
# in it; any other failure is transient (1, retry). pull_late() (OUT/work + run dirs p85b-c*/t*) for wbpush; pull_all() returns 0 only
# when all three rsyncs returned 0 and clips each rsync to the time left. Test hooks: P85E_ROOT, P85E_DIR, P85E_LOCKDIR, P85E_SYSCTL,
# P85E_NTFY (the live units set none of them).
# v3 (2026-11-01 ~00:00 UTC, operator 23:40 "keep the warm-up climb until the board reset"): END_AT helpers. probe/p85e/END_AT is the GB10
# truth (first token = epoch; missing / bad = the cap); the box copy /workspace/p85e/END_AT is what the v3 scheduler reads (wbpush syncs
# it every round; set_end writes both). FINAL_NOW (written by p85e_stop_all.sh: "<mode> <epoch> <reason>") makes the armed final fire at
# once; FINAL_DONE is written when the final is through. Test hook: P85E_CAP.
ROOT=${P85E_ROOT:-/home/bobber/source/lra-a100}; cd "$ROOT" || exit 2
PD=${P85E_DIR:-/home/bobber/source/lra-a100/probe/p85e}; LOCKDIR=${P85E_LOCKDIR:-/tmp}; SYSCTL=${P85E_SYSCTL:-systemctl}
ID0=58565100; MIR=$ROOT/probe/a100-reh-p85e; REH=$ROOT/probe/a100-reh-p85b; HOLD=$ROOT/probe/a100-hold-p85e-$ID0
KEY=$HOME/.ssh/id_ed25519; SOPT="-i $KEY -o BatchMode=yes -o ConnectTimeout=20 -o StrictHostKeyChecking=accept-new"
NTFY=${P85E_NTFY-$(cat "$ROOT/probe/a100-ntfy-topic" 2>/dev/null)}
CAP_EPOCH=${P85E_CAP:-1793577600}   # 2026-11-02 00:00 UTC: the stop rule's hard cap
END_F=$ROOT/probe/p85e/END_AT; FINAL_NOW=$ROOT/probe/p85e/FINAL_NOW; FINAL_DONE=$ROOT/probe/p85e/FINAL_DONE
end_at() { local v; v=$(awk 'NR==1{print $1}' "$END_F" 2>/dev/null); case "$v" in (''|*[!0-9]*) v=$CAP_EPOCH;; esac
  [ "$v" -gt "$CAP_EPOCH" ] && v=$CAP_EPOCH; echo "$v"; }
hm() { date -u -d "@$1" '+%m-%d %H:%M:%S'; }
set_end_local() { local v=$1; shift; printf '%s %s %s\n' "$v" "$(date -u -d "@$v" +%Y-%m-%dT%H:%M:%SZ)" "$*" > "$END_F.tmp" && mv "$END_F.tmp" "$END_F"; }
push_end() {   # $1 = epoch, $2 = note; needs resolve() first; prints the box's "END_AT <epoch> <utc>" line (empty = no reply)
  bsh "bash /workspace/p85e/p85e_ctl.sh set-end $1 ${2:-gb10}" 90 | grep "^END_AT" | tail -n 1; }
box_end() { bsh "bash /workspace/p85e/p85e_ctl.sh get-end" 60 | awk '/^END_AT/{print $2}' | tail -n 1; }
plog() { echo "[$(date -u +%m-%d\ %H:%M:%S)] $*" | tee -a "${PLOG:-$ROOT/probe/p85e/p85e_gb10.log}"; }
push() { [ -n "$NTFY" ] && curl -fsS -m 20 -H "Title: A100 p85e" -H "Priority: urgent" -d "$*" "https://ntfy.sh/$NTFY" > /dev/null 2>&1; true; }
resolve() {   # sets ST IP PT. 0 = running with an ssh address; 1 = not running or not readable right now (transient: retry later);
              # 2 = 58565100 confirmed gone (vastai's instance list read fine and 58565100 not in it). Never reads probe/a100-instance-id.
  local out
  out=$(timeout 60 vastai show instance "$ID0" --raw 2>/dev/null | python3 -c "import json, sys
d = json.load(sys.stdin); assert isinstance(d, dict) and str(d.get('id')) == '$ID0'
p = (d.get('ports') or {}).get('22/tcp') or [{}]; print(d.get('actual_status') or '?', d.get('public_ipaddr') or '-', p[0].get('HostPort') or '-')" 2>/dev/null)
  if [ -z "$out" ]; then   # show failed: vastai raises both for a destroyed id and on a network error, so ask the instance list which one
    out=$(timeout 60 vastai show instances --raw 2>/dev/null | python3 -c "import json, sys
d = json.load(sys.stdin); assert isinstance(d, list)
print('listed' if any(str(x.get('id')) == '$ID0' for x in d) else 'gone')" 2>/dev/null)
    ST="?"; IP=-; PT=-; [ "$out" = gone ] && { ST=gone; return 2; }; return 1
  fi
  read -r ST IP PT <<< "$out"
  [ "${ST:-}" = running ] && [ "${PT:--}" != - ] && [ "${IP:--}" != - ]
}
bsh() { timeout "${2:-90}" ssh $SOPT -p "$PT" "root@$IP" "$1" 2>/dev/null | grep -v "^Welcome\|^Have fun"; }
rs() { local t=$1; shift; timeout "$t" rsync -az --timeout=120 -e "ssh $SOPT -p $PT" "$@" 2>/dev/null; }
pull_p85e() { rs "${1:-600}" "root@$IP:/workspace/p85e/" "$MIR/"; }
pull_late() {   # wbpush, every round: what the watch stops pulling once it blocks in release() on the hold (OUT/work = continuation
                # sessions + twin->main merges; run dirs p85b-c* / p85b-t*); incremental, into the same mirror the pick readers use
  local t=${1:-600} r1 r2
  rs "$t" "root@$IP:/workspace/out-p85b/work/" "$REH/out/work/"; r1=$?
  rs "$t" --include='p85b-[ct]*/' --include='p85b-[ct]*/**' --exclude='*' "root@$IP:/workspace/lra/probe/runs/" "$REH/runs/"; r2=$?
  echo "work=$r1 runs=$r2"; [ $r1 = 0 ] && [ $r2 = 0 ]
}
_left() { local l=$(( P_LEFT - ($(date +%s) - P_T0) )); [ $l -gt $1 ] && l=$1; [ $l -lt 30 ] && l=30; echo $l; }
pull_all() {   # $1 = seconds left. The watch's own pull (OUT + run dirs p85b-*, incl. p85e's p85b-cNN / p85b-tNN) + /workspace/p85e;
               # each rsync bounded by min(its cap, the time left); returns 0 only when all three returned 0
  P_LEFT=${1:-2400}; P_T0=$(date +%s); local r1 r2 r3
  rs "$(_left 900)" "root@$IP:/workspace/out-p85b/" "$REH/out/"; r1=$?
  rs "$(_left 900)" --include="p85b-*/" --include="p85b-*/**" --exclude='*' "root@$IP:/workspace/lra/probe/runs/" "$REH/runs/"; r2=$?
  pull_p85e "$(_left 600)"; r3=$?
  echo "rsync rc out=$r1 runs=$r2 p85e=$r3"; [ $r1 = 0 ] && [ $r2 = 0 ] && [ $r3 = 0 ]
}
