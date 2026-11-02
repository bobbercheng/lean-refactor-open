#!/usr/bin/env bash
# Keep probe/a100-tunnels/<id> on a WORKING tunnel (2026-10-30, after ntfy.sh silently dropped the host's port announcements from 08:14):
# 1. our server's FIXED port (bore.vexorium.net:<port>, host watchdog) when it returns the SSH banner;
# 2. else the newest "listening at bore.pub:N" in the container's /tmp/bore.log, read with `vastai copy` (the host's rsync daemon: no SSH);
# 3. else the newest "tunnel bore.pub:N" on the ntfy topic. Every 60 s; logs changes.
cd "$(dirname "$0")/../.." || exit 2
ID=${1:?id}; FIXED=${2:?fixed bore port}; F=probe/a100-tunnels/$ID; L=probe/a100-alarm/tunnel_refresh.log; T=$(cat probe/a100-ntfy-topic); TMP=probe/a100-alarm/tr_$ID; mkdir -p "$TMP"
banner() { timeout 10 bash -c "exec 3<>/dev/tcp/$1/$2; head -c 7 <&3" 2>/dev/null | grep -q SSH; }
while :; do
  v=""
  if banner bore.vexorium.net "$FIXED"; then v="bore.vexorium.net $FIXED"
  else
    env -u LRA_FAKE_VAST_BIN timeout 120 vastai copy "C.$ID:/tmp/bore.log" "local:$PWD/$TMP/" >/dev/null 2>&1
    p=$(grep -oE "listening at bore.pub:[0-9]+" "$TMP/bore.log" 2>/dev/null | tail -1 | cut -d: -f2)
    if [ -n "$p" ] && banner bore.pub "$p"; then v="bore.pub $p"
    else
      p=$(curl -s -m 20 "https://ntfy.sh/$T/json?poll=1&since=12h" | python3 -c "import sys,json,re; m=[json.loads(l).get('message','') for l in sys.stdin if l.strip()]; t=[x for x in m if re.fullmatch(r'tunnel bore\.pub:\d+', x.strip())]; print(t[-1].split(':')[-1] if t else '')" 2>/dev/null)
      [ -n "$p" ] && banner bore.pub "$p" && v="bore.pub $p"
    fi
  fi
  if [ -n "$v" ] && [ "$v" != "$(cat "$F" 2>/dev/null)" ]; then echo "$v" > "$F"; echo "[$(date -u -Is)] tunnel for $ID now $v" >> "$L"; fi
  [ -z "$v" ] && echo "[$(date -u -Is)] no working tunnel found (fixed $FIXED, disk bore.log, ntfy)" >> "$L"
  sleep 60
done
