#!/usr/bin/env bash
# Show our vast.ai instances (state, $/h, GPU) and, if a tunnel is up, the server's health and READY marker.
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai
vastai show instances --raw | python3 -c '
import json,sys
d=json.load(sys.stdin)
if not d: print("no instances")
for i in d:
    g = i.get; p = (g("ports") or {}).get("22/tcp") or [{}]
    print("id=%s  %s/%s  $%.3f/h  %sx%s  label=%s  ssh: ssh -p %s root@%s (direct)  bid=%s  min_bid=$%.3f" % (g("id"), g("actual_status"), g("intended_status"),
          g("dph_total") or 0, g("gpu_name"), g("num_gpus"), g("label"), p[0].get("HostPort"), g("public_ipaddr"), g("is_bid"), g("min_bid") or 0))
'
for id in $(vastai show instances --raw | python3 -c "import json,sys; print(*[i['id'] for i in json.load(sys.stdin)])"); do "$(dirname "$0")/server_up.sh" "$id" --bridge; done
