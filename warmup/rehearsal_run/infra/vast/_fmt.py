#!/usr/bin/env python3
"""Format `vastai search offers --raw` JSON (stdin) as one line per offer."""
import json, sys
d = json.load(sys.stdin)
if not d:
    print("  (none)")
for o in d:
    print(f"  id={o['id']:<9} ${o['dph_total']:.3f}/h  min_bid=${o.get('min_bid', 0) or 0:.3f}  {o['gpu_name']}x{o['num_gpus']}  vcpu={o.get('cpu_cores_effective')}  "
          f"ram={int((o.get('cpu_ram') or 0) / 1024)}GB  disk={int(o.get('disk_space') or 0)}GB  down={int(o.get('inet_down') or 0)}Mb/s  rel={o.get('reliability2') or 0:.3f}  "
          f"nvlink={o.get('bw_nvlink')}  verified={o.get('verification') or o.get('verified')}  inet$/GB down={float(o.get('inet_down_cost') or 0):.4f} up={float(o.get('inet_up_cost') or 0):.4f}  "
          f"{o.get('geolocation')}")
