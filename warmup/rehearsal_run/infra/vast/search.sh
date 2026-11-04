#!/usr/bin/env bash
# Check (never rent) vast.ai offers for the A100 POC: 4x A100 80 GB, >= 64 vCPU, >= 300 GB disk, storage priced at 300 GiB.
# Usage: infra/vast/search.sh            -> interruptible (bid) and on-demand, verified hosts, then bid on all hosts
set -u
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3
Q='num_gpus=4 gpu_ram>=80 gpu_name=A100_SXM4 cpu_cores_effective>=64 disk_space>=300'
show() { python3 "$(dirname "$0")/_fmt.py"; }
echo "== interruptible (bid), verified hosts"; vastai search offers "$Q" --type bid --storage 300 -o dph_total --limit 10 --raw | show
echo "== on-demand, verified hosts";          vastai search offers "$Q" --type on-demand --storage 300 -o dph_total --limit 10 --raw | show
echo "== interruptible (bid), ALL hosts";     vastai search offers "$Q verified=any rentable=true" -n --type bid --storage 300 -o dph_total --limit 10 --raw | show
echo; echo "account:"; vastai show user --raw | python3 -c 'import json,sys; d=json.load(sys.stdin); print("  credit $%.2f  can_pay=%s" % (d.get("credit") or 0, d.get("can_pay")))   # the money is in credit; balance stays 0'
