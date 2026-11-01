#!/usr/bin/env bash
# Destroy the POC instance (stops billing; the instance disk and HF cache are lost). Requires CONFIRM=yes.
# Usage: CONFIRM=yes infra/vast/destroy.sh <instance_id>
set -eu
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3
ID=${1:?instance id}
echo "would run: vastai destroy instance $ID"
[ "${CONFIRM:-}" = "yes" ] || { echo "(dry run: set CONFIRM=yes)"; exit 0; }
# hold (2026-10-07: test the harness at 8-12 workers before releasing): a follow-up job owns the release while
# probe/a100-hold-<id> exists; earlier chains that call destroy.sh then leave the instance running. FORCE=yes overrides.
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
for H in "$ROOT"/probe/a100-hold*-"$ID"; do   # any hold file (scale test, model trial, ...) keeps the instance
  if [ -e "$H" ] && [ "${FORCE:-}" != "yes" ]; then echo "HELD: $ID reserved by $(cat "$H") ($(basename "$H")); not destroyed"; exit 0; fi
done
# the CLI asks "Are you sure? [y/N]" on stdin; without the piped "y" it prints "Aborted." and still exits 0 (instance <instance> kept billing)
vastai destroy instance "$ID" -y 2>&1 | grep -v DEPRECATED
sleep 10
vastai show instances --raw 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); ids=[i["id"] for i in d]; print("instances left:", [(i["id"], i.get("actual_status")) for i in d]); sys.exit(1 if '"$ID"' in ids else 0)' && echo "destroyed $ID (verified)" || echo "WARNING: $ID still listed — re-run"
