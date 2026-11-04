#!/usr/bin/env bash
# Destroy the POC instance (stops billing; the instance disk and HF cache are lost). Requires CONFIRM=yes.
# Usage: CONFIRM=yes infra/vast/destroy.sh <instance_id>
# Exit codes (review 2026-10-28: callers rented a replacement while a "destroyed" instance was still listed): 0 = gone (verified),
# 1 = still listed after 3 attempts (the caller must NOT rent another one), 2 = HELD by a probe/a100-hold* file (FORCE=yes overrides).
set -eu
. "$(cd "$(dirname "$0")" && pwd)/common.sh"; require vastai python3
ID=${1:?instance id}
echo "would run: vastai destroy instance $ID"
[ "${CONFIRM:-}" = "yes" ] || { echo "(dry run: set CONFIRM=yes)"; exit 0; }
# hold (operator 2026-10-07: test the harness at 8-12 workers before releasing): a follow-up job owns the release while
# probe/a100-hold-<id> exists; earlier chains that call destroy.sh then leave the instance running. FORCE=yes overrides.
ROOT=$(cd "$(dirname "$0")/../.." && pwd)
for H in "$ROOT"/probe/a100-hold*-"$ID"; do   # any hold file (scale test, model trial, ...) keeps the instance
  if [ -e "$H" ] && [ "${FORCE:-}" != "yes" ]; then echo "HELD: $ID reserved by $(cat "$H") ($(basename "$H")); not destroyed"; exit 2; fi
done
listed() { vastai show instances --raw 2>/dev/null | python3 -c 'import json,sys; d=json.load(sys.stdin); ids=[i["id"] for i in d]; print("instances left:", [(i["id"], i.get("actual_status")) for i in d]); sys.exit(1 if '"$ID"' in ids else 0)'; }
for a in 1 2 3; do
  # the CLI asks "Are you sure? [y/N]" on stdin; without the piped "y" it prints "Aborted." and still exits 0 (instance 54533362 kept billing)
  vastai destroy instance "$ID" -y 2>&1 | grep -v DEPRECATED || true
  sleep "${DESTROY_WAIT_S:-10}"
  if listed; then echo "destroyed $ID (verified, attempt $a)"; exit 0; fi
  echo "WARNING: $ID still listed after attempt $a"
done
echo "DESTROY FAILED: $ID still listed after 3 attempts; do not rent a replacement (vastai destroy instance $ID -y by hand)"; exit 1
