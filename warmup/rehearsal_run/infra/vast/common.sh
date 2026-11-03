# Sourced by every infra/vast script. Systemd user services do not get the login PATH: on 2026-10-07 the bridge service could
# not find vastai (fell back to a stale cached port) nor socat (bridge never listened) while the server was up. So: one PATH,
# and every script names the tools it needs and fails at once, loudly, when one is missing.
export PATH="$HOME/.local/bin:$HOME/miniconda3/bin:$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin:$PATH"
# $0 dry runs (probe/a100/dry_run.sh, 2026-10-28): LRA_FAKE_VAST_BIN holds a `vastai` shim (probe/a100/fake_vastai.py) that answers from
# canned state; it goes FIRST so no script can reach the real CLI. Exported so every unit started with -E LRA_FAKE_VAST_BIN inherits it.
[ -n "${LRA_FAKE_VAST_BIN:-}" ] && export PATH="$LRA_FAKE_VAST_BIN:$PATH"
require() { local t miss=""; for t in "$@"; do command -v "$t" >/dev/null 2>&1 || miss="$miss $t"; done
  [ -z "$miss" ] || { echo "FATAL: missing tools:$miss (PATH=$PATH)" >&2; exit 127; }; }
# ONE bid cap (review 2026-10-28: bid_ladder 2.00, regain 2.75 and sentry/provision 3.17 disagreed). BID_CAP in the environment
# overrides it everywhere; the rehearsal sets it from the budget (infra/vast/rehearsal.sh).
BID_CAP_DEFAULT=${BID_CAP:-2.00}
# unit names: a dry run adds a suffix (LRA_UNIT_SUFFIX) so it never stops or replaces a live rental's units
U=${LRA_UNIT_SUFFIX:-}
# KEPT marker (review 2026-10-28, finding 1): every exit that leaves an instance billing "for the operator" writes probe/a100-kept-<id>;
# infra/vast/spend_guard.sh destroys a kept instance after KEPT_GRACE_MIN unless probe/a100-ack-<id> exists (the operator took it over).
kept() {   # instance id, reason
  local root; root=$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)
  printf '%s %s\n' "$(date -u -Is)" "$2" >> "$root/probe/a100-kept-$1"
  echo "KEPT $1: $2 (marker probe/a100-kept-$1; spend_guard destroys it after ${KEPT_GRACE_MIN:-45} min unless probe/a100-ack-$1 exists)"
}
