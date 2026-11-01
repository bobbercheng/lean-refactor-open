# Sourced by every infra/vast script. Systemd user services do not get the login PATH: on 2026-10-07 the bridge service could
# not find vastai (fell back to a stale cached port) nor socat (bridge never listened) while the server was up. So: one PATH,
# and every script names the tools it needs and fails at once, loudly, when one is missing.
export PATH="$HOME/.local/bin:$HOME/miniconda3/bin:$HOME/.elan/bin:/usr/local/bin:/usr/bin:/bin:$PATH"
require() { local t miss=""; for t in "$@"; do command -v "$t" >/dev/null 2>&1 || miss="$miss $t"; done
  [ -z "$miss" ] || { echo "FATAL: missing tools:$miss (PATH=$PATH)" >&2; exit 127; }; }
