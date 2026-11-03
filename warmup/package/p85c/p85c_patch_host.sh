#!/usr/bin/env bash
# ON a replacement box: the p85c agent.py patch only (--open-card), idempotent; from p85c_restart_host.sh step (0).
set -u
W=/workspace; L=$W/p85c_patch.log; log() { echo "[$(date -u +%H:%M:%S)] $*" | tee -a $L; }
cd $W/lra || exit 1
# (0) patch agent.py (idempotent)
python3 - <<'PY' || { log "agent.py patch FAILED: nothing stopped"; exit 1; }
import ast, pathlib
p = pathlib.Path("harness/agent.py"); s = p.read_text()
if "--open-card" not in s:
    a = '    ap.add_argument("--brief-dir", default=None,'
    b = '    if args.brief != "none":\n'
    assert s.count(a) == 1 and s.count(b) == 1, "anchors"
    s = s.replace(a, '    ap.add_argument("--open-card", default=None, help="2026-10-31 p85b: append this generic card (the same for every row) to the opening; honoured under --open-package")\n' + a)
    s = s.replace(b, '    if getattr(args, "open_card", None):   # 2026-10-31 p85b (operator: close the gap): one generic card, the same for every row\n'
                     '        _oc = Path(args.open_card)\n'
                     '        if _oc.exists():\n'
                     '            msgs[0]["content"] += "\\n\\n" + _oc.read_text()\n'
                     '            print(f"{name[:18]:18s} open card: {_oc.name}", flush=True)\n' + b)
    ast.parse(s); p.with_suffix(".py.before-p85c").write_text(pathlib.Path("harness/agent.py").read_text()); p.write_text(s)
print("agent.py patched")
PY
python3 harness/agent.py --help 2>/dev/null | grep -q -- "--open-card" || { log "patched agent.py does not show --open-card: restore and stop"; cp harness/agent.py.before-p85c harness/agent.py; exit 1; }
log "agent.py patched (--open-card)"
