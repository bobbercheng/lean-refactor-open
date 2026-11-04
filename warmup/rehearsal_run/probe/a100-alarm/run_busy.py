#!/usr/bin/env python3
"""The spend guard's BUSY_CHECK (operator 2026-10-30: ask before deleting unless the A100 is idle): reads the run's status from the GCS
bucket (gcs_status.py) and exits 0 = busy (a driver or an agent process alive), 1 = idle (a fresh status with neither alive),
2 = unknown (unreadable or older than --max-age seconds; the guard treats unknown as busy).
    python3 probe/a100-alarm/run_busy.py --label a100-p85 [--max-age 900]"""
import argparse, json, os, subprocess, sys

ap = argparse.ArgumentParser(); ap.add_argument("--label", required=True); ap.add_argument("--max-age", type=int, default=900); a = ap.parse_args()
try:
    r = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), "gcs_status.py"), "--label", a.label],
                       capture_output=True, text=True, timeout=150)
    st = json.loads(r.stdout.strip().splitlines()[-1])
except Exception:  # noqa: BLE001
    sys.exit(2)
if not st.get("ok") or st.get("age_s") is None or st["age_s"] > a.max_age:
    sys.exit(2)
sys.exit(0 if (st.get("driver") or 0) > 0 or (st.get("agents") or 0) > 0 else 1)
