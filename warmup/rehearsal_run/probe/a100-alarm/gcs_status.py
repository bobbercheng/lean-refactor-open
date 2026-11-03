#!/usr/bin/env python3
"""Read the A100 run's status from our GCS bucket (operator 2026-10-30: the A100 must sync its status to the bucket so an interruption or
a dead tunnel never leaves us blind). The host writes /workspace/lra/reh/status.json every 120 s; its sidecar uploads it to
gs://<bucket>/<label>/snap/reh/status.json every 120 s. Prints one JSON line: the status plus its age in seconds.
    python3 probe/a100-alarm/gcs_status.py [--label a100-pkg1]"""
import argparse, json, os, subprocess, time

ap = argparse.ArgumentParser(); ap.add_argument("--label", default="a100-pkg1"); a = ap.parse_args()
G = os.path.expanduser("~/google-cloud-sdk/bin/gcloud") if os.path.exists(os.path.expanduser("~/google-cloud-sdk/bin/gcloud")) else "gcloud"
env = dict(os.environ, CLOUDSDK_CONFIG=os.path.expanduser("~/.config/vexorium/gcloud-sa"), CLOUDSDK_CORE_DISABLE_PROMPTS="1")
url = f"gs://<bucket>/{a.label}/snap/lra/reh/status.json"   # the sidecar is rooted at /workspace
try:
    r = subprocess.run([G, "storage", "cat", url], capture_output=True, text=True, timeout=90, env=env)
    st = json.loads(r.stdout) if r.returncode == 0 and r.stdout.strip() else None
except Exception as e:  # noqa: BLE001
    st, r = None, None
if st is None:
    print(json.dumps({"ok": False, "url": url, "error": (r.stderr.strip()[-200:] if r is not None else "gcloud failed")}))
else:
    print(json.dumps({"ok": True, "age_s": int(time.time()) - int(st.get("epoch") or 0), **st}))
