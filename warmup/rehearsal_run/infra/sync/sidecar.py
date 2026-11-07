#!/usr/bin/env python3
"""Durable-state sidecar for a run (operator 2026-10-09: GCS bucket, reliable persistence; recovery must never need the old instance).

The run writes only to local disk. This process pushes, and nothing ever has to reach into the machine:
  write-through  every new line of the watched verified.jsonl files (each new best proof) is uploaded within ~10 s as its own immutable
                 object  gs://<bucket>/<label>/outbox/<file>/<byte offset>.jsonl;
  write-behind   every --snapshot-every seconds the listed paths are synced incrementally to  gs://<bucket>/<label>/snap/<path>
                 (state, notes, ledgers, trajectories, logs). Nothing is ever deleted remotely.
It keeps running through network errors (it retries next cycle) and never blocks the run. SIGTERM triggers one last snapshot.
Credentials: the bucket-only service-account key (~/.config/vexorium/gcs_sync_key.json), activated in its own gcloud profile directory
(~/.config/vexorium/gcloud-sa), so the user's own gcloud logins are never touched.

    python3 infra/sync/sidecar.py --label a100-80-dev --watch 'probe/runs/fresh-a100-p*/verified.jsonl' \
        --paths harness/work_fresh-a100 probe/runs/fresh-a100-p5 probe/runs/fresh-a100-p6 accounting
"""
from __future__ import annotations

import argparse, glob, os, signal, subprocess, sys, time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
SA_CONFIG = os.path.expanduser("~/.config/vexorium/gcloud-sa")
GCLOUD = os.path.expanduser("~/google-cloud-sdk/bin/gcloud") if os.path.exists(os.path.expanduser("~/google-cloud-sdk/bin/gcloud")) else "gcloud"
stop = False


def log(msg: str) -> None:
    print(time.strftime("[%Y-%m-%dT%H:%M:%SZ] ", time.gmtime()) + msg, flush=True)


def gcloud(*args: str, timeout: int = 600) -> subprocess.CompletedProcess:
    env = dict(os.environ, CLOUDSDK_CONFIG=SA_CONFIG, CLOUDSDK_CORE_DISABLE_PROMPTS="1")
    return subprocess.run([GCLOUD, *args], capture_output=True, text=True, timeout=timeout, env=env)


def activate(key: str) -> None:
    os.makedirs(SA_CONFIG, mode=0o700, exist_ok=True)
    r = gcloud("auth", "activate-service-account", f"--key-file={key}")
    if r.returncode != 0:
        sys.exit(f"cannot activate the service account: {r.stderr.strip()[:300]}")


def write_through(watch: list[str], bucket: str, label: str, offsets: dict) -> int:
    sent = 0
    for pat in watch:
        for f in sorted(glob.glob(os.path.join(ROOT, pat))):
            try:
                size = os.path.getsize(f)
            except OSError:
                continue
            off = offsets.get(f, 0)
            if size <= off:
                continue
            with open(f, "rb") as fh:
                fh.seek(off); data = fh.read(size - off)
            data = data[: data.rfind(b"\n") + 1]   # whole lines only; a line still being written waits for the next cycle
            if not data:
                continue
            tmp = os.path.join(SA_CONFIG, "outbox.tmp")
            with open(tmp, "wb") as t:
                t.write(data)
            rel = os.path.relpath(f, ROOT).replace("/", "__")
            r = gcloud("storage", "cp", tmp, f"{bucket}/{label}/outbox/{rel}/{off:012d}.jsonl", timeout=120)
            if r.returncode == 0:
                offsets[f] = off + len(data); sent += data.count(b"\n")
            else:
                log(f"write-through failed for {rel} (will retry): {r.stderr.strip()[:160]}")
    return sent


def snapshot(paths: list[str], bucket: str, label: str) -> int:
    bad = 0
    for p in paths:
        src = os.path.join(ROOT, p)
        if not os.path.exists(src):
            continue
        dst = f"{bucket}/{label}/snap/{p.rstrip('/')}"
        r = (gcloud("storage", "rsync", "--recursive", src, dst, timeout=1800) if os.path.isdir(src)
             else gcloud("storage", "cp", src, dst, timeout=600))
        if r.returncode != 0:
            bad += 1; log(f"snapshot of {p} failed (will retry): {r.stderr.strip()[:160]}")
    return bad


def main() -> int:
    global stop
    ap = argparse.ArgumentParser()
    ap.add_argument("--label", required=True)
    ap.add_argument("--bucket", default="gs://<bucket>")
    ap.add_argument("--key", default=os.path.expanduser("~/.config/vexorium/gcs_sync_key.json"))
    ap.add_argument("--watch", nargs="*", default=[])
    ap.add_argument("--paths", nargs="*", default=[])
    ap.add_argument("--watch-every", type=int, default=10)
    ap.add_argument("--snapshot-every", type=int, default=120)
    a = ap.parse_args()
    activate(a.key)
    signal.signal(signal.SIGTERM, lambda *_: globals().__setitem__("stop", True))
    offsets: dict = {}
    last_snap = 0.0
    log(f"sidecar up: {a.bucket}/{a.label}; watch {a.watch}; paths {a.paths}")
    while not stop:
        try:
            n = write_through(a.watch, a.bucket, a.label, offsets)
            if n:
                log(f"write-through: {n} new verified record(s)")
            if time.time() - last_snap >= a.snapshot_every:
                t = time.time(); bad = snapshot(a.paths, a.bucket, a.label); last_snap = time.time()
                log(f"snapshot {'ok' if not bad else f'{bad} path(s) failed'} in {last_snap - t:.0f}s")
        except Exception as e:  # noqa: BLE001  never die: the next cycle retries
            log(f"cycle error: {type(e).__name__}: {str(e)[:200]}")
        for _ in range(a.watch_every):
            if stop:
                break
            time.sleep(1)
    write_through(a.watch, a.bucket, a.label, offsets); bad = snapshot(a.paths, a.bucket, a.label)
    log(f"final flush {'ok' if not bad else f'{bad} path(s) failed'}; sidecar down")
    return 0


if __name__ == "__main__":
    sys.exit(main())
