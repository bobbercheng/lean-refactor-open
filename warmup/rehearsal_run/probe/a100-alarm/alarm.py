#!/usr/bin/env python3
"""Critical-error alarm for an A100 package run (operator 2026-10-30 ~05:10 UTC: "setup an alarm for any critical error from the harness,
like the last rehearsal, so we catch it earlier"; the last rehearsal hid 158 of 158 failing calls of three tools for hours).

Every CHECK_S (120 s) it scans the GB10's pulled copy of the run (the lra-a100-watch unit rsyncs OUT/ and the session run dirs every 5 min):
  session logs out/logs/*.log   TOOL ERROR (any), Traceback, "start proof does not compile", api errors / connect retries, junk bursts
  run dirs runs/*/turns.jsonl    api_error statuses
  watch.log / spend guard log    their CRITICAL / destroy lines
Every LIVE_S (300 s) one bounded SSH call to the host (tunnel file probe/a100-tunnels/<id>):
  driver.log new lines           Traceback, WARNING (session tool errors), "done (rc N)" with N != 0
  processes                      driver / agents / vLLM alive; all GPUs at 0% while agents run (twice); /workspace disk >= 90%;
                                 3 failed SSH checks in a row = host or tunnel unreachable
Each alarm: one line "[ts] CRITICAL|WARN key: detail" appended to <reh>/ALARM.log and printed; CRITICAL also pushed to the private ntfy topic
(probe/a100-ntfy-topic). A key re-alerts at most every REALERT_S (30 min), with its updated count. No secrets in any message.
  python3 probe/a100-alarm/alarm.py --reh probe/a100-reh-pkg1 --id 58331591 [--once] [--no-live] [--no-push]"""
from __future__ import annotations

import argparse, datetime as dt, json, re, subprocess, time, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CHECK_S, LIVE_S, REALERT_S = 120, 300, 1800
PATS = [  # (key prefix, regex on a session-log line, level, threshold of new hits per check to alarm)
    ("tool-error", re.compile(r"TOOL ERROR (\w+): (\w+)"), "CRITICAL", 1),
    ("crash", re.compile(r"^Traceback|Error: .*Traceback|^\w*Error: "), "CRITICAL", 1),
    ("start-proof", re.compile(r"start proof does not compile"), "CRITICAL", 1),
    ("connect-retry", re.compile(r"turn \d+: (?!no-thinking|budget reclaim|junk).*(connect|refused|timed out|rate.?limit|\b429\b|\b5\d\d\b|server error|transport)", re.I), "CRITICAL", 5),
    ("junk", re.compile(r"turn \d+: junk "), "WARN", 10),
]


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


class Alarm:
    def __init__(self, reh: Path, iid: str, push: bool, live: bool, run_dir: str = "/workspace/lra-run-pkg1", out_dir: str = "/workspace/out-pkg1"):
        self.reh, self.iid, self.push_on, self.live_on = reh, iid, push, live
        self.run_dir, self.out_dir = run_dir, out_dir
        self.state_f = reh / "alarm_state.json"
        self.st = json.loads(self.state_f.read_text()) if self.state_f.exists() else {"off": {}, "last": {}, "count": {}, "drv_lines": 0,
                                                                                         "ssh_fail": 0, "gpu_idle": 0, "agents0": 0}
        topic_f = ROOT / "probe/a100-ntfy-topic"
        self.topic = topic_f.read_text().strip() if topic_f.exists() else None

    def save(self):
        tmp = self.state_f.with_suffix(".tmp"); tmp.write_text(json.dumps(self.st, indent=1)); tmp.replace(self.state_f)

    def fire(self, level: str, key: str, detail: str, n: int = 1):
        self.st["count"][key] = self.st["count"].get(key, 0) + n
        last = self.st["last"].get(key, 0)
        if time.time() - last < REALERT_S:
            return
        self.st["last"][key] = time.time()
        line = f"[{now()}] {level} {key}: {detail} (total {self.st['count'][key]})"
        with (self.reh / "ALARM.log").open("a") as f:
            f.write(line + "\n")
        print(line, flush=True)
        if level == "CRITICAL" and self.push_on and self.topic:
            try:
                req = urllib.request.Request(f"https://ntfy.sh/{self.topic}", data=f"A100 {key}: {detail}"[:300].encode(),
                                             headers={"Title": "A100 harness alarm", "Priority": "high", "Tags": "rotating_light"})
                urllib.request.urlopen(req, timeout=20).read()
            except Exception as e:  # noqa: BLE001
                print(f"[{now()}] push failed: {type(e).__name__}", flush=True)

    # ------------------------------------------------------------------ local scans of the pulled copy
    def scan_logs(self):
        for f in sorted((self.reh / "out/logs").glob("*.log")):
            off = self.st["off"].get(str(f), 0)
            try:
                size = f.stat().st_size
                if size < off:
                    off = 0
                with f.open("rb") as fh:
                    fh.seek(off); new = fh.read().decode("utf-8", "replace")
            except OSError:
                continue
            self.st["off"][str(f)] = off + len(new.encode("utf-8"))
            hits: dict = {}
            for ln in new.splitlines():
                for key, pat, level, thr in PATS:
                    m = pat.search(ln)
                    if m:
                        k = f"{key}:{m.group(1)}:{m.group(2)}" if key == "tool-error" else key
                        hits.setdefault((k, level, thr), []).append(ln.strip()[:160])
            for (k, level, thr), lines in hits.items():
                # 2026-10-30 06:14 UTC: a FileNotFoundError on a path the MODEL named (lean_check on a file it never wrote) is a model
                # mistake the session recovers from, not a dead tool: WARN, and CRITICAL only from 5 in one check
                # 2026-10-30 17:12: a tool call MISSING a required argument (write_file without "path") raises KeyError: a model mistake too
                if k.endswith(":KeyError") and all(re.search(r"KeyError: '(path|content|code|name|command)'", x) for x in lines):
                    level, thr = ("CRITICAL", 5) if len(lines) >= 5 else ("WARN", 1)
                if k.endswith(":FileNotFoundError") and all("/work/" in x for x in lines):
                    level, thr = ("CRITICAL", 5) if len(lines) >= 5 else ("WARN", 1)
                if len(lines) >= thr:
                    self.fire(level, k, f"{len(lines)} new in {f.name}; e.g. {lines[0]}", len(lines))

    def scan_turns(self):
        n = 0
        for f in (self.reh / "runs").glob("*/turns.jsonl"):
            off = self.st["off"].get(str(f), 0)
            try:
                with f.open("rb") as fh:
                    fh.seek(off); new = fh.read().decode("utf-8", "replace")
            except OSError:
                continue
            self.st["off"][str(f)] = off + len(new.encode("utf-8"))
            n += new.count('"api_error')
        if n >= 3:
            self.fire("CRITICAL", "api-error", f"{n} model API errors in session turn logs since the last check", n)

    def scan_side_logs(self):
        for name, pat in (("watch.log", re.compile(r"CRITICAL|destroy|gone|lost", re.I)),):
            f = self.reh / name
            off = self.st["off"].get(str(f), 0)
            if not f.exists():
                continue
            with f.open("rb") as fh:
                fh.seek(off); new = fh.read().decode("utf-8", "replace")
            self.st["off"][str(f)] = off + len(new.encode("utf-8"))
            for ln in new.splitlines():
                if pat.search(ln):
                    self.fire("CRITICAL", f"watch:{name}", ln.strip()[:200])
        # stale pulls: the watcher stopped pulling (local scans would go blind)
        f = self.reh / "watch.log"
        if f.exists() and time.time() - f.stat().st_mtime > 1200:
            self.fire("CRITICAL", "watch-stale", f"watch.log not updated for {int((time.time() - f.stat().st_mtime) / 60)} min: pulls stopped")

    # ------------------------------------------------------------------ live host check
    def live(self):
        tf = ROOT / f"probe/a100-tunnels/{self.iid}"
        try:
            host, port = tf.read_text().split()[:2]
        except Exception:  # noqa: BLE001
            self.fire("CRITICAL", "tunnel-file", f"no tunnel file {tf.name}"); return
        rc = json.loads((self.reh / "rental.json").read_text()) if (self.reh / "rental.json").exists() else {}
        run_dir = rc.get("run_dir") or self.run_dir; out = rc.get("out") or self.out_dir
        skip = self.st["drv_lines"]
        cmd = (f"L={run_dir}/driver.log; echo DRV $(pgrep -c -f '[o]pen_package.py run'); echo AG $(pgrep -c -f '[h]arness/agent.py'); "
               f"echo VLLM $(pgrep -c -f '[v]llm serve'); echo GPU $(nvidia-smi --query-gpu=utilization.gpu --format=csv,noheader,nounits | tr '\\n' ' '); "
               f"echo DISK $(df --output=pcent /workspace | tail -1 | tr -dc 0-9); echo SUM $(test -f {out}/summary.json && echo 1 || echo 0); "
               f"echo AGDONE $(test -f {out}/agent_stage.json && echo 1 || echo 0); echo LINES $(wc -l < $L); "
               f"tail -n +{skip + 1} $L | grep -E 'Traceback|WARNING|done \\(rc [1-9]|Error' | head -20 | sed 's/^/DL /'")
        try:
            p = subprocess.run(["timeout", "90", "ssh", "-i", str(Path.home() / ".ssh/id_ed25519"), "-o", "BatchMode=yes", "-o", "ConnectTimeout=20",
                                "-o", "StrictHostKeyChecking=no", "-o", "UserKnownHostsFile=/dev/null", "-o", "LogLevel=ERROR", "-p", port,
                                f"root@{host}", cmd], capture_output=True, text=True, timeout=120)
            out_s = p.stdout
        except Exception:  # noqa: BLE001
            out_s = ""
        kv = {}
        for ln in out_s.splitlines():
            a, _, b = ln.partition(" ")
            if a == "DL":
                self.fire("CRITICAL" if ("Traceback" in b or "rc " in b or "Error" in b) else "WARN", "driver-log", b[:200])
            else:
                kv[a] = b.strip()
        if "DRV" not in kv:
            self.st["ssh_fail"] += 1
            # 2026-10-30 08:14 UTC: the bore tunnel died while the run went on; vast's API still tells status and GPU load (no SSH)
            vs = {}
            try:
                q = subprocess.run(["timeout", "60", "vastai", "show", "instance", self.iid, "--raw"], capture_output=True, text=True, timeout=90,
                                   env={k: v for k, v in __import__("os").environ.items() if k != "LRA_FAKE_VAST_BIN"})
                d = json.loads(q.stdout)
                vs = {"status": d.get("actual_status"), "intended": d.get("intended_status"), "bid": d.get("dph_base"),
                      "gpu": round(float(d.get("gpu_util") or 0), 1)}
            except Exception:  # noqa: BLE001
                vs = {"status": "?", "gpu": None}
            self.st["vast"] = vs | {"t": now()}
            if vs.get("status") not in ("running", "?"):
                # 2026-10-30 22:28 UTC (operator: "the monitor script has a bug to catch up outbid accident"): an interruptible instance that
                # vast lists as exited / stopped / offline with intended_status "stopped" was OUTBID: the container is stopped and NOTHING runs
                # (vast's gpu_util is the last reading, the driver log on the disk is only frozen). The old code went on to "ssh-down-run-ok"
                # and "the run keeps going on its own", which is wrong here: say OUTBID, name the ladder's state, and stop the check.
                outbid = vs.get("intended") == "stopped"
                lad = ""
                try:
                    bo = [x for x in (ROOT / "probe/a100-bid.out").read_text(errors="replace").splitlines() if x.strip()]
                    lad = bo[-1][:160] if bo else ""
                except OSError:
                    pass
                if outbid:
                    self.fire("CRITICAL", "OUTBID", f"instance {self.iid} stopped by vast (status {vs.get('status')}, intended stopped): OUTBID; the run is "
                              f"PAUSED (no GPU, no sessions) until the bid ladder wins; our bid ${vs.get('bid')}; ladder: {lad}")
                else:
                    self.fire("CRITICAL", "instance-not-running", f"vast reports {vs.get('status')} (intended {vs.get('intended')}; ssh also failing): "
                              f"the run is NOT running")
                return
            # 2026-10-30: when SSH fails, read the run's driver log straight off the disk with `vastai copy` (the host's rsync daemon: no SSH,
            # no container network). The 12:31 restart was unneeded: the tunnel had only moved ports and its ntfy announcement was lost while
            # the run was healthy. So a restart is called for ONLY when the driver log has stopped changing for 30 min before summary.json.
            disk = {}
            try:
                tmpd = self.reh / "diskcheck"; tmpd.mkdir(exist_ok=True)
                env = {k: v for k, v in __import__("os").environ.items() if k != "LRA_FAKE_VAST_BIN"}
                subprocess.run(["timeout", "180", "vastai", "copy", f"C.{self.iid}:{self.run_dir}/driver.log", f"local:{tmpd}/"],
                               capture_output=True, text=True, timeout=200, env=env)
                subprocess.run(["timeout", "120", "vastai", "copy", f"C.{self.iid}:/workspace/lra/reh/status.json", f"local:{tmpd}/"],
                               capture_output=True, text=True, timeout=140, env=env)
                dl = tmpd / "driver.log"
                if dl.exists():
                    import re as _re
                    txt = dl.read_text(errors="replace")
                    stamps = _re.findall(r"^\[(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)Z?\]", txt, _re.M)
                    last = stamps[-1] if stamps else None
                    import datetime as _dt
                    age = int(time.time() - _dt.datetime.strptime(last, "%Y-%m-%dT%H:%M:%S").replace(tzinfo=_dt.timezone.utc).timestamp()) if last else None
                    done = len(_re.findall(r"session \d+ done", txt))
                    mean = (_re.findall(r"mean ([0-9.]+)", txt) or [None])[-1]
                    disk = {"driver_log_age_s": age, "sessions_done": done, "mean": mean, "last_line": last}
                    st_f = tmpd / "status.json"
                    if st_f.exists():
                        try:
                            disk["status_age_s"] = int(time.time()) - int(json.loads(st_f.read_text()).get("epoch") or 0)
                        except Exception:  # noqa: BLE001
                            pass
            except Exception as e:  # noqa: BLE001
                disk = {"error": f"{type(e).__name__}: {str(e)[:120]}"}
            self.st["disk"] = disk | {"t": now()}
            age = disk.get("driver_log_age_s")
            if age is not None and age > 1800 and not disk.get("summary"):
                self.fire("CRITICAL", "driver-log-stale", f"driver log on the disk unchanged for {age // 60} min ({disk.get('sessions_done')} sessions "
                          f"done, mean {disk.get('mean')}): the run looks stopped; restart rule applies (operator runs the vast restart)")
            elif age is not None:
                self.fire("WARN", "ssh-down-run-ok", f"SSH down but the run is alive on the disk: driver log {age // 60} min old, "
                          f"{disk.get('sessions_done')} sessions done, mean {disk.get('mean')}: no restart")
            if self.st["ssh_fail"] >= 3:
                self.fire("CRITICAL", "host-unreachable", f"{self.st['ssh_fail']} live checks in a row failed over SSH; vast: {vs.get('status')}, "
                          f"GPU {vs.get('gpu')}% (the run keeps going on its own; the tunnel needs to come back before the final pull)")
            return
        self.st["ssh_fail"] = 0
        try:
            self.st["drv_lines"] = int(kv.get("LINES") or skip)
        except ValueError:
            pass
        drv, ag, vl = int(kv.get("DRV") or 0), int(kv.get("AG") or 0), int(kv.get("VLLM") or 0)
        done = kv.get("SUM") == "1"
        if not done and drv == 0:
            self.fire("CRITICAL", "driver-dead", "open_package.py run is not running and summary.json is missing")
        if vl == 0 and not done:
            self.fire("CRITICAL", "vllm-down", "no vLLM server process")
        agent_stage = kv.get("AGDONE") != "1"
        self.st["agents0"] = self.st["agents0"] + 1 if (drv and agent_stage and ag == 0) else 0
        if self.st["agents0"] >= 2:
            self.fire("CRITICAL", "agents-zero", "driver alive in the agent stage but no agent process for 2 checks")
        gpus = [int(x) for x in (kv.get("GPU") or "").split() if x.isdigit()]
        self.st["gpu_idle"] = self.st["gpu_idle"] + 1 if (ag > 0 and gpus and max(gpus) == 0) else 0
        if self.st["gpu_idle"] >= 2:
            self.fire("CRITICAL", "gpu-idle", f"all GPUs at 0% with {ag} agents running (2 checks): model server stuck?")
        disk = int(kv.get("DISK") or 0)
        if disk >= 90:
            self.fire("CRITICAL", "disk", f"/workspace {disk}% full")

    def loop(self, once: bool):
        last_live = 0.0
        while True:
            for fn in (self.scan_logs, self.scan_turns, self.scan_side_logs):
                try:
                    fn()
                except Exception as e:  # noqa: BLE001
                    self.fire("WARN", "alarm-self", f"{fn.__name__}: {type(e).__name__}: {str(e)[:120]}")
            if self.live_on and time.time() - last_live >= LIVE_S:
                try:
                    self.live()
                except Exception as e:  # noqa: BLE001
                    self.fire("WARN", "alarm-self", f"live: {type(e).__name__}: {str(e)[:120]}")
                last_live = time.time()
            self.save()
            if once:
                return
            time.sleep(CHECK_S)


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--reh", required=True); ap.add_argument("--id", required=True)
    ap.add_argument("--run-dir", default="/workspace/lra-run-pkg1"); ap.add_argument("--out-dir", default="/workspace/out-pkg1")
    ap.add_argument("--once", action="store_true"); ap.add_argument("--no-live", action="store_true"); ap.add_argument("--no-push", action="store_true")
    a = ap.parse_args()
    reh = Path(a.reh) if Path(a.reh).is_absolute() else ROOT / a.reh
    print(f"[{now()}] alarm armed on {reh.name} (instance {a.id}; push {'on' if not a.no_push else 'off'}; live {'on' if not a.no_live else 'off'})", flush=True)
    Alarm(reh, a.id, not a.no_push, not a.no_live, a.run_dir, a.out_dir).loop(a.once)
