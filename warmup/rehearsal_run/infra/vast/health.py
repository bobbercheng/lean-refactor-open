#!/usr/bin/env python3
"""Continuous health check of a rented vast.ai A100 instance (operator 2026-10-07: "we also need a health check for vast instance
to identify any critical error as early as possible").

Every INTERVAL seconds it checks, from the outside in:
  vast     instance record: status running (pre-emption / stop / host error = CRITICAL), account balance and hours left
  ssh      direct SSH login, the only SSH path we use (operator 2026-10-07: "as long as direct connection is good, we are good";
           the vast proxy sshN.vast.ai was down at 20:36 while the direct address worked, so it is not checked at all)
  server   infra/vast/server_up.sh --bridge (vast -> TCP -> pinned-TLS API -> real completion -> local bridge)
  inside   one SSH call: vLLM process alive, 4 GPUs visible, nvidia-smi responsive, uncorrected ECC errors, temperature,
           /workspace free space, NEW error lines in vllm.log (Traceback, CUDA/NCCL errors, OOM, dead engine), and a stall
           (requests running but no generation and no log progress)
Output (probe/a100-health.log via the service):
  * every cycle one compact heartbeat line "[hh:mm:ss] ok ..." or "[hh:mm:ss] DEGRADED ...";
  * on every state change of a check: "CRITICAL <check>: ...", "WARN <check>: ..." or "RECOVERED <check>".
Transient failures (one missed SSH or server probe) are WARN; the same failure on CONSEC consecutive cycles is CRITICAL. Hard
faults (pre-emption, dead vLLM, lost GPU, ECC, new engine errors, stall) are CRITICAL at once. The watchdog only reports: acting
on a CRITICAL (re-rent, restart, release) is a decision taken with the evidence in hand. It exits by itself when the instance is
no longer listed (released).

Usage: infra/vast/health.py <instance_id> [--interval 60] [--no-bridge]     (run as a systemd user service: lra-health)
"""
from __future__ import annotations

import argparse, json, os, re, shutil, subprocess, sys, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
os.environ["PATH"] = ":".join(([os.environ["LRA_FAKE_VAST_BIN"]] if os.environ.get("LRA_FAKE_VAST_BIN") else []) +   # $0 dry run: the vastai shim first
                              [str(Path.home() / ".local/bin"), str(Path.home() / "miniconda3/bin"), "/usr/local/bin", "/usr/bin", "/bin",
                               os.environ.get("PATH", "")])
for tool in ("vastai", "ssh", "curl"):
    if not shutil.which(tool):
        sys.exit(f"FATAL: missing tool {tool}")
SSH_KEY = str(Path.home() / ".ssh/id_ed25519")
CONSEC = 3
ERR_RE = r"Traceback|CUDA error|NCCL (WARN|ERROR)|illegal memory|OutOfMemory|out of memory|EngineDead|EngineCore.*(died|failed)|Xid"

INSIDE = r'''
p=$(pgrep -f "vllm serve" >/dev/null && echo 1 || echo 0); echo "vllm=$p"
q=$(timeout 20 nvidia-smi --query-gpu=index,utilization.gpu,temperature.gpu,ecc.errors.uncorrected.volatile.total --format=csv,noheader,nounits 2>/dev/null); echo "smi_rc=$?"
echo "$q" | sed 's/^/gpu=/'
echo "disk_gb=$(df --output=avail -BG /workspace 2>/dev/null | tail -n 1 | tr -dc 0-9)"
L=/workspace/vllm.log
echo "log_age=$(( $(date +%s) - $(stat -c %Y $L 2>/dev/null || echo 0) ))"
echo "err_count=$(grep -acE 'ERR_RE' $L 2>/dev/null)"
echo "err_last=$(grep -aE 'ERR_RE' $L 2>/dev/null | tail -n 1 | cut -c1-160)"
echo "stats=$(grep -a 'Running:' $L 2>/dev/null | tail -n 1 | grep -oE 'generation throughput: [0-9.]+ tokens/s, Running: [0-9]+ reqs, Waiting: [0-9]+ reqs')"
'''.replace("ERR_RE", ERR_RE)


def sh(cmd: list[str], timeout: int) -> tuple[int, str]:
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
        # stdout only on success: vastai prints a DEPRECATED notice on stderr, and mixing it in broke the JSON parse (2026-10-07)
        return r.returncode, (r.stdout or "") if r.returncode == 0 else (r.stdout or "") + (r.stderr or "")
    except subprocess.TimeoutExpired:
        return 124, "timeout"


class Watch:
    def __init__(self, iid: str, bridge: bool = True):
        self.iid = iid; self.bridge = bridge
        self.state: dict[str, tuple[str, str]] = {}    # check -> (level, message) last reported
        self.fails: dict[str, int] = {}
        self.err_count: int | None = None
        self.stall = 0

    def report(self, check: str, level: str, msg: str = "") -> None:
        """level: ok | warn | critical. Prints only on a change of level (or of the critical message)."""
        prev = self.state.get(check, ("ok", ""))
        key = re.sub(r"\s*\(\d+x in a row\)", "", msg)   # the repeat counter must not make an unchanged alert look new (2026-10-08: CRITICAL every minute)
        if level == "ok":
            if prev[0] != "ok":
                log(f"RECOVERED {check}{': ' + msg if msg else ''}")
        elif (level, key) != (prev[0], re.sub(r"\s*\(\d+x in a row\)", "", prev[1])) and not (level == prev[0] == "warn"):
            log(f"{level.upper()} {check}: {msg}")
        self.state[check] = (level, msg if level != "ok" else "")

    def soft(self, check: str, ok: bool, msg: str) -> None:
        """Transient-tolerant check: WARN on the first failure, CRITICAL after CONSEC consecutive ones."""
        self.fails[check] = 0 if ok else self.fails.get(check, 0) + 1
        n = self.fails[check]
        self.report(check, "ok" if ok else ("critical" if n >= CONSEC else "warn"), "" if ok else f"{msg} ({n}x in a row)")   # a recovery line must not repeat the failure text

    def cycle(self) -> bool:
        rc, out = sh(["vastai", "show", "instances", "--raw"], 60)
        try:
            rows = {str(d["id"]): d for d in json.loads(out)}
        except Exception:  # noqa: BLE001
            self.soft("vast", False, f"vastai API unreadable (rc={rc}): {out.strip()[-120:]}")
            log("DEGRADED vast | instance record unreadable this cycle")
            return True
        d = rows.get(self.iid)
        if d is None:
            log(f"instance {self.iid} no longer listed (released); health check exits")
            return False
        st, msg = d.get("actual_status"), (d.get("status_msg") or "")[:100]
        if st != "running" or d.get("intended_status") != "running":
            self.report("vast", "critical", f"status={st} intended={d.get('intended_status')} msg={msg!r} (pre-empted / stopped?)")
        else:
            self.soft("vast", True, "")
        ip = d.get("public_ipaddr"); ports = d.get("ports") or {}
        sshp = (ports.get("22/tcp") or [{}])[0].get("HostPort")
        rc, u = sh(["vastai", "show", "user", "--raw"], 60)
        try:
            bal = float(json.loads(u).get("credit") or 0)   # the money is in credit; balance stays 0
            dph = float(d.get("dph_total") or 0)
            hrs = bal / dph if dph else 99
            self.report("balance", "critical" if hrs < 1 else ("warn" if hrs < 3 else "ok"), f"${bal:.2f} left = {hrs:.1f} h at ${dph:.3f}/h")
        except Exception:  # noqa: BLE001
            bal, hrs = float("nan"), float("nan")
        # SSH: direct (critical path) and the vast proxy (operator convenience only)
        ssh = ["ssh", "-i", SSH_KEY, "-o", "BatchMode=yes", "-o", "ConnectTimeout=15", "-o", "StrictHostKeyChecking=accept-new", "-p", str(sshp), f"root@{ip}"]
        rc, inside = sh(ssh + [INSIDE], 60)
        self.soft("ssh", rc == 0 and "vllm=" in inside, f"direct ssh {ip}:{sshp} failed (rc={rc})")
        # the real serving path
        rc, v = sh([str(HERE / "server_up.sh"), self.iid] + (["--bridge"] if self.bridge else []), 200)   # --no-bridge: the on-instance package never uses the GB10 bridge
        self.soft("server", rc == 0, v.strip().splitlines()[-1] if v.strip() else f"server_up rc={rc}")
        # inside the box
        kv = {}
        gpus = []
        for line in inside.splitlines():
            k, _, val = line.partition("=")
            if k == "gpu":
                gpus.append([x.strip() for x in val.split(",")])
            elif k in ("vllm", "smi_rc", "disk_gb", "log_age", "err_count", "err_last", "stats"):
                kv[k] = val.strip()
        if kv:
            self.report("vllm-process", "ok" if kv.get("vllm") == "1" else "critical", "vLLM process not running")
            if kv.get("smi_rc") != "0":
                self.report("gpus", "critical", f"nvidia-smi failed/hung (rc={kv.get('smi_rc')})")
            else:
                bad = [g for g in gpus if len(g) >= 4 and g[3] not in ("0", "[N/A]", "N/A", "")]
                hot = [g for g in gpus if len(g) >= 3 and g[2].isdigit() and int(g[2]) >= 87]
                if len(gpus) != 4:
                    self.report("gpus", "critical", f"{len(gpus)} GPUs visible, expected 4")
                elif bad:
                    self.report("gpus", "critical", f"uncorrected ECC errors on GPU {[g[0] for g in bad]}")
                elif hot:
                    self.report("gpus", "warn", f"hot GPUs {[(g[0], g[2] + 'C') for g in hot]}")
                else:
                    self.report("gpus", "ok")
            disk = int(kv.get("disk_gb") or 0)
            self.report("disk", "critical" if disk < 5 else ("warn" if disk < 15 else "ok"), f"/workspace {disk} GB free")
            n = int(kv.get("err_count") or 0)
            if self.err_count is not None and n > self.err_count:
                self.report("engine-errors", "critical", f"{n - self.err_count} new error line(s) in vllm.log, last: {kv.get('err_last')}")
            elif self.err_count is not None:
                self.report("engine-errors", "ok")
            self.err_count = n
            m = re.search(r"throughput: ([0-9.]+) tokens/s, Running: (\d+)", kv.get("stats", ""))
            running = int(m.group(2)) if m else 0
            age = int(kv.get("log_age") or 0)
            stalled = running > 0 and (float(m.group(1)) == 0.0 or age > 180)
            self.stall = self.stall + 1 if stalled else 0
            self.report("stall", "critical" if self.stall >= CONSEC else "ok",
                        f"{running} requests running but no generation / no log progress for {self.stall} cycles (log age {age}s)")
        worst = [c for c, (lv, _) in self.state.items() if lv != "ok"]
        tp = re.search(r"throughput: ([0-9.]+) tokens/s, Running: (\d+) reqs, Waiting: (\d+)", kv.get("stats", "") if kv else "")
        log(("ok" if not worst else "DEGRADED " + ",".join(worst)) +
            f" | {len(gpus)} GPU util {'/'.join(g[1] for g in gpus if len(g) > 1)}%"
            + (f" | {tp.group(1)} tok/s run {tp.group(2)} wait {tp.group(3)}" if tp else "")
            + f" | ${bal:.2f} ({hrs:.1f} h)")
        return True


def log(msg: str) -> None:
    print(f"[{time.strftime('%H:%M:%S', time.gmtime())}] {msg}", flush=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("instance_id")
    ap.add_argument("--interval", type=int, default=60)
    ap.add_argument("--no-bridge", action="store_true", help="server check without the local TLS bridge (rehearsal: the data path is on the instance)")
    a = ap.parse_args()
    w = Watch(a.instance_id, bridge=not a.no_bridge)
    log(f"health check for instance {a.instance_id} every {a.interval}s")
    while True:
        t0 = time.time()
        try:
            if not w.cycle():
                return
        except Exception as e:  # noqa: BLE001  -- the watchdog itself must never die on a bad read
            log(f"WARN health: check cycle failed: {type(e).__name__}: {str(e)[:160]}")
        time.sleep(max(5, a.interval - (time.time() - t0)))


if __name__ == "__main__":
    main()
