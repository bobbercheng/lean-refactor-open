#!/usr/bin/env python3
"""postfast driver (post-hoc measurement, 2026-11-05; not what produced any upload).
POST-HOC (2026-11-05) v7/specnext copy: adds only --next-ops (default off; off = the base driver exactly).

Open run 3's seven post-step passes as they were run (passes 1-2 `--ops v3`, 3-4 `--ops v4`, 5 `--ops all --long --long-seconds 6515
--row-seconds 6515`, 6-7 `--ops all --long --long-seconds 1794 --row-seconds 1794`), each pass of each row one UNMODIFIED open_post.py
CLI process (pf_worker.py: execution-only patches), all compiles through the host's compile service (pf_svc.py).
Pipelined per row: a row starts its pass p+1 as soon as its pass p ends (the real runs waited for all 60 rows between passes); pass
p+1's input for the row is its pass p output, as in the real chained runs.
No fixed-point skip by default: re-measurements are fresh heartbeat draws and wall-dependent gates differ between passes, so a pass
that kept its input can still adopt in the next pass (16 of 113 such transitions did in the real run). --skip-no-site skips only after a
pass whose status was no_site (sites() is a pure function of the proof text) when the next pass has the same kind and walls.
Starts from the run's own export only.
Every worker gets PF_PASS=<pass number> and PF_ADOPT_LOG=<out>/adoptions.jsonl in its environment (a worker that supports them logs
its adoptions there; others ignore them).
--cap S (default 0 = none; OFF = the behavior above, unchanged): once the global run time (from this driver's start) reaches S, no
pass is launched any more and every running worker is stopped (SIGTERM, SIGKILL after --cap-grace s, default 30); a stopped pass is
recorded as status 'capped' in passes.jsonl and its row keeps its last COMPLETED pass output (passes never launched are not
recorded); summary.json and the merged proofs.post.jsonl are written as usual. A worker that exits 0 with its report while being
stopped counts as completed. Note: snapshot.py reads adoptions from the logs, so a capped pass's logged adoptions count there (a
deadline stop at the cap keeps them); the merged output here keeps only completed passes. A stopped worker's compiles already running
in pf_svc run on until run_full.sh stops the service, which then kills them (pf_svc's termination handler).
"""
from __future__ import annotations

import argparse, hashlib, json, os, statistics, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument("--code", required=True)
ap.add_argument("--rows", required=True)
ap.add_argument("--heartbeats", required=True)
ap.add_argument("--input", required=True)
ap.add_argument("--out", required=True)
ap.add_argument("--sock", required=True)
ap.add_argument("--worker", required=True)
ap.add_argument("--weights", default=None)
ap.add_argument("--passes", default="v3:2700:7200,v3:2700:7200,v4:2700:7200,v4:2700:7200,L:6515:6515,L:1794:1794,L:1794:1794",
                help="kind:row_seconds:step_seconds per pass (kind v3 | v4 | L = --ops all --long)")
ap.add_argument("--skip-no-site", action="store_true", help="skip a pass after a no_site pass of the same kind and walls")
ap.add_argument("--wall", type=float, default=0.0, help="global window in seconds: every pass's walls are clamped to the time left; "
                                                         "no pass starts with less than --min-pass-s left (0 = no window)")
ap.add_argument("--min-pass-s", type=float, default=60.0)
ap.add_argument("--target", type=float, default=82.556, help="stored mean of the real seven passes (time-to-target in the summary)")
ap.add_argument("--problems", nargs="*", default=None)
ap.add_argument("--cap", type=float, default=0.0, help="global run-time cap in seconds: stop launching passes and stop running workers "
                                                        "(status capped; rows keep their last completed pass); 0 = none")
ap.add_argument("--cap-grace", type=float, default=30.0, help="--cap: seconds between SIGTERM and SIGKILL")
ap.add_argument("--next-ops", action="store_true",
                help="(POST-HOC v7/specnext) give each worker PF_NEXT_OPS=<kind>:<row_s>:<s> of the row's next pass (pf_worker (6) cross "
                     "branches); default off (no such variable)")
a = ap.parse_args()
for _k in ("code", "rows", "heartbeats", "input", "out", "sock", "worker", "weights"):   # workers run with cwd = --code
    if getattr(a, _k):
        setattr(a, _k, os.path.abspath(getattr(a, _k)))

T0 = time.time()
OUT = Path(a.out); OUT.mkdir(parents=True, exist_ok=True)
LOGF = open(OUT / "drive.log", "a")
LL = threading.Lock()


def log(m):
    with LL:
        LOGF.write(f"[{time.strftime('%H:%M:%S', time.gmtime())} +{time.time() - T0:7.1f}s] {m}\n"); LOGF.flush()


def sha16(t: str) -> str:
    return hashlib.sha256((t or "").rstrip().encode()).hexdigest()[:16]


PASSES = []
for i, s in enumerate(a.passes.split(","), 1):
    kind, rs, ss = s.split(":")
    PASSES.append({"pass": i, "kind": kind, "row_seconds": float(rs), "seconds": float(ss)})


def cli_args(cfg, inp: Path, out: Path, name: str) -> list:
    base = ["--rows", a.rows, "--heartbeats", a.heartbeats, "--out", str(out), "--input", str(inp), "--jobs", "1", "--problems", name]
    if cfg["kind"] in ("v3", "v4"):
        extra = ["--ops", cfg["kind"]]
        if cfg["row_seconds"] != 2700.0:
            extra += ["--row-seconds", str(cfg["row_seconds"])]
        if cfg["seconds"] != 7200.0:
            extra += ["--seconds", str(cfg["seconds"])]
        return base + extra
    return base + ["--ops", "all", "--long", "--long-seconds", str(cfg["seconds"]), "--row-seconds", str(cfg["row_seconds"])]


def same_cfg(prev, nxt) -> bool:
    return prev["kind"] == nxt["kind"] and nxt["row_seconds"] == prev["row_seconds"] and nxt["seconds"] == prev["seconds"]


recs = [json.loads(l) for l in Path(a.input).read_text().splitlines() if l.strip()]
weights = json.loads(Path(a.weights).read_text()) if a.weights else {}
want = set(a.problems) if a.problems else None
PL = threading.Lock()
final: dict = {}
timeline: list = []
not_launched: dict = {}   # --cap: row index -> passes never launched


def capped_now() -> bool:
    return bool(a.cap) and time.time() - T0 >= a.cap


def run_worker(cmd, env, lf, tmo):
    """One worker process -> (exit code | "timeout" (the per-pass guard), stopped at --cap?)."""
    if not a.cap:   # no cap: exactly the original call
        try:
            return subprocess.run(cmd, cwd=a.code, env=env, stdout=lf, stderr=subprocess.STDOUT, timeout=tmo).returncode, False
        except subprocess.TimeoutExpired:
            return "timeout", False
    proc = subprocess.Popen(cmd, cwd=a.code, env=env, stdout=lf, stderr=subprocess.STDOUT)
    end = time.monotonic() + tmo
    try:
        while True:
            try:
                return proc.wait(timeout=max(0.05, min(end - time.monotonic(), a.cap - (time.time() - T0)))), False
            except subprocess.TimeoutExpired:
                pass
            if capped_now():
                proc.terminate()
                try:
                    return proc.wait(timeout=a.cap_grace), True
                except subprocess.TimeoutExpired:
                    proc.kill()
                    return proc.wait(), True
            if time.monotonic() >= end:   # as subprocess.run's timeout: SIGKILL, then reap
                proc.kill(); proc.wait()
                return "timeout", False
    except BaseException:
        if proc.poll() is None:
            proc.kill(); proc.wait()
        raise


def run_row(k: int):
    name = recs[k]["name"]
    if want is not None and name not in want:
        final[k] = recs[k]
        return
    inp = Path(a.input)
    line = recs[k]
    prev_cfg, prev_no_site = None, False
    for i_cfg, cfg in enumerate(PASSES):
        p = cfg["pass"]
        if capped_now():   # --cap: launch nothing more; the row keeps its last completed pass output
            not_launched[k] = len(PASSES) - i_cfg
            break
        run_cfg = None
        rdir = OUT / f"r{k:02d}"; rdir.mkdir(exist_ok=True)
        ts = time.time()
        left = (a.wall - (ts - T0)) if a.wall else None
        if left is not None and left < a.min_pass_s:
            ev = {"status": "skipped", "reason": "global wall"}
        elif a.skip_no_site and prev_cfg is not None and prev_no_site and same_cfg(prev_cfg, cfg):
            ev = {"status": "skipped", "reason": "no_site again (same input, same kind and walls)"}
        else:
            out = rdir / f"p{p}"; out.mkdir(exist_ok=True)
            env = dict(os.environ, PF_SOCK=a.sock, PF_CODE=a.code, PF_PRI=str(float(weights.get(name, 0.0))),
                       LRA_HBTOOL_SCRATCH=str(Path(a.code) / "probe/hbtool/.scratch-pf" / f"r{k:02d}p{p}"),
                       PF_PASS=str(p), PF_ADOPT_LOG=str(OUT / "adoptions.jsonl"))
            if a.next_ops and i_cfg + 1 < len(PASSES):   # (v7/specnext) the next pass's kind and walls (its own, unclamped)
                nc = PASSES[i_cfg + 1]
                env["PF_NEXT_OPS"] = f"{nc['kind']}:{nc['row_seconds']:g}:{nc['seconds']:g}"
            run_cfg = dict(cfg)
            if left is not None:   # the window: the CLI's own walls clamped to the time left (a wall stop keeps the confirmed proof)
                run_cfg["row_seconds"] = min(cfg["row_seconds"], float(int(left)))
                run_cfg["seconds"] = min(cfg["seconds"], float(int(left)))
            cmd = [sys.executable, a.worker, *cli_args(run_cfg, inp, out, name)]
            with open(rdir / f"p{p}.log", "w") as lf:
                rc, was_capped = run_worker(cmd, env, lf, min(run_cfg["seconds"], run_cfg["row_seconds"]) + 900)
            rep_p = out / "post_report.json"
            if was_capped and not (rc == 0 and rep_p.exists()):
                ev = {"status": "capped", "reason": f"global cap {a.cap:g} s (worker stopped, rc {rc}); last completed pass output kept"}
            elif rc == 0 and rep_p.exists():
                rep = json.loads(rep_p.read_text())
                rr = rep["rows"][k]
                ev = {"status": rr.get("status"), "reason": rr.get("reason"), "compiles": rr.get("compiles"), "row_seconds": rr.get("seconds"),
                      "gain": rr.get("gain"), "chain": [c.get("op") for c in rr.get("chain") or []], "before": (rr.get("before") or {}).get("score")}
                lines = [l for l in (out / "proofs.post.jsonl").read_text().splitlines() if l.strip()]
                line = json.loads(lines[k])
                inp = out / "proofs.post.jsonl"
            else:
                ev = {"status": "worker_failed", "reason": f"rc {rc}"}
        ev.update(pass_=p, kind=cfg["kind"], name=name, seconds=round(time.time() - ts, 1), t_end=round(time.time() - T0, 1),
                  stored_score=line.get("stored_score"), sha=sha16(line.get("proof")))
        if ev.get("status") != "skipped":
            prev_cfg = run_cfg or cfg
        prev_no_site = ev.get("status") in ("no_site",) or (ev.get("status") == "skipped" and prev_no_site)
        with PL:
            timeline.append(ev)
            with (OUT / "passes.jsonl").open("a") as fh:
                fh.write(json.dumps(ev, ensure_ascii=False) + "\n")
        log(f"r{k:02d} p{p} {name[:44]}: {ev['status']} {ev.get('chain') or ''} {ev['seconds']} s"
            f"{' ' + str(ev.get('compiles')) + ' compiles' if ev.get('compiles') is not None else ''}, stored {line.get('stored_score')}")
    final[k] = line


def stats_loop(stop: threading.Event):
    import socket
    while not stop.wait(60):
        try:
            s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM); s.connect(a.sock)
            f = s.makefile("rwb"); f.write(b'{"op": "stats"}\n'); f.flush()
            log("service " + f.readline().decode().strip()); s.close()
        except Exception as e:  # noqa: BLE001
            log(f"service stats failed: {e}")


log(f"start: {len(recs)} rows, passes {a.passes}, skip_no_site {a.skip_no_site}, wall {a.wall or 'none'}"
    + (f", cap {a.cap:g} s (grace {a.cap_grace:g} s)" if a.cap else ""))
stop = threading.Event()
threading.Thread(target=stats_loop, args=(stop,), daemon=True).start()
order = sorted(range(len(recs)), key=lambda k: -float(weights.get(recs[k]["name"], 0.0)))
with ThreadPoolExecutor(len(recs)) as ex:
    list(ex.map(run_row, order))
stop.set()
lines = [json.dumps(final[k], ensure_ascii=False) for k in range(len(recs))]
(OUT / "proofs.post.jsonl").write_text("".join(l + "\n" for l in lines))
before = [float(r["stored_score"]) for r in recs if isinstance(r.get("stored_score"), (int, float))]
after = [float(final[k]["stored_score"]) for k in range(len(recs)) if isinstance(final[k].get("stored_score"), (int, float))]
summ = {"wall_seconds": round(time.time() - T0, 1), "rows": len(recs), "stored_mean_before": round(statistics.mean(before), 4),
        "stored_mean_after": round(statistics.mean(after), 4), "passes": a.passes, "skip_no_site": a.skip_no_site, "wall": a.wall,
        "output_sha256": hashlib.sha256((OUT / "proofs.post.jsonl").read_bytes()).hexdigest(),
        "input_sha256": hashlib.sha256(Path(a.input).read_bytes()).hexdigest(),
        "statuses": {}, "pass_ends": {}}
for ev in timeline:
    summ["statuses"][ev["status"]] = summ["statuses"].get(ev["status"], 0) + 1
    summ["pass_ends"][str(ev["pass_"])] = max(summ["pass_ends"].get(str(ev["pass_"]), 0), ev["t_end"])
cur = {r["name"]: float(r["stored_score"]) for r in recs if isinstance(r.get("stored_score"), (int, float))}
traj, hit = [], None
for ev in sorted(timeline, key=lambda e: e["t_end"]):
    if isinstance(ev.get("stored_score"), (int, float)):
        cur[ev["name"]] = float(ev["stored_score"])
    m = statistics.mean(cur.values())
    traj.append([ev["t_end"], round(m, 4)])
    if hit is None and m >= a.target:
        hit = ev["t_end"]
summ["target"] = a.target
summ["first_reached_target_s"] = hit
if a.cap:
    summ["cap"] = a.cap
    summ["capped_passes"] = sum(1 for ev in timeline if ev["status"] == "capped")
    summ["passes_not_launched"] = sum(not_launched.values())
    summ["rows_cut_by_cap"] = len({ev["name"] for ev in timeline if ev["status"] == "capped"} | {recs[k]["name"] for k in not_launched})
summ["trajectory"] = traj
(OUT / "summary.json").write_text(json.dumps(summ, indent=1))
log("done " + json.dumps(summ))
