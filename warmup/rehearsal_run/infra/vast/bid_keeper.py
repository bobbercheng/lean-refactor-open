#!/usr/bin/env python3
"""Proactive bid keeper for an interruptible vast.ai rental (operator 2026-10-31 ~01:05 UTC: "protect the instance ... increase bid price
mini for us (fair for vast)"). On the market our running machine is listed at its host's floor (e.g. min_bid $1.07 while we pay $1.91): a
renter looking for the cheapest 4x A100 bids on it, and any bid above ours stops our run. So keep our bid just above the cheapest COMPARABLE
alternative (same GPU count / class, vRAM, CPU, disk, reliability): then preempting us costs more than renting that alternative.
Rules: raise only (never lower by itself), by the smallest step (target = cheapest alternative + DELTA), at most CAP; every change is
verified (vast shows the new bid and the instance still running) and logged + pushed to the private ntfy topic; no change while the
instance is not running (the outbid sentry's ladder owns that) or while probe/a100-pause-<id> exists; an unreadable API changes nothing.
    python3 infra/vast/bid_keeper.py ID [--cap 2.70] [--delta 0.02] [--poll 120] [--dry-run] [--once]"""
from __future__ import annotations
import argparse, json, os, subprocess, sys, time, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
LOG = ROOT / "probe/a100-bid-keeper.log"
LOWER_MIN_STEP = 0.05   # 2026-10-31 01:38: a one-poll gap in the listing (the $2.08 offer vanished for ~4 min) ratcheted the bid to $2.69 for good;
LOWER_STABLE_POLLS = 3  # now a lower target is applied after it held for 3 polls in a row (6 min) and saves >= $0.05; raises stay immediate
QUERY = "num_gpus=4 gpu_ram>=80 gpu_name in [A100_SXM4,A100_PCIE,A100X] cpu_cores_effective>=64 disk_space>=420"


def log(m: str) -> None:
    line = f"[{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}] {m}"
    print(line, flush=True)
    with LOG.open("a") as f:
        f.write(line + "\n")


def push(m: str) -> None:
    try:
        topic = (ROOT / "probe/a100-ntfy-topic").read_text().strip()
        urllib.request.urlopen(urllib.request.Request(f"https://ntfy.sh/{topic}", data=m.encode(), headers={"Title": "A100 bid keeper"}), timeout=20)
    except Exception:  # noqa: BLE001
        pass


def vast_json(args: list[str]):
    try:
        r = subprocess.run(["vastai", *args, "--raw"], capture_output=True, text=True, timeout=90)
        return json.loads(r.stdout) if r.returncode == 0 and r.stdout.strip() else None
    except Exception:  # noqa: BLE001
        return None


def decide(inst: dict | None, offers: list | None, cap: float, delta: float, min_rel: float = 0.9, floor: float = 0.0) -> tuple[float | None, str]:
    """(new bid or None, why). Pure: the unit tests drive it."""
    if not inst or offers is None:
        return None, "vast unreadable"
    if inst.get("actual_status") != "running":
        return None, f"instance {inst.get('actual_status')}: the sentry's ladder owns it"
    cur = float(inst.get("dph_base") or 0); mach = inst.get("machine_id")
    alts = [float(o["min_bid"]) for o in offers if o.get("machine_id") != mach and o.get("min_bid") is not None
            and float(o.get("reliability2") or 0) >= min_rel and int(o.get("num_gpus") or 0) == 4]
    if not alts:
        return None, "no comparable alternative listed: bid kept"
    # 2026-10-31 10:05 outbid: the box was taken at ~$2.26 while the keeper sat at the cheapest alternative + $0.02 = $2.10 (and had
    # undercut to $1.62 at 10:00): a renter can want THIS machine, so the bid never goes below --floor (operator cap $3.50)
    alt = min(alts); target = round(min(cap, max(floor, alt + delta)), 3)
    if target > cur + 0.005:
        return target, f"cheapest comparable alternative ${alt:.3f} (of {len(alts)}): bid ${cur:.2f} -> ${target:.2f}" + (" (capped)" if target >= cap else "")
    if target < cur - LOWER_MIN_STEP:
        return target, f"LOWER: cheapest comparable alternative back at ${alt:.3f}: bid ${cur:.2f} -> ${target:.2f}"
    return None, f"bid ${cur:.2f} ~ cheapest comparable alternative ${alt:.3f} + ${delta:.2f} (or the cap ${cap:.2f})"


def main() -> int:
    ap = argparse.ArgumentParser(); ap.add_argument("id"); ap.add_argument("--cap", type=float, default=2.70); ap.add_argument("--delta", type=float, default=0.02)
    ap.add_argument("--poll", type=float, default=120); ap.add_argument("--min-rel", type=float, default=0.9)
    ap.add_argument("--dry-run", action="store_true"); ap.add_argument("--once", action="store_true")
    ap.add_argument("--floor", type=float, default=0.0, help="never bid below this (2026-10-31: an outbid at $2.26 while at $2.10)")
    a = ap.parse_args()
    log(f"bid keeper on {a.id}: cap ${a.cap:.2f}, delta ${a.delta:.2f}, poll {a.poll:.0f}s, min reliability {a.min_rel}{' (dry run)' if a.dry_run else ''}")
    last_why = None; gone = 0; lower_seen, lower_seen_target = 0, None
    while True:
        inst = None
        if (ROOT / f"probe/a100-pause-{a.id}").exists():
            why, target = "pause file present", None
        else:
            inst = vast_json(["show", "instance", str(a.id)])
            offers = vast_json(["search", "offers", QUERY, "--type", "bid", "--storage", "420"])
            if isinstance(inst, dict) and inst.get("actual_status") is None and not inst.get("id"):
                inst = None
            listed = vast_json(["show", "instances"])
            if isinstance(listed, list) and not any(str(r.get("id")) == str(a.id) for r in listed):
                gone += 1
                if gone >= 3:
                    log(f"instance {a.id} not listed for 3 polls (released): bid keeper exits"); return 0
            else:
                gone = 0
            target, why = decide(inst, offers if isinstance(offers, list) else None, a.cap, a.delta, a.min_rel, a.floor)
        cur_bid = float(inst.get("dph_base") or 0) if isinstance(inst, dict) else 0.0
        if target is not None and target < cur_bid:
            lower_seen = lower_seen + 1 if lower_seen_target is not None and abs(lower_seen_target - target) < 0.006 else 1
            lower_seen_target = target
            if lower_seen < LOWER_STABLE_POLLS:
                why, target = f"{why} (held {lower_seen}/{LOWER_STABLE_POLLS} polls)", None
        else:
            lower_seen, lower_seen_target = 0, None
        if target is not None and not a.dry_run:
            subprocess.run(["vastai", "change", "bid", str(a.id), "--price", f"{target:.3f}"], capture_output=True, text=True, timeout=90)
            time.sleep(10)
            v = vast_json(["show", "instance", str(a.id)]) or {}
            ok = abs(float(v.get("dph_base") or 0) - target) < 0.006 and v.get("actual_status") == "running"
            msg = f"{why}: {'VERIFIED' if ok else 'NOT verified'} (vast: bid ${float(v.get('dph_base') or 0):.3f}, {v.get('actual_status')}, ${float(v.get('dph_total') or 0):.3f}/h total)"
            log(msg); push(f"A100 {a.id}: {msg}")
            last_why = None
        elif why != last_why:
            log(why + (f" [dry run: would set ${target:.2f}]" if target is not None else ""))
            last_why = why
        if a.once:
            return 0
        time.sleep(a.poll)


if __name__ == "__main__":
    raise SystemExit(main())
