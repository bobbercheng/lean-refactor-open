#!/usr/bin/env python3
"""A `vastai` stand-in for the $0 dry run of the rental scripts (probe/a100/dry_run.sh; review 2026-10-28). Answers the subcommands
infra/vast/*.sh use (search offers, create instance, show user / instances / instance, destroy instance, change bid, stop / start)
from a JSON state file (FAKE_VASTAI_STATE), with vastai 1.0.13's output shapes (--raw JSON on stdout, the DEPRECATED notice on
stderr for `show instances`), and records every call in the state's `calls`. The dry run steers it through `vastai fake ...`:
  fake set-status ID exited|running|stopped [intended]   fake set-util ID GPU CPU   fake set-credit X      fake drain X   (credit falls by X per `show user`)
  fake destroy-fails N   (the next N destroys leave the instance listed)         fake outbid-price P  (a bid >= P makes a stopped
  instance run again)    fake dump
Installed as a `vastai` executable in a directory given to the scripts as LRA_FAKE_VAST_BIN (common.sh puts it first on PATH).
No network, no money."""
from __future__ import annotations

import fcntl, json, os, random, sys, time
from pathlib import Path

STATE = Path(os.environ.get("FAKE_VASTAI_STATE") or "probe/a100/fake_state.json")
DEPRECATED = "DEPRECATED: `show instances` ... (fake)"


def default_state() -> dict:
    offers = []
    for i, (mach, bid, geo, down, dcost, cpu, disk, verified) in enumerate([
            (140789, 0.816, "United Kingdom, GB", 1200, 0.0026, 64, 450, "verified"),
            (120040, 1.867, "United Arab Emirates, AE", 93, 0.01, 48, 438, "deverified"),
            (153016, 0.95, "Sweden, SE", 2500, 0.004, 128, 800, "verified")]):
        offers.append({"id": 41351890 + i, "machine_id": mach, "min_bid": bid, "dph_total": bid + 0.1, "gpu_name": "A100 SXM4", "num_gpus": 4,
                       "cpu_cores_effective": cpu, "cpu_ram": 500000, "disk_space": disk, "inet_down": down, "inet_up": 800, "inet_down_cost": dcost,
                       "inet_up_cost": 0.004, "reliability2": 0.99, "bw_nvlink": 600, "verified": verified, "geolocation": geo, "gpu_ram": 81920})
    return {"user": {"credit": 74.35, "can_pay": True, "balance": 0}, "offers": offers, "instances": {}, "next_id": 90000001, "calls": [],
            "drain": 0.0, "destroy_fails": 0, "outbid_price": 99.0, "api_key_counter": 0}


def load() -> dict:
    if not STATE.exists():
        return default_state()
    return json.loads(STATE.read_text())


def save(s: dict) -> None:
    STATE.parent.mkdir(parents=True, exist_ok=True)
    tmp = STATE.with_suffix(".tmp"); tmp.write_text(json.dumps(s, indent=1)); os.replace(tmp, STATE)


def out(obj) -> None:
    print(json.dumps(obj))


def main(argv: list[str]) -> int:
    STATE.parent.mkdir(parents=True, exist_ok=True)
    lock = open(STATE.parent / ".fake_vastai.lock", "w")
    fcntl.flock(lock, fcntl.LOCK_EX)
    s = load()
    s["calls"].append({"t": round(time.time(), 2), "argv": argv[:6]})
    s["calls"] = s["calls"][-500:]
    rc = 0
    try:
        rc = run(s, argv)
    finally:
        save(s)
    return rc


def inst(s: dict, iid: str) -> dict | None:
    return s["instances"].get(str(iid))


def run(s: dict, a: list[str]) -> int:
    if not a:
        print("usage: vastai <command>"); return 2
    cmd = a[0]
    if cmd == "fake":
        op = a[1]
        if op == "set-status":
            i = inst(s, a[2]); i["actual_status"] = a[3]; i["intended_status"] = a[4] if len(a) > 4 else ("running" if a[3] == "running" else "stopped")
        elif op == "set-util":   # fake set-util ID GPU CPU ('none' = the field missing): the spend guard's idle signal
            i = inst(s, a[2]); i["gpu_util"] = None if a[3] == "none" else float(a[3]); i["cpu_util"] = None if a[4] == "none" else float(a[4])
        elif op == "set-credit":
            s["user"]["credit"] = float(a[2])
        elif op == "drain":
            s["drain"] = float(a[2])
        elif op == "destroy-fails":
            s["destroy_fails"] = int(a[2])
        elif op == "outbid-price":
            s["outbid_price"] = float(a[2])
        elif op == "dump":
            out(s)
        else:
            print(f"fake: unknown op {op}"); return 2
        return 0
    if cmd == "show" and a[1] == "user":
        s["user"]["credit"] = round(max(0.0, s["user"]["credit"] - s.get("drain", 0.0)), 4)
        out(s["user"]); return 0
    if cmd == "show" and a[1] == "instances":
        print(DEPRECATED, file=sys.stderr)
        out(list(s["instances"].values())); return 0
    if cmd == "show" and a[1] == "instance":
        i = inst(s, a[2])
        if i is None:
            print("no instance", file=sys.stderr); return 1
        out(i); return 0
    if cmd == "search" and a[1] == "offers":
        q = a[2] if len(a) > 2 else ""
        res = s["offers"]
        if "verified=any" not in q:
            res = [o for o in res if o["verified"] == "verified"]
        for tok in q.split():
            if tok.startswith("disk_space>="):
                res = [o for o in res if o["disk_space"] >= float(tok.split(">=")[1])]
            if tok.startswith("cpu_cores_effective>="):
                res = [o for o in res if o["cpu_cores_effective"] >= float(tok.split(">=")[1])]
            if tok.startswith("inet_down>="):
                res = [o for o in res if o["inet_down"] >= float(tok.split(">=")[1])]
        out(res); return 0
    if cmd == "create" and a[1] == "instance":
        offer = int(a[2])
        o = next((x for x in s["offers"] if x["id"] == offer), None)
        if o is None:
            out({"success": False, "error": "no_such_ask", "msg": "no such ask"}); return 1
        if o.get("refuse_create"):   # vast answered 410 no_such_ask for an offer it still listed as rentable (UK 51417952, 2026-10-28)
            out({"error": True, "status_code": 410, "msg": f"error 410/3907: no_such_ask  Instance type {offer} is no longer available."}); return 1
        bid = float(a[a.index("--bid_price") + 1]) if "--bid_price" in a else o["min_bid"] + 0.01
        iid = s["next_id"]; s["next_id"] += 1
        s["api_key_counter"] += 1
        s["instances"][str(iid)] = {"id": iid, "machine_id": o["machine_id"], "actual_status": "running", "intended_status": "running",
                                    "status_msg": "", "public_ipaddr": "127.0.0.1", "ports": {"22/tcp": [{"HostPort": "22"}], "8000/tcp": [{"HostPort": "8000"}]},
                                    "dph_total": round(bid + 0.02, 3), "dph_base": bid, "min_bid": o["min_bid"], "is_bid": True, "gpu_name": o["gpu_name"],
                                    "num_gpus": 4, "label": a[a.index("--label") + 1] if "--label" in a else "", "inet_down_cost": o["inet_down_cost"],
                                    "gpu_util": 0.0, "cpu_util": 0.0}
        out({"success": True, "new_contract": iid, "instance_api_key": "fake%032d" % s["api_key_counter"]}); return 0
    if cmd == "destroy" and a[1] == "instance":
        iid = str(a[2])
        if s.get("destroy_fails", 0) > 0:
            s["destroy_fails"] -= 1; print("destroying instance (fake: left listed this time)"); return 0
        s["instances"].pop(iid, None); print(f"destroying instance {iid}."); return 0
    if cmd == "change" and a[1] == "bid":
        i = inst(s, a[2])
        if i is None:
            return 1
        price = float(a[a.index("--price") + 1]); i["dph_base"] = price; i["dph_total"] = round(price + 0.02, 3)
        if i["actual_status"] != "running" and price >= s.get("outbid_price", 99.0) - 1e-9:
            i["actual_status"] = "running"; i["intended_status"] = "running"
        out({"success": True, "msg": f"bid changed to {price}"}); return 0
    if cmd == "stop" and a[1] == "instance":
        i = inst(s, a[2]); i["actual_status"] = "exited"; i["intended_status"] = "stopped"; out({"success": True}); return 0
    if cmd == "start" and a[1] == "instance":
        # like vast: a start request of an outbid interruptible instance waits (intended running) until its bid wins (the ladder, Oct 29,
        # asks for a start after every raise; the fake used to start it at any price, so the dry run's B3 saw RUNNING below the market)
        i = inst(s, a[2]); i["intended_status"] = "running"
        if not i.get("is_bid") or i.get("dph_base", 0) >= s.get("outbid_price", 99.0) - 1e-9:
            i["actual_status"] = "running"
        out({"success": True}); return 0
    if cmd == "--version":
        print("fake-vastai 1.0.13"); return 0
    print(f"fake vastai: unsupported: {' '.join(a)}", file=sys.stderr); return 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
