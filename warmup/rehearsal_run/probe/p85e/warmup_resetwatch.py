#!/usr/bin/env python3
"""GB10 unit lra-warmup-resetwatch (2026-11-01 ~00:00 UTC; operator 2026-10-31 23:40 UTC "Keep A100 do warm-up climbing until the board is
reset on Nov 1"): ends the A100 warm-up climb (p85e) when the public OPEN board is reset.

Every EVERY_S (600 s, never more often) one read of the open board via leaderboard/local_leaderboard.py fetch_board (lean-refactor);
when that returns None, one raw read of the same endpoint tells "empty table" from "fetch failed". A read is RESET EVIDENCE when
  * rows came back and our row ("Vexorium") is missing, or none of the baseline (team, score) pairs is still on the board, or
  * the read succeeded but the table has no rows (weaker: needs EMPTY_N reads in a row).
Reset = RESET_N (2) evidence reads in a row (EMPTY_N = 3 for empty tables), or the climb guard's marker
(probe/a100-upload/climb/BOARD_RESET*) exists. The baseline = probe/p85e/board_baseline_open.json (the first read with our row).
On a reset: probe/p85e/BOARD_RESET (evidence), v3.1: also probe/a100-upload/climb/BOARD_RESET (if absent; the pick watcher watch88_v3
wakes on it), ntfy push, `p85e_stop_all.sh now board-reset` (END_AT=now + the armed final: final pull,
pick, hold removed; the p85b driver is NOT stopped), and the climb guard's stop (probe/a100-upload/climb/climb_stop.sh board-reset) when
it exists and its marker does not; then exit.
Credit rule after the release (stop rule a): while probe/p85e/RELEASE_SEEN says the A100 was KEPT ("decision": "keep"), every poll
checks vast credit - dph x hours to END_AT >= need; when not: `p85e_stop_all.sh end-driver credit-short` + ntfy, and exit.
Ends at END (2026-11-02 00:05 UTC) or when probe/p85e/FINAL_DONE exists. Single instance: flock probe/p85e/resetwatch.lock.
Log probe/p85e/resetwatch.log (stdout); state probe/p85e/resetwatch_state.json. Test hooks: RW_ROOT, RW_EVERY, RW_FETCH (a JSON file of
rows instead of the board), RW_NO_ACT=1 (log the actions only), RW_NTFY."""
import fcntl, html, json, os, re, subprocess, sys, time, urllib.request
from pathlib import Path

ROOT = Path(os.environ.get("RW_ROOT") or "/home/bobber/source/lra-a100"); P = ROOT / "probe/p85e"
LR = Path("/home/bobber/source/lean-refactor/leaderboard")
END = float(os.environ.get("RW_END") or 1793577900)        # 2026-11-02 00:05 UTC
EVERY = float(os.environ.get("RW_EVERY") or 600)
RESET_N, EMPTY_N = 2, 3
OUR = "Vexorium"
EP = "_leaderboard_open_html_1"
STATE, MARK, BASE = P / "resetwatch_state.json", P / "BOARD_RESET", P / "board_baseline_open.json"
RELEASE, FINAL_DONE = P / "RELEASE_SEEN", P / "FINAL_DONE"
STOP_ALL = Path(os.environ.get("RW_STOP_ALL") or "/home/bobber/source/lra-a100/probe/p85e/p85e_stop_all.sh")
GUARD_DIR = ROOT / "probe/a100-upload/climb"
NO_ACT = os.environ.get("RW_NO_ACT") == "1"
sys.path.insert(0, str(LR))
import local_leaderboard as lb  # noqa: E402


def log(m: str) -> None:
    print(f"[{time.strftime('%m-%d %H:%M:%S', time.gmtime())}] {m}", flush=True)


def push(m: str, prio: str = "urgent") -> None:
    topic = os.environ.get("RW_NTFY")
    if topic is None:
        try:
            topic = (ROOT / "probe/a100-ntfy-topic").read_text().strip()
        except OSError:
            topic = ""
    if not topic:
        return
    try:
        req = urllib.request.Request(f"https://ntfy.sh/{topic}", data=m.encode(), headers={"Title": "A100 warm-up reset watch", "Priority": prio})
        urllib.request.urlopen(req, timeout=20).read()
    except Exception as e:  # noqa: BLE001
        log(f"ntfy failed: {type(e).__name__}")


def raw_read() -> tuple:
    """('empty', []) when the endpoint answered with a table without data rows, ('error', why) otherwise (the same two requests as
    fetch_board; used only when fetch_board returned None)."""
    try:
        req = urllib.request.Request(f"{lb.API}/{EP}", data=b'{"data":[]}', headers={"content-type": "application/json"})
        eid = json.load(urllib.request.urlopen(req, timeout=30))["event_id"]
        sse = urllib.request.urlopen(f"{lb.API}/{EP}/{eid}", timeout=90).read().decode()
        data = [l[5:].strip() for l in sse.splitlines() if l.startswith("data:")]
        v = json.loads(data[-1])[0]
        if not isinstance(v, str) or "<table" not in v.lower():
            return "error", f"no table in the answer ({str(v)[:80]!r})"
        rows = [tr for tr in re.findall(r"<tr[^>]*>(.*?)</tr>", v, re.S) if re.search(r"<td[^>]*>\s*\d+\s*</td>", tr)]
        return ("empty", []) if not rows else ("error", "table rows the parser did not take")
    except Exception as e:  # noqa: BLE001
        return "error", f"{type(e).__name__}: {str(e)[:120]}"


def read_board() -> tuple:
    """('ok', rows) / ('empty', []) / ('error', why)."""
    if os.environ.get("RW_FETCH"):
        try:
            d = json.loads(Path(os.environ["RW_FETCH"]).read_text())
        except (OSError, ValueError) as e:
            return "error", str(e)
        return ("ok", d) if d else ("empty", []) if d == [] else ("error", "test: null")
    rows = lb.fetch_board(EP)
    if rows:
        return "ok", rows
    return raw_read()


def pairs(rows: list) -> set:
    return {(r[1].strip(), r[3].strip()) for r in rows if len(r) >= 4}


def credit_check(rel: dict) -> str | None:
    """None = fine; else why the A100 must stop now (credit short for the official run)."""
    try:
        c = json.loads(subprocess.run(["vastai", "show", "user", "--raw"], capture_output=True, text=True, timeout=60).stdout)["credit"]
        c = float(c)
    except Exception:  # noqa: BLE001
        log("credit check: vast credit unreadable this poll (no action)"); return None
    try:
        end_at = float((P / "END_AT").read_text().split()[0])
    except (OSError, ValueError, IndexError):
        end_at = 1793577600.0
    end_at = min(end_at, 1793577600.0)
    dph = float(rel.get("dph") or 3.92); need = float(rel.get("need") or 375)
    left = c - dph * max(0.0, end_at - time.time()) / 3600
    if left < need:
        return f"vast credit ${c:.2f} - ${dph:.2f}/h x {max(0, end_at - time.time()) / 3600:.1f} h to END_AT = ${left:.2f} < need ${need:.0f}"
    return None


def act_stop(mode: str, reason: str) -> str:
    if NO_ACT:
        return f"(RW_NO_ACT) would run: bash {STOP_ALL} {mode} {reason}"
    try:
        r = subprocess.run(["bash", str(STOP_ALL), mode, reason], capture_output=True, text=True, timeout=120)
    except Exception as e:  # noqa: BLE001
        return f"p85e_stop_all.sh failed: {type(e).__name__}: {e}"
    lines = (r.stdout + r.stderr).strip().splitlines()
    return lines[-1] if lines else f"rc {r.returncode}"


def main() -> int:
    P.mkdir(parents=True, exist_ok=True)
    lk = open(P / "resetwatch.lock", "w")
    try:
        fcntl.flock(lk, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        log("another reset watcher holds resetwatch.lock: exit"); return 0
    st = {"evid": 0, "empty": 0, "errors": 0, "err_since": None, "reads": 0, "warned_err": False}
    try:
        st.update(json.loads(STATE.read_text()))
    except (OSError, ValueError):
        pass
    log(f"reset watcher up (pid {os.getpid()}): open board every {EVERY:.0f} s until {time.strftime('%m-%d %H:%M', time.gmtime(END))} UTC; "
        f"reset = {RESET_N} reads without '{OUR}' or with no baseline pair ({EMPTY_N} for empty tables) or {GUARD_DIR}/BOARD_RESET*; "
        f"baseline {'present' if BASE.exists() else 'from the first read with our row'}")
    nxt = float(st.get("last_read") or 0) + EVERY   # v3.1: a restart keeps the 10-min spacing of the board reads
    while time.time() < END and not FINAL_DONE.exists():
        if MARK.exists():
            log("BOARD_RESET marker already present: nothing more to do"); return 0
        now = time.time()
        # the climb guard's marker (the $0-loop side) counts as an observed reset
        gm = sorted(GUARD_DIR.glob("BOARD_RESET*")) if GUARD_DIR.exists() else []
        trigger, why = False, ""
        if gm:
            trigger, why = True, f"climb guard marker {gm[0].name}"
        if not trigger and now >= nxt:
            nxt = now + EVERY
            kind, val = read_board(); st["reads"] += 1; st["last_read"] = now
            if kind == "ok":
                st["errors"], st["err_since"], st["warned_err"] = 0, None, False
                names = {r[1].strip() for r in val}
                if not BASE.exists() and OUR in names:
                    BASE.write_text(json.dumps({"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "rows": val}, ensure_ascii=False, indent=0))
                    log(f"baseline written: {len(val)} rows")
                base = pairs(json.loads(BASE.read_text())["rows"]) if BASE.exists() else set()
                keep = len(pairs(val) & base) if base else None
                ours = next((r for r in val if r[1].strip() == OUR), None)
                evid = ours is None or (keep == 0)
                st["evid"] = st["evid"] + 1 if evid else 0; st["empty"] = 0
                log(f"board: {len(val)} rows; ours {ours[3] + ' #' + ours[0] if ours else 'MISSING'}; baseline pairs kept "
                    f"{keep if keep is not None else '?'}/{len(base) if base else '?'}; evidence {st['evid']}/{RESET_N}")
                if st["evid"] >= RESET_N:
                    trigger, why = True, (f"{RESET_N} reads in a row: our row {'missing' if ours is None else 'present'}, baseline pairs kept "
                                          f"{keep}; top {val[0][1]} {val[0][3]}")
            elif kind == "empty":
                st["empty"] += 1; st["errors"], st["err_since"] = 0, None
                log(f"board: answered with an EMPTY table; empty reads {st['empty']}/{EMPTY_N}")
                if st["empty"] >= EMPTY_N:
                    trigger, why = True, f"{EMPTY_N} empty board reads in a row"
            else:
                st["errors"] += 1; st["err_since"] = st["err_since"] or now
                log(f"board read failed ({val}); failures in a row {st['errors']} (evidence counters kept)")
                if now - st["err_since"] >= 3600 and not st["warned_err"]:
                    st["warned_err"] = True; push(f"WARN reset watch: the open board has been unreadable for 1 h ({val})", "high")
            # the credit rule after the release (stop rule a)
            try:
                rel = json.loads(RELEASE.read_text()) if RELEASE.exists() else None
            except (OSError, ValueError):
                rel = None
            if rel and rel.get("decision") == "keep" and not trigger:
                cw = credit_check(rel)
                if cw:
                    log(f"CREDIT SHORT after the release: {cw}: ending the A100 climb (driver too)")
                    out = act_stop("end-driver", "credit-short-after-release")
                    log(f"stop: {out}"); push(f"A100 climb ended after the release: {cw}. {out}")
                    STATE.write_text(json.dumps(st)); return 0
            STATE.write_text(json.dumps(st))
        if trigger:
            ev = {"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "why": why}
            log(f"BOARD RESET observed ({why}): ending the A100 climb (END_AT=now + final; the driver is not stopped)")
            if not NO_ACT:
                MARK.write_text(json.dumps(ev) + "\n")
                gmark = GUARD_DIR / "BOARD_RESET"   # v3.1: the pick watcher (watch88_v3) and climb_guard read this one
                if not gmark.exists():
                    try:
                        GUARD_DIR.mkdir(parents=True, exist_ok=True)
                        tmp = GUARD_DIR / ".BOARD_RESET.resetwatch.tmp"
                        tmp.write_text(json.dumps(dict(ev, by="lra-warmup-resetwatch")) + "\n"); os.replace(tmp, gmark)
                        log(f"climb guard marker written: {gmark}")
                    except OSError as e:
                        log(f"climb guard marker NOT written ({type(e).__name__}: {e})")
            out = act_stop("now", "board-reset")
            log(f"stop: {out}")
            cs = GUARD_DIR / "climb_stop.sh"
            if cs.exists() and not gm:
                if NO_ACT:
                    log(f"(RW_NO_ACT) would run: bash {cs} board-reset")
                else:
                    try:
                        r = subprocess.run(["bash", str(cs), "board-reset"], capture_output=True, text=True, timeout=120,
                                           env=dict(os.environ, CLIMB_CALLER="lra-warmup-resetwatch"))
                        log(f"climb_stop.sh board-reset: {(r.stdout + r.stderr).strip()[-200:]}")
                    except Exception as e:  # noqa: BLE001
                        log(f"climb_stop.sh board-reset failed: {type(e).__name__}")
            push(f"Open board RESET observed ({why}). A100 climb ending: {out}. The driver finishes by itself (12:00 UTC); to end it early: "
                 f"bash {STOP_ALL} end-driver")
            return 0
        time.sleep(15)
    log(f"reset watcher end ({'final done' if FINAL_DONE.exists() else 'END'})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
