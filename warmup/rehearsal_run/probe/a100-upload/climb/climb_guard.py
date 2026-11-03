#!/usr/bin/env python3
"""climb_guard.py (GB10, unit lra-climb-guard; 2026-10-31 23:50 UTC): ends the warm-up climb when the public OPEN board is reset, or at the
hard cap 2026-11-02 00:00 UTC (operator 23:40: "Keep A100 do warm-up climbing until the board is reset on Nov 1").

Poll: the open board via the Arena's Gradio API (leaderboard/local_leaderboard.py: its API and its row parser, as fetch_board does, but an
empty board is told apart from a failed fetch), AT MOST every 10 min (the last fetch time is kept in board_state.json across restarts).
Baseline: the first good read (board_baseline.json). A read is a reset candidate when
  (a) our row "Vexorium" (present in the baseline) is gone while other rows are shown, or
  (b) none of the baseline rows (submitter, combined %) is still shown (incl. an empty board).
Confirmed after 2 consecutive candidate reads ((a)) or 3 ((b) with an empty board); a failed fetch neither confirms nor clears.
On a confirmed reset: climb/BOARD_RESET (evidence JSON), then `climb_stop.sh board-reset` (detached), exit. At the hard cap:
`climb_stop.sh cap`, exit. Exits at once when climb/STOPPED exists (someone stopped the climb). Single instance: flock guard.lock.
Env for tests only: GUARD_DIR (default this dir), GUARD_FAKE (a JSONL file: one board per line, {"rows": [[...8 cells]]} or {"error": "..."}),
GUARD_MIN_GAP_S (600), GUARD_CAP (ISO), GUARD_STOP (the stop command prefix).
"""
from __future__ import annotations
import fcntl, html, json, os, re, subprocess, sys, time, urllib.request
from datetime import datetime, timezone
from pathlib import Path

C = Path(os.environ.get("GUARD_DIR", str(Path(__file__).resolve().parent)))
STATE, BASE, MARK, STOPPED = C / "board_state.json", C / "board_baseline.json", C / "BOARD_RESET", C / "STOPPED"
STOP_CMD = os.environ.get("GUARD_STOP", f"/bin/bash {C / 'climb_stop.sh'}")
MIN_GAP = float(os.environ.get("GUARD_MIN_GAP_S", 600))
CAP = datetime.fromisoformat(os.environ.get("GUARD_CAP", "2026-11-02T00:00:00+00:00")).timestamp()
OURS, EP = "Vexorium", "_leaderboard_open_html_1"
FAKE = os.environ.get("GUARD_FAKE")
sys.path.insert(0, "/home/bobber/source/lean-refactor/leaderboard")
try:
    import local_leaderboard as LB   # noqa: E402
    API = LB.API
except Exception:  # noqa: BLE001
    API = "https://delta-lab-ai-lean-refactor-arena.hf.space/gradio_api/call"


def log(m: str) -> None:
    print(f"[{time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}] {m}", flush=True)


def rd(p: Path, d):
    try:
        return json.loads(p.read_text())
    except (OSError, ValueError):
        return d


def wr(p: Path, v) -> None:
    t = p.with_name("." + p.name + ".tmp"); t.write_text(json.dumps(v, ensure_ascii=False, indent=1)); os.replace(t, p)


_fake_i = [0]


def fetch() -> tuple[str, list]:
    """("ok", rows) with rows possibly empty, or ("error", [message]). Same request and row parser as LB.fetch_board."""
    if FAKE:
        lines = [json.loads(l) for l in open(FAKE) if l.strip()]
        d = lines[min(_fake_i[0], len(lines) - 1)]; _fake_i[0] += 1
        return ("error", [d["error"]]) if "error" in d else ("ok", d["rows"])
    try:
        req = urllib.request.Request(f"{API}/{EP}", data=b'{"data":[]}', headers={"content-type": "application/json"})
        eid = json.load(urllib.request.urlopen(req, timeout=30))["event_id"]
        sse = urllib.request.urlopen(f"{API}/{EP}/{eid}", timeout=90).read().decode()
        data = [l[5:].strip() for l in sse.splitlines() if l.startswith("data:")]
        v = json.loads(data[-1])[0]
        if not isinstance(v, str) or "<" not in v:
            return "error", [f"unexpected payload {str(v)[:120]}"]
        rows = []
        for tr in re.findall(r"<tr[^>]*>(.*?)</tr>", v, re.S):
            cells = [re.sub(r"\s+", " ", html.unescape(re.sub(r"<[^>]+>", " ", td))).strip() for td in re.findall(r"<t[dh][^>]*>(.*?)</t[dh]>", tr, re.S)]
            if cells and re.match(r"^\d+$", cells[0]) and len(cells) >= 8:
                rows.append(cells[:8])
        return "ok", rows
    except Exception as e:  # noqa: BLE001
        return "error", [f"{type(e).__name__}: {str(e)[:200]}"]


def stop(mode: str) -> None:
    r = subprocess.run(f"{STOP_CMD} {mode}", shell=True, capture_output=True, text=True, timeout=120)
    log(f"climb_stop.sh {mode}: rc {r.returncode} {(r.stdout + r.stderr).strip()[-300:]}")


def main() -> int:
    C.mkdir(parents=True, exist_ok=True)
    lk = open(C / "guard.lock", "a+")
    try:
        fcntl.flock(lk, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except OSError:
        log("another climb_guard holds guard.lock: exit"); return 0
    st = rd(STATE, {}) or {}
    log(f"climb_guard start: cap {datetime.fromtimestamp(CAP, timezone.utc):%Y-%m-%dT%H:%M}Z, min gap {MIN_GAP:.0f} s, "
        f"candidates so far {st.get('cand', 0)}, baseline {'present' if BASE.exists() else 'none yet'}")
    while True:
        if STOPPED.exists():
            log(f"STOPPED marker present ({STOPPED.read_text().strip()[:120]}): exit"); return 0
        now = time.time()
        if now >= CAP:
            log("hard cap reached"); stop("cap"); return 0
        wait = (st.get("last_fetch") or 0) + MIN_GAP - now
        if wait > 0:
            time.sleep(min(30.0, wait)); continue
        status, rows = fetch()
        st["last_fetch"] = time.time(); st["last_status"] = status
        if status != "ok":
            log(f"fetch failed ({rows[0]}): no decision (candidates stay {st.get('cand', 0)})"); wr(STATE, st); continue
        base = rd(BASE, None)
        if base is None:
            base = {"at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "rows": rows}
            if not rows:
                log("first read is an EMPTY board: no baseline yet (cannot tell a reset)"); wr(STATE, st); continue
            wr(BASE, base)
            log(f"baseline: {len(rows)} rows; ours: {next((r[3] for r in rows if r[1] == OURS), 'ABSENT')}")
        brows = base["rows"]; bset = {(r[1], r[3]) for r in brows}; ours_in_base = any(r[1] == OURS for r in brows)
        names = {r[1] for r in rows}; kept = sum(1 for r in rows if (r[1], r[3]) in bset)
        why = None
        if ours_in_base and rows and OURS not in names:
            why = f"our row {OURS} gone ({len(rows)} rows shown)"
        elif kept == 0:
            why = "empty board" if not rows else f"none of the {len(brows)} baseline rows shown ({len(rows)} rows)"
        need = 3 if (why == "empty board") else 2
        st["cand"] = st.get("cand", 0) + 1 if why else 0
        ours = next((r[3] for r in rows if r[1] == OURS), "ABSENT")
        log(f"board: {len(rows)} rows, {kept} unchanged vs baseline, ours {ours}" + (f"; RESET CANDIDATE {st['cand']}/{need}: {why}" if why else ""))
        wr(STATE, st)
        if why and st["cand"] >= need:
            ev = {"at": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "why": why, "reads": st["cand"], "rows_now": rows[:12],
                  "baseline_at": base["at"], "baseline_rows": len(brows)}
            wr(MARK, ev)
            log(f"BOARD RESET confirmed: {why}"); stop("board-reset"); return 0


if __name__ == "__main__":
    sys.exit(main())
