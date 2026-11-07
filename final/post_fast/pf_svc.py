#!/usr/bin/env python3
"""postfast compile service (post-hoc measurement, 2026-11-05). One process per host owns:
  - the compile memo, with DRAW semantics: key = (command with the .lean path masked, LEAN_PATH, LEAN_SYSROOT, cwd for `lake`, sha256 of
    the file text). Heartbeats of a fresh compile vary by a few units between compiles of the same text (the module name is random), and
    the uploaded code re-measures on purpose (paired re-reading, every pass's r0). So every stored compile is one DRAW: an on-path
    (charged) request consumes an unconsumed draw (e.g. one a speculative compile produced) or compiles a fresh one; it never reuses a
    draw the charged path already consumed. A repeat draw carries its draw index to the prefix backend, which serves it from a server of
    its own (its own random module name, so an independent draw, like a fresh `lean` with a new random file name). Speculative requests reuse any draw. A draw keeps its ORIGINAL compile seconds;
    a draw longer than the request's timeout is returned as a timeout (hit and miss alike). Timeouts and crashes are never stored;
  - one priority slot gate for every Lean process on the host: priority [on-path 0 / speculative 1, -row weight]; a queued speculative
    compile is promoted (sticky) when an on-path request for the same key waits on it; a speculative compile whose client has gone and
    that no one waits on is dropped when its slot comes up;
  - a memory floor (no launch while MemAvailable is below --min-free-gb; bounded wait); timeouts kill the whole process group;
  - optionally the prefix-reuse backend (--backend module with run(req) -> result or None for "not handled").
Workers (pf_worker.py: one unmodified open_post.py CLI process per row and pass) send every Lean launch here over a Unix socket, one
JSON line per request and per response. Requests: {"op": "run", "cmd", "file_index", "cwd", "env", "content", "timeout", "pri", "lake"}
and {"op": "stats"}.

--store-timeouts (OFF by default; off = everything above, unchanged): a timed-out compile of a request with timeout T is stored as a
draw too, {"r": {"timed_out": True, "seconds": T, ...}, "to": T, "consumed"}: it proves the compile needs more than T. A request FITS
a timed-out draw only if its own timeout is set and <= T; a successful draw fits every request (one longer than the request's timeout
is answered as a timeout, as always). Charged requests take the FIRST unconsumed fitting draw in creation order (success or timeout:
what one fresh, independent compile would be) and consume it; speculative requests reuse the LATEST fitting draw. A fitting timed-out
draw is answered exactly like the service's timeout answer, {"timed_out": True, "seconds": <the request's timeout>, "stdout": "",
"stderr": "", "returncode": None, "memo": "hit"}; it is never served to a longer (or no) timeout and never as a success. A stored
draw is consumed iff a charged request was answered with it (the owner if charged; else the charged joiner that claimed the compile,
when the in-flight join rule gave it the timeout). Crashes stay unstored; the in-flight join rules are unchanged; repeat draws take
a per-key index that only increases (stored timeouts and crashed repeats included). Stats: to_stored, to_hit_charged, to_hit_spec,
to_skipped_longer (requests that passed over an eligible timed-out draw shorter than their own timeout; once per request).

--hold-timeouts (OFF by default; off = no request is ever held): a CHARGED request (pri[0] == 0) with a timeout T whose answer is a
timeout (a stored timed-out draw, a draw longer than T, a joined timeout, a fresh compile) is answered no sooner than T seconds after
it arrived, which is the wall time a fresh compile that times out takes. The uploaded code reads wall time around timed-out compiles
(e.g. hintgrind's PROBE_WALL_S: no probe file starts after 600 s of probing), so a timeout answered at once would let it start work a
real run does not start. Successful answers and speculative requests are never held. Stats: held, held_ms.

--ahead-draws (POST-HOC 2026-11-05, v7/specnext; OFF by default; off = no request is handled differently, the "ahead" field is
ignored): a SPECULATIVE request with {"ahead": n} (n >= 1) asks for the n-th draw the charged path will take next: the n-th
unconsumed draw of its key that fits its timeout (the order charged requests take draws in), compiled as a repeat draw (unconsumed,
the same owner / join / store rules as any compile: a charged request may join it and then consumes it) while fewer exist; the
answer is that draw (as_answer; a stored timed-out draw as the timeout answer) with "ahead": n, and the asker never consumes it.
Ahead requests of one key run one at a time; at most n + 2 compiles per request, and a compile that is not stored (a crash, or a
timeout without --store-timeouts) ends it with "ahead": 0. pf_worker (6) uses it for the paired re-reading (c2, i2) and for the
next CLI pass's r0. Stats: ahead_hit, ahead_compile, ahead_wait, ahead_unstored.

Termination (always on; it changes nothing while the service runs): every running fresh compile is registered, and on SIGTERM /
SIGINT (run_full.sh's `kill` after END) the service SIGKILLs each compile's process group and the backend's servers (its shutdown(),
if it has one), launches nothing more, and exits. Before, its compiles (own sessions, timeout enforced only by the service) outlived
it, e.g. the charged compiles of workers stopped by pf_drive --cap.
"""
from __future__ import annotations

import argparse, hashlib, heapq, importlib.util, json, os, select, signal, socket, socketserver, subprocess, sys, threading, time
from collections import Counter

ap = argparse.ArgumentParser()
ap.add_argument("--sock", required=True)
ap.add_argument("--slots", type=int, default=40)
ap.add_argument("--log", required=True)
ap.add_argument("--min-free-gb", type=float, default=24.0)
ap.add_argument("--backend", default=None, help="python file with run(req) -> result dict or None")
ap.add_argument("--memo-in", default=None, help="(unused by default) a memo file to preload")
ap.add_argument("--store-timeouts", action="store_true",
                help="store timed-out compiles as draws (served only to requests whose timeout is <= the draw's); default off")
ap.add_argument("--hold-timeouts", action="store_true",
                help="answer a charged request's timeout no sooner than its timeout after it arrived (a fresh compile's wall); default off")
ap.add_argument("--ahead-draws", action="store_true",
                help="(POST-HOC v7/specnext) serve speculative {'ahead': n} requests: the n-th unconsumed draw; default off")
a = ap.parse_args()
import resource   # one socket + one handler thread per outstanding request (speculation included): lift the soft fd limit (1024 on the VMs)
_soft, _hard = resource.getrlimit(resource.RLIMIT_NOFILE)
resource.setrlimit(resource.RLIMIT_NOFILE, (_hard, _hard))

T0 = time.time()
LOGF = open(a.log, "a")
LL = threading.Lock()


def log(m):
    with LL:
        LOGF.write(f"[{time.strftime('%H:%M:%S', time.gmtime())} +{time.time() - T0:7.1f}s] {m}\n"); LOGF.flush()


STATS = Counter()
SL = threading.Lock()


def stat(k, n=1):
    with SL:
        STATS[k] += n


class Ticket:
    __slots__ = ("ev", "granted", "pri", "want")

    def __init__(self):
        self.ev, self.granted, self.pri, self.want = threading.Event(), False, None, None


class Gate:
    """Priority slots. A ticket can be promoted (an on-path request waits on a speculative compile of the same key): before it queues,
    the better priority is remembered (sticky) and used when it queues; once queued, the better priority is pushed again and the stale
    heap entry is skipped when popped."""
    def __init__(self, n):
        self.n, self.busy, self.lock, self.heap, self.seq, self.waiting = n, 0, threading.Lock(), [], 0, 0

    def acquire(self, pri, t: Ticket):
        with self.lock:
            pri = tuple(pri) if t.want is None else min(tuple(pri), t.want)
            if self.busy < self.n and not self.waiting:
                self.busy += 1; t.granted = True
                return
            t.pri = pri; self.seq += 1; self.waiting += 1
            heapq.heappush(self.heap, (t.pri, self.seq, t))
        t.ev.wait()

    def promote(self, t: Ticket, pri) -> bool:
        with self.lock:
            pri = tuple(pri)
            if t.granted:
                return False
            if t.pri is None:   # not queued yet: sticky
                t.want = pri if t.want is None else min(t.want, pri)
                return True
            if pri >= t.pri:
                return False
            t.pri = pri; self.seq += 1
            heapq.heappush(self.heap, (t.pri, self.seq, t))
            return True

    def release(self):
        with self.lock:
            while self.heap:
                t = heapq.heappop(self.heap)[2]
                if t.granted:
                    continue
                t.granted = True; self.waiting -= 1; t.ev.set()
                return
            self.busy -= 1


GATE = Gate(a.slots)
MEMO: dict = {}
INFL: dict = {}
HW: dict = {}   # --store-timeouts: per key, the highest draw index handed to a compile so far (0 = the first, plain compile)
ML = threading.Lock()
LIVE: set = set()             # running fresh-compile processes (the termination handler kills their process groups)
LIVE_LK = threading.Lock()    # held around each launch, so a launch never slips past the termination handler
STOPPING = threading.Event()
BACKEND = None
if a.backend:
    spec = importlib.util.spec_from_file_location("pf_backend", a.backend)
    BACKEND = importlib.util.module_from_spec(spec); spec.loader.exec_module(BACKEND)
    log(f"backend loaded: {a.backend}")


def mem_free_gb() -> float:
    with open("/proc/meminfo") as f:
        for line in f:
            if line.startswith("MemAvailable:"):
                return int(line.split()[1]) / 1048576.0
    return 0.0


def key_of(req) -> str:
    cmd = list(req["cmd"]); cmd[req["file_index"]] = "<FILE>"
    env = req.get("env") or {}
    raw = json.dumps([cmd, req.get("cwd") if req.get("lake") else "", env.get("LEAN_PATH", ""), env.get("LEAN_SYSROOT", ""),
                      hashlib.sha256(req["content"].encode()).hexdigest()])
    return hashlib.sha256(raw.encode()).hexdigest()


def run_fresh(req, use_backend=True) -> dict:
    waited = 0.0
    while mem_free_gb() < a.min_free_gb and waited < 600:
        time.sleep(2); waited += 2
    if waited:
        stat("mem_wait_s", int(waited))
    if BACKEND is not None and use_backend:
        try:
            r = BACKEND.run(req)
            if r is not None:
                stat("backend")
                return r
        except Exception as e:  # noqa: BLE001  (the fresh compile is the fallback)
            stat("backend_error")
            log(f"backend error: {type(e).__name__}: {str(e)[:200]}")
    with LIVE_LK:
        if STOPPING.is_set():   # the service is terminating: no new process (the answer is a crash: never stored)
            return {"stdout": "", "stderr": "compile service stopping", "returncode": None, "seconds": 0.0, "timed_out": False}
        t0 = time.monotonic()
        proc = subprocess.Popen(req["cmd"], cwd=req.get("cwd"), env=req.get("env"), stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                text=True, start_new_session=True)
        LIVE.add(proc)
    try:
        with proc:
            try:
                out, err = proc.communicate(timeout=req.get("timeout"))
            except subprocess.TimeoutExpired:
                try:
                    os.killpg(proc.pid, signal.SIGKILL)   # lake env lean: the lean child too
                except ProcessLookupError:
                    pass
                proc.communicate()
                return {"timed_out": True, "seconds": time.monotonic() - t0, "stdout": "", "stderr": "", "returncode": None}
        return {"stdout": out, "stderr": err, "returncode": proc.returncode, "seconds": time.monotonic() - t0, "timed_out": False}
    finally:
        with LIVE_LK:
            LIVE.discard(proc)


def memoizable(r) -> bool:
    """Only complete, ordinary Lean exits are reused (0 = clean, 1 = errors); a timeout or a crash is load-dependent, never reused."""
    return not r.get("timed_out") and r.get("returncode") in (0, 1)


def timeout_answer(to, how) -> dict:
    """The service's answer 'this compile times out at the request's timeout' (no compile ran for this request)."""
    return {"timed_out": True, "seconds": float(to), "stdout": "", "stderr": "", "returncode": None, "memo": how}


def as_answer(r, to, how) -> dict:
    """A draw as the request sees it: longer than the request's timeout -> a timeout (the same rule for hits and misses)."""
    if not r.get("timed_out") and to is not None and float(r["seconds"]) > float(to):
        stat(f"{how}_over_timeout")
        return timeout_answer(to, how)
    return dict(r, memo=how)


def fits(d, to) -> bool:
    """--store-timeouts: may draw d answer a request with timeout `to`? A timed-out draw (ran its T = d["to"] seconds unfinished) only
    for a set timeout <= T; a successful draw always (as_answer turns one longer than `to` into a timeout)."""
    if not d["r"].get("timed_out"):
        return True
    return to is not None and d.get("to") is not None and float(to) <= float(d["to"])


def pick(draws, to, charged):
    """--store-timeouts: the draw a request takes (caller holds ML): charged = the FIRST unconsumed fitting draw in creation order,
    speculative = the LATEST fitting draw. -> (draw or None, whether an eligible timed-out draw was passed over as too short)."""
    skipped = False
    for d in (draws if charged else reversed(draws)):
        if charged and d["consumed"]:
            continue
        if fits(d, to):
            return d, skipped
        skipped = True
    return None, skipped


def took_timeout(inf, r) -> bool:
    """--store-timeouts: did a charged request get this timed-out compile as its answer? The owner if charged; else the charged joiner
    that claimed it, by the in-flight join rule (handle_run: owner's timeout >= its own and the seconds >= its own)."""
    if inf.get("owner_charged"):
        return True
    ct = inf.get("claim_to")
    return bool(inf["claimed"]) and ct is not None and inf["to"] is not None and float(inf["to"]) >= float(ct) \
        and float(r["seconds"]) >= float(ct)


def peer_closed(conn) -> bool:
    if conn is None:
        return False
    try:
        # selfix (POST-HOC 2026-11-05): poll(), not select() (select() raises ValueError for fd >= 1024; 448 handler errors on 1 host)
        po = select.poll()
        po.register(conn.fileno(), select.POLLIN | select.POLLHUP | select.POLLERR)
        rd = po.poll(0)
        return bool(rd) and conn.recv(1, socket.MSG_PEEK | socket.MSG_DONTWAIT) == b""
    except (BlockingIOError, InterruptedError):
        return False
    except OSError:
        return True


AHEAD_LKS: dict = {}   # --ahead-draws: one ahead request per key at a time


def handle_ahead(req, conn=None):
    """--ahead-draws (module docstring): the n-th unconsumed fitting draw of the key, compiled while fewer exist; never consumed here."""
    k = key_of(req)
    to = req.get("timeout")
    pri = tuple(req.get("pri") or (1, 0))
    n = max(1, int(req.get("ahead") or 1))
    with ML:
        lk = AHEAD_LKS.setdefault(k, threading.Lock())
    with lk:
        for _ in range(n + 3):
            with ML:
                draws = MEMO.get(k) or []
                unc = [d for d in draws if not d["consumed"] and (fits(d, to) if a.store_timeouts else True)]
                if len(unc) >= n:
                    d = unc[n - 1]
                    stat("ahead_hit")
                    out = timeout_answer(to, "ahead") if d["r"].get("timed_out") else as_answer(d["r"], to, "ahead")
                    return dict(out, ahead=n)
                inf = INFL.get(k)
                if inf is None:   # our own compile, registered in flight: a charged request for the key joins (and claims) it
                    inf = INFL[k] = {"done": threading.Event(), "ticket": Ticket(), "claimed": False, "to": to, "res": None, "waiters": 0,
                                     "owner_charged": False, "claim_to": None}
                    mine, repeat, ndraw = True, bool(draws), len(draws)
                    if a.store_timeouts and repeat:
                        ndraw = max(ndraw, HW.get(k, 0) + 1)
                        HW[k] = ndraw
                else:
                    inf["waiters"] += 1
                    mine = False
            if not mine:   # someone's compile of the key is running: its draw first (consumed if a charged request claimed it)
                stat("ahead_wait")
                inf["done"].wait()
                with ML:
                    inf["waiters"] -= 1
                continue
            try:
                GATE.acquire(pri, inf["ticket"])
                try:
                    with ML:
                        idle = not inf["claimed"] and inf["waiters"] == 0
                    if idle and peer_closed(conn):
                        stat("dropped_orphan")
                        return None
                    r = run_fresh(dict(req, draw=ndraw) if repeat else req)
                finally:
                    GATE.release()
                r["timeout"] = to
                stored = True
                if memoizable(r):
                    with ML:
                        MEMO.setdefault(k, []).append({"r": r, "consumed": bool(inf["claimed"])})
                elif a.store_timeouts and r.get("timed_out") and to is not None:
                    with ML:
                        MEMO.setdefault(k, []).append({"r": dict(r, seconds=float(to), measured_s=r.get("seconds")), "to": float(to),
                                                       "consumed": took_timeout(inf, r)})
                    stat("to_stored")
                else:
                    stat("not_memoized"); stored = False
                inf["res"] = r
                stat("compile"); stat("compile_s", int(r["seconds"])); stat("ahead_compile")
                if repeat:
                    stat("fresh_draw")
                if not stored:
                    stat("ahead_unstored")
                    return dict(as_answer(r, to, "miss"), ahead=0)
            finally:
                with ML:
                    if INFL.get(k) is inf:
                        INFL.pop(k, None)
                inf["done"].set()
    stat("ahead_unstored")
    return {"timed_out": False, "stdout": "", "stderr": "ahead: no draw", "returncode": None, "seconds": 0.0, "memo": "ahead", "ahead": 0}


def handle_run(req, conn=None):
    if a.ahead_draws and req.get("ahead") and tuple(req.get("pri") or (0, 0))[0] != 0:
        return handle_ahead(req, conn)
    k = key_of(req)
    to = req.get("timeout")
    pri = tuple(req.get("pri") or (0, 0))
    charged = pri[0] == 0
    skip_counted = False
    while True:
        with ML:
            draws = MEMO.get(k) or []
            if a.store_timeouts:
                d, skipped = pick(draws, to, charged)
                if skipped and not skip_counted:
                    skip_counted = True
                    stat("to_skipped_longer")
                if d is not None:
                    if charged:
                        d["consumed"] = True
                    if d["r"].get("timed_out"):
                        stat("to_hit_charged" if charged else "to_hit_spec")
                        return timeout_answer(to, "hit")
                    stat("hit" if charged else "spec_hit")
                    return as_answer(d["r"], to, "hit")
            elif charged:
                d = next((d for d in draws if not d["consumed"]), None)
                if d is not None:
                    d["consumed"] = True
                    stat("hit")
                    return as_answer(d["r"], to, "hit")
            elif draws:
                stat("spec_hit")
                return as_answer(draws[-1]["r"], to, "hit")
            inf = INFL.get(k)
            if inf is None:
                inf = INFL[k] = {"done": threading.Event(), "ticket": Ticket(), "claimed": charged, "to": to, "res": None, "waiters": 0,
                                 "owner_charged": charged, "claim_to": to if charged else None}
                mine, repeat, ndraw = True, charged and bool(draws), len(draws)
            elif charged and inf["claimed"]:
                inf, mine, repeat, ndraw = None, True, True, len(draws) + 1   # the in-flight draw is someone else's: our own fresh draw
            else:
                if charged:
                    inf["claimed"] = True
                    inf["claim_to"] = to
                inf["waiters"] += 1
                mine, repeat, ndraw = False, False, 0
            if a.store_timeouts and mine and repeat:   # a repeat draw's index only increases (concurrent / crashed repeats included)
                ndraw = max(ndraw, HW.get(k, 0) + 1)
                HW[k] = ndraw
        if not mine:
            stat("wait")
            if charged and GATE.promote(inf["ticket"], pri):
                stat("promoted")
            inf["done"].wait()
            with ML:
                inf["waiters"] -= 1
            if charged:
                r = inf["res"]
                if r is None:          # the owner failed or dropped: start over
                    continue
                if r.get("timed_out"):
                    if inf["to"] is not None and to is not None and float(inf["to"]) >= float(to) and float(r["seconds"]) >= float(to):
                        stat("joined_timeout")
                        return {"timed_out": True, "seconds": float(to), "stdout": "", "stderr": "", "returncode": None, "memo": "joined"}
                    continue           # a shorter timeout than ours ran out: compile again
                stat("joined")
                return as_answer(r, to, "joined")
            continue                   # speculative: the draw is in the memo now (or start over)
        own = inf if inf is not None else {"done": threading.Event(), "ticket": Ticket(), "claimed": True, "to": to, "res": None, "waiters": 0,
                                           "owner_charged": True, "claim_to": to}
        try:
            GATE.acquire(pri, own["ticket"])
            try:
                if not charged and inf is not None:
                    with ML:
                        idle = not own["claimed"] and own["waiters"] == 0
                    if idle and peer_closed(conn):
                        stat("dropped_orphan")
                        return None
                r = run_fresh(dict(req, draw=ndraw) if repeat else req)
            finally:
                GATE.release()
            r["timeout"] = to
            if memoizable(r):
                with ML:
                    MEMO.setdefault(k, []).append({"r": r, "consumed": bool(own["claimed"])})
            elif a.store_timeouts and r.get("timed_out") and to is not None:   # proves: this compile needs more than T = to
                with ML:
                    MEMO.setdefault(k, []).append({"r": dict(r, seconds=float(to), measured_s=r.get("seconds")), "to": float(to),
                                                   "consumed": took_timeout(own, r)})
                stat("to_stored")
            else:
                stat("not_memoized")
            own["res"] = r
            stat("compile"); stat("compile_s", int(r["seconds"]))
            if repeat:
                stat("fresh_draw")
            return as_answer(r, to, "miss")
        finally:
            if inf is not None:
                with ML:
                    if INFL.get(k) is inf:
                        INFL.pop(k, None)
                inf["done"].set()


def hold(req, out, t_arr) -> None:
    """--hold-timeouts: a charged request answered as a timeout waits until its timeout has passed since it arrived (module docstring)."""
    to = req.get("timeout")
    if not out.get("timed_out") or to is None or tuple(req.get("pri") or (0, 0))[0] != 0:
        return
    wait = t_arr + float(to) - time.monotonic()
    if wait > 0:
        stat("held"); stat("held_ms", int(wait * 1000))
        time.sleep(wait)


class H(socketserver.StreamRequestHandler):
    def handle(self):
        t_arr = time.monotonic()   # the request's arrival (--hold-timeouts)
        try:
            req = json.loads(self.rfile.readline())
            if req.get("op") == "stats":
                with SL:
                    out = dict(STATS)
                out.update(memo=len(MEMO), draws=sum(len(v) for v in list(MEMO.values())), busy=GATE.busy, queued=GATE.waiting, mem_free_gb=round(mem_free_gb(), 1),
                           up_s=round(time.time() - T0, 1))
                if a.store_timeouts:
                    with ML:
                        out["to_draws"] = sum(1 for v in MEMO.values() for d in v if d["r"].get("timed_out"))
            else:
                out = handle_run(req, self.connection)
                if out is None:   # dropped: the client is gone
                    return
                if a.hold_timeouts:
                    hold(req, out, t_arr)
            self.wfile.write((json.dumps(out) + "\n").encode())
        except Exception as e:  # noqa: BLE001
            stat("handler_error")
            log(f"handler error: {type(e).__name__}: {str(e)[:300]}")
            try:
                self.wfile.write((json.dumps({"error": f"{type(e).__name__}: {e}"}) + "\n").encode())
            except Exception:  # noqa: BLE001
                pass


class S(socketserver.ThreadingMixIn, socketserver.UnixStreamServer):
    daemon_threads = True
    request_queue_size = 512


if os.path.exists(a.sock):
    os.unlink(a.sock)
srv = S(a.sock, H)
log(f"service up: slots {a.slots}, min free {a.min_free_gb} GB, sock {a.sock}" + (", store timeouts" if a.store_timeouts else "")
    + (", hold timeouts" if a.hold_timeouts else ""))


def terminate(signum, _frame):
    """SIGTERM / SIGINT (module docstring): kill every running compile's process group and the backend's servers, then exit. Runs in
    the main thread (serve_forever), which never holds LIVE_LK or LL; a launch in progress finishes registering first."""
    n = 0
    with LIVE_LK:
        STOPPING.set()
        for proc in list(LIVE):
            try:
                os.killpg(proc.pid, signal.SIGKILL)
                n += 1
            except (ProcessLookupError, PermissionError):
                pass
    nb, berr = 0, ""
    if BACKEND is not None and callable(getattr(BACKEND, "shutdown", None)):
        try:
            nb = int(BACKEND.shutdown() or 0)
        except Exception as e:  # noqa: BLE001
            berr = f" (backend shutdown error: {type(e).__name__}: {str(e)[:200]})"
    try:
        log(f"service stopped by signal {signum}: killed {n} running compile(s), {nb} backend server(s){berr}")
    finally:
        os._exit(0)


signal.signal(signal.SIGTERM, terminate)
signal.signal(signal.SIGINT, terminate)


def ticker():
    while True:
        time.sleep(60)
        with SL:
            s = dict(STATS)
        log(f"stats {json.dumps(s)} memo {len(MEMO)} busy {GATE.busy} queued {GATE.waiting} free {mem_free_gb():.0f} GB")


threading.Thread(target=ticker, daemon=True).start()
srv.serve_forever()
