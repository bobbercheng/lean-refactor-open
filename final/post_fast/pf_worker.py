#!/usr/bin/env python3
"""postfast worker v2 (post-hoc measurement, 2026-11-05): runs the UNMODIFIED open_post.py CLI of the uploaded code (a25416f5) for one
row and one pass (`--problems <row>`, the pass's own flags). The charged search path is the original code, sequential and in ORDER:
open_post.generate, improve_row's reads, pins, paired re-reading and audit all run exactly as written. Execution-only changes:
  1. every Lean launch goes to the host's compile service (pf_svc.py: exact memo, class-first priority slots); a hit carries the original
     compile seconds, so the code's time-dependent inputs read the same compile time as on the first compile;
  2. SPECULATION, never charged and isolated: while the original generate() runs the ops one after another, each op's generator also runs
     in its own thread against an uncharged run() and a separate Evaluator, with every op-module memory (module-level dicts / sets) scoped
     to the speculative threads; its compiles land in the service memo, so the original sequential generate() mostly finds its compiles
     done. Likewise the reads a pass will take (improve_row's own filters), a full measurement's other pins, a candidate's pins and its
     sorry-audit compiles are warmed in parallel. Speculation never touches the charged meter, the real Evaluator or the real op memories;
  3. Evaluator._run takes the calling thread's timeout (not the shared Evaluator.timeout).
Optional, OFF by default (unset = the behaviour above exactly; fullA / fullB ran without them):
  4. ADOPTION SIDE LOG (env PF_ADOPT_LOG=<file>, PF_PASS=<CLI pass number>): logging only. The audit open_post.default_audit() returns
     is wrapped (as for audit_warm); after the real audit returns, one JSON line is appended to PF_ADOPT_LOG (thread lock + flock, one
     open / append / close per line): {t, row, pass_cli, audit, why, decl, pid, w0} and, read from the calling improve_row frame (its
     locals are only read), {pass_inner, op, score, tokens, heartbeats, inc_score, before}. improve_row (a25416f5) audits a candidate
     only after its pins, the paired re-reading and the stored-score floor passed, and adopts it iff the audit status is "clean" or
     "skipped" (the `pass k adopted <op> (a -> b)` line follows at once); a "sorry" / "unknown" audit rejects it and the next candidate
     may be audited. So audits are NOT one-to-one with adoptions: the records with audit in {clean, skipped} are, in order, per row and
     CLI pass (snapshot.py --adopt-dir pairs them with the log lines). A raising audit is recorded as audit "raised" (then re-raised).
  5. HINTGRIND SHADOW LOOKAHEAD (env PF_HG_LOOKAHEAD=1; hg_shadow_start below): speculation only. hintgrind sends its probe files one
     after another and file k+1 depends on file k's outcome; the shadow runs the uploaded hintgrind.query once more per round, in the
     speculative scope with a private memory overlay, with a run() that compiles Query A for real (speculatively, waiting) and answers
     every probe file as a service TIMEOUT at once while the real compile is sent fire-and-forget (kept connected until answered), so
     the query's own all-timeout branch emits the files the charged path sends when every earlier file times out. A fired file's
     scratch file is deleted by its sender only after the service answered (the service compiles that path later; a charged request
     for the same text may join that compile). The shadow fires only the files the charged loop can start within hintgrind's
     PROBE_WALL_S (hg_wall_files: ceil(PROBE_WALL_S / T) for probe timeout T), never more than MAX_FILES.
     DECISIONS: the shadow's timed-out files reach the charged loop sooner than T after it asks (it joins a compile that started
     earlier, or a stored timeout with pf_svc --store-timeouts), so its PROBE_WALL_S clock would see less time than a fresh compile
     gives and it could start more files than the uploaded code does. Run it with pf_svc --hold-timeouts (a charged timeout answer
     is never sent sooner than T after the request arrived) when decisions must match; without it, PROBE_WALL_S outcomes can differ.
  6. SPECULATIVE NEXT ROUND (POST-HOC 2026-11-05, v7/specnext; env PF_SPEC_NEXT=k, unset / "0" = off; "" or "1" = k 1): speculation
     only. improve_row confirms its best reading (pins, paired re-reading, stored-score floor, audit) before the next round's
     generate() starts on the adopted proof. When the CHARGED path calls meter.pins(decl) from improve_row (the confirmation's first
     step), the pins wrapper reads the improve_row frame (read only) and starts a speculative BRANCH for each of the top-k provisional
     winners from the current one on (the frame's `reads`, in improve_row's own sorted order): round k+1's per-op generate parts on
     that candidate (the a25416f5 generate() split into parts that run in parallel, in its ORDER, with its lane reserve rule), each
     part's reads warmed as soon as its candidates exist (improve_row's own filters, READS, timeout). A within-pass branch runs with a
     private DEEP COPY of the real op memories taken at the hook (the confirmation never touches op memories, so this is the state
     the charged round k+1 starts with); it is abandoned if the charged path enters generate() before the copy is done.
     inc_hb: the next round's inc_hb is int(max-hb reading of rd and the paired re-reading c2). c2 is a later DRAW of the candidate's
     primary compile: under pf_svc's draw semantics a speculative request never creates a second draw, so (base service) the branch
     starts with rd's heartbeats and, when the charged c2 returns (the measure wrapper sees the confirming decl), the exact value is
     computed as improve_row does; a branch with another inc_hb is restarted (an unreadable c2 cancels the branch: the charged path
     rejects the candidate). PF_SPEC_NEXT_AHEAD=1 (needs this directory's pf_svc --ahead-draws): at the hook the branch also asks the
     service for the draws the charged path will take next ({"ahead": n}: the n-th unconsumed draw, compiled if missing, never
     consumed by the asker): c2 of every branch candidate and i2 (the incumbent's re-reading) of the current one, and warms the
     current candidate's audit; the c2 draw gives the exact inc_hb early. A service without the extension answers with the latest
     draw and no "ahead" marker: the branch then keeps rd's value (counted as sn_ahead_unsupported).
     Cancellation: a branch ends when the charged path calls pins for a candidate outside the branch's top-k window (the earlier one
     was rejected), when it enters generate() on another proof, when the charged generate() it ran ahead of returns (the base
     speculation and read warm-up take over), when its c2 does not read, or at process exit (as every speculation).
     Last inner round (pas == PASSES): the next round is the next CLI pass (a new process). Only with PF_NEXT_OPS=<kind>:<row_s>:<s>
     (pf_drive --next-ops sets it: the next pass's kind v3 | v4 | L and walls): a CROSS branch runs that pass's ORDER with EMPTY op
     memories (a fresh process), its lane reserve (--long for L) and a row wall of row_s; its inc_hb / compile_s are the next pass's
     r0 reading (a later draw): estimated from rd (heartbeats, seconds), exact with PF_SPEC_NEXT_AHEAD (draw n = 2: after c2).
     When the charged generate() starts on a branch's proof with the branch's inc_hb (a confirmed branch whose memories are copied),
     generate() skips its own per-op speculation for that round (the branch runs the same ops, with the exact memories; counted
     sn_base_skipped); any other branch state: the base speculation runs, but after a skipped round its scoped op memories lag the
     charged ones, so it can speculate texts the charged path never asks for (performance only; review 2026-11-05). The charged c2
     decides the branch's inc_hb; a later ahead answer never overrides it. Branch work runs on its own executor.
     PF_SPEC_NEXT_MAXQ=N (optional): a branch does not start while the service has more than N queued compiles.
     Speculation never touches the charged meter, the real Evaluator or the real op memories, never raises into the charged path.
     Not implemented: PF_SPEC_NEXT_DEPTH (round k+2): it would need the branch to predict its own confirmation; left out.
  7. MERGED-CANDIDATE WARM-UP (POST-HOC 2026-11-05, v7/merge/merge_warm.py next to this file; on exactly when the decision code's
     LRA_POST_MERGE=1, i.e. with the v7m open_post.py): after the read warm-up, merge_warm.warm_merge computes improve_row's merged
     text from the warmed readings (the decision code's own merge_candidate) and warms its primary reading, other pins and audit
     speculatively. Speculation only (one task; never raises; never charged). Its stats print at exit ("merge warm").
Usage: PF_SOCK=... PF_CODE=... PF_PRI=<row weight> python3 pf_worker.py <open_post.py arguments>
"""
from __future__ import annotations

import collections, copy, fcntl, importlib, json, math, os, re, socket, subprocess, sys, threading, time, types, uuid
from concurrent.futures import ThreadPoolExecutor

CODE = os.environ["PF_CODE"]
SOCK = os.environ["PF_SOCK"]
PRI = float(os.environ.get("PF_PRI", "0"))
sys.path.insert(0, CODE)
TL = threading.local()
NOSPEC = os.environ.get("PF_NOSPEC") == "1"   # control runs: no speculation at all (only the compile service)
ADOPT_LOG = os.environ.get("PF_ADOPT_LOG") or None   # (4) adoption side log; unset = off
HG_LOOKAHEAD = os.environ.get("PF_HG_LOOKAHEAD") == "1"   # (5) hintgrind shadow lookahead; default off
HG_FF_SEND_WAIT_S = 30.0   # a shadow launch waits (at most this long) until its request is written, so launches reach the service in order
WORKER_T0 = time.time()


def _spec_next_k(v):
    """(6) PF_SPEC_NEXT: unset or "0" -> 0 (off); "" or not a number -> 1; else the number."""
    if v is None:
        return 0
    v = v.strip()
    if not v:
        return 1
    try:
        return max(0, int(v))
    except ValueError:
        return 1


SPEC_NEXT = _spec_next_k(os.environ.get("PF_SPEC_NEXT"))   # (6) speculative next round; 0 = off
MERGE_WARM = os.environ.get("LRA_POST_MERGE") == "1"   # (7) v7m merged-candidate warm-up (merge_warm.py); follows the decision flag
SPEC_NEXT_AHEAD = SPEC_NEXT > 0 and os.environ.get("PF_SPEC_NEXT_AHEAD") == "1"
NEXT_OPS = (os.environ.get("PF_NEXT_OPS") or None) if SPEC_NEXT else None
SPEC_NEXT_MAXQ = os.environ.get("PF_SPEC_NEXT_MAXQ") if SPEC_NEXT else None


def is_spec() -> bool:
    return bool(getattr(TL, "spec", False))


def _pri():
    return [1 if is_spec() else 0, -PRI]


SPEC_INFLIGHT = threading.BoundedSemaphore(int(os.environ.get("PF_SPEC_INFLIGHT", "24")))   # speculative RPCs open at once per worker


def _rpc_once(req: dict, on_sent=None) -> dict:
    s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
    try:
        s.connect(SOCK)
        f = s.makefile("rwb")
        f.write((json.dumps(req) + "\n").encode()); f.flush()
        if on_sent is not None:   # (5) a shadow launch: written; the caller goes on, this thread waits for the answer
            on_sent()
        line = f.readline()
    finally:
        s.close()
    if not line:
        raise ConnectionError("service closed the connection")
    out = json.loads(line)
    if "error" in out:
        raise ConnectionError(f"service error: {out['error']}")
    return out


def rpc(req: dict) -> dict:
    """Speculative: one bounded try (a failure only loses the warm-up). Charged: a service failure is never a compile result; retry with
    backoff for up to ~10 min, then end the worker (exit 3): pf_drive records worker_failed and the pass's input stands."""
    if is_spec():
        with SPEC_INFLIGHT:
            return _rpc_once(req)
    delay, t0 = 1.0, time.monotonic()
    while True:
        try:
            return _rpc_once(req)
        except (ConnectionError, FileNotFoundError, OSError, json.JSONDecodeError) as e:
            if time.monotonic() - t0 > 600:
                print(f"[pf_worker] compile service unusable for 600 s on the charged path ({type(e).__name__}: {e}); ending the worker",
                      flush=True)
                sys.stdout.flush(); sys.stderr.flush()
                os._exit(3)
            time.sleep(delay); delay = min(delay * 2, 30.0)


def rpc_run_lean(cmd, cwd=None, env=None, capture_output=True, text=True, timeout=None, **kw):
    """Drop-in for scorer.memgate.run_lean: the host's service runs the exact command; raises TimeoutExpired like it."""
    cmd = [str(c) for c in cmd]
    fi = max(i for i, c in enumerate(cmd) if c.endswith(".lean"))
    path = cmd[fi] if os.path.isabs(cmd[fi]) else os.path.join(str(cwd or os.getcwd()), cmd[fi])
    with open(path) as fh:
        content = fh.read()
    req = {"op": "run", "cmd": cmd, "file_index": fi, "cwd": str(cwd) if cwd else os.getcwd(), "env": dict(env or os.environ),
           "content": content, "timeout": timeout, "pri": _pri(), "lake": os.path.basename(cmd[0]) == "lake"}
    sn_ahead = SPEC_NEXT_AHEAD and is_spec() and int(getattr(TL, "sn_ahead", 0) or 0)
    if sn_ahead:   # (6) the n-th draw the charged path will take next (pf_svc --ahead-draws); speculative only
        req["ahead"] = sn_ahead
    if HG_LOOKAHEAD and getattr(TL, "hg_ff", False) and is_spec():
        r = hg_fire(req, timeout)   # (5) a shadow's probe file: sent fire-and-forget, answered here as a service timeout
    else:
        r = rpc(req)
    if sn_ahead:
        TL.sn_ahead_ok = bool(r.get("ahead"))
    if r.get("timed_out"):
        raise subprocess.TimeoutExpired(cmd, timeout)
    cp = subprocess.CompletedProcess(cmd, r["returncode"], r["stdout"], r["stderr"])
    cp.pf_seconds = r.get("seconds")
    return cp


import scorer.memgate as MG   # noqa: E402
MG.run_lean = rpc_run_lean
from scorer import compile as C   # noqa: E402
C.run_lean = rpc_run_lean
from harness import hb_tool_eval as HE   # noqa: E402
from harness import endstage as ES   # noqa: E402
from harness import open_post as P   # noqa: E402
from harness import open_package as OPK   # noqa: E402
try:
    from harness import lean_untrunc as LU   # noqa: E402
    LU.run_lean = rpc_run_lean
except Exception:  # noqa: BLE001
    pass

_ORIG_GENERATE = P.generate
SPEC = ThreadPoolExecutor(96, thread_name_prefix="spec")
CL = threading.Lock()
STATS = {"spec_tasks": 0, "spec_errors": 0, "spec_cancelled": 0}
if HG_LOOKAHEAD:   # only with the option on: the default run's final stats line stays as it was
    STATS.update(hg_shadow_runs=0, hg_shadow_files=0, hg_shadow_errors=0, hg_shadow_wall_stops=0)


def bound_spec(fn):
    """fn in a speculative thread (TL.spec): errors and budget stops are swallowed."""
    def w():
        TL.spec = True
        try:
            fn()
        except P._Stop:
            STATS["spec_cancelled"] += 1
        except Exception:  # noqa: BLE001
            STATS["spec_errors"] += 1
        finally:
            TL.spec = False
    STATS["spec_tasks"] += 1
    return SPEC.submit(w)


# ------------------------------------------------------------------------------------------------ op-module memories: speculative scope
def _fresh_like(x):
    """An empty container of x's kind (a defaultdict keeps its factory)."""
    if isinstance(x, collections.defaultdict):
        return collections.defaultdict(x.default_factory)
    try:
        return type(x)()
    except Exception:  # noqa: BLE001
        y = copy.copy(x); y.clear()
        return y


class SpecScoped:
    """A module-level container: the original object for the charged path, a separate one for speculative threads."""
    __slots__ = ("_real", "_spec", "_lk")

    def __init__(self, real):
        object.__setattr__(self, "_real", real)
        object.__setattr__(self, "_lk", threading.Lock())
        try:
            sp = type(real)()
        except Exception:  # noqa: BLE001  (e.g. defaultdict: copy then clear keeps the factory)
            sp = copy.copy(real); sp.clear()
        object.__setattr__(self, "_spec", sp)

    def _c(self):
        if not is_spec():
            return object.__getattribute__(self, "_real")
        ov = getattr(TL, "scope_over", None)
        if ov is None:
            return object.__getattribute__(self, "_spec")
        # (5) a speculative thread with a private overlay (the hintgrind shadow): a container of its own, created empty on first use
        c = ov.get(id(self))
        if c is None:
            c = ov[id(self)] = _fresh_like(object.__getattribute__(self, "_real"))   # its kind only (nothing is copied)
        return c

    def __getattr__(self, a):
        return getattr(self._c(), a)

    def __contains__(self, x):
        return x in self._c()

    def __getitem__(self, k):
        return self._c()[k]

    def __setitem__(self, k, v):
        self._c()[k] = v

    def __delitem__(self, k):
        del self._c()[k]

    def __iter__(self):
        return iter(list(self._c()))

    def __len__(self):
        return len(self._c())

    def __bool__(self):
        return bool(self._c())

    def __ior__(self, o):
        self._c().__ior__(o)
        return self

    def __repr__(self):
        return f"SpecScoped({self._c()!r})"


LAZY = ("harness.tools.t3_suggest", "harness.dialect", "harness.gap_rules", "harness.normalize", "harness.sweep", "harness.tools.golf_ops",
        "harness.tools.t1_compress", "harness.tools.t5_joint", "harness.tools.t4_nameless", "harness.dialect_unhyg", "harness.post.d4_measure",
        "harness.post.opus_hoist", "harness.post.opus_screen", "harness.post.t4ind")
SKIP_MODS = {"harness.open_post", "harness.endstage", "harness.hb_tool_eval", "harness.open_package"}


def scope_op_memories(order) -> int:
    """Import the pass's op modules (as the run would) and scope every empty module-level dict / set / list of harness modules."""
    P._mods()
    for mod in LAZY:   # modules the ops import inside functions (their memories scoped too)
        try:
            importlib.import_module(mod)
        except Exception:  # noqa: BLE001
            pass
    for n in order:
        try:
            P._op(n)
        except Exception:  # noqa: BLE001  (v1 ops live in the d4_* modules; a missing module is skipped)
            pass
    n = 0
    for name, m in list(sys.modules.items()):
        if not isinstance(m, types.ModuleType) or not name.startswith("harness") or name in SKIP_MODS:
            continue
        for k, v in list(vars(m).items()):
            if k.startswith("__") or isinstance(v, SpecScoped):
                continue
            if isinstance(v, (dict, set, list)) and len(v) == 0:
                setattr(m, k, SpecScoped(v)); n += 1
    return n


# ------------------------------------------------------------------------------------------------ Evaluator: per-thread timeout and count
_ev_init = HE.Evaluator.__init__


def _ev_init_patched(self, *a, **k):
    _ev_init(self, *a, **k)
    self._gate.run_lean = rpc_run_lean


HE.Evaluator.__init__ = _ev_init_patched


def _run(self, row, version, body, lean_args=(), first_line=1, quiet_prefix_sorry=False):
    binary, env = self._runtime(row, version)
    with self._count_lock:
        if self.compiles >= self.max_compiles:
            return C.CompileResult(False, None, 0, ["compile budget exhausted"])
        self.compiles += 1
    TL.phys = getattr(TL, "phys", 0) + 1
    to = getattr(TL, "ev_to", None) or self.timeout
    path = self.scratch / f"c_{uuid.uuid4().hex}.lean"
    path.write_text(body)
    start = time.monotonic()
    try:
        result = rpc_run_lean([str(binary), "--json", f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}", *lean_args, str(path)],
                              cwd=self.scratch, env=env, capture_output=True, text=True, timeout=to)
    except subprocess.TimeoutExpired:
        return C.CompileResult(False, None, time.monotonic() - start, ["timeout"], timed_out=True)
    finally:
        if getattr(TL, "hg_keep", None) == str(path):   # (5) a fired shadow probe file: its sender (hg_fire) deletes it once answered
            TL.hg_keep = None
        else:
            path.unlink(missing_ok=True)
    secs = getattr(result, "pf_seconds", None)
    secs = (time.monotonic() - start) if secs is None else float(secs)
    return C._parse(result, secs, first_line, sorry_blind=C._warn_sorry_off(lean_args), switch=C._sorry_switch(body, first_line),
                    quiet_prefix_sorry=quiet_prefix_sorry)


HE.Evaluator._run = _run


# ------------------------------------------------------------------------------------------------ Meter: thread-local timeout; speculation
def _to_eff(meter, to):
    return meter.timeout if not to else max(1, min(int(meter.timeout), int(math.ceil(float(to)))))


def _compile_with(ev, meter, decl, version, count, to_eff):
    prev = getattr(TL, "ev_to", None)
    TL.ev_to, TL.phys = to_eff, 0
    try:
        r = ev._compile(meter.row, decl, version, count=count)
    except Exception as e:  # noqa: BLE001  (fails closed, as Meter._one)
        r = C.CompileResult(False, None, 0.0, [f"environment: {type(e).__name__}: {e}"[:300]])
    finally:
        TL.ev_to = prev
    return r, TL.phys


def spec_ev(meter):
    """The meter's speculative Evaluator: same row, timeout and scratch as the real one, its own state (never the charged one)."""
    with CL:
        ev = getattr(meter, "_pf_spec_ev", None)
        if ev is None:
            ev = HE.Evaluator({meter.name: meter.row}, meter.heartbeats, max_compiles=1 << 30, timeout=meter.timeout,
                              scratch_root=meter.scratch)
            meter._pf_spec_ev = ev
    return ev


def warm(meter, decl, version, count, to):
    if NOSPEC:
        return
    to_eff = _to_eff(meter, to)
    bound_spec(lambda: _compile_with(spec_ev(meter), meter, decl, version, count, to_eff))


_orig_one = ES.Meter._one


def _one(self, decl, version, count, path):
    if path != "direct":
        return _orig_one(self, decl, version, count, path)
    to_eff = _to_eff(self, getattr(TL, "cand_to", None))
    if is_spec():   # a speculative op calling the meter (measure / pins / command): the spec Evaluator, never charged
        return _compile_with(spec_ev(self), self, decl, version, count, to_eff)
    r, n = _compile_with(self._evaluator(), self, decl, version, count, to_eff)
    with CL:
        self.compiles += n
    return r, n


class _cand:
    def __init__(self, t):
        self.t = t

    def __enter__(self):
        self.prev = getattr(TL, "cand_to", None); TL.cand_to = self.t

    def __exit__(self, *e):
        TL.cand_to = self.prev


def measure(self, decl, full=True, Z=None, timeout=None):
    decl = decl.strip()
    path = self.freeze()
    bad = self._check(decl)
    if bad:
        return {"ok": False, "error": bad, "compiles": 0, "meter": path}
    n = 0
    with _cand(timeout):
        if full and path == "direct":
            for v in self.versions[1:]:
                warm(self, decl, v, False, timeout)
        prim, k = self._one(decl, self.versions[0], True, path); n += k
        compat = None
        if full and prim.ok and prim.heartbeats is not None:
            compat = {self.versions[0]: True}
            for v in self.versions[1:]:
                r, k = self._one(decl, v, False, path); n += k
                compat[v] = bool(r.ok)
    out = self._reading(decl, prim, compat, Z, path, n)
    if SPEC_NEXT and not full and not is_spec():   # (6) the charged paired re-reading of a confirming candidate (never raises)
        sn_on_measure(decl, out)
    return out


def pins(self, decl, timeout=None):
    raw = decl
    decl = decl.strip()
    path = self.freeze()
    if SPEC_NEXT and not is_spec():   # (6) the charged confirmation starts: speculate the next round (never raises)
        sn_on_pins(self, decl, sys._getframe(1), timeout)
    n = 0
    compat = {self.versions[0]: True}
    with _cand(timeout):
        if path == "direct":
            for v in self.versions[1:]:
                warm(self, decl, v, False, timeout)
        for v in self.versions[1:]:
            r, k = self._one(decl, v, False, path); n += k
            compat[v] = bool(r.ok)
    return {"compat": compat, "compiles": n}


ES.Meter._one = _one
ES.Meter.measure = measure
ES.Meter.pins = pins


def make_meter(row, ref_hb, scratch, log_fn=None):
    class PostMeter(ES.Meter):
        def command(self, text, version=None, timeout=None):
            path = self.freeze()
            with _cand(timeout):
                return self._one(text, version or self.versions[0], False, path)
    m = PostMeter(row, ref_hb, prefer="direct", log=log_fn or (lambda *x: None))
    if scratch is not None:
        m.scratch = str(scratch)
    return m


P.make_meter = make_meter


def audit_warm(row, decl):
    if NOSPEC:
        return
    from probe.verify_candidates import newest_first
    for v in newest_first(row["version_info"]):
        bound_spec(lambda v=v: C.audit_axioms(row, decl, v, timeout=OPK.AUDIT_TIMEOUT_S))


_orig_default_audit = P.default_audit
_SL = threading.Lock()


def _stat(k, n=1):
    with _SL:
        STATS[k] = STATS.get(k, 0) + n


# (4) adoption side log (module docstring): logging only, never a different return value or exception
_ADOPT_LK = threading.Lock()
_FRAME_KEYS = (("pass_inner", "pas", None), ("op", "c", "op"), ("score", "mc", "score"), ("tokens", "mc", "tokens"),
               ("heartbeats", "mc", "heartbeats"), ("inc_score", "mi", "score"))


def _improve_row_facts(fr) -> dict:
    """The confirming candidate's facts from the calling improve_row frame (read only): inner pass, op, exact score, tokens and
    heartbeats of the reading the CLI keeps (inc["m"] after adoption), the paired incumbent score and the CLI pass's r0 score."""
    out = {}
    if fr is None or fr.f_code is not P.improve_row.__code__:
        return out
    loc = fr.f_locals
    for key, var, field in _FRAME_KEYS:
        try:
            v = loc[var]
            v = v if field is None else v[field]
            if isinstance(v, (int, float, str)) and not isinstance(v, bool):
                out[key] = v
        except Exception:  # noqa: BLE001
            pass
    try:
        out["before"] = float(loc["res"]["before"]["score"])
    except Exception:  # noqa: BLE001
        pass
    return out


def _append_line(path: str, rec: dict) -> None:
    data = (json.dumps(rec, ensure_ascii=False) + "\n").encode()
    with _ADOPT_LK:
        fd = os.open(path, os.O_WRONLY | os.O_APPEND | os.O_CREAT, 0o644)
        try:
            fcntl.flock(fd, fcntl.LOCK_EX)   # one file per host: every worker of the host appends to it
            try:
                view = memoryview(data)
                while view:
                    view = view[os.write(fd, view):]
            finally:
                fcntl.flock(fd, fcntl.LOCK_UN)
        finally:
            os.close(fd)


def adopt_log(row, decl, out, fr) -> None:
    try:
        st, why = (out[0], out[1]) if isinstance(out, tuple) and len(out) == 2 else (str(out), "")
        ps = os.environ.get("PF_PASS")
        try:
            pass_cli = int(ps) if ps is not None else None
        except ValueError:
            pass_cli = None
        rec = {"t": time.time(), "row": row.get("name"), "pass_cli": pass_cli, "audit": st, "why": str(why)[:300], "decl": decl,
               "pid": os.getpid(), "w0": WORKER_T0}
        rec.update(_improve_row_facts(fr))
        _append_line(ADOPT_LOG, rec)
    except Exception:  # noqa: BLE001  (logging only)
        _stat("adopt_log_errors")


def default_audit():
    aud = _orig_default_audit()

    def audit(row, decl):
        audit_warm(row, decl)
        if ADOPT_LOG is None:
            return aud(row, decl)
        fr = sys._getframe(1)
        try:
            try:
                out = aud(row, decl)
            except BaseException as e:
                adopt_log(row, decl, ("raised", f"{type(e).__name__}: {e}"), fr)
                raise
            adopt_log(row, decl, out, fr)
            return out
        finally:
            del fr
    return audit


P.default_audit = default_audit


# ------------------------------------------------------------------------------------------------ generate: speculate in parallel, then the original
class SpecBudget:
    """What a speculative op sees as run.budget: the real wall and the real meter's count (read-only); it never charges, and it stops the
    speculation when the round it belongs to is over."""
    def __init__(self, b, round_):
        self.b, self.round = b, round_
        self.max = getattr(b, "max", 1 << 30)
        self.meter = getattr(b, "meter", None)
        self.deadline = getattr(b, "deadline", float("inf"))

    def left_s(self):
        return self.b.left_s() if self.b is not None else float("inf")

    def need(self, n):
        if self.round["over"] or (self.b is not None and self.b.left_s() <= 0):
            raise P._Stop("speculation over")


def op_tasks(proof, statement, run, versions, exchange, compile_s, say, inc_hb, row_ctx):
    """open_post.generate's per-op calls, one callable per op (implied + kskip together), in ORDER, with its lane-reserve rule."""
    I, Q, CP, MS, KS = P._mods()
    from scorer.tokenize import split_declaration
    body = split_declaration(proof, statement)
    order = P.ORDER
    out = []
    if "implied" in order and I.query_text(proof, statement) is not None:
        out.append(lambda: I.query(proof, statement, run, versions=versions, stats={}, log=say))
    if "closerprep" in order and body is not None and CP.closer_sites(body) and MS.renamed(statement, 0) is not None:
        out.append(lambda: CP.query(proof, statement, run, versions=versions, ctx={"compile_s": compile_s, "exchange": exchange},
                                    stats={}, log=say))
    if "inlineeq" in order and Q.query_text(proof, statement) is not None:
        out.append(lambda: Q.query(proof, statement, run, versions=versions, stats={}, log=say))
    for name, fn in (("hintgrind", lambda: P._gen_hintgrind(proof, statement, run, versions, exchange, compile_s, say, inc_hb)),
                     ("projpath", lambda: P._gen_projpath(proof, statement, run, versions, exchange, compile_s, say)),
                     ("lexsurf", lambda: P._gen_lexsurf(proof, statement, run, versions, exchange, compile_s, say)),
                     ("jointres", lambda: P._op("jointres").generate(proof, statement, run, versions, exchange, compile_s, say,
                                                                     ctx=dict(row_ctx or {}))),
                     ("t4ind", lambda: P.gen_t4ind(proof, statement, run, compile_s, say)),
                     ("ctorsearch", lambda: P.gen_ctorsearch(proof, statement, run, versions, exchange, compile_s, say)),
                     *((n, (lambda n=n: P._gen_lane(n, proof, statement, run, versions, exchange, compile_s, say, inc_hb))) for n in P.LANE_OPS)):
        if name not in order:
            continue
        bud = getattr(run, "budget", None)
        if name in P.LANE_OPS and bud is not None and bud.left_s() < P.lane_reserve_s(name, compile_s):
            continue
        out.append(fn)
    return out


# ------------------------------------------------------------------------------------------------ (5) hintgrind shadow lookahead
# hintgrind.query (a25416f5) sends, through its `run(text, version)`: Query A (`run(query_a_text(...), primary)`, once per probing), then
# the probe files (`run(probe_file(...)[0], oldest)`, one after another, at most MAX_FILES, while PROBE_WALL_S lasts), then, only when a
# probe file gave a clean answer, the screen files (`screen_text`, primary). A probe file whose reading is missing (`parse_probe` finds no
# `#check lraHGDummy` marker: a timeout gives no messages) is "lost"; a lost file that timed out (`r.timed_out`, menu not `try`, more than
# 2 copies) is retried first at half its size. So under an all-timeout reading the next file's text is fixed by the previous one alone:
# the shadow below answers every probe file as a timeout at once and the uploaded loop emits exactly that sequence.
# Classification of a text the shadow's run() receives (hg_classify), first match wins:
#   query_a  the text equals query_a_text(statement, query_names(proof, statement)) (pure, computed by the shadow), or it holds both
#            Query A's `#eval` markers (`LRAHGA`, `Lean.resolveGlobalConst`): compiled for real (speculatively; the shadow waits);
#   probe    it starts with PROBE_HEAD (`theorem lraHGDummy ...` + `#check lraHGDummy`: Query A starts the same way, hence checked first)
#            and holds a probe copy line `set_option maxHeartbeats N in`: fire-and-forget + an immediate service-timeout answer;
#   other    anything else (a screen file: never reached in the all-timeout branch): the shadow ends there.
_HG_PROBE_COPY = re.compile(r"\nset_option maxHeartbeats \d+ in\n")
_HG_DONE: set = set()


class _ShadowEnd(Exception):
    """The shadow's own stop (its file bound, or a text that is neither Query A nor a probe file)."""


def hg_classify(text: str, qa_text, HG) -> str:
    if qa_text is not None and text == qa_text:
        return "query_a"
    if "LRAHGA" in text and "Lean.resolveGlobalConst" in text:
        return "query_a"
    if text.startswith(HG.PROBE_HEAD) and _HG_PROBE_COPY.search(text):
        return "probe"
    return "other"


def _req_file(req: dict) -> str:
    """The request's .lean path as rpc_run_lean resolved it (the Evaluator's scratch is absolute)."""
    p = req["cmd"][req["file_index"]]
    return p if os.path.isabs(p) else os.path.join(req["cwd"], p)


def hg_fire(req: dict, timeout) -> dict:
    """Send `req` (speculative priority, already in it) in a daemon thread that stays connected until the service answers (pf_svc drops
    a queued speculative compile whose client has gone: peer_closed / dropped_orphan), wait only until it is written (launch order),
    and return what the service returns for a timed-out compile.
    The request's scratch file must outlive this call: the service compiles that path later (a fresh compile, or the prefix backend
    reading it), and a charged request for the same text may join that compile. So the caller's Evaluator._run leaves it in place
    (TL.hg_keep, set only once the sender thread has started) and the sender deletes it after the service's answer (or its failure)."""
    sent = threading.Event()
    fpath = _req_file(req)

    def go():
        try:
            with SPEC_INFLIGHT:
                _rpc_once(req, on_sent=sent.set)
        except Exception:  # noqa: BLE001  (lost warm-up only)
            _stat("hg_shadow_errors")
        finally:
            sent.set()
            try:
                os.unlink(fpath)
            except OSError:
                pass
    threading.Thread(target=go, daemon=True, name="hg-shadow-ff").start()
    TL.hg_keep = fpath
    _stat("hg_shadow_files")
    sent.wait(HG_FF_SEND_WAIT_S)
    return {"timed_out": True, "seconds": float(timeout) if timeout is not None else 0.0, "stdout": "", "stderr": "", "returncode": None,
            "memo": "shadow"}


def hg_wall_files(HG, T) -> int:
    """(5) The most probe files the charged loop can START when every file times out at T s and each timed-out answer reaches it no
    sooner than T s after it asked (a fresh compile; pf_svc --hold-timeouts guarantees it for memo / joined answers too): hintgrind
    starts file n only while `time.time() - t0 <= PROBE_WALL_S`, and before file n more than (n-1)*T s have passed since t0 (t0 is
    taken before Query A; Query A and the loop's own steps take a positive time), so file n needs (n-1)*T < PROBE_WALL_S:
    n <= ceil(PROBE_WALL_S / T). Never more than MAX_FILES. Read at call time (the module's current PROBE_WALL_S)."""
    n_max = int(HG.MAX_FILES)
    try:
        wall, t = float(HG.PROBE_WALL_S), float(T)
    except (TypeError, ValueError, AttributeError):
        return n_max
    if not (t > 0) or not math.isfinite(wall) or not math.isfinite(t):
        return n_max
    return max(1, min(n_max, int(math.ceil(wall / t))))


def _hg_overlay(HG, statement, seed) -> None:
    """A fresh private overlay for this thread: every scoped memory empty, hintgrind's cache holding a copy of the seed entry."""
    TL.scope_over = {}
    TL.scope_over[id(HG._CACHE)] = {} if seed is None else {HG._sha(statement): dict(seed, texts=set(seed["texts"]), results=[])}


def _hg_shadow(HG, proof, statement, run, meter, versions, exchange, compile_s, inc_hb, round_, seed):
    """The shadow (hg_shadow_start). Three uploaded-query calls, each on a fresh overlay: (1) a dry call whose run() records the first
    request and stops (the uploaded code decides whether this round sends anything at all: skip rules, sites, cache); (2) Query A
    compiled for real, waiting, when that first request is Query A; (3) the shadow query proper, whose Query A is then a memo hit, so
    its probe loop starts at once (its PROBE_WALL_S clock starts before Query A: a long speculative wait for Query A would otherwise
    use up the wall before the first file)."""
    TL.spec = True
    try:
        if not HG.has_sites(proof, statement):   # generate()'s own pre-check for hintgrind (_gen_hintgrind)
            return
        ctx = {"compile_s": compile_s, "exchange": exchange, "inc_hb": inc_hb}
        first = []

        def dry(text, version=None):
            first.append((text, version))
            raise _ShadowEnd("dry")
        _hg_overlay(HG, statement, seed)
        try:
            HG.query(proof, statement, dry, versions=versions, ctx=dict(ctx), stats={}, log=None)
        except _ShadowEnd:
            pass
        if not first:
            return   # the charged query sends nothing this round either
        _stat("hg_shadow_runs")
        qa_text = HG.query_a_text(statement, HG.query_names(proof, statement))
        to_eff = _to_eff(meter, P.QUERY_TIMEOUT)   # what the charged run() gives meter.command (timeout=QUERY_TIMEOUT)
        n_fire = hg_wall_files(HG, to_eff)          # PROBE_WALL_S: files the charged loop cannot start are not fired
        fired = [0]

        def srun(text, version=None):
            if round_["over"]:
                raise P._Stop("speculation over")
            v = version or meter.versions[0]
            kind = hg_classify(text, qa_text, HG)
            if kind == "query_a":
                r = _compile_with(spec_ev(meter), meter, text, v, False, to_eff)[0]
                if not r.ok and any(str(e).startswith("environment:") for e in (r.errors or [])):
                    _stat("hg_shadow_errors")   # no compile (service / environment): the charged Query A will read otherwise
                    raise _ShadowEnd("query_a")
                return r
            if kind != "probe" or fired[0] >= HG.MAX_FILES:
                raise _ShadowEnd(kind)
            if fired[0] >= n_fire:
                _stat("hg_shadow_wall_stops")
                raise _ShadowEnd("probe wall")
            fired[0] += 1
            TL.hg_ff = True
            try:
                return _compile_with(spec_ev(meter), meter, text, v, False, to_eff)[0]
            finally:
                TL.hg_ff = False
        srun.meter = meter
        srun.budget = SpecBudget(getattr(run, "budget", None), round_)
        if hg_classify(first[0][0], qa_text, HG) == "query_a":
            srun(*first[0])
        _hg_overlay(HG, statement, seed)
        HG.query(proof, statement, srun, versions=versions, ctx=dict(ctx), stats={}, log=None)
    except (P._Stop, _ShadowEnd):
        pass
    except Exception:  # noqa: BLE001  (speculation only)
        _stat("hg_shadow_errors")
    finally:
        TL.hg_ff = False
        TL.scope_over = None
        TL.spec = False


def hg_shadow_start(proof, statement, run, meter, versions, exchange, compile_s, inc_hb, round_):
    """Called by generate() in the CHARGED thread before the original generate(): at most one shadow per (row, CLI pass, proof sha) and
    per round, on the speculative executor. The shadow's hintgrind cache entry is seeded with the charged cache entry's probe state as
    it is now (read only, before the charged hintgrind of this round runs), so the shadow probes exactly when the charged query will
    (fresh proof, or a reprobe); its results start empty (a cached round sends no probe file). Returns the future (None: no shadow)."""
    try:
        if "hintgrind" not in P.ORDER:
            return None
        HG = P._op("hintgrind")
        if not isinstance(HG._CACHE, SpecScoped):   # not scoped: the shadow could not be kept apart from the charged memory
            _stat("hg_shadow_errors")
            return None
        key = (getattr(meter, "name", None), os.environ.get("PF_PASS", ""), P.sha16(proof))
        with _SL:
            if key in _HG_DONE or round_.get("hg_shadow"):
                return None
            _HG_DONE.add(key); round_["hg_shadow"] = True
        ent = object.__getattribute__(HG._CACHE, "_real").get(HG._sha(statement))
        seed = None if ent is None else {"probed": bool(ent.get("probed")), "results": [], "qa": None,
                                         "texts": set(ent.get("texts") or ()), "reprobes": int(ent.get("reprobes") or 0)}
        vs = list(versions) if versions is not None else None   # the charged query's own argument (a copy)
        return SPEC.submit(_hg_shadow, HG, proof, statement, run, meter, vs, exchange, compile_s, inc_hb, round_, seed)
    except Exception:  # noqa: BLE001
        _stat("hg_shadow_errors")
        return None


def _merge_warm_mod():
    """(7) merge_warm.py from this script's directory, by path (works under python3 -I too); cached in sys.modules."""
    m = sys.modules.get("merge_warm")
    if m is None:
        import importlib.util
        spec = importlib.util.spec_from_file_location("merge_warm", os.path.join(os.path.dirname(os.path.abspath(__file__)), "merge_warm.py"))
        m = importlib.util.module_from_spec(spec)
        sys.modules["merge_warm"] = m
        spec.loader.exec_module(m)
    return m


def generate(proof, statement, run, versions, exchange, compile_s, log_fn, inc_hb=None, row_ctx=None):
    meter = getattr(run, "meter", None)
    round_ = {"over": False}
    if SPEC_NEXT:   # (6) a new charged round: branches on another proof end, the one on this proof runs on (never raises)
        sn_gen_start(proof)
    if meter is not None and meter.freeze() == "direct" and not NOSPEC:
        try:
            def srun(text, version=None):
                if round_["over"]:
                    raise P._Stop("speculation over")
                return _compile_with(spec_ev(meter), meter, text, version or meter.versions[0], False, _to_eff(meter, P.QUERY_TIMEOUT))[0]
            srun.meter = meter
            srun.budget = SpecBudget(getattr(run, "budget", None), round_)
            TL.spec = True
            try:
                if SPEC_NEXT and sn_covers(proof, inc_hb):   # (6) the confirmed branch already runs these ops (exact memories)
                    tasks = []; _stat("sn_base_skipped")
                else:
                    tasks = op_tasks(proof, statement, srun, versions, exchange, compile_s, (lambda *x: None), inc_hb, row_ctx)
            finally:
                TL.spec = False
            for fn in tasks:
                bound_spec(fn)
        except Exception:  # noqa: BLE001  (speculation never changes the charged path)
            STATS["spec_errors"] += 1
        if HG_LOOKAHEAD:   # (5) never raises; reads the charged hintgrind cache before the original generate() below
            hg_shadow_start(proof, statement, run, meter, versions, exchange, compile_s, inc_hb, round_)
    try:
        fam = _ORIG_GENERATE(proof, statement, run, versions, exchange, compile_s, log_fn, inc_hb=inc_hb, row_ctx=row_ctx)
    finally:
        round_["over"] = True
        if SPEC_NEXT:   # (6) the charged generate() is done: every branch ends (the read warm-up below takes over)
            sn_gen_end()
    try:   # warm the reads improve_row will take this pass (its static filter, dedup, inlineeq screen rule, READS, timeout)
        if meter is not None and meter.freeze() == "direct":
            to = max(P.CAND_TIMEOUT_MIN, int(P.CAND_TIMEOUT_MULT * (compile_s or P.CAND_TIMEOUT_MIN)))
            for op in P.ORDER:
                seen, cs2 = set(), []
                for c in fam.get(op) or []:
                    why = P.static_ok(c["decl"].rstrip(), statement)
                    key = P.sha16(c["decl"])
                    if why or key in seen or c["decl"].rstrip() == proof.rstrip():
                        continue
                    seen.add(key); cs2.append(c)
                if op == "inlineeq" and len(cs2) > P.SCREEN_MIN:
                    continue
                for c in cs2[:P.READS[op]]:
                    d = c["decl"].rstrip().strip()
                    if meter._check(d) is None:
                        warm(meter, d, meter.versions[0], True, to)
            if MERGE_WARM and not NOSPEC:   # (7) the round's merged candidate (v7m): same text as improve_row's, warmed speculatively
                MW = _merge_warm_mod()
                MW.warm_merge(P, sys.modules[__name__], fam, proof, statement, meter, compile_s,
                              MW.inc_metric(sys._getframe(1), P, meter, proof, inc_hb))
    except Exception:  # noqa: BLE001
        STATS["spec_errors"] += 1
    return fam


# ------------------------------------------------------------------------------------------------ (6) speculative next round
_ALL_ORDER = P.ORDER   # the module's default ORDER (--ops all = an L pass), read before main() rebinds it
_V3_RESERVE = (P.V3_RESERVE_MIN_S, P.V3_RESERVE_MULT)   # the v3 query reserve (an --long process rebinds the module's pair)
SN_LK = threading.Lock()
_SN_IMPORT_LK = threading.Lock()   # a cross branch's imports (never held by the charged thread)
SN: dict = {"gen": 0, "branches": {}, "cur": None, "c2_asked": set()}
SN_EXEC = ThreadPoolExecutor(64, thread_name_prefix="specnext") if SPEC_NEXT else None   # branch work: never queued behind SPEC's tasks
if SPEC_NEXT:   # only with the option on: the default run's final stats line stays as it was
    STATS.update(sn_branches=0, sn_cross=0, sn_cancelled=0, sn_restarts=0, sn_confirmed=0, sn_tasks=0, sn_task_stops=0, sn_reads=0,
                 sn_errors=0, sn_stale=0, sn_busy_skips=0, sn_copy_fallbacks=0, sn_ahead=0, sn_ahead_unsupported=0, sn_c2_unreadable=0,
                 sn_base_skipped=0)


def _next_cfg():
    """PF_NEXT_OPS=<kind>:<row_s>:<s> (pf_drive --next-ops) -> (order, long, the next pass's row wall) or None."""
    if not NEXT_OPS:
        return None
    try:
        kind, rs, ss = NEXT_OPS.split(":")
        return {"v3": P.V3_ORDER, "v4": P.V4_ORDER, "L": _ALL_ORDER}[kind], kind == "L", min(float(rs), float(ss))
    except Exception:  # noqa: BLE001
        return None


def _reserve_fn(long_: bool):
    """open_post.lane_reserve_s of a pass of the given kind (--long or not), whatever this process's own kind."""
    mn, mult = (P.LONG_V3_RESERVE_MIN_S, P.LONG_V3_RESERVE_MULT) if long_ else _V3_RESERVE

    def v3r(cs):
        return max(mn, mult * float(cs or P.CAND_TIMEOUT_MIN))

    def fn(name, cs):
        if name in P.V5_OPS:
            return min(max(P.V5_RESERVE_MIN_S, P.V5_RESERVE_MULT * float(cs or P.CAND_TIMEOUT_MIN)), v3r(cs))
        return v3r(cs)
    return fn


class _NextBudget:
    """A cross branch's row budget as the next CLI pass will see it (its row wall from now on; read only)."""
    def __init__(self, row_s, meter):
        self.deadline, self.max, self.meter = time.time() + float(row_s), P.ROW_COMPILES, meter

    def left_s(self):
        return self.deadline - time.time()


def sn_parts(order, proof, statement, run, versions, exchange, compile_s, inc_hb, row_ctx, reserve_fn) -> list:
    """open_post.generate (a25416f5) split into parts that can run in parallel: [(name, fn -> {op: candidates})], the ops of `order`
    only, each op's calls and candidate post-processing exactly as generate() makes them (implied + kskip together: kskip reads
    implied's query), the lane reserve rule evaluated now (generate() evaluates it when the op's turn comes)."""
    I, Q, CP, MS, KS = P._mods()
    from scorer.tokenize import split_declaration
    body = split_declaration(proof, statement)
    say = (lambda *a: None)
    parts = []
    if "implied" in order or "kskip" in order:
        def f_ik():
            out, ctx = {}, {}
            if "implied" in order and I.query_text(proof, statement) is not None:
                got = I.query(proof, statement, run, versions=versions, stats={}, log=say) or {}
                ctx.update(got)
                out["implied"] = I.candidates(proof, statement, ctx=dict(got, opt_in=list(P.IMPLIED_OPT_IN)))
            if "kskip" in order:
                out["kskip"] = KS.candidates(proof, statement, ctx=ctx)
            return out
        parts.append(("implied+kskip", f_ik))
    if "closerprep" in order and body is not None and CP.closer_sites(body) and MS.renamed(statement, 0) is not None:
        def f_cp():
            cctx = {"compile_s": compile_s, "exchange": exchange}
            got = CP.query(proof, statement, run, versions=versions, ctx=cctx, stats={}, log=say) or {}
            return {"closerprep": CP.candidates(proof, statement, exchange=exchange, ctx=dict(got, **cctx))}
        parts.append(("closerprep", f_cp))
    if "inlineeq" in order:
        def f_q():
            qt = Q.query_text(proof, statement)
            got = (Q.query(proof, statement, run, versions=versions, stats={}, log=say) or {}) if qt is not None else {}
            return {"inlineeq": Q.candidates(proof, statement, exchange=exchange, ctx=got)}
        parts.append(("inlineeq", f_q))
    named = (("hintgrind", lambda: P._gen_hintgrind(proof, statement, run, versions, exchange, compile_s, say, inc_hb)),
             ("projpath", lambda: P._gen_projpath(proof, statement, run, versions, exchange, compile_s, say)),
             ("lexsurf", lambda: P._gen_lexsurf(proof, statement, run, versions, exchange, compile_s, say)),
             ("jointres", lambda: P._op("jointres").generate(proof, statement, run, versions, exchange, compile_s, say,
                                                             ctx=dict(row_ctx or {}))),
             ("t4ind", lambda: P.gen_t4ind(proof, statement, run, compile_s, say)),
             ("ctorsearch", lambda: P.gen_ctorsearch(proof, statement, run, versions, exchange, compile_s, say).get("ctorsearch")),
             *((n, (lambda n=n: P._gen_lane(n, proof, statement, run, versions, exchange, compile_s, say, inc_hb))) for n in P.LANE_OPS))
    for name, fn in named:
        if name not in order:
            continue
        bud = getattr(run, "budget", None)
        if name in P.LANE_OPS and bud is not None and bud.left_s() < reserve_fn(name, compile_s):
            continue
        parts.append((name, (lambda fn=fn, name=name: {name: fn()})))
    return parts


def sn_warm_reads(meter, proof, statement, fam, compile_s, br) -> None:
    """Warm the reads improve_row takes from `fam` on `proof` (its static filter, dedup, inlineeq screen rule, READS, timeout); the same
    rule as generate()'s read warm-up above."""
    to = max(P.CAND_TIMEOUT_MIN, int(P.CAND_TIMEOUT_MULT * (compile_s or P.CAND_TIMEOUT_MIN)))
    for op, cands in (fam or {}).items():
        if br["over"]:
            return
        seen, cs2 = set(), []
        for c in cands or []:
            why = P.static_ok(c["decl"].rstrip(), statement)
            key = P.sha16(c["decl"])
            if why or key in seen or c["decl"].rstrip() == proof.rstrip():
                continue
            seen.add(key); cs2.append(c)
        if op == "inlineeq" and len(cs2) > P.SCREEN_MIN:
            continue
        for c in cs2[:P.READS.get(op, 0)]:
            d = c["decl"].rstrip().strip()
            if meter._check(d) is None:
                warm(meter, d, meter.versions[0], True, to)
                _stat("sn_reads")


def _sn_overlay(cross: bool) -> dict:
    """A branch's private op memories: a deep copy of every scoped memory's REAL container (within pass: the charged round k+1 starts
    from exactly this state), or nothing for a cross branch (a fresh process: SpecScoped makes each one empty on first use)."""
    ov: dict = {}
    if cross:
        return ov
    for name, m in list(sys.modules.items()):
        if not name.startswith("harness") or not isinstance(m, types.ModuleType):
            continue
        for v in list(vars(m).values()):
            if isinstance(v, SpecScoped) and id(v) not in ov:
                real = object.__getattribute__(v, "_real")
                try:
                    ov[id(v)] = copy.deepcopy(real)
                except Exception:  # noqa: BLE001  (an uncopyable memory starts empty in the branch: waste only)
                    ov[id(v)] = _fresh_like(real)
                    _stat("sn_copy_fallbacks")
    return ov


def _sn_scope_order(order) -> None:
    """A cross branch: import the next pass's op modules (as its process would) and scope the empty module-level memories of harness
    modules first imported here (this process's charged path never used them), so the branch never writes a real container."""
    with _SN_IMPORT_LK:
        before = set(sys.modules)
        for n in order:
            try:
                P._op(n)
            except Exception:  # noqa: BLE001
                pass
        for name in sorted(set(sys.modules) - before):
            m = sys.modules.get(name)
            if not isinstance(m, types.ModuleType) or not name.startswith("harness") or name in SKIP_MODS:
                continue
            for k, v in list(vars(m).items()):
                if not k.startswith("__") and not isinstance(v, SpecScoped) and isinstance(v, (dict, set, list)) and len(v) == 0:
                    setattr(m, k, SpecScoped(v))


def _sn_busy() -> bool:
    try:
        return int(_rpc_once({"op": "stats"}).get("queued") or 0) > int(SPEC_NEXT_MAXQ)
    except Exception:  # noqa: BLE001
        return False


def _sn_main(br) -> None:
    """A branch (speculative thread): its op memories, then every generate part in a thread of its own (each part's reads warmed when
    its candidates exist)."""
    TL.spec = True
    try:
        if br["over"]:
            return
        if SPEC_NEXT_MAXQ is not None and _sn_busy():
            br["over"] = True; _stat("sn_busy_skips")
            return
        if br["cross"]:
            _sn_scope_order(br["order"])
        ov = _sn_overlay(br["cross"])
        if not br["cross"] and SN["gen"] != br["gen"]:   # the charged path entered generate() meanwhile: the copy may be torn
            br["over"] = True; _stat("sn_stale")
            return
        br["overlay"] = ov
        meter = br["meter"]

        def srun(text, version=None):
            if br["over"]:
                raise P._Stop("speculation over")
            return _compile_with(spec_ev(meter), meter, text, version or meter.versions[0], False, _to_eff(meter, P.QUERY_TIMEOUT))[0]
        srun.meter = meter
        srun.budget = SpecBudget(br["budget"], br)
        TL.scope_over = ov
        try:
            parts = sn_parts(br["order"], br["decl"], br["st"], srun, list(meter.versions), br["exchange"], br["compile_s"],
                             br["inc_hb"], br["row_ctx"], br["reserve"])
        finally:
            TL.scope_over = None
        for _name, fn in parts:
            _sn_task(br, fn)
    except Exception:  # noqa: BLE001  (speculation only)
        _stat("sn_errors")
    finally:
        TL.scope_over = None
        TL.spec = False


def _sn_task(br, fn) -> None:
    def w():
        TL.spec = True
        TL.scope_over = br.get("overlay")
        try:
            if br["over"]:
                return
            fam = fn()
            TL.scope_over = None
            if not br["over"]:
                sn_warm_reads(br["meter"], br["decl"], br["st"], fam, br["compile_s"], br)
        except P._Stop:
            _stat("sn_task_stops")
        except Exception:  # noqa: BLE001
            _stat("sn_errors")
        finally:
            TL.scope_over = None
            TL.spec = False
    _stat("sn_tasks")
    SN_EXEC.submit(w)


def _sn_launch(br) -> None:
    _stat("sn_branches")
    if br["cross"]:
        _stat("sn_cross")
    SN_EXEC.submit(_sn_main, br)


def _sn_cancel(key, why="sn_cancelled") -> None:
    """Caller holds SN_LK."""
    br = SN["branches"].pop(key, None)
    if br is not None:
        br["over"] = True
        _stat(why)


def sn_restart(key, br, inc_hb, compile_s, charged=False) -> None:
    """The branch's inc_hb / compile_s are now known exactly: keep it if they match, else end it and start it again with them.
    charged=True: the value comes from the charged path's own c2 (sn_on_measure) and is final; an ahead result (charged=False) never
    overrides it (review 2026-11-05: when the charged c2 joins the ahead request's compile, the service answers the ahead request with a
    LATER draw, which used to overwrite the exact value and cost the round's speculation)."""
    with SN_LK:
        if br["over"] or SN["branches"].get(key) is not br or SN["gen"] != br["gen"]:   # (never once the charged round started)
            return
        if not charged and br.get("charged_exact"):
            _stat("sn_ahead_stale_ignored")
            return
        if inc_hb == br["inc_hb"] and compile_s == br["compile_s"]:
            br["exact"] = True
            if charged:
                br["charged_exact"] = True
            return
        br["over"] = True
        nb = dict(br, over=False, inc_hb=inc_hb, compile_s=compile_s, exact=True, overlay=None, charged_exact=charged)
        if br["cross"]:
            nb["budget"] = _NextBudget(br["row_s"], br["meter"])
        SN["branches"][key] = nb
    _stat("sn_restarts")
    _sn_launch(nb)


def _sn_ahead(meter, decl, n, to):
    """(CompileResult, honoured) of the n-th draw the charged path takes next of decl's primary measured compile (speculative)."""
    TL.sn_ahead, TL.sn_ahead_ok = n, False
    try:
        r = _compile_with(spec_ev(meter), meter, decl, meter.versions[0], True, _to_eff(meter, to))[0]
        _stat("sn_ahead")
        ok = bool(getattr(TL, "sn_ahead_ok", False))
        if not ok:
            _stat("sn_ahead_unsupported")
        return r, ok
    finally:
        TL.sn_ahead = 0


def _sn_ahead_plain(meter, decl, version, n) -> None:
    """A cross branch: the n-th next draw of decl's plain compile on a non-primary pin (the next pass's r0 reads every pin)."""
    TL.spec = True
    TL.sn_ahead, TL.sn_ahead_ok = n, False
    try:
        _compile_with(spec_ev(meter), meter, decl, version, False, _to_eff(meter, None))
        _stat("sn_ahead")
    except Exception:  # noqa: BLE001
        _stat("sn_errors")
    finally:
        TL.sn_ahead = 0
        TL.spec = False


def _sn_ahead_task(meter, key, decl, rd_hb, n, to) -> None:
    """n == 1: c2 of a branch candidate (within pass: the exact inc_hb; an unreadable c2: the charged path rejects it); n == 2 (a cross
    branch): the next CLI pass's r0 reading (its inc_hb and compile_s); key None: only the draw (i2)."""
    TL.spec = True
    try:
        r, ok = _sn_ahead(meter, decl, n, to)
        if not ok or key is None:
            return
        with SN_LK:
            br = SN["branches"].get(key)
        if br is None or br["cross"] != (n == 2):
            return
        readable = bool(r.ok) and r.heartbeats is not None
        if not readable:
            with SN_LK:
                if SN["branches"].get(key) is br:
                    _sn_cancel(key, "sn_c2_unreadable")
            return
        if n == 1:
            cur = SN["cur"]
            if cur is not None and cur["c2_seen"] and cur["decl"] == decl.strip():   # the charged c2 is in: it decides (sn_on_measure)
                _stat("sn_ahead_stale_ignored")
                return
            sn_restart(key, br, int(rd_hb if rd_hb >= r.heartbeats else r.heartbeats), br["compile_s"])
        else:
            secs = round(float(r.seconds), 2) if isinstance(r.seconds, (int, float)) else 0.0
            sn_restart(key, br, int(r.heartbeats), float(secs or 0.0) or None)
    except Exception:  # noqa: BLE001
        _stat("sn_errors")
    finally:
        TL.spec = False


def sn_on_pins(meter, decl, fr, to) -> None:
    """(6) The charged path starts confirming `decl` (improve_row's meter.pins call; `fr` its frame, read only)."""
    try:
        if fr is None or fr.f_code is not P.improve_row.__code__ or NOSPEC:
            return
        loc = fr.f_locals
        pas, reads, inc, row = loc["pas"], list(loc["reads"]), loc["inc"], loc["row"]
        st, run, exchange, compile_s, row_ctx = loc["st"], loc["run"], loc["exchange"], loc["compile_s"], loc["row_ctx"]
        inc_proof = inc["proof"]
        ordered = sorted(reads, key=lambda x: (-x[0], x[1]))
        idx = next((i for i, x in enumerate(ordered) if x[2]["decl"].rstrip().strip() == decl), None)
        if idx is None:
            return
        within = pas < P.PASSES
        nxt = None if within else _next_cfg()
        g = SN["gen"]
        want = {}
        for _s, _k, c, rd in ordered[idx: idx + SPEC_NEXT]:
            d = c["decl"].rstrip().strip()
            want[(g, P.sha16(d))] = (d, rd)
        new, asks = [], []
        with SN_LK:
            SN["cur"] = {"gen": g, "decl": decl, "rd_hb": int(ordered[idx][3]["heartbeats"]), "c2_seen": False}
            for key in list(SN["branches"]):
                if key not in want:
                    _sn_cancel(key)
            for key, (d, rd) in want.items():
                if (within or nxt is not None) and key not in SN["branches"]:
                    if within:
                        br = {"cross": False, "order": P.ORDER, "reserve": P.lane_reserve_s, "budget": getattr(run, "budget", None),
                              "compile_s": compile_s, "inc_hb": int(rd["heartbeats"]), "row_ctx": row_ctx}
                    else:
                        order, long_, row_s = nxt   # row_ctx: row_mods(row, primary pin) whenever jointres is in ORDER (v3 / v4 / all)
                        br = {"cross": True, "order": order, "reserve": _reserve_fn(long_), "budget": _NextBudget(row_s, meter),
                              "row_s": row_s, "compile_s": float(rd.get("seconds") or 0.0) or None, "inc_hb": int(rd["heartbeats"]),
                              "row_ctx": row_ctx if "jointres" in order else {}}
                    br.update(key=key, gen=g, decl=d, st=st, exchange=exchange, meter=meter, over=False, exact=False, overlay=None)
                    SN["branches"][key] = br
                    new.append(br)
                if SPEC_NEXT_AHEAD and key not in SN["c2_asked"]:
                    SN["c2_asked"].add(key)
                    asks.append((key, d, int(rd["heartbeats"])))
        for br in new:
            _sn_launch(br)
        if SPEC_NEXT_AHEAD:   # the draws the charged confirmation takes next, and its audit, start now (speculative, uncharged)
            SN_EXEC.submit(_sn_ahead_task, meter, None, inc_proof.strip(), 0, 1, to)   # i2: the incumbent's re-reading
            for key, d, rd_hb in asks:
                SN_EXEC.submit(_sn_ahead_task, meter, key, d, rd_hb, 1, to)       # c2
                if not within and nxt is not None:
                    SN_EXEC.submit(_sn_ahead_task, meter, key, d, rd_hb, 2, None)  # the next pass's r0 (timeout: the meter's)
                    for v in meter.versions[1:]:                                   # ... and its other pins (after this pass's pins)
                        SN_EXEC.submit(_sn_ahead_plain, meter, d, v, 2)
            audit_warm(row, decl)
    except Exception:  # noqa: BLE001  (speculation never changes the charged path)
        _stat("sn_errors")


def sn_on_measure(decl, out) -> None:
    """(6) A charged primary-only reading: when it is the confirming candidate's paired re-reading c2, the next round's inc_hb is now
    exact (improve_row: the larger of rd and c2): a within-pass branch with another value is restarted, an unreadable c2 ends it."""
    try:
        cur = SN["cur"]
        if cur is None or cur["c2_seen"] or cur["gen"] != SN["gen"] or decl.strip() != cur["decl"]:
            return
        cur["c2_seen"] = True
        key = (cur["gen"], P.sha16(cur["decl"]))
        with SN_LK:
            br = SN["branches"].get(key)
            if br is None or br["cross"]:
                return
            if not P._ok(out):
                _sn_cancel(key, "sn_c2_unreadable")
                return
        hb = int(cur["rd_hb"] if cur["rd_hb"] >= out["heartbeats"] else out["heartbeats"])
        sn_restart(key, br, hb, br["compile_s"], charged=True)
    except Exception:  # noqa: BLE001
        _stat("sn_errors")


def sn_gen_start(proof) -> None:
    """(6) The charged path enters generate() on `proof`: a within-pass branch on it runs on (confirmed), every other branch ends."""
    try:
        if is_spec():
            return
        p = proof.strip()
        with SN_LK:
            SN["gen"] += 1
            SN["cur"] = None
            SN["c2_asked"] = set()
            for key, br in list(SN["branches"].items()):
                if br["cross"] or br["decl"] != p or br["over"]:
                    _sn_cancel(key)
                else:   # (its gen stays the hook's: a branch still copying the memories finds itself stale)
                    _stat("sn_confirmed")
    except Exception:  # noqa: BLE001
        _stat("sn_errors")


def sn_covers(proof, inc_hb) -> bool:
    """(6) Called by generate() right after sn_gen_start: True when a live confirmed branch runs this round's ops on `proof` with this
    inc_hb (generate() then skips its own per-op speculation: the branch has the exact op memories); a branch with another inc_hb ends."""
    try:
        p = proof.strip()
        with SN_LK:
            for key, br in list(SN["branches"].items()):
                if not br["cross"] and br["decl"] == p and not br["over"]:
                    if br["inc_hb"] == inc_hb and br.get("overlay") is not None:
                        return True
                    _sn_cancel(key)
        return False
    except Exception:  # noqa: BLE001
        _stat("sn_errors")
        return False


def sn_gen_end() -> None:
    """(6) The charged generate() returned: every branch ends (its compiles are in the memo; the base read warm-up takes over)."""
    try:
        if is_spec():
            return
        with SN_LK:
            for key in list(SN["branches"]):
                br = SN["branches"].pop(key)
                br["over"] = True
    except Exception:  # noqa: BLE001
        _stat("sn_errors")


P.generate = generate


if __name__ == "__main__":
    argv = sys.argv[1:]
    ops = argv[argv.index("--ops") + 1] if "--ops" in argv else "all"
    order = {"v1": P.V1_ORDER, "v2": P.V2_ORDER, "v3": P.V3_ORDER, "v4": P.V4_ORDER}.get(ops, P.ORDER)
    n_scoped = scope_op_memories(order)
    print(f"[pf_worker] ops {ops}: {len(order)} ops, {n_scoped} op-module memories scoped for speculation", flush=True)
    before = set(sys.modules)
    rc = 1
    try:
        rc = P.main(argv)
    except BaseException:  # noqa: BLE001  (exit at once: never drain the speculative queue at interpreter shutdown)
        import traceback
        traceback.print_exc()
        rc = 1
    finally:
        late = sorted(m for m in set(sys.modules) - before if m.startswith("harness"))
        if late:
            print(f"[pf_worker] harness modules imported after the scan (memories not scoped): {late}", flush=True)
        print(f"[pf_worker] speculation {json.dumps(STATS)}", flush=True)
        if MERGE_WARM and "merge_warm" in sys.modules:
            print(f"[pf_worker] merge warm {json.dumps(sys.modules['merge_warm'].STATS)}", flush=True)
        SPEC.shutdown(wait=False, cancel_futures=True)
        sys.stdout.flush(); sys.stderr.flush()
        os._exit(rc if isinstance(rc, int) else 1)
