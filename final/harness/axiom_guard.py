#!/usr/bin/env python3
"""Axiom guard (2026-11-24): at export, the axioms of every row's proof are read, and no row keeps a proof whose value rests on `sorry`.

Why. The held-out test of the post stage (66 library rows, 2026-11-24) found one output that compiles with no Lean message at all,
while `#print axioms` of the theorem reads `sorryAx` alone: Lean elaborated a failed part to `sorry` without logging an error. The
post stage's gate reads compile errors and sorry messages, not axioms, so it adopted that step. This guard reads the axioms at
export, outside the post stage: the post stage's own scripts (post_fast/) are unchanged.

The reading (forced_reading): the row's proof followed by `#print axioms <name>` (the plain and the namespace-qualified name),
compiled unmeasured through the package's own scorer/compile.py with warn.sorry forced on, also inside `module` files. It is the
construction of the verifier that found the flaw, with one difference in how the output is read: the verifier keeps the list of the
last print, the guard the union of the lists of both prints, so a qualified name that resolves to another constant cannot hide the
declaration's own `sorryAx`. For the reference proof's reading, which sets what is allowed (below), it takes what EVERY print reads
(the intersection), so such a name cannot widen the allowance either.

The rule (pin_state, classify), per row over its listed toolchains (pins), relative to the row's reference proof (the rows file's
`src`), as the export's own audit (harness/open_package.py audit_proof) is, but failing closed where that audit keeps the proof:
  pin BAD        Lean's sorry message on the declaration's lines or a way to hide that message, whatever the reference proof reads; an
                 axiom outside propext, Classical.choice and Quot.sound (sorryAx, Lean.ofReduceBool, ...) that the reference proof's
                 reading on the same pin does not show; any such axiom when that reading is not available (FAIL CLOSED: not read in
                 time, a reader error, a timeout, no axiom list, a sorry message, a switch or an error in its declaration; a row
                 without a reference proof), or when the proof's own compile timed out or reports an error in the declaration;
  pin OK         axioms within those three (or none), or within those three and the axioms of the reference proof's reading on the
                 same pin (the allowance: "axioms as the reference proof"), no sorry message, no error in the declaration, no timeout;
  pin NOT READ   no axiom list. Either by construction (`structural`: on v4.27.0 the print cannot run inside a `module` file), or
                 because the compile timed out, reported an error in the declaration or failed, or the time budget ran out first.
                 A reading with an axiom outside the three is never NOT READ: it is OK through the allowance or BAD.
  row PASS       no pin BAD and at least one pin OK: a pin that is not read never passes a row on its own;
  row FAIL       some pin BAD (also: the record holds no proof text);
  row NOT READ   no pin BAD and no pin OK.
The reference's reading is the same forced reading of the reference proof's text. It is read lazily: only for a (row, pin) on which
some other proof of the row reads an axiom outside the three in a complete reading (needs_reference), once per (row, pin) for the run
(every proof of the row on that pin uses the same reading), and ahead of every other reading. Until it comes, that pin reads BAD (fail
closed), so the row's earlier proofs are queued at once, behind it, and read while it is read; the row is decided at the end on
every reading that has come. When it does not come in time, the pin is BAD. The reference proof as a fallback candidate is judged by
the same rule against its own reading: on axioms it passes by construction (its axioms are the allowance), but only with a complete
reading of its own on that pin: no sorry message on its declaration, no switch, no timeout or error in the declaration together with
an axiom outside the three, and, for the row to pass, at least one pin OK.
What the allowance gives up: on a pin where the reference proof itself reads sorryAx (a lemma of the library proved by `sorry`), a
proof whose own value became sorry (held-out row 42's fault) passes too; `#print axioms` cannot tell the two apart (the export
audit has the same limit).

What happens to each row (guard_file):
  PASS       kept.
  NOT READ   kept, because nothing was read against it: its proof can still rest on `sorry`. The log names it; exit status 3.
  FAIL       replaced by the newest earlier proof of the row that PASSES the same check, tried in this order: the post stage's
             input (proofs.picks.jsonl), the agent stage's export (proofs.export.jsonl), the row's reference proof (the rows
             file's `src`, stored score 33.33). The candidates are read as soon as one pin of the row reads BAD (also a pin
             that waits for the reference's reading). When no candidate passes (none read within the budget, or all BAD), the
             row gets its reference proof, and if that proof did not pass the log says so and the exit status is 3. A row set
             back only because the reference's reading was not available is named apart in the summary line (exit status 0 all
             the same): its proof may be sound, and the guard does not bring it back (PROOFS.axiom-guard and
             proofs.merged.jsonl.axiom-guard keep the files as before its first write).
A proof that read BAD is never written. The one exception is a row whose reference proof does not pass its own reading (a sorry
message on its declaration, a reading that failed or did not come): its reference proof, the library's own, is then written as the
last proof left, and the exit status is 3. A lemma of the library proved by `sorry` does not make the reference fail: the reference
reads that `sorryAx` in a complete reading, and the row's proofs that read no other axiom pass through the allowance (held-out row 25).
The log names each pin that passed through the allowance with the reference's axioms; the summary line counts the rows whose written
or kept proof passes only through it, the (row, pin) pairs that needed the reference's reading and how many of those came in full.

Read order. The reference's readings for the allowance come before everything else. The rows whose proof differs from their line in
the last fallback file (by default proofs.export.jsonl: the rows the post stage changed, the only ones its gate can have let through)
come first: their newest toolchain, then the earlier proofs of any row that failed (or waits for the reference's reading), then their
older toolchains; then the other rows, newest toolchain first.
Writing. PROOFS is rewritten by rename, only if it still holds what the guard read (else nothing is written, exit 1); its first
content is kept once as PROOFS.axiom-guard. When PROOFS is named proofs.jsonl, the lines of its sibling proofs.merged.jsonl (the post
stage's merged rows, which a resumed job and `run.sh export` merge back) that hold a proof the guard set back are set back the same
way, its first content kept once as proofs.merged.jsonl.axiom-guard.

    python3 harness/axiom_guard.py PROOFS.jsonl --rows ROWS.jsonl [--fallback FILE ...] [--budget S] [--timeout S] [--jobs N]
                                   [--report OUT.json] [--no-write]
Without --fallback the candidates are PROOFS.jsonl's siblings proofs.picks.jsonl and proofs.export.jsonl, where they exist.
--budget: seconds for all readings (default: $LRA_AXIOM_GUARD_S, else 420); no compile starts with less than 5 s left, and the
guard stops waiting 30 s after the budget, then decides and writes. --timeout: seconds for one compile (default 300, never past the
budget). --jobs: compiles at once (default: the physical cores, at most 48).
exit 0: every row PASSES, and every toolchain of the proof it keeps was read (a toolchain not read by construction aside);
exit 3: some row is NOT READ, PASSES with a toolchain that was not read (time, error), got a reference proof that did not pass, or
is in the rows file but not in PROOFS (all named in the output; the replacements are written all the same);
exit 1: not checked (a file cannot be read as JSONL, PROOFS changed while the guard read it, an error): nothing written."""
from __future__ import annotations

import hashlib, heapq, itertools, json, os, signal, sys, threading, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.kernel_guard import SEED_SCORE, assert_clean, check_forbidden, debug_option  # noqa: E402

STD_AXIOMS = frozenset({"propext", "Classical.choice", "Quot.sound"})   # = scorer.compile.AXIOM_ALLOW
OK, BAD, NOT_READ = "ok", "bad", "not read"                             # pin states
PASS, FAIL = "pass", "fail"                                             # row verdicts (and NOT_READ)
BUDGET_ENV = "LRA_AXIOM_GUARD_S"
DEFAULT_BUDGET_S = 420     # run.sh: the guard runs after the post stage, in the job's 600 s safety margin (README, "Axiom guard")
DEFAULT_TIMEOUT_S = 300
MAX_JOBS = 48              # compiles at once at most: the post stage's 48 slots, measured on 64 cores
MIN_START_S = 5            # no compile starts with less than this left in the budget
GRACE_S = 30               # the guard stops waiting this long after the budget, whatever still runs
RC_OK, RC_NOT_CHECKED, RC_NOT_READ = 0, 1, 3
FALLBACK_NAMES = ("proofs.picks.jsonl", "proofs.export.jsonl")
MERGED_NAME = "proofs.merged.jsonl"   # post_fast/merge_post.py's copy of its last merge, beside proofs.jsonl
ROLE_TEXT = {"proofs.picks.jsonl": "the post stage's input", "proofs.export.jsonl": "the agent stage's export",
             "reference": "the reference proof"}
STOP = threading.Event()   # set by SIGTERM / SIGINT: no compile starts any more, and the guard decides with what it has read


class Changed(Exception):
    """PROOFS changed between the guard's read and its write: nothing is written."""


def sha16(text: str) -> str:
    return hashlib.sha256((text or "").rstrip().encode()).hexdigest()[:16]


def utc() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def role_text(role: str) -> str:
    return ROLE_TEXT.get(role, role)


def text_of(x) -> str:
    """A record's proof text: a string, else "" (no proof)."""
    return x if isinstance(x, str) else ""


# ------------------------------------------------------------------------------------------------------------------------ the rule
def extra_axioms(reading) -> list[str]:
    """The axioms of a reading outside propext, Classical.choice and Quot.sound, sorted ([] when none, or no list)."""
    axs = reading.get("axioms") if isinstance(reading, dict) else None
    return sorted(set(axs) - STD_AXIOMS) if axs else []


def complete(reading) -> bool:
    """A complete reading: an axiom list, and no reader error, sorry message, switch, timeout or error in the declaration."""
    return (isinstance(reading, dict) and reading.get("axioms") is not None and not reading.get("error") and not reading.get("sorry_warning")
            and not reading.get("switch") and not reading.get("timed_out") and not reading.get("decl_errors"))


def needs_reference(reading) -> bool:
    """A reading that the reference proof's reading on its pin decides: complete, with an axiom outside the three. Every other reading
    is decided without the reference (the allowance never applies to it)."""
    return complete(reading) and bool(extra_axioms(reading))


def ref_allowance(ref) -> tuple[frozenset | None, str]:
    """(the axioms outside the three that the reference proof's reading `ref` on one pin allows, why). None: that reading is not
    available, so nothing beyond the three is allowed on that pin (fail closed). Only a complete reading allows anything."""
    if ref is None:
        return None, "not read within the time budget"
    if not isinstance(ref, dict):
        return None, "no reading"
    if ref.get("error"):
        return None, str(ref["error"])[:160]
    if ref.get("sorry_warning"):
        return None, "Lean's sorry message on its declaration"
    if ref.get("switch"):
        return None, "its text names a way to hide Lean's sorry message"
    if ref.get("timed_out"):
        return None, "its compile timed out"
    if ref.get("axioms") is None:
        return None, "its print gave no axiom list" + (" (a `module` file)" if ref.get("module") else "")
    if ref.get("decl_errors"):
        return None, "its compile reports an error in the declaration"
    lists = ref.get("lists")
    if isinstance(lists, list) and lists and all(isinstance(x, list) for x in lists):
        # what EVERY print reads: a name that resolves to another constant (whose axioms the union holds) never widens the allowance
        return frozenset.intersection(*(frozenset(x) - STD_AXIOMS for x in lists)), "read"
    if ref.get("prints_differ"):
        return None, "its prints read different lists, and the lists were not kept"
    return frozenset(extra_axioms(ref)), "read"


def pin_state(reading: dict | None, ref: dict | None = None) -> tuple[str, str]:
    """(OK | BAD | NOT_READ, why) of one reading ({"axioms": list | None, "sorry_warning", "switch", "timed_out", "decl_errors",
    "error", "module"}; None = not read at all) against `ref`, the reference proof's reading on the same pin (None: not available).
    Evidence of sorry decides first, whatever else the reading says; an axiom outside the three passes only through the allowance."""
    if reading is None:
        return NOT_READ, "not read within the time budget"
    if reading.get("error"):
        return NOT_READ, str(reading["error"])[:160]
    if reading.get("sorry_warning"):
        return BAD, "Lean's sorry message on the declaration"
    if reading.get("switch"):
        return BAD, "the text names a way to hide Lean's sorry message"
    axs = reading.get("axioms")
    extra = extra_axioms(reading)
    if extra:
        what = f"axioms {extra}" + (" (the value is sorry)" if extra == ["sorryAx"] else "")
        if reading.get("timed_out") or reading.get("decl_errors"):   # the allowance needs a complete reading of the proof too
            return BAD, what + ("; the compile timed out" if reading.get("timed_out") else "; the compile reports an error in the declaration")
        allowed, rwhy = ref_allowance(ref)
        if allowed is None:
            return BAD, what + f"; the reference proof's reading here is not available ({rwhy}): nothing beyond the three is allowed"
        outside = [a for a in extra if a not in allowed]
        if outside:
            return BAD, what + ("; the reference proof reads standard axioms here" if not allowed else
                                f"; the reference proof reads {sorted(allowed)} here, not {outside}")
        return OK, f"axioms as the reference proof: {extra}"
    if reading.get("timed_out"):
        return NOT_READ, "the compile timed out"
    if axs is None:
        return NOT_READ, "the print gave no axiom list" + (" (a `module` file)" if reading.get("module") else "")
    if reading.get("decl_errors"):
        return NOT_READ, "the compile reports an error in the declaration"
    return OK, "standard axioms" if axs else "no axioms"


def allowance_pins(readings: dict, refs: dict | None = None) -> list[str]:
    """The pins on which a proof is OK only through the allowance (an axiom outside the three that its reference proof reads too)."""
    refs = refs or {}
    return [v for v, r in readings.items() if extra_axioms(r) and pin_state(r, refs.get(v))[0] == OK]


def structural(reading: dict | None) -> bool:
    """A pin that is not read by construction, not for lack of time or an error: the print gives no list inside a `module` file (on
    v4.27.0 it cannot run there), the compile otherwise clean. More time would not read it."""
    return (isinstance(reading, dict) and reading.get("axioms") is None and bool(reading.get("module")) and not reading.get("error")
            and pin_state(reading)[0] == NOT_READ and not reading.get("timed_out") and not reading.get("decl_errors"))


def classify(readings: dict, refs: dict | None = None) -> tuple[str, str, dict]:
    """(PASS | FAIL | NOT_READ, why, {pin: (state, why)}) of one proof from its readings {pin: reading or None}, against the reference
    proof's readings {pin: reading or None} (None, or a pin left out: not available, so nothing beyond the three is allowed there)."""
    refs = refs or {}
    states = {v: pin_state(r, refs.get(v)) for v, r in readings.items()}
    bad = [f"{v}: {w}" for v, (s, w) in states.items() if s == BAD]
    if bad:
        return FAIL, "; ".join(bad), states
    rel = allowance_pins(readings, refs)
    std = [v for v, (s, _) in states.items() if s == OK and v not in rel]
    unread = [f"{v}: {w}" for v, (s, w) in states.items() if s == NOT_READ]
    if std or rel:
        why = "; ".join(([f"standard axioms on {', '.join(std)}"] if std else [])
                        + [f"axioms as the reference proof on {v}: {extra_axioms(readings[v])}" for v in rel])
        return PASS, why + (f"; not read on {'; '.join(unread)}" if unread else ""), states
    return NOT_READ, "; ".join(unread) or "no toolchain to read on", states


def unread_in_time(readings: dict) -> list[str]:
    """The pins of one proof that are NOT READ for a reason other than the structural one (time, an error, a timeout)."""
    return [v for v, r in readings.items() if pin_state(r)[0] == NOT_READ and not structural(r)]


# --------------------------------------------------------------------------------------------------------------------- the reading
def print_lists(messages: list, print_line: int) -> list[list[str]]:
    """The axiom list of EVERY `#print axioms` message at or after `print_line`, in order ([] = 'does not depend on any axioms').
    scorer.compile.parse_axioms reads the same messages the same way but keeps only the last."""
    from scorer import compile as C
    out = []
    for m in messages:
        if C._msg_line(m, print_line) < print_line:
            continue
        d = str(m.get("data", ""))
        if "does not depend on any axioms" in d:
            out.append([])
        else:
            mm = C._AXIOMS_RE.search(d)
            if mm:
                out.append([a.strip() for a in mm.group(1).split(",") if a.strip()])
    return out


def forced_reading(row: dict, proof: str, version: str, timeout: float) -> dict:
    """One forced `#print axioms` of `proof` for `row` on `version`, through scorer/compile.py (warn.sorry on, `module` files included).
    "axioms": the union of the lists of both prints (None: no print gave one); "lists": each print's list, in order."""
    from scorer import compile as C
    name = C.decl_name(row["statement"], row.get("name"))
    if not name:
        return {"error": "the statement declares no name to print"}
    tmo = max(1, int(timeout))
    if row["source"] == "putnambench":
        core, mods, module = row["header"].rstrip(), "", False
        run = lambda text: C.compile_putnam(row["header"], text, version, count=False, timeout=tmo)
    else:
        core, mods = C.split_modifiers(C.file_prefix(row, version))
        args = C._with_warn_sorry(C.lakefile_options(row["source"], version))
        module = bool(C._MODULE_LINE.match(core))
        run = lambda text: C.compile_project(row, text, version, count=False, timeout=tmo, lean_args=args)
    first = C._first_line(core)
    head = proof.rstrip() + "\n\n"
    names = list(dict.fromkeys([name, C.qualified_name(name, C.current_namespace(core))]))
    print_line = first + 1 + (mods + head).count("\n")
    r = run(head + "".join(f"set_option pp.fullNames true in\n#print axioms {n}\n" for n in names))
    a = C.AxiomAudit(name, C.parse_axioms(r.messages, print_line), None, r, first, print_line)
    lists = print_lists(r.messages, print_line)
    axioms = list(dict.fromkeys(x for l in lists for x in l)) if lists else None
    return {"axioms": axioms, "lists": lists, "sorry_warning": a.sorry_warning, "switch": a.switch, "timed_out": bool(r.timed_out), "module": module,
            "decl_errors": [str(e)[:160] for e in a.decl_errors][:2], "print_errors": len(a.print_errors), "prints": len(lists),
            "prints_differ": len({tuple(sorted(l)) for l in lists}) > 1, "seconds": round(r.seconds, 1)}


def prepare_env(budget_s: float) -> None:
    """The real reader's environment, as the export's audit and the verifier set it: warn.sorry forced on, git trusts the env
    checkouts, and the memory gate gives up a compile it cannot admit within the budget."""
    from harness.open_package import SORRY_GUARD_ENV, git_trust
    os.environ.update(SORRY_GUARD_ENV)
    git_trust(os.environ)
    from scorer import memgate
    memgate.MAX_WAIT_S = max(1, min(int(memgate.MAX_WAIT_S), int(budget_s)))


def physical_cores() -> int:
    """Physical cores among the CPUs this process may use (SMT siblings counted once); the usable CPUs when the topology is unknown."""
    try:
        cpus = os.sched_getaffinity(0)
    except (AttributeError, OSError):
        return os.cpu_count() or 4
    seen = set()
    for c in cpus:
        try:
            t = Path(f"/sys/devices/system/cpu/cpu{c}/topology")
            seen.add(((t / "physical_package_id").read_text().strip(), (t / "core_id").read_text().strip()))
        except OSError:
            seen.add(("cpu", str(c)))
    return max(1, len(seen))


def versions_of(row: dict) -> list[str]:
    from probe.verify_candidates import newest_first
    return newest_first(row.get("version_info") or [])


class Readings:
    """Readings of (row, proof, pin) keys by a pool of daemon threads, highest priority first, inside one deadline."""

    def __init__(self, reader, jobs: int, deadline: float, timeout_s: float, clock=time.monotonic):
        self.reader, self.deadline, self.timeout_s, self.clock = reader, deadline, float(timeout_s), clock
        self.cv = threading.Condition()
        self.heap: list = []
        self.seq = itertools.count()
        self.results: dict = {}
        self.queued: set = set()
        self.prio: dict = {}
        self.started: set = set()
        self.closed = False
        for i in range(max(1, int(jobs))):
            threading.Thread(target=self._work, daemon=True, name=f"axiom-guard-{i}").start()

    def submit(self, prio: tuple, key: tuple, row: dict, proof: str, pin: str) -> None:
        """Queue one reading; a key is read once. A key still waiting is moved up when it is submitted again with a higher priority."""
        with self.cv:
            if self.closed:
                return
            if key in self.queued and (key in self.started or key in self.results or prio >= self.prio[key]):
                return
            self.queued.add(key)
            self.prio[key] = prio
            heapq.heappush(self.heap, (prio, next(self.seq), key, row, proof, pin))
            self.cv.notify()

    def _work(self) -> None:
        while True:
            with self.cv:
                while not self.heap and not self.closed:
                    self.cv.wait()
                if self.closed:
                    return
                _p, _s, key, row, proof, pin = heapq.heappop(self.heap)
                if key in self.started or key in self.results:
                    continue   # the older entry of a reading that was moved up, and has been taken
                left = self.deadline - self.clock()
                if STOP.is_set() or left < MIN_START_S:
                    self.results[key] = {"error": "not started: " + ("the guard was stopped" if STOP.is_set() else "the time budget ran out")}
                    self.cv.notify_all()
                    continue
                self.started.add(key)
            t0 = self.clock()
            try:
                res = self.reader(row, proof, pin, min(self.timeout_s, left))
                res = dict(res) if isinstance(res, dict) else {"error": f"the reader returned {type(res).__name__}"}
            except Exception as e:   # a reading that fails is NOT READ, never OK
                res = {"error": f"{type(e).__name__}: {str(e)[:160]}"}
            res.setdefault("seconds", round(self.clock() - t0, 1))
            with self.cv:
                self.results[key] = res
                self.cv.notify_all()

    def drain(self, on_result, stop_at: float) -> bool:
        """Call on_result(key) for each new result (it may submit more) until every queued key has a result (True), or until
        `stop_at` or a stop signal (False)."""
        seen: set = set()
        while True:
            with self.cv:
                new = [k for k in self.results if k not in seen]
                if not new:
                    if self.queued <= set(self.results):
                        return True
                    if self.clock() >= stop_at or STOP.is_set():
                        return False
                    self.cv.wait(timeout=0.5)
                    continue
            for k in new:
                seen.add(k)
                on_result(k)

    def close(self) -> dict:
        """No more readings start; the results so far."""
        with self.cv:
            self.closed = True
            self.cv.notify_all()
            return dict(self.results)


# ------------------------------------------------------------------------------------------------------------------------ the file
def parse_jsonl(data: bytes, where) -> tuple[list[str], list[dict]]:
    """(non-empty raw lines, their records). Raises ValueError when a line is not a JSON object."""
    raw = [l for l in data.decode().splitlines() if l.strip()]
    recs = [json.loads(l) for l in raw]
    if not all(isinstance(r, dict) for r in recs):
        raise ValueError(f"{where}: a line is not a JSON object")
    return raw, recs


def read_jsonl_lines(path) -> tuple[list[str], list[dict]]:
    """(non-empty raw lines, their records). Raises OSError / ValueError when a line is not a JSON object."""
    return parse_jsonl(Path(path).read_bytes(), path)


def write_if_unchanged(path: Path, text: str, expect: bytes) -> None:
    """Write `text` to `path` by rename, only if `path` still holds `expect`; its first content is kept once as <path>.axiom-guard.
    Raises Changed when it does not hold `expect` (nothing is written)."""
    tmp = path.with_name(path.name + ".axiom-guard.tmp")   # one fixed name: a stale one from a killed guard is overwritten
    tmp.write_text(text)
    fd = os.open(tmp, os.O_RDONLY)
    os.fsync(fd)
    os.close(fd)
    if path.read_bytes() != expect:
        tmp.unlink()
        raise Changed(f"{path} changed while the guard read it")
    keep = path.with_name(path.name + ".axiom-guard")
    if not keep.exists():
        keep.write_bytes(expect)
    os.replace(tmp, path)


def reference_record(name: str, row: dict, note: str) -> dict:
    return {"name": name, "proof": (row.get("src") or "").rstrip() + "\n", "source": "seed", "stored_score": SEED_SCORE, "tokens": None,
            "heartbeats": None, "axiom_guard": note}


def candidates(name: str, row: dict | None, cur: str, fallbacks: list) -> list:
    """[(role, record)] to try, in order, for a row whose proof read BAD: each fallback file's line for the row, then the reference
    proof; a text equal to the current proof or to an earlier candidate, without the row's statement, or that fails the Arena's
    forbidden list or the kernel guard, is left out (the reference only needs to set no debug option)."""
    out, seen = [], {cur.rstrip()}
    for role, recs in fallbacks:
        rec = recs.get(name)
        p = text_of((rec or {}).get("proof")).rstrip()
        if not p or p in seen or row is None or row["statement"].strip() not in p or check_forbidden(p) is not None:
            continue
        seen.add(p)
        out.append((role, rec))
    src = text_of((row or {}).get("src")).rstrip()
    if src and src not in seen and not debug_option(src):
        out.append(("reference", {"name": name, "proof": src + "\n"}))
    return out


def _stored(r: dict | None):
    s = (r or {}).get("stored_score")
    return s if isinstance(s, (int, float)) and not isinstance(s, bool) else None


def set_back_merged(path: Path, replaced: dict, log) -> bool:
    """In PROOFS' sibling proofs.merged.jsonl, replace each line of a replaced row ({name: (failing proof, new record)}) that holds that
    same failing proof by the new record, so a later merge (a resumed job, `run.sh export`) does not bring the failing proof back.
    True when the file was written."""
    mp = path.with_name(MERGED_NAME)
    if not replaced or not mp.exists():
        return False
    try:
        data = mp.read_bytes()
        raw, recs = parse_jsonl(data, mp)
        new = {}
        for i, r in enumerate(recs):
            hit = replaced.get(r.get("name")) if isinstance(r.get("name"), str) else None
            if hit and text_of(r.get("proof")).rstrip() == hit[0].rstrip():
                new[i] = json.dumps(hit[1], ensure_ascii=False)
        if not new:
            return False
        write_if_unchanged(mp, "".join(new.get(i, raw[i]) + "\n" for i in range(len(raw))), data)
    except (OSError, ValueError, Changed) as e:
        log(f"{utc()} axiom guard: WARNING: {mp} not set back ({type(e).__name__}: {str(e)[:160]}): a resumed job or `run.sh export` "
            "merges its rows back, and the guard reads them again then")
        return False
    log(f"{utc()} axiom guard: {mp}: the same {len(new)} row(s) set back (first content kept as {mp.name}.axiom-guard)")
    return True


def guard_file(proofs_path, rows_path, fallback_paths=None, *, budget_s: float = DEFAULT_BUDGET_S, timeout_s: float = DEFAULT_TIMEOUT_S,
               jobs: int | None = None, reader=None, write: bool = True, log=print, clock=time.monotonic) -> dict:
    """Read every row of PROOFS (see the module text), replace the rows that read BAD, write the file by rename when a row changed.
    Returns the report; report["rc"] is the exit code. Raises OSError / ValueError when PROOFS or ROWS cannot be read."""
    t_start = clock()
    path = Path(proofs_path)
    first = path.read_bytes()   # what the guard reads; the file is written only if it still holds this
    raw, recs = parse_jsonl(first, path)
    rows = {r["name"]: r for r in read_jsonl_lines(rows_path)[1]}
    if fallback_paths is None:
        fallback_paths = [p for p in (path.with_name(n) for n in FALLBACK_NAMES) if p.exists()]
    fallbacks = []
    for fp in fallback_paths:
        try:
            fallbacks.append((Path(fp).name, {r.get("name"): r for r in read_jsonl_lines(fp)[1]}))
        except (OSError, ValueError) as e:
            log(f"{utc()} axiom guard: fallback file {fp} not used ({type(e).__name__}: {str(e)[:120]})")
    reader = reader or forced_reading
    cur_of = {k: text_of(r.get("proof")) for k, r in enumerate(recs)}
    pins = {}
    for r in recs:
        n = r.get("name")
        if n in rows and n not in pins:
            pins[n] = versions_of(rows[n])
    names_in = {r.get("name") for r in recs}
    missing = [n for n in rows if n not in names_in]
    if not recs:
        log(f"{utc()} axiom guard: WARNING: {path} holds no row")
    if missing:
        log(f"{utc()} axiom guard: WARNING: {len(missing)} row(s) of the rows file are not in {path}, so not read: "
            f"{', '.join(missing[:5])}{' ...' if len(missing) > 5 else ''}")
    # the rows the post stage changed come first: a proof equal to its line in the last fallback file (the agent stage's export) did not
    # pass the post stage's gate
    base_role, base = fallbacks[-1] if fallbacks else ("", {})
    exposed = {k: text_of((base.get(r.get("name")) or {}).get("proof")).rstrip() != cur_of[k].rstrip() for k, r in enumerate(recs)}
    n_pins = sum(len(pins.get(r.get("name"), [])) for r in recs)
    jobs = max(1, int(jobs or min(physical_cores(), MAX_JOBS, max(1, n_pins))))
    deadline = t_start + max(0.0, float(budget_s))
    log(f"{utc()} axiom guard: {path}: {len(recs)} rows, {n_pins} (row, toolchain) readings, {jobs} threads, budget {float(budget_s):.0f} s, "
        f"{float(timeout_s):.0f} s per compile; fallbacks: {', '.join(role_text(f[0]) for f in fallbacks) or 'none'}, then the reference proof; "
        f"read first: the {sum(exposed.values())} row(s) whose proof differs from " + (f"{base_role}" if fallbacks else "a fallback file (none: all)"))
    pool = Readings(reader, jobs, deadline, timeout_s, clock)

    def key(name, proof, pin):
        return (name, sha16(proof), pin)

    owner: dict = {}          # key -> row indices whose CURRENT proof it reads
    cands_of: dict = {}       # row index -> [(role, record)], once submitted
    first_reads = []
    for k, r in enumerate(recs):
        n, ps = r.get("name"), pins.get(r.get("name"), [])
        for rank, v in enumerate(ps if cur_of[k].strip() else []):
            kk = key(n, cur_of[k], v)
            owner.setdefault(kk, []).append(k)
            tier = (0 if rank == 0 else 2) if exposed[k] else (3 if rank == 0 else 4)
            first_reads.append(((tier, rank, k), kk, rows[n], cur_of[k], v))
    for args in sorted(first_reads, key=lambda x: x[0]):   # in priority order: a thread that starts at once takes the first
        pool.submit(*args)

    def ref_text(n) -> str:
        return text_of((rows.get(n) or {}).get("src"))

    def ref_key(n, v):
        return key(n, ref_text(n), v)

    def ref_reading(n, v, res: dict) -> dict | None:
        """The reference proof's reading of row n on pin v in the results `res` (None: not read, so far); a row without a reference proof
        reads as an error (nothing is allowed beyond the three)."""
        if not ref_text(n).strip():
            return {"error": "the row has no reference proof"}
        return res.get(ref_key(n, v))

    def refs_of(n, res: dict) -> dict:
        return {v: ref_reading(n, v, res) for v in pins.get(n, [])}

    ref_asked: set = set()    # (row name, pin) on which a proof other than the reference needed its reading (read once, for the whole run)

    def submit_candidates(k: int) -> None:
        if k in cands_of:
            return
        n = recs[k].get("name")
        cands_of[k] = candidates(n, rows.get(n), cur_of[k], fallbacks)
        for ci, (_role, rec) in enumerate(cands_of[k]):
            for pr, v in enumerate(pins.get(n, [])):
                pool.submit((1, ci, pr, k), key(n, rec["proof"], v), rows[n], rec["proof"], v)

    def on_result(kk) -> None:
        n, _h, v = kk
        res = pool.results
        if needs_reference(res.get(kk)) and (n, v) not in ref_asked and ref_text(n).strip() and kk != ref_key(n, v):   # (not itself)
            ref_asked.add((n, v))   # the reference's reading on this pin, ahead of every other reading (moved up if already queued)
            pool.submit((-1, pins[n].index(v)), ref_key(n, v), rows[n], ref_text(n), v)
        # a current proof that reads BAD on pin v has its earlier proofs read. One that waits for the reference's reading reads BAD until
        # it comes (fail closed): its earlier proofs are queued now, behind that reading, and read while it is read, not one compile
        # later (review 2026-11-24: under a tight budget they were left unread). The row is decided at the end, on every reading that came.
        for k in owner.get(kk, []):
            if pin_state(res.get(kk), ref_reading(n, v, res))[0] == BAD:
                submit_candidates(k)

    for k in range(len(recs)):   # a record without a proof text is no proof: its candidates are read at once
        if not cur_of[k].strip():
            submit_candidates(k)
    drained = pool.drain(on_result, deadline + GRACE_S)
    results = pool.close()
    if not drained:
        log(f"{utc()} axiom guard: {'stopped by a signal' if STOP.is_set() else 'the time budget ran out'}: {len(pool.queued) - len(results)} of "
            f"{len(pool.queued)} readings unfinished; the rows they belong to are decided on what was read")

    def readings_of(name, proof):
        return {v: results.get(key(name, proof, v)) for v in pins.get(name, [])}

    def verdict_of(name, proof):
        if not (proof or "").strip():
            return FAIL, "the record holds no proof text", {}
        return classify(readings_of(name, proof), refs_of(name, results))

    def allowed_on(name, proof) -> list:
        """The pins on which `proof` is OK only through the allowance."""
        return allowance_pins(readings_of(name, proof), refs_of(name, results)) if (proof or "").strip() else []

    def ref_axioms(name, pin):
        rr = ref_reading(name, pin, results)
        return rr.get("axioms") if isinstance(rr, dict) else None

    def allowance_text(name, ps) -> str:
        return ", ".join(f"{p} (the reference proof reads {ref_axioms(name, p)})" for p in ps)

    def ref_fields(name, pin, reading) -> dict:
        """The reference's reading on a pin where the proof's reading needed it (all None elsewhere): "read" (in full) or why it is not
        available; its axioms and what it allows, only when read in full."""
        if not needs_reference(reading):
            return {"reference_reading": None, "reference_axioms": None, "reference_allows": None}
        rr = ref_reading(name, pin, results)
        allowed, rwhy = ref_allowance(rr)
        if allowed is None:
            return {"reference_reading": rwhy, "reference_axioms": None, "reference_allows": None}
        return {"reference_reading": rwhy, "reference_axioms": rr.get("axioms"), "reference_allows": sorted(allowed)}

    def for_want_of_reference(name, proof, states) -> bool:
        """Every pin on which `proof` reads BAD reads BAD only because the reference's reading there is not available."""
        rd, refs = readings_of(name, proof), refs_of(name, results)
        bad = [p for p, (s, _w) in states.items() if s == BAD]
        return bool(bad) and all(needs_reference(rd[p]) and ref_allowance(refs.get(p))[0] is None for p in bad)

    out, details, replaced, not_read, ref_floor, partial, by_allowance, ref_unavailable = list(recs), [], [], [], [], [], [], []
    for k, r in enumerate(recs):
        n = r.get("name")
        if n not in rows:
            v, why, states = NOT_READ, "the row is not in the rows file", {}
        else:
            v, why, states = verdict_of(n, cur_of[k])
        got = {p: results.get(key(n, cur_of[k], p)) or {} for p in states}
        d = {"k": k, "name": n, "verdict": v, "why": why, "proof_sha": sha16(cur_of[k]), "read_first": exposed[k],
             "pins": {p: {"state": s, "why": w, "structural": structural(got[p]) if s == NOT_READ else False, "axioms": got[p].get("axioms"),
                          "allowance_used": s == OK and bool(extra_axioms(got[p])), **ref_fields(n, p, got[p]),
                          "prints_differ": got[p].get("prints_differ"), "seconds": got[p].get("seconds")} for p, (s, w) in states.items()}}
        if v == NOT_READ:
            not_read.append(k)
            log(f"{utc()} axiom guard: row {k} {n}: NOT READ, kept (nothing was read against it; its proof may rest on sorry): {why}")
        elif v == PASS:
            gaps = unread_in_time(readings_of(n, cur_of[k]))
            if gaps:
                partial.append(k)
            al = allowed_on(n, cur_of[k])
            if al:
                by_allowance.append(k)
            log(f"{utc()} axiom guard: row {k} {n}: pass ({why})" + (f"; NOT READ IN FULL: {', '.join(gaps)}" if gaps else "")
                + (f"; ONLY THROUGH THE ALLOWANCE on {allowance_text(n, al)}" if al else ""))
        else:
            tried, chosen = [], None
            for role, rec in cands_of.get(k) or candidates(n, rows.get(n), cur_of[k], fallbacks):
                cv, cwhy, _ = verdict_of(n, rec["proof"])
                tried.append({"role": role, "verdict": cv, "why": cwhy, "proof_sha": sha16(rec["proof"]), "stored_score": _stored(rec),
                              "allowance": allowed_on(n, rec["proof"]) if cv == PASS else []})
                if cv == PASS:
                    chosen = (role, rec, cv, cwhy)
                    break
            if chosen is None:   # no candidate passed: the floor is the row's reference proof
                ref = next((t for t in tried if t["role"] == "reference"), None)
                src = text_of(rows[n].get("src"))
                rv, rwhy = (ref["verdict"], ref["why"]) if ref else verdict_of(n, src)[:2]
                chosen = ("reference", {"proof": src.rstrip() + "\n"}, rv, rwhy)
                ref_floor.append(k)
            role, rec, cv, cwhy = chosen
            old_s = _stored(r)
            if rec["proof"].rstrip() == cur_of[k].rstrip():   # the failing proof is the reference proof itself: nothing else to write
                d.update(chosen="kept: it is the reference proof", chosen_verdict=cv, chosen_why=cwhy, candidates=tried, old_stored_score=old_s)
                log(f"{utc()} axiom guard: row {k} {n}: FAIL ({why}); the proof is the row's reference proof, kept: no proof of this row passes")
                details.append(d)
                continue
            al = allowed_on(n, rec["proof"]) if cv == PASS else []
            if cv == PASS:
                gaps = unread_in_time(readings_of(n, rec["proof"]))
                if gaps:
                    partial.append(k)
                    cwhy += f"; NOT READ IN FULL: {', '.join(gaps)}"
                if al:
                    by_allowance.append(k)
                    cwhy += f"; ONLY THROUGH THE ALLOWANCE on {allowance_text(n, al)}"
            note = (f"the proof read {why}; set back to {role_text(role)}" + (f" ({cwhy})" if cv == PASS else
                    f", which did not pass either ({cv}: {cwhy}): no proof of this row passes"))
            if role == "reference":
                new = reference_record(n, rows[n], note)
            else:
                new = dict(rec)
                new["name"] = n
                new["proof"] = rec["proof"] if rec["proof"].endswith("\n") else rec["proof"] + "\n"
                new["axiom_guard"] = note
            assert cv != FAIL or role == "reference", "a proof that read BAD is never written (the reference floor aside)"
            out[k] = new
            replaced.append(k)
            if for_want_of_reference(n, cur_of[k], states):   # the proof may be sound: named apart (review 2026-11-24)
                ref_unavailable.append(k)
            d.update(chosen=role, chosen_verdict=cv, chosen_why=cwhy, candidates=tried, old_stored_score=old_s, new_stored_score=_stored(new),
                     old_source=r.get("source"), new_source=new.get("source"), chosen_allowance=al)
            log(f"{utc()} axiom guard: row {k} {n}: FAIL ({why}) -> REPLACED by {role_text(role)}, stored {old_s} -> {_stored(new)}, source "
                f"{r.get('source')} -> {new.get('source')}" + ("" if cv == PASS else f"; that proof did not pass either ({cv}: {cwhy})")
                + (f"; that proof passes ONLY THROUGH THE ALLOWANCE on {allowance_text(n, al)}" if al else ""))
        details.append(d)
    unread_pins = sum(1 for k, d in enumerate(details) if k not in replaced for p in d["pins"].values() if p["state"] == NOT_READ)
    unread_structural = sum(1 for k, d in enumerate(details) if k not in replaced for p in d["pins"].values() if p["structural"])
    rc = RC_NOT_READ if not_read or ref_floor or partial or missing or not recs else RC_OK
    written, merged_written, changed = False, False, None
    if replaced and write:
        assert_clean(out, f"axiom guard {path}")   # the kernel guard: no proof with a debug option is written
        text = "".join((raw[k] if k not in replaced else json.dumps(out[k], ensure_ascii=False)) + "\n" for k in range(len(recs)))
        try:
            write_if_unchanged(path, text, first)
            written = True
        except Changed as e:
            changed = str(e)
            rc = RC_NOT_CHECKED
            log(f"{utc()} axiom guard: NOT CHECKED: {changed} (another writer, e.g. a live job's merge): nothing written; run it again")
        if written and path.name == "proofs.jsonl":
            merged_written = set_back_merged(path, {recs[k].get("name"): (cur_of[k], out[k]) for k in replaced}, log)
    secs = round(clock() - t_start, 1)
    means = [round(sum(x) / len(x), 4) if x and len(x) == len(recs) else None
             for x in ([_stored(r) for r in recs if _stored(r) is not None], [_stored(r) for r in out if _stored(r) is not None])]
    counts = {PASS: sum(d["verdict"] == PASS for d in details), FAIL: sum(d["verdict"] == FAIL for d in details), NOT_READ: len(not_read)}
    names = lambda ks: [details[k]["name"] for k in ks]
    n_ref_complete = sum(1 for n, v in ref_asked if ref_allowance(results.get(ref_key(n, v)))[0] is not None)
    rep = {"status": "done", "file": str(path), "rows": len(recs), "readings_planned": n_pins, "readings_done": len(results),
           "pins_not_read": unread_pins, "pins_not_read_structural": unread_structural, "jobs": jobs, "budget_s": float(budget_s),
           "timeout_s": float(timeout_s), "seconds": secs, "complete": drained, "verdicts": counts, "stored_mean_before": means[0],
           "stored_mean_after": means[1], "replaced": names(replaced), "not_read": names(not_read), "not_read_in_full": names(partial),
           "reference_not_passing": names(ref_floor), "missing_from_file": missing, "written": written, "merged_written": merged_written,
           "passed_by_allowance": names(by_allowance), "set_back_for_want_of_reference": names(ref_unavailable),
           "reference_readings": len(ref_asked), "reference_readings_complete": n_ref_complete,
           "changed": changed, "write": write, "rc": rc, "at": utc(), "running_at_end": len(pool.started - set(results)), "per_row": details}
    tail = (f"{len(recs)} rows: {counts[PASS]} pass, {counts[FAIL]} read BAD, {len(replaced)} set back"
            + (f" ({', '.join(map(str, rep['replaced']))})" if replaced else "")
            + (f" ({len(ref_unavailable)} of them only because the reference proof's reading was not available: "
               f"{', '.join(map(str, rep['set_back_for_want_of_reference']))}; the guard does not bring their proofs back)" if ref_unavailable else "")
            + f", {len(not_read)} NOT READ" + (f" (kept: {', '.join(map(str, rep['not_read']))})" if not_read else "")
            + (f", {len(partial)} NOT READ IN FULL ({', '.join(map(str, rep['not_read_in_full']))})" if partial else "")
            + (f", {len(rep['reference_not_passing'])} on a reference proof that does not pass ({', '.join(map(str, rep['reference_not_passing']))})"
               if rep["reference_not_passing"] else "")
            + (f", {len(missing)} of the rows file missing" if missing else "")
            + f"; {len(by_allowance)} pass only through the reference proof's axioms"
            + (f" ({', '.join(map(str, rep['passed_by_allowance']))})" if by_allowance else "")
            + f"; stored mean {means[0]} -> {means[1]}; {len(results)} of {len(pool.queued)} readings done in {secs:.0f} s "
            + f"({len(ref_asked)} (row, toolchain) pair(s) needed the reference proof's reading, {n_ref_complete} read in full), "
            + f"{unread_pins} pin(s) of the kept proofs not read ({unread_structural} by construction); "
            + ("file rewritten (first content kept as " + path.name + ".axiom-guard)" if written else
               "file unchanged" + (" (--no-write)" if replaced and not write else " (it changed meanwhile)" if changed else "")))
    log(f"{utc()} axiom guard: {'OK' if rc == RC_OK else 'NOT CHECKED' if rc == RC_NOT_CHECKED else 'NOT EVERY ROW READ AND PASSING'}: {tail}")
    return rep


def _kill_children() -> None:
    """Kill the process groups of compiles still running (each runs in its own session, scorer/memgate.run_lean)."""
    me = os.getpid()
    try:
        pids = [int(p) for p in os.listdir("/proc") if p.isdigit()]
    except OSError:
        return
    for pid in pids:
        try:
            with open(f"/proc/{pid}/stat") as f:
                ppid = int(f.read().rsplit(")", 1)[1].split()[1])
            if ppid == me and os.getpgid(pid) == pid:   # a session leader we started: a compile's own process group
                os.killpg(pid, signal.SIGKILL)
        except (OSError, ValueError, IndexError):
            continue


def main(argv=None, reader=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("proofs", help="a proofs file (JSONL: name, proof, stored_score, ...)")
    ap.add_argument("--rows", required=True, help="the benchmark rows (JSONL; `version_info` lists the toolchains, `src` the reference proof)")
    ap.add_argument("--fallback", action="append", default=None, metavar="FILE",
                    help="an earlier proofs file to take a row from when its proof reads BAD, in the order given (repeatable); default: "
                         "PROOFS' siblings proofs.picks.jsonl (the post stage's input) and proofs.export.jsonl (the agent stage's "
                         "export), where they exist. The row's reference proof always comes last. Rows whose proof equals their "
                         "line in the last fallback file are read after the others")
    ap.add_argument("--budget", type=float, default=None,
                    help=f"seconds for all readings (default: ${BUDGET_ENV}, else {DEFAULT_BUDGET_S})")
    ap.add_argument("--timeout", type=float, default=DEFAULT_TIMEOUT_S, help="seconds for one compile, never past the budget")
    ap.add_argument("--jobs", type=int, default=None, help=f"compiles at once (default: the physical cores, at most {MAX_JOBS})")
    ap.add_argument("--report", default=None, help="write the full report (JSON, no proof text) here; it says `running` until the guard ends")
    ap.add_argument("--no-write", action="store_true", help="read and report only; PROOFS is never written")
    a = ap.parse_args(argv)

    def report(d: dict) -> None:
        if a.report:
            try:
                Path(a.report).write_text(json.dumps(d, indent=1, ensure_ascii=False))
            except OSError as e:
                print(f"{utc()} axiom guard: report not written ({e})", flush=True)

    def not_checked(why: str) -> dict:
        print(f"{utc()} axiom guard: {a.proofs}: NOT CHECKED, nothing written ({why[:300]})", flush=True)
        return {"status": "not checked", "rc": RC_NOT_CHECKED, "file": a.proofs, "why": why[:300], "at": utc()}

    report({"status": "running", "rc": None, "file": a.proofs, "at": utc()})   # a guard killed from outside leaves this
    budget = a.budget
    if budget is None:
        try:
            budget = float(os.environ.get(BUDGET_ENV) or DEFAULT_BUDGET_S)
        except ValueError:
            report(not_checked(f"{BUDGET_ENV}={os.environ.get(BUDGET_ENV)!r} is not a number of seconds"))
            return RC_NOT_CHECKED
    old = {s: signal.signal(s, lambda *_: STOP.set()) for s in (signal.SIGTERM, signal.SIGINT)}
    try:
        if reader is None:
            prepare_env(budget)
        rep = guard_file(a.proofs, a.rows, a.fallback, budget_s=budget, timeout_s=a.timeout, jobs=a.jobs, reader=reader,
                         write=not a.no_write, log=lambda s: print(s, flush=True))
    except Exception as e:   # any failure before the write: not checked (a file that is not JSONL, a record that is not a row, ...)
        rep = not_checked(f"{type(e).__name__}: {e}")
    finally:
        for s, h in old.items():
            signal.signal(s, h)
    report(rep)
    sys.stdout.flush()
    sys.stderr.flush()
    if rep.get("running_at_end"):
        _kill_children()   # compiles still running past the budget (their reading is not used); the pool's threads are daemons
    return rep["rc"]


if __name__ == "__main__":
    raise SystemExit(main())
