#!/usr/bin/env python3
"""The post stage's gate audit (2026-11-24, operator decision (b)): the export guard's rule at each adoption.

Why. The held-out test of the post stage (66 library rows, 2026-11-24) adopted, on row 42 (a Lean `module` file, v4.34.0), a step
whose value Lean's error recovery had made `sorry` with no message at all. The published gate (open_package.audit_proof through
scorer.compile.audit_axioms) skips the axiom print inside `module` files and there reads only Lean's sorry message, so it let the
step through; three more steps built on it, and the export's axiom guard (harness/axiom_guard.py) then set the whole row back to the
stage's input (69.21 -> 33.33) although steps 1-6 were sound (65.54). This audit reads, at each adoption, what the guard reads at
export, so a step the guard would read as resting on sorry is not adopted and the stage keeps searching from the last sound proof.
Limit (as the guard's): a toolchain on which the row's file is a `module` file before v4.30 is not read for axioms (Lean prints no
list there); only Lean's sorry message is read on it. A silent sorry that shows only on such a toolchain is still adopted. Rows:
10 of the 60 final rows (Strata, v4.27.0; each also lists v4.31.0, which is read); none of the 66 held-out rows of the 2026-11-24
run (every pin v4.30 or later). Lean reads such a toolchain through a second file that imports the compiled one (`lean -o`, then
`import`; review 2026-11-24); not built.

What. gate_audit(row, proof, versions) -> (status, why) is the audit open_post.default_audit() returns (improve_row adopts a candidate
iff its status is "clean" or "skipped"). In order:
  1. the hook check of the candidate's text (finer_sorry.hooks): a text that registers an elaborator, a macro, a parser, ... can make
     `#print axioms` print what it likes: "sorry", nothing compiled;
  2. per pin, newest first, ONE compile (gate_reading: scorer.compile.audit_axioms with module_print=True): the candidate followed by
     `#print axioms` of its plain and namespace-qualified name, unmeasured, warn.sorry forced on, inside `module` files too, on every
     toolchain, as the guard's forced reading. In a `module` file before v4.30 (scorer.compile.prints_in_module) Lean answers the
     print with an error and no list, and the pin is NOT READ BY CONSTRUCTION when that reading is the guard's structural one:
     Lean's sorry message is still read there. A forced print with no list from v4.30 fails closed ("unknown");
  3. the reading is judged by the export guard's rule (axiom_guard.pin_state, with the finer sorry check on): evidence of sorry
     (Lean's sorry message on the declaration's lines, the switch, a hook) is BAD whatever else it reads; an axiom outside propext,
     Classical.choice and Quot.sound is OK only when the row's reference proof (row["src"]) reads it on the same pin
     (axiom_guard.ref_allowance: what every print of the reference reads), and where sorryAx passes through that allowance, the finer
     sorry check (finer_sorry.decide on the finer readings of the candidate and of the reference, axiom_guard.finer_reading) decides.
     The reference's readings are taken only when the candidate's reading needs them (axiom_guard.needs_reference, needs_finer), once
     per (row name, pin, sha of the reference's text) per process (ReadOnce: thread-safe, a second caller waits for the first one's
     reading). Kept (keep_reading): a complete reading, one that failed on evidence (Lean's sorry message, the switch, a hook, an
     error Lean reported in the declaration) and one that timed out under the full timeout; every other reading (a reader error, a
     finer reading's "not compiled again ... s left", a timeout under a shortened timeout, a compile that ended with no Lean message,
     a reading that raised) is handed to its callers and taken again by the next audit that needs it.
Verdicts: "sorry"   a pin BAD on evidence (returned at once: the older pins are not compiled);
          "unknown" a pin not read (a timeout, an error in the declaration, a failed compile, a forced print with no list, the audit
                    deadline, a reader that raised) or BAD only for want of a reading (the reference's, or a finer one): rejected, as
                    the published gate rejects "unknown";
          "skipped" every other pin OK, and some pin not read by construction (with no sorry message there);
          "clean"   every pin OK.
Invariant (tests/test_post_audit.py): whatever this gate accepts, the export guard (finer check on) accepts on the same readings
(a "clean" candidate is the guard's PASS; a "skipped" one PASSES there, or is NOT READ when no pin can be read, and kept); and this
gate accepts nothing the published gate rejects on the same compiles.
Cost: one compile per pin, of the text post_fast/pf_worker.audit_warm compiles ahead (it calls audit_axioms without module_print;
open_post.default_audit sets scorer.compile.GATE_MODULE_PRINT in the post stage's processes, so the warm-up and this audit compile
the same text). A candidate that reads an axiom outside the three adds the reference's reading on that pin (once per process); one
that passes through the allowance with sorryAx adds its own finer reading and the reference's (the latter once per process). These
extra readings are fresh, serial `lake env lean` compiles: nothing warms them, the candidate's finer text carries a fresh nonce, and
a post-stage worker process (one per row and pass) starts with an empty cache. No deadline is passed (as published), so the worst
case per pin is four compiles of AUDIT_TIMEOUT_S each (candidate, reference, own finer with the import retry, reference finer).
Switch: LRA_POST_AUDIT=published (open_post.audit_mode) restores the gate as published (open_package.audit_proof, the skip in `module`
files); unset, "" or "guard": this audit; any other value: this audit, with a warning in the log."""
from __future__ import annotations

import sys, threading, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness import axiom_guard as AG  # noqa: E402
from harness import finer_sorry as FS  # noqa: E402

CLEAN, SKIPPED, SORRY, UNKNOWN = "clean", "skipped", "sorry", "unknown"   # the gate's statuses (as open_package.audit_proof's)
ACCEPTED = (CLEAN, SKIPPED)                                               # improve_row adopts iff the status is one of these
PIN_OK, PIN_BAD, PIN_CONSTRUCTION, PIN_UNKNOWN = "ok", "bad", "construction", "unknown"   # pin_verdict's codes
WAIT_MARGIN_S = 60   # a caller waiting for another audit's reading of the reference waits its own compile timeout and this long


# --------------------------------------------------------------------------------------------------------------------- the reading
def gate_reading(row: dict, proof: str, version: str, timeout: float) -> dict:
    """One compile of `proof` for `row` on `version` (scorer.compile.audit_axioms, module_print=True: the print forced, `module`
    files included), as a reading pin_state reads (axiom_guard.audit_reading). "by_construction": a `module` file on a toolchain
    before v4.30 (scorer.compile.prints_in_module), where Lean's print gives no list (pin_verdict: not read by construction only
    when the reading is also axiom_guard.structural)."""
    from scorer import compile as C
    a = C.audit_axioms(row, proof, version, timeout=max(1, int(timeout)), module_print=True)
    if a.skipped == "no-name":   # (no row of the final or the held-out benchmark: every statement declares its name)
        return {"error": "the statement declares no name to print", "axioms": None,
                "seconds": round(a.compile.seconds, 1) if a.compile is not None else 0.0}
    module = a.skipped == "module" or C.module_file(row, version)
    rd = AG.audit_reading(a, module)
    rd["by_construction"] = bool(module) and (a.skipped == "module" or not C.prints_in_module(version))
    return rd


def keep_reading(r, shortened: bool) -> bool:
    """A reading of the reference proof (axioms or finer) that ReadOnce keeps for the process: complete, failed on evidence that
    more time would not change (Lean's sorry message, the switch, a hook, an error Lean reported in the declaration), or timed out
    under the full timeout (`shortened` False). Not kept: a reader error (a finer reading's "not compiled again ... s left"
    included), a timeout under a shortened timeout, a compile that ended with no Lean message (`lean exit ...`: a killed process)."""
    if not isinstance(r, dict):
        return False
    if r.get("hook") or r.get("sorry_warning") or r.get("switch"):
        return True
    if r.get("timed_out"):
        return not shortened
    if r.get("error"):
        return False
    return not any(str(e).startswith("lean exit") for e in r.get("decl_errors") or [])


class ReadOnce:
    """Readings taken once per key for the process (the reference proof's, per (row name, pin, sha of its text)). Thread-safe: a
    caller that finds the reading being taken waits for it (at most `wait_s`). A reading that raised, or that `keep` rejects
    (keep_reading), is handed to the callers waiting for it but not kept: the next caller takes it again."""

    def __init__(self):
        self._lk = threading.Lock()
        self._d: dict = {}
        self.taken = 0   # readings started (calls of fn)

    def get(self, key, fn, keep=lambda r: True, wait_s: float | None = None):
        with self._lk:
            ent = self._d.get(key)
            mine = ent is None
            if mine:
                ent = self._d[key] = [threading.Event(), None]
                self.taken += 1
        if not mine:
            return ent[1] if ent[0].wait(wait_s) else {"error": "the reading another audit takes did not come in time"}
        val, kept = {"error": "the reading did not finish"}, False
        try:
            val = fn()
            kept = bool(keep(val))
        except Exception as e:  # noqa: BLE001  (a reading that fails is no reading: not available)
            val = {"error": f"{type(e).__name__}: {str(e)[:160]}"}
        finally:
            if not kept:
                with self._lk:
                    if self._d.get(key) is ent:
                        del self._d[key]
            ent[1] = val
            ent[0].set()
        return val

    def keys(self) -> list:
        with self._lk:
            return list(self._d)


CACHE = ReadOnce()   # the process's readings of the reference proofs (an object, not a module-level dict: pf_worker scopes those)


# ------------------------------------------------------------------------------------------------------------------------ the rule
def pin_verdict(rd: dict | None, ref: dict | None, finer: tuple = (None, None)) -> tuple[str, str]:
    """(PIN_OK | PIN_BAD | PIN_CONSTRUCTION | PIN_UNKNOWN, why) of the candidate's reading `rd` on one pin, by the export guard's rule
    (axiom_guard.pin_state with the finer sorry check on) against the reference's reading `ref` there (None: not available) and the
    finer readings `finer` (the candidate's, the reference's; consulted only where sorryAx passes through the allowance). A pin the
    guard reads BAD only because the reference's reading or a finer reading is not available is PIN_UNKNOWN; one it does not read is
    PIN_CONSTRUCTION when the gate compiled it without the print by construction (axiom_guard.structural), else PIN_UNKNOWN."""
    st, why = AG.pin_state(rd, ref, finer)
    if st == AG.OK:
        return PIN_OK, why
    if st == AG.BAD:
        if AG.needs_reference(rd) and AG.ref_allowance(ref)[0] is None:
            return PIN_UNKNOWN, why
        if AG.needs_finer(rd, ref):
            f = AG.finer_decide(rd, ref, finer)[2]
            if FS.wanting(f["finer_reading"]) or FS.wanting(f["finer_reference_reading"]):
                return PIN_UNKNOWN, why
        return PIN_BAD, why
    if isinstance(rd, dict) and rd.get("by_construction") and AG.structural(rd):
        return PIN_CONSTRUCTION, why
    return PIN_UNKNOWN, why


def gate_audit(row: dict, proof: str, versions: list[str], *, timeout: float | None = None, deadline: float | None = None,
               reader=None, finer_reader=None, cache: ReadOnce | None = None, clock=time.time) -> tuple[str, str]:
    """(clean | skipped | sorry | unknown, why) of the candidate `proof` on the pins `versions` (newest first), as the module text says.
    `timeout`: seconds per compile (default open_package.AUDIT_TIMEOUT_S, as the published gate); `deadline` (clock time): no pin
    starts with less than open_package.AUDIT_MIN_PIN_S left, and no compile runs past it. `reader` / `finer_reader`: stand-ins for
    gate_reading / axiom_guard.finer_reading (tests); both are wrapped by axiom_guard.with_hooks as in the guard (the reference's
    texts included). `cache`: the reference's readings (default: the process's CACHE)."""
    from harness.open_package import AUDIT_MIN_PIN_S, AUDIT_TIMEOUT_S
    full = AUDIT_TIMEOUT_S if timeout is None else timeout
    read = AG.with_hooks(reader or gate_reading, FS.hooks)
    fread = AG.with_hooks(finer_reader or AG.finer_reading, FS.finer_hooks)
    cache = CACHE if cache is None else cache

    def tmo() -> int:
        return int(full if deadline is None else max(1, min(full, deadline - clock())))

    def late() -> bool:
        return deadline is not None and deadline - clock() < AUDIT_MIN_PIN_S

    if not versions:
        return UNKNOWN, "the row lists no pin"
    hook = FS.hooks(proof)
    if hook:
        return SORRY, f"hook check: {hook}; not compiled"[:300]
    src = AG.text_of(row.get("src"))
    sha = AG.sha16(src)

    def reference(kind: str, v: str, fn):
        """The reference proof's reading of `kind` ("axioms" | "finer") on pin v: once per (row, pin, sha) for the process."""
        if not src.strip():
            return {"error": "the row has no reference proof"}
        if late():
            return None
        t = tmo()
        return cache.get((kind, row.get("name"), v, sha), lambda: fn(row, src, v, t), keep=lambda r: keep_reading(r, t < full),
                         wait_s=t + WAIT_MARGIN_S)

    def own_finer(v: str):
        if late():
            return None
        try:
            return fread(row, proof, v, tmo())
        except Exception as e:  # noqa: BLE001
            return {"error": f"{type(e).__name__}: {str(e)[:160]}"}

    unknown, construction, read_ok = [], [], []
    for v in versions:
        if late():
            unknown.append(f"{v}: the audit deadline was reached")
            continue
        try:
            rd = read(row, proof, v, tmo())
        except Exception as e:  # noqa: BLE001  (as the published gate: a reading that raises is unknown)
            unknown.append(f"{v}: {type(e).__name__}: {str(e)[:80]}")
            continue
        if not isinstance(rd, dict):
            unknown.append(f"{v}: the reader returned {type(rd).__name__}")
            continue
        ref = reference("axioms", v, read) if AG.needs_reference(rd) else None
        finer = (own_finer(v), reference("finer", v, fread)) if AG.needs_finer(rd, ref) else (None, None)
        code, why = pin_verdict(rd, ref, finer)
        if code == PIN_BAD:
            return SORRY, f"axiom audit on {v}: {why}"[:300]
        if code == PIN_UNKNOWN:
            unknown.append(f"{v}: {why}")
        elif code == PIN_CONSTRUCTION:
            construction.append(v)
        else:
            read_ok.append(f"{v}: {why}")
    if unknown:
        return UNKNOWN, "; ".join(unknown)[:300]
    if construction:
        return SKIPPED, (f"sorry message check only on {', '.join(construction)} (a `module` file before v4.30: no axiom list); no sorry"
                         + (f"; {'; '.join(read_ok)}" if read_ok else ""))[:300]
    return CLEAN, f"no sorry on {len(versions)} pin(s): {'; '.join(read_ok)}"[:300]
