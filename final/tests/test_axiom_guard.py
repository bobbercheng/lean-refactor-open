#!/usr/bin/env python3
"""Tests of the axiom guard (harness/axiom_guard.py) and of its two places in run.sh (2026-11-24).

They start no Lean, no model and no network. The compile layer is replaced by stand-ins: a reader that returns a reading per proof
text, or scorer.compile's functions patched to return a recorded Lean message list. The one test of the shipped reader runs it on a
machine without the library environments, where every reading fails before any Lean starts. From this folder's parent:
    python3 -B -m unittest discover -s tests -v
The tests write small files into new folders under the system temp directory (TMPDIR) and leave them there."""
from __future__ import annotations

import hashlib, json, os, random, re, stat, subprocess, sys, tempfile, threading, time, unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
ROWS_FILE = ROOT / "data/official/rows.jsonl"
os.environ.setdefault("LRA_ROWS_FILE", str(ROWS_FILE))
os.environ.setdefault("LRA_HBS_FILE", str(ROOT / "data/official/heartbeats.jsonl"))
from harness import axiom_guard as AG  # noqa: E402
from harness import option_guard as KG  # noqa: E402

# These tests are the guard as published (tag open-camready-20261125), so they run with the finer sorry check off: off must restore
# that behaviour exactly. tests/test_finer_sorry.py tests the check on, and compares off with the published guard itself. The switch
# is set for this module's tests only (setUpModule / tearDownModule, review 2026-11-24) and for the scripts they start (ENV).
_FINER_BEFORE = None


def setUpModule():
    global _FINER_BEFORE
    _FINER_BEFORE = os.environ.get(AG.FINER_ENV)
    os.environ[AG.FINER_ENV] = "off"


def tearDownModule():
    if _FINER_BEFORE is None:
        os.environ.pop(AG.FINER_ENV, None)
    else:
        os.environ[AG.FINER_ENV] = _FINER_BEFORE


ENV = dict(os.environ, PYTHONDONTWRITEBYTECODE="1", LRA_AXIOM_GUARD_FINER="off")
STD = ["propext", "Classical.choice", "Quot.sound"]
GOOD = {"axioms": STD}
SORRY = {"axioms": ["sorryAx"]}
MEASURED = ("post_stage.sh", "pf_drive.py", "pf_svc.py", "pf_worker.py", "prefix_backend.py", "snapshot.py", "merge_post.py")
FINGERPRINT = "b4ac6d42002767a0"   # the seven post-stage scripts as measured for tier B on 2026-11-25


def rows() -> list:
    return [json.loads(l) for l in ROWS_FILE.read_text().splitlines() if l.strip()]


def tmpdir() -> Path:
    return Path(tempfile.mkdtemp(prefix="lra-axiom-guard-"))


def write_jsonl(path: Path, recs: list) -> None:
    path.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in recs))


def proof(row: dict, tag: str) -> str:
    """A proof text of the row marked with `tag` (the stand-in reader keys on the mark)."""
    return row["statement"] + f" := by\n  -- mark:{tag}:\n  exact foo\n"


def rec(row: dict, tag: str, score: float, source: str = "post") -> dict:
    return {"name": row["name"], "proof": proof(row, tag), "source": source, "stored_score": score, "tokens": 10, "heartbeats": 100}


class StubReader:
    """readings by mark: {tag: reading | callable(row, pin) -> reading}; the reference proof (no mark) reads `ref`; records the calls."""

    def __init__(self, by_tag: dict, ref=None, default=GOOD, delay: float = 0.0):
        self.by_tag, self.ref, self.default, self.delay = by_tag, ref, default, delay
        self.calls, self.lock = [], threading.Lock()

    def __call__(self, row, text, pin, timeout):
        m = re.search(r"-- mark:(\w+):", text)
        with self.lock:
            self.calls.append((row["name"], m.group(1) if m else "reference", pin, timeout))
        if self.delay:
            time.sleep(self.delay)
        r = (self.by_tag.get(m.group(1), self.default) if m else (self.ref if self.ref is not None else self.default))
        return r(row, pin) if callable(r) else r


def quiet():
    lines = []
    return lines, lines.append


# ------------------------------------------------------------------------------------------------------------------------ the rule
class Rule(unittest.TestCase):
    def test_standard_axioms_on_every_pin_pass(self):
        v, why, st = AG.classify({"v4.34.1": GOOD, "v4.34.0": {"axioms": ["propext", "Quot.sound"]}})
        self.assertEqual(v, AG.PASS, why)
        self.assertEqual({p: s for p, (s, _) in st.items()}, {"v4.34.1": AG.OK, "v4.34.0": AG.OK})
        self.assertEqual(AG.classify({"v4.34.0": {"axioms": []}})[0], AG.PASS)   # "does not depend on any axioms"

    def test_sorryAx_alone_fails(self):
        """The held-out row 42: no Lean message at all, `#print axioms` reads sorryAx alone."""
        v, why, _ = AG.classify({"v4.34.0": {"axioms": ["sorryAx"], "sorry_warning": False, "decl_errors": []}})
        self.assertEqual(v, AG.FAIL)
        self.assertIn("sorryAx", why)
        self.assertIn("the value is sorry", why)

    def test_sorryAx_with_others_fails(self):
        for axs in (["propext", "sorryAx"], ["propext", "Classical.choice", "Quot.sound", "sorryAx"]):
            v, why, _ = AG.classify({"v4.31.0": {"axioms": axs}})
            self.assertEqual(v, AG.FAIL, axs)
            self.assertIn("sorryAx", why)

    def test_any_other_axiom_fails(self):
        for ax in ("Lean.ofReduceBool", "Lean.trustCompiler", "myAxiom", "Classical.em"):
            self.assertEqual(AG.classify({"v4.31.0": {"axioms": STD + [ax]}})[0], AG.FAIL, ax)

    def test_sorry_message_fails_even_with_standard_axioms(self):
        self.assertEqual(AG.classify({"v4.31.0": dict(GOOD, sorry_warning=True)})[0], AG.FAIL)
        self.assertEqual(AG.classify({"v4.31.0": {"axioms": None, "sorry_warning": True}})[0], AG.FAIL)
        self.assertEqual(AG.classify({"v4.31.0": dict(GOOD, switch=True)})[0], AG.FAIL)   # a text that can hide the message

    def test_no_print_on_a_v4_27_module_pin_with_a_good_other_pin_passes(self):
        v, why, st = AG.classify({"v4.31.0": GOOD, "v4.27.0": {"axioms": None, "module": True, "decl_errors": []}})
        self.assertEqual(v, AG.PASS)
        self.assertEqual(st["v4.27.0"][0], AG.NOT_READ)
        self.assertIn("not read on v4.27.0", why)
        self.assertIn("module", why)

    def test_no_print_on_every_pin_is_not_read_never_pass(self):
        v, why, _ = AG.classify({"v4.31.0": {"axioms": None}, "v4.27.0": {"axioms": None, "module": True}})
        self.assertEqual(v, AG.NOT_READ)
        self.assertEqual(AG.classify({})[0], AG.NOT_READ)

    def test_a_bad_pin_beats_good_ones(self):
        self.assertEqual(AG.classify({"v4.34.1": GOOD, "v4.34.0": SORRY})[0], AG.FAIL)
        self.assertEqual(AG.classify({"v4.31.0": {"axioms": None}, "v4.27.0": SORRY})[0], AG.FAIL)
        self.assertEqual(AG.classify({"v4.31.0": None, "v4.27.0": SORRY})[0], AG.FAIL)

    def test_readings_that_failed_are_never_ok(self):
        for r in (None, {"error": "FileNotFoundError: no env"}, dict(GOOD, timed_out=True), {"axioms": None},
                  dict(GOOD, decl_errors=["12:3: unknown identifier"])):
            self.assertEqual(AG.pin_state(r)[0], AG.NOT_READ, r)
        self.assertEqual(AG.classify({"a": GOOD, "b": {"error": "x"}})[0], AG.PASS)   # one OK pin and no BAD pin
        self.assertEqual(AG.classify({"a": dict(GOOD, timed_out=True), "b": None})[0], AG.NOT_READ)

    def test_evidence_of_sorry_decides_before_a_timeout_or_an_error_in_the_declaration(self):
        """Review 2026-11-24: a reading that timed out (or reports an error) but carries a sorry message or sorryAx is BAD, not NOT READ."""
        for r in ({"axioms": None, "timed_out": True, "sorry_warning": True}, {"axioms": ["sorryAx"], "timed_out": True},
                  {"axioms": None, "timed_out": True, "switch": True}, {"axioms": ["sorryAx"], "decl_errors": ["12:3: type mismatch"]}):
            self.assertEqual(AG.pin_state(r)[0], AG.BAD, r)
        self.assertEqual(AG.classify({"v4.31.0": GOOD, "v4.27.0": {"axioms": ["sorryAx"], "timed_out": True}})[0], AG.FAIL)
        self.assertEqual(AG.pin_state({"error": "x", "sorry_warning": True})[0], AG.NOT_READ)   # the guard's own wrapper failed

    def test_structural_not_read_is_only_the_module_case(self):
        self.assertTrue(AG.structural({"axioms": None, "module": True, "decl_errors": []}))
        for r in (None, {"axioms": None}, {"axioms": None, "module": True, "timed_out": True}, {"error": "x", "module": True},
                  {"axioms": None, "module": True, "decl_errors": ["1:1: e"]}, {"axioms": None, "module": True, "sorry_warning": True},
                  dict(GOOD, module=True)):
            self.assertFalse(AG.structural(r), r)
        self.assertEqual(AG.unread_in_time({"a": GOOD, "b": {"axioms": None, "module": True}, "c": None, "d": dict(GOOD, timed_out=True)}),
                         ["c", "d"])

    def test_the_tier_b_reading_passes_unchanged(self):
        """The fresh read of the 81.466 output (2026-11-24; RESULTS.md, "Revised package, measured"): on every pin the print reads the standard
        axioms with no sorry message, except the v4.27.0 pins of the 10 Strata rows (rows 0-9), where it gives no list. Under the
        guard's rule every row passes, so the guard leaves that file as it is."""
        rs = rows()
        n = 0
        for k, r in enumerate(rs):
            vs = AG.versions_of(r)
            readings = {v: ({"axioms": None, "module": True} if k < 10 and v == "v4.27.0" else GOOD) for v in vs}
            n += len(vs)
            self.assertEqual(AG.classify(readings)[0], AG.PASS, r["name"])
        self.assertEqual(n, 127)
        self.assertEqual(sum(1 for r in rs[:10] if "v4.27.0" in AG.versions_of(r)), 10)


class RelativeRule(unittest.TestCase):
    """The allowance (2026-11-24, the export audit's rule): an axiom outside the three passes on a pin when the row's reference proof
    reads it on that pin too, in a complete reading. When that reading is not available the pin is BAD (fail closed), never NOT READ:
    a row NOT READ keeps its proof."""

    def test_sorryAx_with_the_reference_reading_sorryAx_is_ok(self):
        for axs, ref_axs in ((["sorryAx"], ["sorryAx"]), (["sorryAx"], ["propext", "sorryAx"]), (STD + ["sorryAx"], ["sorryAx"]),
                             (["propext", "sorryAx"], STD + ["sorryAx", "myAxiom"])):
            st, why = AG.pin_state({"axioms": axs}, {"axioms": ref_axs})
            self.assertEqual(st, AG.OK, (axs, ref_axs, why))
            self.assertEqual(why, "axioms as the reference proof: ['sorryAx']")
        readings = {"v4.34.1": SORRY, "v4.34.0": GOOD}
        v, why, _ = AG.classify(readings, {"v4.34.1": SORRY})
        self.assertEqual(v, AG.PASS, why)
        self.assertEqual(why, "standard axioms on v4.34.0; axioms as the reference proof on v4.34.1: ['sorryAx']")
        self.assertEqual(AG.allowance_pins(readings, {"v4.34.1": SORRY}), ["v4.34.1"])
        self.assertEqual(AG.allowance_pins({"v4.34.1": GOOD}, {"v4.34.1": SORRY}), [])   # standard axioms need no allowance

    def test_sorryAx_with_the_reference_reading_standard_axioms_is_bad(self):
        """The held-out row 42: the reference proof reads standard axioms, the output sorryAx with no Lean message."""
        for ref in (GOOD, {"axioms": []}, {"axioms": ["propext"]}):
            st, why = AG.pin_state(SORRY, ref)
            self.assertEqual(st, AG.BAD, ref)
            self.assertIn("the value is sorry", why)
            self.assertIn("the reference proof reads standard axioms here", why)
        self.assertEqual(AG.classify({"v4.34.1": SORRY, "v4.34.0": GOOD}, {"v4.34.1": GOOD, "v4.34.0": GOOD})[0], AG.FAIL)

    def test_fail_closed_when_the_reference_reading_is_not_available(self):
        """Not read (in time), a reader error, a timeout (even one that printed sorryAx), no list, an error in its declaration, Lean's
        sorry message on its declaration, a switch, or no reference reading passed at all: BAD."""
        for ref in (None, {"error": "not started: the time budget ran out"}, {"error": "RuntimeError: no env"},
                    {"axioms": ["sorryAx"], "timed_out": True}, {"axioms": None, "timed_out": True}, {"axioms": None},
                    {"axioms": None, "module": True}, {"axioms": ["sorryAx"], "decl_errors": ["3:1: unknown identifier"]},
                    {"axioms": ["sorryAx"], "sorry_warning": True}, {"axioms": ["sorryAx"], "switch": True}, "not a reading"):
            st, why = AG.pin_state(SORRY, ref)
            self.assertEqual(st, AG.BAD, ref)
            self.assertIn("not available", why)
            self.assertIsNone(AG.ref_allowance(ref)[0], ref)
            self.assertEqual(AG.classify({"v4.31.0": SORRY, "v4.27.0": GOOD}, {"v4.31.0": ref, "v4.27.0": GOOD})[0], AG.FAIL, ref)
        self.assertEqual(AG.classify({"v4.31.0": SORRY})[0], AG.FAIL)                          # no reference readings at all
        self.assertEqual(AG.classify({"v4.31.0": SORRY}, {"v4.27.0": SORRY})[0], AG.FAIL)      # the reference's reading is per pin

    def test_a_custom_axiom_passes_only_when_the_reference_reads_it_on_that_pin(self):
        my = {"axioms": STD + ["myAxiom"]}
        self.assertEqual(AG.pin_state(my, {"axioms": ["propext", "myAxiom"]}), (AG.OK, "axioms as the reference proof: ['myAxiom']"))
        st, why = AG.pin_state(my, SORRY)                                  # absent from the reference's reading: BAD
        self.assertEqual((st, why), (AG.BAD, "axioms ['myAxiom']; the reference proof reads ['sorryAx'] here, not ['myAxiom']"))
        self.assertEqual(AG.pin_state({"axioms": ["sorryAx", "myAxiom"]}, SORRY)[0], AG.BAD)   # one axiom outside its set is enough
        self.assertEqual(AG.pin_state({"axioms": ["Lean.ofReduceBool"]}, {"axioms": ["Lean.ofReduceBool", "sorryAx"]})[0], AG.OK)
        self.assertEqual(AG.classify({"a": my, "b": my}, {"a": my, "b": GOOD})[0], AG.FAIL)   # read on another pin: allows nothing here

    def test_a_sorry_message_or_a_switch_is_bad_whatever_the_reference_reads(self):
        for r in (dict(SORRY, sorry_warning=True), dict(GOOD, sorry_warning=True), {"axioms": None, "sorry_warning": True},
                  dict(SORRY, switch=True)):
            self.assertEqual(AG.pin_state(r, SORRY)[0], AG.BAD, r)
            self.assertEqual(AG.classify({"v4.31.0": r}, {"v4.31.0": SORRY})[0], AG.FAIL, r)
            self.assertFalse(AG.needs_reference(r), r)   # decided without the reference: it is not read for it

    def test_the_allowance_needs_a_complete_reading_of_the_proof(self):
        """A reading with an axiom outside the three whose compile timed out or reports an error in the declaration is BAD even when
        the reference reads the same axioms (its sorryAx may come from that error); the reference is not read for it."""
        for r in (dict(SORRY, timed_out=True), dict(SORRY, decl_errors=["5:2: type mismatch"])):
            self.assertEqual(AG.pin_state(r, SORRY)[0], AG.BAD, r)
            self.assertFalse(AG.needs_reference(r), r)
        self.assertTrue(AG.needs_reference(SORRY))
        self.assertTrue(AG.needs_reference({"axioms": STD + ["myAxiom"]}))
        for r in (GOOD, {"axioms": []}, None, {"axioms": None}, {"error": "x", "axioms": ["sorryAx"]}):
            self.assertFalse(AG.needs_reference(r), r)

    def test_the_reference_allows_only_what_every_print_reads(self):
        """Review 2026-11-24: the reading holds the union of the two prints' lists. When one name resolves to another constant that
        reads sorryAx, that union would let a proof whose own value is sorry through on a reference whose own declaration is standard.
        The allowance is what every print of the reference reads (the intersection); prints that differ without their lists: none."""
        other = {"axioms": STD + ["sorryAx"], "lists": [STD, STD + ["sorryAx"]], "prints": 2, "prints_differ": True}
        self.assertEqual(AG.ref_allowance(other), (frozenset(), "read"))
        st, why = AG.pin_state({"axioms": STD + ["sorryAx"], "prints_differ": True}, other)
        self.assertEqual((st, why), (AG.BAD, "axioms ['sorryAx'] (the value is sorry); the reference proof reads standard axioms here"))
        self.assertEqual(AG.pin_state(dict(SORRY, prints_differ=True), {"axioms": STD + ["sorryAx"], "prints_differ": True})[0], AG.BAD)
        self.assertIsNone(AG.ref_allowance({"axioms": ["sorryAx"], "prints_differ": True})[0])
        both = {"axioms": STD + ["sorryAx", "myAxiom"], "lists": [["sorryAx", "propext"], ["sorryAx", "myAxiom"] + STD], "prints_differ": True}
        self.assertEqual(AG.ref_allowance(both)[0], frozenset({"sorryAx"}))   # held-out row 25's case still passes
        self.assertEqual(AG.pin_state(SORRY, both), (AG.OK, "axioms as the reference proof: ['sorryAx']"))
        self.assertEqual(AG.pin_state({"axioms": ["myAxiom"]}, both)[0], AG.BAD)
        one = {"axioms": ["sorryAx"], "lists": [["sorryAx"]], "prints": 1, "prints_differ": False}
        self.assertEqual(AG.ref_allowance(one)[0], frozenset({"sorryAx"}))

    def test_the_reference_proof_judged_against_its_own_reading(self):
        """The reference proof as the last candidate: on axioms it passes by construction (its axioms are the allowance), but only with
        a complete reading of its own; without one it fails or is not read, as any proof."""
        for R, want in ((SORRY, AG.PASS), (GOOD, AG.PASS), ({"axioms": STD + ["sorryAx", "myAxiom"]}, AG.PASS),
                        (dict(SORRY, sorry_warning=True), AG.FAIL), (dict(GOOD, sorry_warning=True), AG.FAIL), (dict(SORRY, switch=True), AG.FAIL),
                        (dict(SORRY, timed_out=True), AG.FAIL), (dict(SORRY, decl_errors=["1:1: e"]), AG.FAIL), (None, AG.NOT_READ),
                        ({"error": "x"}, AG.NOT_READ), ({"axioms": None}, AG.NOT_READ), (dict(GOOD, decl_errors=["1:1: e"]), AG.NOT_READ),
                        (dict(GOOD, timed_out=True), AG.NOT_READ)):
            self.assertEqual(AG.classify({"v4.31.0": R}, {"v4.31.0": R})[0], want, R)


# --------------------------------------------------------------------------------------------------------------------- the reading
class Reading(unittest.TestCase):
    """forced_reading builds the verifier's text and reads Lean's messages with scorer.compile's own parser."""

    def fake_result(self, msgs, ok=True, timed_out=False):
        from scorer.compile import CompileResult
        return CompileResult(ok, None, 1.5, [f"{m['pos']['line']}:0: {m['data']}" for m in msgs if m["severity"] == "error"],
                             timed_out=timed_out, messages=msgs)

    def test_project_row_text_and_flags(self):
        from scorer import compile as C
        r = next(x for x in rows() if x["source"] == "strata")
        core = "module\n\nimport Foo\n\nnamespace Lambda\n\n"
        seen = {}
        pf = proof(r, "x")

        def cp(row, text, version, *, count=True, timeout=900, lean_args=None, _quiet_prefix_sorry=False):
            seen.update(text=text, version=version, count=count, timeout=timeout, lean_args=lean_args)
            first = C._first_line(core)
            pl = first + 1 + (pf.rstrip() + "\n\n").count("\n")
            return self.fake_result([{"severity": "information", "pos": {"line": pl + 1}, "data": "'Lambda.x' depends on axioms: [propext, sorryAx]"},
                                     {"severity": "warning", "pos": {"line": 2}, "data": "declaration uses 'sorry'"}])   # in the prefix: not ours
        with mock.patch.object(C, "file_prefix", return_value=core), mock.patch.object(C, "lakefile_options", return_value=("-Dwarn.sorry=false",)), \
                mock.patch.object(C, "compile_project", side_effect=cp):
            got = AG.forced_reading(r, pf, "v4.27.0", 123.7)
        name = C.decl_name(r["statement"], r["name"])
        self.assertFalse(seen["count"])
        self.assertEqual(seen["timeout"], 123)
        self.assertEqual(seen["lean_args"][-1], "-Dwarn.sorry=true")
        self.assertNotIn("-Dwarn.sorry=false", seen["lean_args"])
        want = pf.rstrip() + "\n\n" + "".join(f"set_option pp.fullNames true in\n#print axioms {n}\n"
                                               for n in dict.fromkeys([name, C.qualified_name(name, "Lambda")]))
        self.assertEqual(seen["text"], want)
        self.assertEqual(got["axioms"], ["propext", "sorryAx"])
        self.assertTrue(got["module"])          # forced inside a module file (scorer.compile.audit_axioms skips those)
        self.assertFalse(got["sorry_warning"])  # the prefix's sorry message is the library's
        self.assertEqual(AG.pin_state(got)[0], AG.BAD)

    def test_sorry_message_on_the_declaration_and_no_list(self):
        from scorer import compile as C
        r = next(x for x in rows() if x["source"] == "cslib")
        core = "import Foo\n\n"
        pf = proof(r, "x")

        def cp(row, text, version, **kw):
            return self.fake_result([{"severity": "warning", "pos": {"line": C._first_line(core) + 2}, "data": "declaration uses 'sorry'"}])
        with mock.patch.object(C, "file_prefix", return_value=core), mock.patch.object(C, "lakefile_options", return_value=()), \
                mock.patch.object(C, "compile_project", side_effect=cp):
            got = AG.forced_reading(r, pf, "v4.31.0", 60)
        self.assertIsNone(got["axioms"])
        self.assertTrue(got["sorry_warning"])
        self.assertFalse(got["module"])
        self.assertEqual(AG.pin_state(got)[0], AG.BAD)

    def test_both_prints_are_read_and_a_sorryAx_in_either_fails(self):
        """Review 2026-11-24: scorer.compile.parse_axioms keeps the LAST print; when the qualified name resolves to another constant
        (current_namespace misreads `public noncomputable section`), its clean list would hide the declaration's sorryAx. The guard
        reads the union of both prints."""
        from scorer import compile as C
        r = next(x for x in rows() if x["source"] == "strata")
        core = "import Foo\n\nnamespace Lambda\n\n"
        pf = proof(r, "x")
        for lists in ((["propext", "sorryAx"], ["propext"]), (["propext"], ["propext", "sorryAx"])):
            def cp(row, text, version, **kw):
                pl = C._first_line(core) + 1 + (pf.rstrip() + "\n\n").count("\n")
                return self.fake_result([{"severity": "information", "pos": {"line": pl + 1}, "data": f"'x' depends on axioms: [{', '.join(lists[0])}]"},
                                         {"severity": "information", "pos": {"line": pl + 3}, "data": f"'Lambda.x' depends on axioms: [{', '.join(lists[1])}]"}])
            with mock.patch.object(C, "file_prefix", return_value=core), mock.patch.object(C, "lakefile_options", return_value=()), \
                    mock.patch.object(C, "compile_project", side_effect=cp):
                got = AG.forced_reading(r, pf, "v4.31.0", 60)
            self.assertEqual(sorted(got["axioms"]), ["propext", "sorryAx"], lists)
            self.assertEqual(got["lists"], list(lists))   # each print's list, in order: the reference's allowance is their intersection
            self.assertEqual(AG.ref_allowance(got)[0], frozenset())
            self.assertTrue(got["prints_differ"])
            self.assertEqual(got["prints"], 2)
            self.assertEqual(AG.pin_state(got)[0], AG.BAD, lists)

        def same(row, text, version, **kw):   # both names resolve to the same constant: one list, as before
            pl = C._first_line(core) + 1 + (pf.rstrip() + "\n\n").count("\n")
            return self.fake_result([{"severity": "information", "pos": {"line": pl + k}, "data": "'Lambda.x' does not depend on any axioms"}
                                     for k in (1, 3)])
        with mock.patch.object(C, "file_prefix", return_value=core), mock.patch.object(C, "lakefile_options", return_value=()), \
                mock.patch.object(C, "compile_project", side_effect=same):
            got = AG.forced_reading(r, pf, "v4.31.0", 60)
        self.assertEqual((got["axioms"], got["prints_differ"]), ([], False))
        self.assertEqual(AG.pin_state(got), (AG.OK, "no axioms"))

    def test_putnam_row_and_timeout(self):
        from scorer import compile as C
        r = next(x for x in rows() if x["source"] == "putnambench")
        seen = {}

        def cpu(header, text, version, *, count=True, timeout=600):
            seen.update(header=header, count=count, timeout=timeout, text=text)
            return self.fake_result([], ok=False, timed_out=True)
        with mock.patch.object(C, "compile_putnam", side_effect=cpu):
            got = AG.forced_reading(r, r["src"], "v4.9.0", 0.2)
        self.assertEqual(seen["header"], r["header"])
        self.assertFalse(seen["count"])
        self.assertEqual(seen["timeout"], 1)
        self.assertIn("#print axioms", seen["text"])
        self.assertEqual(AG.pin_state(got), (AG.NOT_READ, "the compile timed out"))


# ------------------------------------------------------------------------------------------------------------------------ the file
class Fallback(unittest.TestCase):
    def setUp(self):
        self.rs = rows()[10:14]   # PhysLib rows: two pins each
        self.d = tmpdir()
        write_jsonl(self.d / "rows.jsonl", self.rs)
        self.p = self.d / "proofs.jsonl"
        write_jsonl(self.p, [rec(r, f"cur{k}", 70.0 + k) for k, r in enumerate(self.rs)])
        write_jsonl(self.d / "proofs.picks.jsonl", [rec(r, f"picks{k}", 60.0 + k, "agent") for k, r in enumerate(self.rs)])
        write_jsonl(self.d / "proofs.export.jsonl", [rec(r, f"export{k}", 50.0 + k, "agent") for k, r in enumerate(self.rs)])
        self.raw = self.p.read_text().splitlines()

    def guard(self, reader, **kw):
        lines, log = quiet()
        kw.setdefault("budget_s", 30)
        rep = AG.guard_file(self.p, self.d / "rows.jsonl", kw.pop("fallbacks", None), reader=reader, log=log, **kw)
        return rep, "\n".join(lines)

    def line(self, k):
        return json.loads(self.p.read_text().splitlines()[k])

    def test_every_row_passes_and_the_file_is_not_touched(self):
        st = os.stat(self.p)
        rep, log = self.guard(StubReader({}))
        self.assertEqual((rep["rc"], rep["written"], rep["replaced"]), (0, False, []))
        self.assertEqual(os.stat(self.p).st_mtime_ns, st.st_mtime_ns)
        self.assertEqual(self.p.read_text().splitlines(), self.raw)
        self.assertFalse((self.d / "proofs.jsonl.axiom-guard").exists())
        self.assertEqual(rep["readings_done"], 8)
        self.assertIn("axiom guard: OK: 4 rows: 4 pass", log.splitlines()[-1])

    def test_the_post_stage_input_comes_first(self):
        rep, log = self.guard(StubReader({"cur1": SORRY}))
        self.assertEqual(rep["rc"], 0)
        new = self.line(1)
        self.assertEqual((new["proof"], new["source"], new["stored_score"]), (proof(self.rs[1], "picks1"), "agent", 61.0))
        self.assertIn("sorryAx", new["axiom_guard"])
        got = self.p.read_text().splitlines()
        self.assertEqual([got[k] for k in (0, 2, 3)], [self.raw[k] for k in (0, 2, 3)])   # every other line byte for byte
        self.assertEqual((self.d / "proofs.jsonl.axiom-guard").read_text().splitlines(), self.raw)
        d = rep["per_row"][1]
        self.assertEqual((d["verdict"], d["chosen"], d["old_stored_score"], d["new_stored_score"]), (AG.FAIL, "proofs.picks.jsonl", 71.0, 61.0))
        self.assertIn(f"row 1 {self.rs[1]['name']}: FAIL", log)
        self.assertIn("REPLACED by the post stage's input, stored 71.0 -> 61.0, source post -> agent", log)

    def test_then_the_agent_export_then_the_reference(self):
        self.guard(StubReader({"cur0": SORRY, "picks0": SORRY, "cur2": SORRY, "picks2": SORRY, "export2": SORRY}))
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "export0"))
        r2 = self.line(2)
        self.assertEqual((r2["proof"], r2["source"], r2["stored_score"]), (self.rs[2]["src"].rstrip() + "\n", "seed", KG.SEED_SCORE))
        self.assertEqual(self.line(1)["proof"], proof(self.rs[1], "cur1"))

    def test_one_bad_pin_is_enough_and_a_candidate_must_pass_on_every_pin_it_reads(self):
        bad_old = lambda row, pin: SORRY if pin == AG.versions_of(row)[-1] else GOOD
        self.guard(StubReader({"cur3": bad_old, "picks3": bad_old}))
        self.assertEqual(self.line(3)["proof"], proof(self.rs[3], "export3"))

    def test_when_no_proof_passes_the_reference_is_written_and_the_exit_status_says_so(self):
        """The reference proof shows Lean's sorry message on its own declaration: it allows nothing (fail closed) and does not pass."""
        rep, log = self.guard(StubReader({"cur1": SORRY, "picks1": SORRY, "export1": SORRY}, ref=dict(SORRY, sorry_warning=True)))
        self.assertEqual(rep["rc"], AG.RC_NOT_READ)
        self.assertEqual(rep["reference_not_passing"], [self.rs[1]["name"]])
        self.assertEqual(self.line(1)["proof"], self.rs[1]["src"].rstrip() + "\n")
        self.assertIn("did not pass either", log)
        self.assertIn("NOT EVERY ROW READ AND PASSING", log.splitlines()[-1])

    def test_candidates_that_cannot_stand_are_left_out(self):
        r = self.rs[0]
        cur = proof(r, "cur0")
        fb = [("proofs.picks.jsonl", {r["name"]: {"name": r["name"], "proof": cur}}),                          # the failing text itself
              ("a", {r["name"]: {"name": r["name"], "proof": "theorem other : True := trivial\n"}}),             # not the row's statement
              ("b", {r["name"]: {"name": r["name"], "proof": proof(r, "dbg").replace("exact foo", "set_option debug.example true in exact foo")}}),
              ("c", {r["name"]: {"name": r["name"], "proof": proof(r, "sry").replace("exact foo", "sorry")}}),    # the Arena's list
              ("d", {r["name"]: {"name": r["name"], "proof": proof(r, "ok")}}),
              ("e", {r["name"]: {"name": r["name"], "proof": proof(r, "ok")}})]                                  # the same text again
        got = AG.candidates(r["name"], r, cur, fb)
        self.assertEqual([role for role, _ in got], ["d", "reference"])
        self.assertEqual(AG.candidates(r["name"], r, r["src"], fb[4:])[-1][0], "d")   # the reference is the failing text: not again

    def test_explicit_fallbacks_keep_their_order_and_a_broken_file_is_skipped(self):
        (self.d / "broken.jsonl").write_text("not json\n")
        rep, log = self.guard(StubReader({"cur0": SORRY}), fallbacks=[self.d / "broken.jsonl", self.d / "proofs.export.jsonl",
                                                                       self.d / "proofs.picks.jsonl", self.d / "missing.jsonl"])
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "export0"))
        self.assertIn("broken.jsonl not used", log)
        self.assertIn("missing.jsonl not used", log)

    def test_default_fallbacks_are_the_siblings_that_exist(self):
        (self.d / "proofs.picks.jsonl").unlink()
        self.guard(StubReader({"cur0": SORRY}))
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "export0"))

    def test_a_record_without_proof_text_and_a_row_not_in_the_rows_file(self):
        recs = [json.loads(l) for l in self.raw]
        recs[0]["proof"] = ""
        recs[2]["name"] = "no such row"
        write_jsonl(self.p, recs)
        rep, log = self.guard(StubReader({}))
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"))
        self.assertEqual(rep["not_read"], ["no such row"])
        self.assertEqual(rep["rc"], AG.RC_NOT_READ)
        self.assertEqual(self.line(2)["name"], "no such row")   # kept as it is

    def test_no_write(self):
        rep, log = self.guard(StubReader({"cur1": SORRY}), write=False)
        self.assertEqual((rep["written"], rep["replaced"]), (False, [self.rs[1]["name"]]))
        self.assertEqual(self.p.read_text().splitlines(), self.raw)
        self.assertIn("(--no-write)", log.splitlines()[-1])

    def test_the_first_content_is_kept_once(self):
        self.guard(StubReader({"cur1": SORRY}))
        first = (self.d / "proofs.jsonl.axiom-guard").read_bytes()
        self.guard(StubReader({"cur0": SORRY}))
        self.assertEqual((self.d / "proofs.jsonl.axiom-guard").read_bytes(), first)
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"))
        self.assertEqual(self.line(1)["proof"], proof(self.rs[1], "picks1"))

    def test_report_holds_no_proof_text(self):
        rep, _ = self.guard(StubReader({"cur1": SORRY}))
        text = json.dumps(rep)
        self.assertNotIn("exact foo", text)
        self.assertNotIn(self.rs[1]["statement"][:40], text)

    def test_the_merged_file_is_set_back_too(self):
        """Review 2026-11-24: proofs.merged.jsonl (merge_post's copy, merged back by a resumed job and by `run.sh export`) gets the same
        replacement, so the failing proof does not come back; its other lines, and a line that holds another proof, stay byte for byte."""
        merged = self.d / "proofs.merged.jsonl"
        recs = [json.loads(l) for l in self.raw]
        recs[2] = rec(self.rs[2], "other2", 75.0)   # row 2's merged line holds another proof than proofs.jsonl
        write_jsonl(merged, recs)
        mraw = merged.read_text().splitlines()
        rep, log = self.guard(StubReader({"cur1": SORRY, "cur2": SORRY}))
        self.assertTrue(rep["merged_written"])
        got = merged.read_text().splitlines()
        self.assertEqual(json.loads(got[1])["proof"], proof(self.rs[1], "picks1"))
        self.assertEqual(got[1], self.p.read_text().splitlines()[1])
        self.assertEqual([got[k] for k in (0, 2, 3)], [mraw[k] for k in (0, 2, 3)])
        self.assertEqual((self.d / "proofs.merged.jsonl.axiom-guard").read_text().splitlines(), mraw)
        self.assertIn("proofs.merged.jsonl: the same 1 row(s) set back", log)
        # what merge_post does on the next `run.sh export`: the set-back line comes back, not the failing proof
        from post_fast import merge_post
        write_jsonl(self.d / "picks_as_export.jsonl", [rec(r, f"picks{k}", 60.0 + k, "agent") for k, r in enumerate(self.rs)])
        with mock.patch("builtins.print"):
            merge_post.main(str(merged), str(self.d / "rows.jsonl"), str(self.d / "picks_as_export.jsonl"))
        self.assertNotIn("mark:cur1:", (self.d / "picks_as_export.jsonl").read_text())

    def test_the_merged_file_is_not_touched_when_no_row_is_replaced_or_with_no_write(self):
        merged = self.d / "proofs.merged.jsonl"
        write_jsonl(merged, [json.loads(l) for l in self.raw])
        st = os.stat(merged)
        self.guard(StubReader({}))
        self.guard(StubReader({"cur1": SORRY}), write=False)
        self.assertEqual(os.stat(merged).st_mtime_ns, st.st_mtime_ns)
        self.assertFalse((self.d / "proofs.merged.jsonl.axiom-guard").exists())

    def test_a_file_changed_while_it_was_read_is_not_written(self):
        """Review 2026-11-24: compare-and-swap. Another writer (a live job's merge, a second export) changes PROOFS while the guard reads:
        nothing is written, exit 1."""
        def change(row, pin):
            if not getattr(change, "done", False):
                change.done = True
                with open(self.p, "a") as f:
                    f.write(self.raw[0] + "\n")
            return SORRY
        rep, log = self.guard(StubReader({"cur1": change}), jobs=1)
        self.assertEqual(rep["rc"], AG.RC_NOT_CHECKED)
        self.assertFalse(rep["written"])
        self.assertEqual(self.p.read_text().splitlines(), self.raw + [self.raw[0]])
        self.assertFalse((self.d / "proofs.jsonl.axiom-guard").exists())
        self.assertFalse((self.d / "proofs.jsonl.axiom-guard.tmp").exists())
        self.assertIn("NOT CHECKED", log.splitlines()[-1])

    def test_a_pass_with_a_toolchain_not_read_in_time_is_not_ok(self):
        """Review 2026-11-24: the newest toolchain reads clean, the older one timed out (or was never started): the row keeps its proof,
        but the exit status is 3, never 0. Only the structural `module` case may stay unread with exit 0."""
        old = lambda row, pin: GOOD if pin == AG.versions_of(row)[0] else {"axioms": None, "timed_out": True}
        rep, log = self.guard(StubReader({"cur0": old}))
        self.assertEqual(rep["rc"], AG.RC_NOT_READ)
        self.assertEqual(rep["not_read_in_full"], [self.rs[0]["name"]])
        self.assertEqual(rep["verdicts"][AG.PASS], 4)
        self.assertEqual(self.p.read_text().splitlines(), self.raw)
        self.assertIn("NOT READ IN FULL", log)
        self.assertIn("NOT EVERY ROW READ AND PASSING", log.splitlines()[-1])
        mod = lambda row, pin: GOOD if pin == AG.versions_of(row)[0] else {"axioms": None, "module": True, "decl_errors": []}
        rep, log = self.guard(StubReader({"cur0": mod}))
        self.assertEqual(rep["rc"], AG.RC_OK)
        self.assertEqual(rep["pins_not_read_structural"], 1)
        # a replacement that passes on one toolchain only, the other not read in time: written, exit 3
        rep, _ = self.guard(StubReader({"cur1": SORRY, "picks1": old}))
        self.assertEqual(self.line(1)["proof"], proof(self.rs[1], "picks1"))
        self.assertEqual((rep["rc"], rep["not_read_in_full"]), (AG.RC_NOT_READ, [self.rs[1]["name"]]))

    def test_a_proof_that_is_not_a_string_is_no_proof(self):
        recs = [json.loads(l) for l in self.raw]
        recs[0]["proof"] = 12345
        write_jsonl(self.p, recs)
        rep, _ = self.guard(StubReader({}))
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"))
        self.assertEqual(rep["rc"], AG.RC_OK)

    def test_an_empty_file_or_rows_missing_from_it_are_not_ok(self):
        write_jsonl(self.p, [json.loads(l) for l in self.raw][:2])
        rep, log = self.guard(StubReader({}))
        self.assertEqual((rep["rc"], len(rep["missing_from_file"])), (AG.RC_NOT_READ, 2))
        self.assertIn("2 row(s) of the rows file are not in", log)
        self.p.write_text("")
        rep, log = self.guard(StubReader({}))
        self.assertEqual((rep["rc"], rep["rows"]), (AG.RC_NOT_READ, 0))
        self.assertIn("holds no row", log)
        self.assertEqual(self.p.read_text(), "")

    def ref_calls(self, rd) -> list:
        return [(n, pin) for n, tag, pin, _t in rd.calls if tag == "reference"]

    def test_the_reference_is_read_only_where_a_proof_reads_another_axiom(self):
        """Lazy: no reading of a reference proof when every proof reads standard axioms; for row 1, whose proof reads sorryAx on its
        newest pin only, one reading of its reference for the allowance, on that pin, first; none for another row. The reference
        reads sorryAx there too (held-out row 25): row 1 keeps its proof, exit 0, file untouched. While that reading was pending the pin
        read BAD (fail closed), so the row's earlier proofs were read meanwhile (review 2026-11-24), the reference on the older pin
        among them as the last candidate; none of them is used."""
        rd = StubReader({})
        rep, log = self.guard(rd)
        self.assertEqual((self.ref_calls(rd), rep["reference_readings"], rep["passed_by_allowance"]), ([], 0, []))
        self.assertIn("; 0 pass only through the reference proof's axioms;", log.splitlines()[-1])
        vs = AG.versions_of(self.rs[1])
        rd = StubReader({"cur1": lambda row, pin: SORRY if pin == vs[0] else GOOD}, ref=SORRY)
        rep, log = self.guard(rd, jobs=1)
        calls = [(n, t, p) for n, t, p, _x in rd.calls]
        later = [i for i, c in enumerate(calls) if c[1] in ("picks1", "export1") or c == (self.rs[1]["name"], "reference", vs[1])]
        self.assertLess(calls.index((self.rs[1]["name"], "reference", vs[0])), min(later))   # the allowance's reading first
        self.assertEqual(sorted(c for c in calls if c[0] == self.rs[1]["name"] and c[1] != "cur1"),
                         sorted([(self.rs[1]["name"], t, v) for t in ("picks1", "export1") for v in vs] + [(self.rs[1]["name"], "reference", v) for v in vs]))
        self.assertEqual(len(calls), len(set(calls)))   # nothing read twice: the allowance's reading serves as the candidate's
        self.assertEqual((rep["rc"], rep["written"], rep["replaced"], rep["passed_by_allowance"]), (0, False, [], [self.rs[1]["name"]]))
        self.assertEqual((rep["reference_readings"], rep["reference_readings_complete"], rep["set_back_for_want_of_reference"]), (1, 1, []))
        self.assertEqual(self.p.read_text().splitlines(), self.raw)
        pins = rep["per_row"][1]["pins"]
        self.assertEqual({f: pins[vs[0]][f] for f in ("state", "allowance_used", "reference_reading", "reference_axioms", "reference_allows")},
                         {"state": AG.OK, "allowance_used": True, "reference_reading": "read", "reference_axioms": ["sorryAx"],
                          "reference_allows": ["sorryAx"]})
        self.assertEqual((pins[vs[1]]["allowance_used"], pins[vs[1]]["reference_reading"], pins[vs[1]]["reference_axioms"]),
                         (False, None, None))   # standard axioms: the allowance is not consulted
        self.assertFalse(any(p["allowance_used"] for d in rep["per_row"] if d["k"] != 1 for p in d["pins"].values()))
        self.assertIn(f"row 1 {self.rs[1]['name']}: pass (standard axioms on {vs[1]}; axioms as the reference proof on {vs[0]}: ['sorryAx'])"
                      f"; ONLY THROUGH THE ALLOWANCE on {vs[0]} (the reference proof reads ['sorryAx'])", log)
        last = log.splitlines()[-1]
        self.assertIn("axiom guard: OK: 4 rows: 4 pass, 0 read BAD, 0 set back, 0 NOT READ", last)
        self.assertIn(f"; 1 pass only through the reference proof's axioms ({self.rs[1]['name']});", last)
        self.assertIn("(1 (row, toolchain) pair(s) needed the reference proof's reading, 1 read in full)", last)

    def test_one_reference_reading_per_pin_serves_every_proof_of_the_row(self):
        """Row 1's proof and both earlier proofs read sorryAx, its reference standard axioms (on both pins): the reference is read once
        per pin for all three, and not again as the last candidate, which passes and is written."""
        rd = StubReader({"cur1": SORRY, "picks1": SORRY, "export1": SORRY})
        rep, log = self.guard(rd)
        vs = AG.versions_of(self.rs[1])
        self.assertEqual(sorted(self.ref_calls(rd)), sorted((self.rs[1]["name"], v) for v in vs))
        self.assertEqual(len(rd.calls), len({(n, t, p) for n, t, p, _x in rd.calls}))   # nothing read twice
        self.assertEqual(len(rd.calls), 8 + 2 + 2 + 2)   # the 8 first readings, the reference's 2, picks1's 2, export1's 2
        self.assertEqual(self.line(1)["proof"], self.rs[1]["src"].rstrip() + "\n")
        self.assertEqual((rep["rc"], rep["reference_readings"], rep["reference_readings_complete"], rep["passed_by_allowance"]), (0, 2, 2, []))
        self.assertEqual(rep["set_back_for_want_of_reference"], [])   # its reference reads standard axioms: BAD on the reading itself
        self.assertEqual([c["verdict"] for c in rep["per_row"][1]["candidates"]], [AG.FAIL, AG.FAIL, AG.PASS])
        self.assertIn("the reference proof reads standard axioms here", rep["per_row"][1]["candidates"][0]["why"])

    def test_a_candidate_may_pass_through_the_allowance(self):
        """Row 1's proof shows Lean's sorry message (BAD whatever the reference reads); the post stage's input reads sorryAx as its
        reference does: written, and counted as passing only through the allowance."""
        rd = StubReader({"cur1": dict(SORRY, sorry_warning=True), "picks1": SORRY}, ref=SORRY)
        rep, log = self.guard(rd)
        self.assertEqual(self.line(1)["proof"], proof(self.rs[1], "picks1"))
        self.assertEqual((rep["rc"], rep["replaced"], rep["passed_by_allowance"]), (0, [self.rs[1]["name"]], [self.rs[1]["name"]]))
        self.assertEqual(rep["per_row"][1]["chosen_allowance"], AG.versions_of(self.rs[1]))
        self.assertIn("ONLY THROUGH THE ALLOWANCE", self.line(1)["axiom_guard"])
        self.assertIn("that proof passes ONLY THROUGH THE ALLOWANCE on", log)

    def test_fail_closed_the_proof_is_set_back_when_its_reference_cannot_be_read(self):
        """Row 1's proof reads sorryAx; its reference's reading fails (a reader error, a timeout that printed sorryAx, no list, the
        reader raises): the row reads BAD and is set back to the post stage's input, never kept, never NOT READ."""
        def boom(row, pin):
            raise RuntimeError("no env")
        name, vs = self.rs[1]["name"], AG.versions_of(self.rs[1])
        for ref, why in (({"error": "x"}, "x"), ({"axioms": ["sorryAx"], "timed_out": True}, "its compile timed out"),
                         (dict(GOOD, timed_out=True), "its compile timed out"),   # a list it printed before the timeout: not read in full
                         ({"axioms": None}, "its print gave no axiom list"), (boom, "RuntimeError: no env")):
            write_jsonl(self.p, [json.loads(l) for l in self.raw])
            rep, log = self.guard(StubReader({"cur1": SORRY}, ref=ref))
            self.assertEqual(self.line(1)["proof"], proof(self.rs[1], "picks1"), ref)
            self.assertEqual((rep["rc"], rep["verdicts"][AG.FAIL], rep["not_read"], rep["passed_by_allowance"]), (0, 1, [], []), ref)
            self.assertIn("the reference proof's reading here is not available", rep["per_row"][1]["why"])
            # named apart (review 2026-11-24): the proof may be sound; the report says why the reference's reading is missing
            self.assertEqual((rep["set_back_for_want_of_reference"], rep["reference_readings"], rep["reference_readings_complete"]),
                             ([name], 2, 0), ref)
            self.assertEqual({(p["reference_reading"], p["reference_axioms"], p["reference_allows"]) for p in rep["per_row"][1]["pins"].values()},
                             {(why, None, None)}, ref)   # a timed-out reading that printed sorryAx shows no axioms
            last = log.splitlines()[-1]
            self.assertIn(f"axiom guard: OK: 4 rows: 3 pass, 1 read BAD, 1 set back ({name}) (1 of them only because the reference proof's "
                          f"reading was not available: {name}; the guard does not bring their proofs back), 0 NOT READ", last)
            self.assertIn("(2 (row, toolchain) pair(s) needed the reference proof's reading, 0 read in full)", last)
        # every earlier proof reads sorryAx too: the reference is written as the last proof left (exit 3), never the failing proof
        write_jsonl(self.p, [json.loads(l) for l in self.raw])
        rep, _ = self.guard(StubReader({"cur1": SORRY, "picks1": SORRY, "export1": SORRY}, ref={"error": "x"}))
        self.assertEqual(self.line(1)["proof"], self.rs[1]["src"].rstrip() + "\n")
        self.assertEqual((rep["rc"], rep["reference_not_passing"]), (AG.RC_NOT_READ, [self.rs[1]["name"]]))
        # a proof BAD on its own reading (a sorry message on one pin) is not set back for want of the reference, whatever the other pin
        write_jsonl(self.p, [json.loads(l) for l in self.raw])
        rep, _ = self.guard(StubReader({"cur1": lambda row, pin: SORRY if pin == vs[0] else dict(GOOD, sorry_warning=True)}, ref={"error": "x"}))
        self.assertEqual((rep["replaced"], rep["set_back_for_want_of_reference"]), ([name], []))

    def test_the_reference_as_a_candidate_is_judged_against_its_own_reading(self):
        """Point 5 at file level (review 2026-11-24): row 1's proof and both earlier proofs show Lean's sorry message (BAD whatever the
        reference reads); the reference proof reads sorryAx in a complete reading on both pins (a library lemma proved by sorry). As
        the last candidate it passes through its own reading's allowance: written, exit 0, not a reference that does not pass."""
        bad = dict(SORRY, sorry_warning=True)
        rd = StubReader({"cur1": bad, "picks1": bad, "export1": bad}, ref=SORRY)
        rep, log = self.guard(rd)
        self.assertEqual(self.line(1)["proof"], self.rs[1]["src"].rstrip() + "\n")
        self.assertEqual((rep["rc"], rep["reference_not_passing"], rep["passed_by_allowance"]), (0, [], [self.rs[1]["name"]]))
        d = rep["per_row"][1]
        self.assertEqual(([c["verdict"] for c in d["candidates"]], d["chosen"], d["chosen_verdict"]), ([AG.FAIL, AG.FAIL, AG.PASS], "reference", AG.PASS))
        self.assertEqual(d["chosen_allowance"], AG.versions_of(self.rs[1]))
        self.assertEqual(rep["reference_readings"], 0)   # no other proof needed it: read as the candidate only, once per pin
        self.assertEqual(sorted(self.ref_calls(rd)), sorted((self.rs[1]["name"], v) for v in AG.versions_of(self.rs[1])))

    def test_the_earlier_proofs_are_read_while_the_reference_is_read(self):
        """Review 2026-11-24: a pin that waits for the reference's reading reads BAD until it comes, so the row's earlier proofs are
        queued at once, behind it: with two threads, the post stage's input is read while the reference's reading is still running
        (here the reference's reading ends only once the input has been read, or after 3 s). Before, they waited for it: one compile
        more, and under a tight budget the input was not read and the row got its reference proof."""
        gate, events, lock = threading.Event(), [], threading.Lock()
        vs = AG.versions_of(self.rs[1])

        def ref(row, pin):
            if row["name"] == self.rs[1]["name"] and pin == vs[0]:
                gate.wait(3)
                with lock:
                    events.append("reference read")
            return GOOD

        def picks(row, pin):
            with lock:
                events.append(f"picks1 {pin}")
            gate.set()
            return GOOD
        rep, _ = self.guard(StubReader({"cur1": lambda row, pin: SORRY if pin == vs[0] else GOOD, "picks1": picks}, ref=ref), jobs=2)
        self.assertLess(events.index(f"picks1 {vs[0]}"), events.index("reference read"), events)
        self.assertEqual(self.line(1)["proof"], proof(self.rs[1], "picks1"))
        self.assertEqual(rep["rc"], 0)

    def test_a_row_without_a_reference_proof_allows_nothing(self):
        rs = [dict(r) for r in self.rs]
        rs[1]["src"] = ""
        write_jsonl(self.d / "rows.jsonl", rs)
        rd = StubReader({"cur1": SORRY}, ref=SORRY)
        rep, _ = self.guard(rd)
        self.assertEqual(self.ref_calls(rd), [])   # nothing to read
        self.assertEqual(self.line(1)["proof"], proof(self.rs[1], "picks1"))
        self.assertIn("not available (the row has no reference proof)", rep["per_row"][1]["why"])
        self.assertEqual(rep["rc"], 0)
        self.assertEqual(rep["set_back_for_want_of_reference"], [self.rs[1]["name"]])
        self.assertEqual({p["reference_reading"] for p in rep["per_row"][1]["pins"].values()}, {"the row has no reference proof"})

    def test_rows_the_post_stage_changed_are_read_first(self):
        """Review 2026-11-24: only rows whose proof differs from the agent stage's export can carry a step the post stage's gate let
        through; with one thread, their readings come before every other row's."""
        recs = [json.loads(l) for l in self.raw]
        write_jsonl(self.d / "proofs.export.jsonl", [r if k != 2 else rec(self.rs[2], "export2", 52.0, "agent") for k, r in enumerate(recs)])
        rd = StubReader({}, delay=0.02)
        rep, log = self.guard(rd, jobs=1)
        vs = [AG.versions_of(r) for r in self.rs]
        calls = [(n, tag, pin) for n, tag, pin, _t in rd.calls]
        self.assertEqual(calls[:2], [(self.rs[2]["name"], "cur2", v) for v in vs[2]])   # the changed row, both toolchains
        self.assertEqual(calls[2:5], [(self.rs[k]["name"], f"cur{k}", vs[k][0]) for k in (0, 1, 3)])
        self.assertEqual([d["read_first"] for d in rep["per_row"]], [False, False, True, False])
        self.assertIn("read first: the 1 row(s) whose proof differs from proofs.export.jsonl", log)


class NeverWriteABadProof(unittest.TestCase):
    """Random readings for the current proof, the two fallbacks and the reference: a proof that read BAD is never written, except
    the reference proof when nothing passes; a row whose proof reads BAD never keeps it; a row that passes is never touched."""

    def test_random(self):
        rs = rows()[20:30]
        rnd = random.Random(20261124)
        choices = [GOOD, SORRY, {"axioms": None}, dict(GOOD, sorry_warning=True), {"axioms": STD + ["sorryAx"]}, {"error": "x"},
                   {"axioms": ["myAxiom"]}, dict(SORRY, timed_out=True), {"axioms": ["sorryAx", "myAxiom"]}]
        ref_choices = choices + [SORRY, SORRY, dict(SORRY, sorry_warning=True), {"axioms": ["sorryAx"], "decl_errors": ["1:1: e"]}]
        for trial in range(40):
            d = tmpdir()
            write_jsonl(d / "rows.jsonl", rs)
            write_jsonl(d / "proofs.jsonl", [rec(r, f"cur{k}", 70.0) for k, r in enumerate(rs)])
            write_jsonl(d / "proofs.picks.jsonl", [rec(r, f"picks{k}", 60.0) for k, r in enumerate(rs)])
            write_jsonl(d / "proofs.export.jsonl", [rec(r, f"export{k}", 50.0) for k, r in enumerate(rs)])
            table = {f"{w}{k}": {v: rnd.choice(choices) for v in AG.versions_of(r)} for k, r in enumerate(rs) for w in ("cur", "picks", "export")}
            refs = {r["name"]: {v: rnd.choice(ref_choices) for v in AG.versions_of(r)} for r in rs}

            def reader(row, text, pin, timeout):
                m = re.search(r"-- mark:(\w+):", text)
                return (table[m.group(1)] if m else refs[row["name"]])[pin]
            rep = AG.guard_file(d / "proofs.jsonl", d / "rows.jsonl", reader=reader, budget_s=30, log=lambda s: None)
            out = [json.loads(l) for l in (d / "proofs.jsonl").read_text().splitlines()]
            for k, r in enumerate(rs):
                m = re.search(r"-- mark:(\w+):", out[k]["proof"])
                readings = table[m.group(1)] if m else refs[r["name"]]
                verdict = AG.classify(readings, refs[r["name"]])[0]
                cur_verdict = AG.classify(table[f"cur{k}"], refs[r["name"]])[0]
                if m is not None:   # a proof other than the reference stands: an axiom outside the three only as the reference reads it
                    for v, x in readings.items():
                        extra = set(x.get("axioms") or []) - set(STD)
                        ref = refs[r["name"]][v]
                        if extra and not x.get("error"):
                            self.assertTrue(ref.get("axioms") is not None and extra <= set(ref["axioms"]) and not any(
                                ref.get(f) or x.get(f) for f in ("error", "sorry_warning", "switch", "timed_out", "decl_errors")), (trial, k, v, x, ref))
                if cur_verdict == AG.FAIL:
                    self.assertNotEqual(out[k]["proof"], proof(r, f"cur{k}"), (trial, k))
                else:
                    self.assertEqual(out[k]["proof"], proof(r, f"cur{k}"), (trial, k))
                if verdict == AG.FAIL:
                    self.assertIsNone(m, (trial, k, "a BAD proof other than the reference was written"))
                    self.assertIn(r["name"], rep["reference_not_passing"])
                if m is None and verdict == AG.PASS:   # a reference that passes on its own reading is never "a reference that does not pass"
                    self.assertNotIn(r["name"], rep["reference_not_passing"], (trial, k))
                if m is None and cur_verdict == AG.FAIL and verdict != AG.PASS:
                    self.assertEqual(rep["rc"], AG.RC_NOT_READ)
            self.assertEqual(rep["rc"] == AG.RC_OK, not rep["not_read"] and not rep["reference_not_passing"] and not rep["not_read_in_full"])


class HeldOutCases(unittest.TestCase):
    """The two held-out rows that read sorryAx (2026-11-24), in a file of 10 rows whose other proofs read standard axioms. Row 42: the
    output reads sorryAx with no Lean message, its reference proof standard axioms: set back to the post stage's input. Row 25: its
    reference proof reads sorryAx itself (a lemma of the library proved by sorry), and so does the output: kept. Exit 0. The stored
    scores are stand-ins chosen to give row 42's change of -35.88 (C: the VM run of the guard on the held-out output measures it)."""

    def test_rows_42_and_25(self):
        rs = rows()[20:30]
        R42, R25 = 3, 7
        d = tmpdir()
        write_jsonl(d / "rows.jsonl", rs)
        cur = [rec(r, f"cur{k}", 80.0) for k, r in enumerate(rs)]
        cur[R42]["stored_score"] = 69.21
        write_jsonl(d / "proofs.jsonl", cur)
        picks = [rec(r, f"picks{k}", 60.0, "agent") for k, r in enumerate(rs)]
        picks[R42]["stored_score"] = 33.33
        write_jsonl(d / "proofs.picks.jsonl", picks)
        write_jsonl(d / "proofs.export.jsonl", picks)
        raw = (d / "proofs.jsonl").read_text().splitlines()
        n25 = rs[R25]["name"]
        rd = StubReader({f"cur{R42}": SORRY, f"cur{R25}": SORRY}, ref=lambda row, pin: SORRY if row["name"] == n25 else GOOD)
        lines, log = quiet()
        rep = AG.guard_file(d / "proofs.jsonl", d / "rows.jsonl", reader=rd, budget_s=60, log=log)
        out = (d / "proofs.jsonl").read_text().splitlines()
        self.assertEqual(rep["rc"], AG.RC_OK)
        self.assertEqual((rep["replaced"], rep["passed_by_allowance"]), ([rs[R42]["name"]], [n25]))
        self.assertEqual(json.loads(out[R42])["proof"], proof(rs[R42], f"picks{R42}"))
        self.assertEqual([out[k] for k in range(10) if k != R42], [raw[k] for k in range(10) if k != R42])   # row 25 kept as it was
        self.assertAlmostEqual(rep["stored_mean_after"] - rep["stored_mean_before"], -35.88 / 10, places=3)
        self.assertEqual({n for n, t, _p, _x in rd.calls if t == "reference"}, {rs[R42]["name"], n25})
        self.assertEqual(rep["reference_readings"], len(AG.versions_of(rs[R42])) + len(AG.versions_of(rs[R25])))
        self.assertEqual((rep["reference_readings_complete"], rep["set_back_for_want_of_reference"]), (rep["reference_readings"], []))
        self.assertIn(f"axiom guard: OK: 10 rows: 9 pass, 1 read BAD, 1 set back ({rs[R42]['name']}), 0 NOT READ; "
                      f"1 pass only through the reference proof's axioms ({n25}); stored mean", lines[-1])


class Pool(unittest.TestCase):
    def test_a_waiting_reading_moves_up_and_none_is_read_twice(self):
        """The reference's reading for the allowance may already wait in the queue as a candidate: submitted again with a higher
        priority it moves up; a reading already taken or done is not read again."""
        gate, order = threading.Event(), []

        def reader(row, text, pin, timeout):
            if text == "A":
                gate.wait(10)
            order.append(text)
            return GOOD
        pool = AG.Readings(reader, 1, time.monotonic() + 60, 30)
        ka, kb, kc = (("r", t, "p") for t in "ABC")
        pool.submit((0,), ka, {}, "A", "p")
        t0 = time.monotonic()
        while ka not in pool.started and time.monotonic() - t0 < 10:   # the one thread has taken A and waits
            time.sleep(0.01)
        pool.submit((1,), kb, {}, "B", "p")
        pool.submit((2,), kc, {}, "C", "p")
        pool.submit((-1,), kc, {}, "C", "p")   # moved up
        pool.submit((-1,), ka, {}, "A", "p")   # taken: not again
        pool.submit((5,), kc, {}, "C", "p")    # a lower priority changes nothing
        gate.set()
        self.assertTrue(pool.drain(lambda k: None, time.monotonic() + 30))
        pool.close()
        self.assertEqual(order, ["A", "C", "B"])


class Budget(unittest.TestCase):
    def setUp(self):
        self.rs = rows()[10:16]
        self.d = tmpdir()
        write_jsonl(self.d / "rows.jsonl", self.rs)
        self.p = self.d / "proofs.jsonl"
        write_jsonl(self.p, [rec(r, f"cur{k}", 70.0) for k, r in enumerate(self.rs)])
        write_jsonl(self.d / "proofs.picks.jsonl", [rec(r, f"picks{k}", 60.0) for k, r in enumerate(self.rs)])
        self.raw = self.p.read_text().splitlines()
        AG.STOP.clear()

    def tearDown(self):
        AG.STOP.clear()

    def test_rows_not_read_in_time_keep_their_proof_and_the_exit_status_says_so(self):
        slow = lambda row, pin: time.sleep(12) or GOOD
        t0 = time.monotonic()
        with mock.patch.object(AG, "GRACE_S", 1), mock.patch.object(AG, "MIN_START_S", 0.1):
            rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=StubReader({"cur4": slow, "cur5": slow}), budget_s=1.5, jobs=4,
                                log=lambda s: None)
        self.assertLess(time.monotonic() - t0, 8)              # the budget (1.5 s) and the grace (1 s), not the slow readings (12 s)
        self.assertEqual(rep["rc"], AG.RC_NOT_READ)
        self.assertEqual(sorted(rep["not_read"]), sorted([self.rs[4]["name"], self.rs[5]["name"]]))
        self.assertEqual(self.p.read_text().splitlines(), self.raw)
        self.assertFalse(rep["complete"])
        self.assertGreaterEqual(rep["running_at_end"], 1)

    def test_budget_zero_reads_nothing_and_changes_nothing(self):
        rd = StubReader({"cur0": SORRY})
        rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=rd, budget_s=0, log=lambda s: None)
        self.assertEqual(rd.calls, [])
        self.assertEqual((rep["rc"], len(rep["not_read"]), rep["written"]), (AG.RC_NOT_READ, 6, False))
        self.assertEqual(self.p.read_text().splitlines(), self.raw)

    def test_a_bad_row_whose_candidates_are_not_read_in_time_gets_the_reference_never_its_proof(self):
        slow = lambda row, pin: time.sleep(3) or GOOD
        with mock.patch.object(AG, "GRACE_S", 0.5), mock.patch.object(AG, "MIN_START_S", 0.1):
            rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=StubReader({"cur0": SORRY, "picks0": slow}, ref=slow), budget_s=1.5,
                                jobs=12, log=lambda s: None)
        out = json.loads(self.p.read_text().splitlines()[0])
        self.assertEqual(out["proof"], self.rs[0]["src"].rstrip() + "\n")
        self.assertEqual(rep["reference_not_passing"], [self.rs[0]["name"]])
        self.assertEqual(rep["rc"], AG.RC_NOT_READ)
        # the reference's reading for the allowance did not come in time: the proof's sorryAx is BAD (fail closed), not NOT READ
        self.assertEqual(rep["per_row"][0]["verdict"], AG.FAIL)
        self.assertIn("the reference proof's reading here is not available (not read within the time budget)", rep["per_row"][0]["why"])

    def test_each_compile_gets_at_most_the_time_left(self):
        rd = StubReader({})
        AG.guard_file(self.p, self.d / "rows.jsonl", reader=rd, budget_s=40, timeout_s=300, log=lambda s: None)
        self.assertTrue(all(0 < t <= 40 for *_x, t in rd.calls), rd.calls)
        rd = StubReader({})
        AG.guard_file(self.p, self.d / "rows.jsonl", reader=rd, budget_s=400, timeout_s=7, log=lambda s: None)
        self.assertTrue(all(t == 7 for *_x, t in rd.calls))

    def test_order_newest_pin_of_every_row_then_candidates_then_older_pins(self):
        """One thread. Row 2's proof reads sorryAx on its newest pin: the reference's reading there comes next (the thread has already
        taken row 3's reading when the result arrives), ahead of the other newest pins; until it comes that pin reads BAD (fail
        closed), so row 2's candidates are queued with it, and come after the newest pins and before the older pins (the reference's
        newest-pin reading is not read again as a candidate). It reads standard axioms: row 2 reads BAD, set back to its input."""
        rd = StubReader({"cur2": SORRY}, delay=0.05)   # the delay gives the main thread time to queue the next readings
        rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=rd, budget_s=60, jobs=1, log=lambda s: None)
        vs = [AG.versions_of(r) for r in self.rs]
        calls = [(n, tag, pin) for n, tag, pin, _t in rd.calls]
        self.assertEqual(calls[:4], [(r["name"], f"cur{k}", vs[k][0]) for k, r in enumerate(self.rs[:4])])
        self.assertEqual(calls[4], (self.rs[2]["name"], "reference", vs[2][0]))                       # the allowance's reading: first
        self.assertEqual(calls[5:7], [(self.rs[k]["name"], f"cur{k}", vs[k][0]) for k in (4, 5)])
        self.assertEqual(calls[7:10], [(self.rs[2]["name"], "picks2", v) for v in vs[2]] + [(self.rs[2]["name"], "reference", vs[2][1])])
        self.assertEqual(calls[10:], [(r["name"], f"cur{k}", vs[k][1]) for k, r in enumerate(self.rs)])   # then the older pins
        # row 2's older pin needs the reference too (sorryAx there): it was read already, as a candidate, and is not read again
        self.assertEqual((rep["reference_readings"], rep["reference_readings_complete"], len(calls), len(set(calls))), (2, 2, 16, 16))
        self.assertEqual(json.loads(self.p.read_text().splitlines()[2])["proof"], proof(self.rs[2], "picks2"))

    def test_a_reading_that_raises_is_not_read(self):
        def boom(row, pin):
            raise RuntimeError("no env")
        rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=StubReader({"cur1": boom}), budget_s=30, log=lambda s: None)
        self.assertEqual(rep["not_read"], [self.rs[1]["name"]])
        self.assertIn("RuntimeError: no env", rep["per_row"][1]["why"])

    def test_a_stop_signal_ends_the_readings(self):
        def stop(row, pin):
            AG.STOP.set()
            return GOOD
        rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=StubReader({"cur0": stop}), budget_s=60, jobs=1, log=lambda s: None)
        self.assertEqual(rep["verdicts"][AG.PASS], 1)
        self.assertEqual(rep["rc"], AG.RC_NOT_READ)
        self.assertEqual(self.p.read_text().splitlines(), self.raw)

    def test_threads_default_to_the_physical_cores_at_most_48(self):
        """Review 2026-11-24: one thread per usable CPU meant 127 Lean processes at once on a 128-thread node."""
        rs = rows()
        d = tmpdir()
        write_jsonl(d / "rows.jsonl", rs)
        write_jsonl(d / "proofs.jsonl", [rec(r, f"c{k}", 70.0) for k, r in enumerate(rs)])
        for cores, want in ((128, 48), (20, 20)):
            with mock.patch.object(AG, "physical_cores", return_value=cores):
                rep = AG.guard_file(d / "proofs.jsonl", d / "rows.jsonl", reader=StubReader({}), budget_s=30, log=lambda s: None)
            self.assertEqual((rep["jobs"], rep["readings_planned"], rep["rc"]), (want, 127, 0))
        rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=StubReader({}), budget_s=30, log=lambda s: None)
        self.assertLessEqual(rep["jobs"], min(AG.MAX_JOBS, rep["readings_planned"]))
        self.assertTrue(1 <= AG.physical_cores() <= len(os.sched_getaffinity(0)))

    def test_the_sixty_final_rows_shape_passes_with_exit_0(self):
        """The fresh read of the 81.466 output (2026-11-24): standard axioms on every pin but the v4.27.0 pins of the 10 Strata rows, where
        the print gives no list inside a `module` file. The guard leaves such a file unchanged, with exit 0 (C: the reading is a stand-in)."""
        rs = rows()
        d = tmpdir()
        write_jsonl(d / "rows.jsonl", rs)
        write_jsonl(d / "proofs.jsonl", [rec(r, f"c{k}", 81.0) for k, r in enumerate(rs)])
        before = (d / "proofs.jsonl").read_bytes()
        strata = {r["name"] for r in rs[:10]}
        rd = lambda row, text, pin, t: {"axioms": None, "module": True, "decl_errors": []} if row["name"] in strata and pin == "v4.27.0" else GOOD
        rep = AG.guard_file(d / "proofs.jsonl", d / "rows.jsonl", reader=rd, budget_s=60, log=lambda s: None)
        self.assertEqual((rep["rc"], rep["verdicts"][AG.PASS], rep["pins_not_read"], rep["pins_not_read_structural"]), (0, 60, 10, 10))
        self.assertEqual((rep["reference_readings"], rep["passed_by_allowance"], rep["replaced"]), (0, [], []))   # all standard: none
        self.assertEqual((d / "proofs.jsonl").read_bytes(), before)


# ------------------------------------------------------------------------------------------------------------------------- the CLI
class Cli(unittest.TestCase):
    def setUp(self):
        self.quiet = mock.patch("builtins.print")
        self.quiet.start()
        self.addCleanup(self.quiet.stop)
        self.d = tmpdir()
        rs = rows()
        self.rs = [rs[0], rs[20], rs[50]]   # Strata, cslib, PutnamBench
        write_jsonl(self.d / "rows.jsonl", self.rs)
        self.p = self.d / "proofs.jsonl"
        write_jsonl(self.p, [{"name": r["name"], "proof": r["src"].rstrip() + "\n", "source": "seed", "stored_score": 33.33} for r in self.rs])
        self.raw = self.p.read_bytes()

    def test_the_shipped_reader_without_environments_reads_nothing_and_says_so(self):
        """No library environment and no toolchain here: every reading fails before a Lean process starts (the env folders do not
        exist), so every row is NOT READ, kept, and the exit status is 3."""
        if any((ROOT / "envs").glob("*-v4*")):
            self.skipTest("library environments present (a node where setup.sh ran): this test needs a tree without them")
        env = dict(ENV, ELAN_HOME=str(self.d / "no-elan"), LRA_MEMGATE_DIR=str(self.d), PATH="/usr/bin:/bin")
        rep = self.d / "rep.json"
        r = subprocess.run([sys.executable, "-B", "harness/axiom_guard.py", str(self.p), "--rows", str(self.d / "rows.jsonl"), "--budget", "60",
                            "--report", str(rep)], cwd=ROOT, env=env, capture_output=True, text=True, timeout=180)
        self.assertEqual(r.returncode, AG.RC_NOT_READ, r.stdout[-800:] + r.stderr[-800:])
        self.assertIn("NOT EVERY ROW READ AND PASSING", r.stdout.splitlines()[-1])
        self.assertEqual(self.p.read_bytes(), self.raw)
        data = json.loads(rep.read_text())
        self.assertEqual(sorted(data["not_read"]), sorted(x["name"] for x in self.rs))
        self.assertTrue(all("Error" in p["why"] for d in data["per_row"] for p in d["pins"].values()), data["per_row"])
        self.assertEqual(sum(len(d["pins"]) for d in data["per_row"]), sum(len(AG.versions_of(x)) for x in self.rs))
        self.assertEqual(list((ROOT / "envs").rglob("LRAScratch")), [])   # nothing was written into the package tree

    def test_main_with_a_reader(self):
        argv = [str(self.p), "--rows", str(self.d / "rows.jsonl"), "--budget", "30"]
        self.assertEqual(AG.main(argv, reader=StubReader({})), 0)
        # every proof is the row's reference proof: reading sorryAx, it is judged against its own reading and passes (the allowance)
        self.assertEqual(AG.main(argv, reader=StubReader({}, ref=SORRY)), 0)
        rd = StubReader({}, ref=dict(SORRY, sorry_warning=True))   # with Lean's sorry message on its declaration it fails
        self.assertEqual(AG.main(argv, reader=rd), AG.RC_NOT_READ)
        self.assertEqual(self.p.read_bytes(), self.raw)   # the reference proof is the current proof: kept, flagged

    def test_not_checked(self):
        (self.d / "bad.jsonl").write_text('{"name": "x", "proof": "p"}\nnot json\n')
        for argv in ([str(self.d / "bad.jsonl"), "--rows", str(self.d / "rows.jsonl")], [str(self.d / "missing.jsonl"), "--rows", str(self.d / "rows.jsonl")],
                     [str(self.p), "--rows", str(self.d / "missing.jsonl")]):
            self.assertEqual(AG.main(argv, reader=StubReader({})), AG.RC_NOT_CHECKED, argv)
        self.assertEqual(self.p.read_bytes(), self.raw)
        with mock.patch.dict(os.environ, {AG.BUDGET_ENV: "7 min"}):
            self.assertEqual(AG.main([str(self.p), "--rows", str(self.d / "rows.jsonl")], reader=StubReader({})), AG.RC_NOT_CHECKED)

    def test_any_error_is_not_checked_and_the_report_is_written_on_every_path(self):
        """Review 2026-11-24: a record that is not a row (a name that is a list) raised out of main; and the report of an earlier run was
        left standing when this one did not finish. Now: exit 1, a report that says so; `running` while the guard reads."""
        rep = self.d / "rep.json"
        (self.d / "odd.jsonl").write_text(json.dumps({"name": ["x"], "proof": "p"}) + "\n")
        self.assertEqual(AG.main([str(self.d / "odd.jsonl"), "--rows", str(self.d / "rows.jsonl"), "--report", str(rep)], reader=StubReader({})),
                         AG.RC_NOT_CHECKED)
        data = json.loads(rep.read_text())
        self.assertEqual((data["status"], data["rc"]), ("not checked", 1))
        self.assertIn("TypeError", data["why"])
        seen = []
        rd = lambda row, text, pin, t: seen.append(json.loads(rep.read_text())["status"]) or GOOD
        self.assertEqual(AG.main([str(self.p), "--rows", str(self.d / "rows.jsonl"), "--report", str(rep)], reader=rd), 0)
        self.assertEqual(set(seen), {"running"})
        self.assertEqual((json.loads(rep.read_text())["status"], json.loads(rep.read_text())["rc"]), ("done", 0))

    def test_budget_from_the_environment(self):
        lines = []
        self.quiet.stop()
        with mock.patch.dict(os.environ, {AG.BUDGET_ENV: "77"}), mock.patch("builtins.print", side_effect=lambda *a, **k: lines.append(" ".join(map(str, a)))):
            AG.main([str(self.p), "--rows", str(self.d / "rows.jsonl")], reader=StubReader({}))
        self.assertIn("budget 77 s", lines[0])

    def test_help(self):
        r = subprocess.run([sys.executable, "-B", "harness/axiom_guard.py", "--help"], cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 0, r.stderr)
        for flag in ("--fallback", "--budget", "--timeout", "--no-write", "--report"):
            self.assertIn(flag, r.stdout)


# -------------------------------------------------------------------------------------------------------------------------- run.sh
STUB_GUARD = """import json, os, sys, time
sys.path.insert(0, {root!r})
from harness import axiom_guard as AG
with open(os.environ["STUB_ARGV_LOG"], "a") as f:
    f.write(json.dumps(sys.argv[1:]) + "\\n")
if os.environ.get("STUB_RC"):
    print("stub guard: crashed"); sys.exit(int(os.environ["STUB_RC"]))
spec = json.loads(os.environ.get("STUB_READINGS") or "{{}}")
STD = ["propext", "Classical.choice", "Quot.sound"]
def reader(row, text, pin, timeout):
    if "-- mark:" not in text and os.environ.get("STUB_REF"):   # the reference proof
        return json.loads(os.environ["STUB_REF"])
    for mark, r in spec.items():
        if "-- mark:" + mark + ":" in text:
            if r == "slow":
                time.sleep(timeout); return {{"axioms": None, "timed_out": True}}
            return r
    return {{"axioms": STD}}
rc = AG.main(sys.argv[1:], reader=reader)
if os.environ.get("STUB_TRAILER"):   # a line after the summary, as a memory-gate message of a thread still waiting
    print(os.environ["STUB_TRAILER"], file=sys.stderr, flush=True)
raise SystemExit(rc)
"""
PYWRAP = """#!/bin/bash
# run.sh's $PY in these tests: the axiom guard with a stand-in reader, the export as a copy of a prepared file, anything else real
case "$1" in
  harness/axiom_guard.py) shift; exec {py} -B {stub} "$@";;
  harness/open_package.py) cp "$FAKE_EXPORT" "$OUT/proofs.jsonl"; exit "${{FAKE_EXPORT_RC:-0}}";;
  *) exec {py} -B "$@";;
esac
"""


class RunScript(unittest.TestCase):
    """run.sh needs a set-up node, so its axiom-guard lines are cut out of the file and run here with stand-ins for the job around
    them (the log helpers, the Python, the paths, the export). The lines run are the shipped ones."""
    STUBS = ('set -u\nlra_log() { echo "$*"; }\nlra_die() { echo "FAILED: $*"; exit 1; }\nstop_all() { :; }\n'
             'fail() { echo "CHECK FAILED: $*"; }\nrun() { "$@"; }\nLOGD=$OUT/logs; mkdir -p "$LOGD"\n')

    def setUp(self):
        self.sh = (ROOT / "run.sh").read_text()
        self.rs = rows()[10:13]
        self.d = tmpdir()
        write_jsonl(self.d / "rows.jsonl", self.rs)
        self.out = self.d / "final"
        self.out.mkdir()
        (self.d / "stub_guard.py").write_text(STUB_GUARD.format(root=str(ROOT)))
        w = self.d / "py"
        w.write_text(PYWRAP.format(py=sys.executable, stub=self.d / "stub_guard.py"))
        w.chmod(w.stat().st_mode | stat.S_IXUSR)
        self.argv_log = self.d / "argv.log"

    def block(self, first: str, last: str) -> str:
        ls = self.sh.splitlines()
        i = [k for k, l in enumerate(ls) if l.startswith(first)]
        self.assertEqual(len(i), 1, first)
        j = next(k for k in range(i[0], len(ls)) if ls[k].startswith(last))
        return "\n".join(ls[i[0]:j + 1]) + "\n"

    def run_lines(self, body: str, **env):
        hour_ago = str(int(time.time()) - 3600)   # the clock started an hour ago (START), and so did this run.sh (T_START)
        e = dict(ENV, PY=str(self.d / "py"), ROWS=str(self.d / "rows.jsonl"), HBS="hbs", OUT=str(self.out), RC="0", DRY="0",
                 STUB_ARGV_LOG=str(self.argv_log))
        e.update({"START": hour_ago, "T_START": hour_ago, "MODE": "run"}, **env)
        return subprocess.run(["bash", "-c", self.STUBS + body], cwd=ROOT, env=e, capture_output=True, text=True, timeout=180)

    def budget(self, line: int = -1) -> str:
        argv = json.loads(self.argv_log.read_text().splitlines()[line])
        return argv[argv.index("--budget") + 1]

    def files(self, cur: dict, picks: dict | None = None):
        write_jsonl(self.out / "proofs.jsonl", [rec(r, cur.get(k, f"cur{k}"), 70.0) for k, r in enumerate(self.rs)])
        if picks is not None:
            write_jsonl(self.out / "proofs.picks.jsonl", [rec(r, picks.get(k, f"picks{k}"), 60.0, "agent") for k, r in enumerate(self.rs)])

    def fns(self) -> str:
        return self.block("kg_file() {", "kg_file() {") + self.block("AGRC=0", "AGRC=0") + self.block("ag_file() {", "}")

    def test_places_in_run_sh(self):
        sh = self.sh
        # export: the export, its copy, the merge, the axiom guard, the option guard's check, exit code 5, exit
        e0 = sh.index('if [ "$MODE" = export ]; then')
        seq = [sh.index(s, e0) for s in ("harness/open_package.py export", 'cp -f "$OUT/proofs.jsonl" "$OUT/proofs.export.jsonl"',
                                          "post_fast/merge_post.py", 'ag_file "$OUT/proofs.jsonl"', "kg_file \"$OUT/proofs.jsonl\"",
                                          "exit code 5 (axiom guard)", 'exit "$RC"')]
        self.assertEqual(seq, sorted(seq))
        # the job: the copy before the post stage; the guard after it, before the option guard's last check; exit code 5 before exit
        seq = [sh.index(s) for s in ('cmp -s "$OUT/proofs.jsonl" "$OUT/proofs.merged.jsonl" || cp -f "$OUT/proofs.jsonl" "$OUT/proofs.export.jsonl"',
                                     "bash post_fast/post_stage.sh", 'then ag_file "$OUT/proofs.jsonl" ""',
                                     'else ag_file "$OUT/proofs.jsonl" $((AEND', "KRC=0;", "exit code 5 (axiom guard): $OUT/proofs.jsonl is the output")]
        self.assertEqual(seq, sorted(seq))
        self.assertLess(sh.index("exit code 5 (axiom guard): $OUT/proofs.jsonl is the output"), sh.rindex('exit "$RC"'))
        self.assertEqual(sh.count('"$PY" harness/axiom_guard.py'), 1)   # one call, in ag_file
        self.assertEqual(sh.count("ag_file \""), 3)               # run.sh export; the job's end (a recovery, or in the clock's margin)
        self.assertIn('timeout --foreground -k 10 $((b + 60)) "$PY" harness/axiom_guard.py', sh)
        k = sh.index("on_signal() {")   # a promoted interim file was not axiom-checked: the log says so
        self.assertIn("neither the export's axiom audit nor the axiom guard: run 'bash run.sh export'", sh[k:sh.index("exit 143", k)])

    def end(self) -> str:
        ag = self.block("SAF=${LRA_SAFETY_S:-600}", 'else ag_file "$OUT/proofs.jsonl" $((AEND')
        return self.fns() + ag + self.block("KRC=0;", 'exit "$RC"')

    def test_job_end_a_row_that_reads_sorryAx_is_set_back_and_the_job_is_done(self):
        self.files({1: "bad"}, picks={})
        now = int(time.time())
        r = self.run_lines(self.end(), JOB_END=str(now + 100), STUB_READINGS=json.dumps({"bad": {"axioms": ["sorryAx"]}}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("axiom guard: OK: 3 rows: 2 pass, 1 read BAD, 1 set back", r.stdout)
        self.assertIn("DONE", r.stdout)
        out = [json.loads(l) for l in (self.out / "proofs.jsonl").read_text().splitlines()]
        self.assertEqual(out[1]["proof"], proof(self.rs[1], "picks1"))
        self.assertIn("REPLACED by the post stage's input", (self.out / "logs" / "axiom_guard.log").read_text())
        self.assertTrue((self.out / "logs" / "axiom_guard.json").exists())
        self.assertIn("no row sets a debug option", (self.out / "logs" / "option_guard.log").read_text())   # the option guard ran after
        self.assertEqual(self.budget(0), "420")   # the default: the margin left (100 + 600 - 120 - 70 s) is larger

    def test_job_end_a_row_whose_reference_reads_sorryAx_too_is_kept_and_the_job_is_done(self):
        """Held-out row 25's case at the job's end: the proof reads sorryAx, and so does the row's reference proof: kept, exit 0."""
        self.files({1: "bad"}, picks={})
        before = (self.out / "proofs.jsonl").read_bytes()
        r = self.run_lines(self.end(), JOB_END=str(int(time.time()) + 100), STUB_READINGS=json.dumps({"bad": {"axioms": ["sorryAx"]}}),
                           STUB_REF=json.dumps({"axioms": ["sorryAx"]}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("axiom guard: OK: 3 rows: 3 pass, 0 read BAD, 0 set back", r.stdout)
        self.assertIn(f"1 pass only through the reference proof's axioms ({self.rs[1]['name']})", r.stdout)
        self.assertIn("DONE", r.stdout)
        self.assertEqual((self.out / "proofs.jsonl").read_bytes(), before)
        r = self.run_lines(self.end(), JOB_END=str(int(time.time()) + 100), STUB_READINGS=json.dumps({"bad": {"axioms": ["sorryAx"]}}),
                           STUB_REF=json.dumps({"error": "not started: the time budget ran out"}))   # fail closed: set back
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("axiom guard: OK: 3 rows: 2 pass, 1 read BAD, 1 set back", r.stdout)
        self.assertIn("(1 of them only because the reference proof's reading was not available", r.stdout)   # in the job's log too
        self.assertNotIn("mark:bad:", (self.out / "proofs.jsonl").read_text())

    def test_job_end_budget_is_cut_to_the_safety_margin_and_a_row_not_read_gives_exit_5(self):
        self.files({0: "slow"})
        now = int(time.time())
        # 76 s left before 120 s ahead of the allocation's end: 70 s of them for the guard's grace, kill and write, 6 s of reading
        r = self.run_lines(self.end(), JOB_END=str(now - 600 + 120 + 76), STUB_READINGS=json.dumps({"slow": "slow"}))
        self.assertTrue(4 <= int(self.budget()) <= 6, self.budget())
        self.assertEqual(r.returncode, 5, r.stdout + r.stderr)
        self.assertIn("WARNING (axiom guard): not every row", r.stdout)
        self.assertIn("DONE", r.stdout)
        self.assertIn("exit code 5 (axiom guard)", r.stdout)
        # the clock ran out during this run (it was not over at its start): nothing is read, the file stays, exit 5
        r = self.run_lines(self.end(), JOB_END=str(now - 1800), T_START=str(now - 7200))
        self.assertEqual(r.returncode, 5, r.stdout + r.stderr)
        self.assertEqual(self.budget(), "0")
        r = self.run_lines(self.end(), JOB_END=str(now + 100), LRA_SAFETY_S="600.0")   # a float safety margin does not break the line
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        r = self.run_lines(self.end(), JOB_END=str(now + 100), LRA_SAFETY_S="0600")    # nor a leading zero (600, not octal 384)
        self.assertEqual((r.returncode, self.budget()), (0, "420"), r.stdout + r.stderr)

    def test_a_recovery_on_a_clock_already_over_gets_the_full_budget(self):
        """Review 2026-11-24: LRA_RESUME=1 after the clock ran out (only the end stage and the export run). post_stage.sh merges
        proofs.merged.jsonl back before it skips, and the guard used to get 0 s: the row whose value is sorry stayed. Now the guard gets
        its full budget, as in `run.sh export`, and sets the row back."""
        self.files({1: "bad"}, picks={})
        now = int(time.time())
        r = self.run_lines(self.end(), JOB_END=str(now - 7200), START=str(now - 180000), T_START=str(now - 5),
                           STUB_READINGS=json.dumps({"bad": {"axioms": ["sorryAx"]}}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual(self.budget(), "420")
        self.assertNotIn("mark:bad:", (self.out / "proofs.jsonl").read_text())
        self.assertIn("axiom guard: OK: 3 rows: 2 pass, 1 read BAD, 1 set back", r.stdout)

    def test_the_guard_never_runs_past_48_h_from_the_clock_start(self):
        """Review 2026-11-24: with LRA_JOB_SECONDS=172800 the clock's end is 48 h after its start, and the clock's end + LRA_SAFETY_S is
        past the 48 h. The guard's window ends 120 s before START + 48 h instead."""
        self.files({})
        now = int(time.time())
        start = now - 172800 + 100   # 100 s left of the 48 h; the clock's end is the 48 h
        r = self.run_lines(self.end(), START=str(start), T_START=str(start), JOB_END=str(start + 172800))
        self.assertEqual((r.returncode, self.budget()), (5, "0"), r.stdout + r.stderr)
        r = self.run_lines(self.end(), START=str(start), T_START=str(start), JOB_END=str(start + 172800 - 600))   # the default clock: as before
        self.assertEqual(self.budget(), "0")
        start = now - 3600
        r = self.run_lines(self.end(), START=str(start), T_START=str(start), JOB_END=str(now + 100))
        self.assertEqual((r.returncode, self.budget()), (0, "420"), r.stdout + r.stderr)

    def test_the_outer_timeout_and_a_guard_that_does_not_end(self):
        """The guard runs under `timeout --foreground -k 10 (budget + 60)`: a guard stopped by it (rc 124) or killed (137) is not checked,
        and the job ends with exit code 5. (`timeout` is wrapped to record its arguments; the guard's stand-in exits with the code.)"""
        self.files({})
        wrap = 'timeout() { echo "$*" > "$STUB_ARGV_LOG.timeout"; command timeout "$@"; }\n'
        r = self.run_lines(wrap + self.end(), JOB_END=str(int(time.time()) + 100))
        self.assertEqual(Path(str(self.argv_log) + ".timeout").read_text().split()[:4], ["--foreground", "-k", "10", "480"])
        for rc in ("124", "137"):
            r = self.run_lines(self.end(), JOB_END=str(int(time.time()) + 100), STUB_RC=rc)
            self.assertEqual(r.returncode, 5, r.stdout + r.stderr)
            self.assertIn(f"was not checked for axioms (rc {rc}", r.stdout)

    def test_the_summary_line_is_found_after_other_output(self):
        self.files({})
        r = self.run_lines(self.end(), JOB_END=str(int(time.time()) + 100), STUB_TRAILER="[memgate] GIVE UP c_x after 1s: need 8000 MB")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("axiom guard: OK: 3 rows: 3 pass", r.stdout)
        self.assertNotIn("GIVE UP", "\n".join(l for l in r.stdout.splitlines() if "axiom guard: OK" in l))

    def test_post_route_off_a_failing_row_gets_its_reference_proof(self):
        """LRA_POST_ROUTE=off: no proofs.picks.jsonl or proofs.export.jsonl is made, so a failing row goes to its reference proof."""
        self.files({1: "bad"})
        r = self.run_lines(self.end(), JOB_END=str(int(time.time()) + 100), LRA_POST_ROUTE="off",
                           STUB_READINGS=json.dumps({"bad": {"axioms": ["sorryAx"]}}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        out = [json.loads(l) for l in (self.out / "proofs.jsonl").read_text().splitlines()]
        self.assertEqual((out[1]["proof"], out[1]["source"]), (self.rs[1]["src"].rstrip() + "\n", "seed"))

    def test_the_export_copy_is_not_made_from_the_post_stage_output(self):
        """Review 2026-11-24: a re-run whose driver wrote no new export leaves proofs.jsonl = the post stage's last merge; copying it
        over proofs.export.jsonl lost the agent stage's export. Now the copy is made only from a file that is not that merge."""
        body = self.block('  cmp -s "$OUT/proofs.jsonl"', '    || lra_log "WARNING: no copy')
        exp = self.out / "proofs.export.jsonl"
        self.files({})
        r = self.run_lines(body)                   # no merged file: a fresh job's export, copied
        self.assertEqual(exp.read_text(), (self.out / "proofs.jsonl").read_text(), r.stdout + r.stderr)
        write_jsonl(exp, [rec(r_, f"export{k}", 50.0, "agent") for k, r_ in enumerate(self.rs)])
        agent = exp.read_text()
        (self.out / "proofs.merged.jsonl").write_bytes((self.out / "proofs.jsonl").read_bytes())
        self.run_lines(body)                       # proofs.jsonl is the post stage's last merge: the export copy stays
        self.assertEqual(exp.read_text(), agent)
        self.files({0: "new0"})
        self.run_lines(body)                       # a new export (it differs from the merge): copied
        self.assertIn("mark:new0:", exp.read_text())

    def test_off_and_not_checked(self):
        self.files({1: "bad"}, picks={})
        before = (self.out / "proofs.jsonl").read_bytes()
        (self.out / "logs").mkdir()
        (self.out / "logs" / "axiom_guard.json").write_text('{"status": "done", "rc": 0}')   # an earlier run's report
        r = self.run_lines(self.end(), JOB_END=str(int(time.time())), LRA_AXIOM_GUARD="off", STUB_READINGS=json.dumps({"bad": {"axioms": ["sorryAx"]}}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("axiom guard: OFF (LRA_AXIOM_GUARD=off)", r.stdout)
        self.assertEqual((self.out / "proofs.jsonl").read_bytes(), before)
        self.assertFalse(self.argv_log.exists())
        self.assertIn("axiom guard: OFF", (self.out / "logs" / "axiom_guard.log").read_text())   # under OUT/logs too, not only stdout
        self.assertEqual(json.loads((self.out / "logs" / "axiom_guard.json").read_text())["status"], "off")
        r = self.run_lines(self.end(), JOB_END=str(int(time.time())), STUB_RC="1")
        self.assertEqual(r.returncode, 5, r.stdout + r.stderr)
        self.assertIn("was not checked for axioms (rc 1", r.stdout)

    def test_the_option_guard_code_stays_4(self):
        write_jsonl(self.out / "proofs.jsonl", [dict(rec(r, f"cur{k}", 70.0), proof=r["statement"] + " := by\n  set_option debug.example true in exact foo\n")
                                                 for k, r in enumerate(self.rs)])
        r = self.run_lines(self.end(), JOB_END=str(int(time.time())), STUB_RC="1")
        self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
        self.assertIn("FAILED (option guard)", r.stdout)

    def test_no_proofs_file(self):
        r = self.run_lines(self.end(), JOB_END=str(int(time.time())))
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("FAILED: no proofs file", r.stdout)
        self.assertFalse(self.argv_log.exists())

    def export_block(self) -> str:
        return self.fns() + self.block('  run "$PY" harness/open_package.py export', '  exit "$RC"')

    def test_export_mode(self):
        """run.sh export: the export writes the picks, the merge brings the post stage's rows back (one reads sorryAx), the guard
        sets that row back to the post stage's input, the option guard checks the result."""
        picks = [rec(r, f"picks{k}", 60.0, "agent") for k, r in enumerate(self.rs)]
        write_jsonl(self.d / "export.jsonl", picks)
        write_jsonl(self.out / "proofs.picks.jsonl", picks)
        write_jsonl(self.out / "proofs.merged.jsonl", [rec(r, "bad" if k == 2 else f"post{k}", 80.0) for k, r in enumerate(self.rs)])
        r = self.run_lines(self.export_block(), FAKE_EXPORT=str(self.d / "export.jsonl"), STUB_READINGS=json.dumps({"bad": {"axioms": ["sorryAx"]}}))
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertEqual((self.out / "proofs.export.jsonl").read_text(), (self.d / "export.jsonl").read_text())
        out = [json.loads(l) for l in (self.out / "proofs.jsonl").read_text().splitlines()]
        self.assertEqual([o["proof"] for o in out], [proof(self.rs[0], "post0"), proof(self.rs[1], "post1"), proof(self.rs[2], "picks2")])
        self.assertIn("no row sets a debug option", (self.out / "logs" / "option_guard.log").read_text())
        argv = json.loads(self.argv_log.read_text().splitlines()[0])
        self.assertEqual(argv[argv.index("--budget") + 1], "420")
        r = self.run_lines(self.export_block(), FAKE_EXPORT=str(self.d / "export.jsonl"), STUB_READINGS=json.dumps({"post0": "slow"}),
                           LRA_AXIOM_GUARD_S="3")
        self.assertEqual(r.returncode, 5, r.stdout + r.stderr)
        self.assertIn("exit code 5 (axiom guard)", r.stdout)
        r = self.run_lines(self.export_block(), FAKE_EXPORT=str(self.d / "export.jsonl"), FAKE_EXPORT_RC="3", STUB_RC="1")
        self.assertEqual(r.returncode, 3, r.stdout + r.stderr)   # the export's own failure code is never masked

    def test_export_mode_sets_the_merged_file_back_so_the_next_export_stays_clean(self):
        picks = [rec(r, f"picks{k}", 60.0, "agent") for k, r in enumerate(self.rs)]
        write_jsonl(self.d / "export.jsonl", picks)
        write_jsonl(self.out / "proofs.picks.jsonl", picks)
        write_jsonl(self.out / "proofs.merged.jsonl", [rec(r, "bad" if k == 2 else f"post{k}", 80.0) for k, r in enumerate(self.rs)])
        env = dict(FAKE_EXPORT=str(self.d / "export.jsonl"), STUB_READINGS=json.dumps({"bad": {"axioms": ["sorryAx"]}}))
        r = self.run_lines(self.export_block(), **env)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertNotIn("mark:bad:", (self.out / "proofs.merged.jsonl").read_text())
        r = self.run_lines(self.export_block(), **env)   # a second export: the merge brings back no failing proof, nothing to set back
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertNotIn("mark:bad:", (self.out / "proofs.jsonl").read_text())
        self.assertIn("axiom guard: OK: 3 rows: 3 pass, 0 read BAD", r.stdout)

    def test_dry_export_runs_no_guard(self):
        write_jsonl(self.d / "export.jsonl", [rec(r, f"picks{k}", 60.0, "agent") for k, r in enumerate(self.rs)])
        r = self.run_lines(self.export_block(), FAKE_EXPORT=str(self.d / "export.jsonl"), DRY="1")
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertFalse(self.argv_log.exists())
        self.assertFalse((self.out / "proofs.export.jsonl").exists())

    def test_settings_are_checked_before_anything_starts(self):
        lines = (self.block('case "${LRA_AXIOM_GUARD:-on}" in', 'case "${LRA_AXIOM_GUARD:-on}" in')
                 + self.block('[[ "${LRA_AXIOM_GUARD_S:-420}" =~', '[[ "${LRA_AXIOM_GUARD_S:-420}" =~'))
        self.assertLess(self.sh.index(lines.splitlines()[0]), self.sh.index('\nif [ "$MODE" = check ]; then\n'))
        for env in ({"LRA_AXIOM_GUARD": "no"}, {"LRA_AXIOM_GUARD": "ON"}, {"LRA_AXIOM_GUARD_S": "7m"}, {"LRA_AXIOM_GUARD_S": "-1"},
                    {"LRA_AXIOM_GUARD_S": "420.5"}, {"LRA_AXIOM_GUARD_S": "08"}, {"LRA_AXIOM_GUARD_S": "0420"}, {"LRA_AXIOM_GUARD_S": "00"}):
            r = self.run_lines(lines, **env)
            self.assertIn("CHECK FAILED: LRA_AXIOM_GUARD", r.stdout, env)
        for env in ({}, {"LRA_AXIOM_GUARD": "on"}, {"LRA_AXIOM_GUARD": "off"}, {"LRA_AXIOM_GUARD_S": "0"}, {"LRA_AXIOM_GUARD_S": "900"}):
            r = self.run_lines(lines, **env)
            self.assertEqual((r.returncode, r.stdout), (0, ""), env)

    def test_check_warns_when_the_guard_is_off_or_the_margin_is_short(self):
        lines = (self.block('[ "${LRA_AXIOM_GUARD:-on}" != off ]', '[ "${LRA_AXIOM_GUARD:-on}" != off ]')
                 + self.block('[ "$MODE" = export ] || [[ ! "${LRA_SAFETY_S', '  || lra_log "WARNING: LRA_SAFETY_S'))
        self.assertLess(self.sh.index(lines.splitlines()[0]), self.sh.index('\nif [ "$MODE" = check ]; then\n'))
        for env, want in (({"LRA_AXIOM_GUARD": "off"}, "WARNING: LRA_AXIOM_GUARD=off"), ({"LRA_SAFETY_S": "200"}, "WARNING: LRA_SAFETY_S=200"),
                          ({"LRA_SAFETY_S": "250.5"}, "WARNING: LRA_SAFETY_S=250.5"), ({}, ""), ({"LRA_SAFETY_S": "0600"}, ""),
                          ({"LRA_SAFETY_S": "300"}, ""), ({"LRA_SAFETY_S": "200", "MODE": "export"}, "")):
            r = self.run_lines(lines, **env)
            self.assertEqual(r.returncode, 0, (env, r.stderr))
            self.assertEqual(r.stdout.strip()[:len(want)] if want else r.stdout, want, env)


# ---------------------------------------------------------------------------------------------------------- the measured code path
class MeasuredScripts(unittest.TestCase):
    def test_fingerprint_of_the_seven_post_stage_scripts(self):
        """The seven scripts as measured for tier B on 2026-11-25, unchanged: sha256 of each file, one per line, in
        this order, then sha256 of those lines, first 16 hex digits."""
        lines = "".join(hashlib.sha256((ROOT / "post_fast" / f).read_bytes()).hexdigest() + "\n" for f in MEASURED)
        self.assertEqual(hashlib.sha256(lines.encode()).hexdigest()[:16], FINGERPRINT)

    def test_the_guard_is_not_in_the_post_stage(self):
        for f in MEASURED:
            self.assertNotIn("axiom_guard", (ROOT / "post_fast" / f).read_text(), f)

    def test_target_is_a_reporting_field_only(self):
        """pf_drive.py's and snapshot.py's --target fill the summary's time-to-target and nothing else: no stop, no
        row decision reads it (README, "The fast post stage in run.sh")."""
        for f, uses in (("pf_drive.py", 2), ("snapshot.py", 2)):
            src = (ROOT / "post_fast" / f).read_text()
            hits = [l.strip() for l in src.splitlines() if re.search(r"\ba\.target\b", l)]
            self.assertEqual(len(hits), uses, (f, hits))
            for l in hits:
                self.assertRegex(l, r"^(if hit is None and m >= a\.target:|summ\[\"target\"\] = a\.target|"
                                    r"if statistics\.mean\(snap\(t\)\) >= a\.target - 1e-9:|res\[\"target\"\] = a\.target)$", (f, l))
        drive = (ROOT / "post_fast" / "pf_drive.py").read_text()
        k = drive.index("if hit is None and m >= a.target:")
        self.assertEqual(drive[k:].splitlines()[1].strip(), "hit = ev[\"t_end\"]")
        self.assertLess(drive.index('(OUT / "proofs.post.jsonl").write_text'), k)   # the output is written before the field is computed


if __name__ == "__main__":
    unittest.main()
