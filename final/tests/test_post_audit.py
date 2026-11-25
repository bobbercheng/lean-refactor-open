#!/usr/bin/env python3
"""Tests of the post stage's gate audit (harness/post_audit.py, 2026-11-24) and of its switch (harness/open_post.default_audit).

They start no Lean. Either the gate's readers are replaced by stand-ins that return a reading per (text, pin), or scorer.compile's
compile layer (file_prefix, lakefile_options, compile_project, compile_putnam) is replaced by World, which records every compile and
builds Lean's messages from a table (the axiom prints, the sorry message, errors, timeouts, the finer program's lines), parsed by
scorer.compile's own parser. The published gate and the job's export audit are executed from their verbatim text
(tests/data/post_gate_published.py.txt, tag open-camready-20261125) for the comparisons. The Lean side is checked on the library
environments by tests/finer_lean/run_gate.py.
    python3 -B -m pytest -q -p no:cacheprovider tests/test_post_audit.py"""
from __future__ import annotations

import ast, contextlib, hashlib, io, json, os, random, re, subprocess, sys, threading, time, unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
ROWS_FILE = ROOT / "data/official/rows.jsonl"
os.environ.setdefault("LRA_ROWS_FILE", str(ROWS_FILE))
os.environ.setdefault("LRA_HBS_FILE", str(ROOT / "data/official/heartbeats.jsonl"))

from harness import axiom_guard as AG  # noqa: E402
from harness import finer_sorry as FS  # noqa: E402
from harness import open_package as OPK  # noqa: E402
from harness import open_post as OP  # noqa: E402
from harness import post_audit as PA  # noqa: E402
from probe.verify_candidates import newest_first  # noqa: E402
from scorer import compile as C  # noqa: E402

PUBLISHED = ROOT / "tests/data/post_gate_published.py.txt"
PUBLISHED_SHA256 = "c09afd0f3a8e5dacb40d2dc00dee2f12be765fb93a8e6c5f7989d42813c65da4"
STD = ["propext", "Classical.choice", "Quot.sound"]
SORRYAX = STD + ["sorryAx"]


def rows() -> list:
    return [json.loads(l) for l in ROWS_FILE.read_text().splitlines() if l.strip()]


def marked(row: dict, tag: str) -> str:
    return row["statement"] + f" := by\n  -- mark:{tag}:\n  exact foo\n"


def tag_of(text: str) -> str:
    m = re.search(r"-- mark:(\w+):", text or "")
    return m.group(1) if m else "?"


def with_src(row: dict, pins: list | None = None) -> dict:
    r = dict(row, src=marked(row, "src"))
    if pins is not None:
        r["version_info"] = [{v: "0" * 40} for v in pins]
    return r


def row_of(source: str) -> dict:
    return next(r for r in rows() if r["source"] == source)


# ------------------------------------------------------------------------------------------------------------- the published code
def published() -> dict:
    """The published functions, executed from their verbatim text: audit_axioms in scorer.compile's live namespace (it sees the
    stand-ins patched there), audit_proof and audit_export in a copy of open_package's (audit_export calls the published
    audit_proof), default_audit in a copy of open_post's. During a published run, C.audit_axioms and OPK.audit_proof are patched to
    the published ones (published_chain), because the published code imports them by name at call time."""
    text = PUBLISHED.read_text()
    tree = ast.parse(text)
    src = {n.name: ast.get_source_segment(text, n) for n in tree.body if isinstance(n, ast.FunctionDef)}
    ns: dict = {}
    exec(src["audit_axioms"], C.__dict__, ns)   # noqa: S102  (globals: the live module; the name is bound in ns only)
    g = dict(vars(OPK))
    exec(src["audit_proof"], g)                # noqa: S102
    exec(src["audit_export"], g)               # noqa: S102
    g["log"] = lambda *a, **k: None
    g2 = dict(vars(OP))
    exec(src["default_audit"], g2)             # noqa: S102
    return {"audit_axioms": ns["audit_axioms"], "audit_proof": g["audit_proof"], "audit_export": g["audit_export"],
            "default_audit": g2["default_audit"]}


@contextlib.contextmanager
def published_chain(pub: dict):
    with mock.patch.object(C, "audit_axioms", pub["audit_axioms"]), mock.patch.object(OPK, "audit_proof", pub["audit_proof"]):
        yield


# ------------------------------------------------------------------------------------------------------------- stand-in compiles
class World:
    """scorer.compile's compile layer replaced: every compile recorded in .calls; Lean's messages built from `truth`
    {(text tag, pin): {"axioms": list | None (each print's list, default STD), "lists": [per print], "sorry": a sorry message on the
    declaration's first line, "lib_sorry": one in the file's prefix (the library's), "decl_error", "timeout", "finer": {"sources",
    "own"} for the finer program}}. `modules`: the (row name, pin) whose file is a `module` file; there the print gives an error and
    no list before v4.30 (prints_in_module), as Lean does."""

    def __init__(self, truth: dict | None = None, modules=(), mods: str = ""):
        self.truth, self.modules, self.mods, self.calls = dict(truth or {}), set(modules), mods, []
        self.lk = threading.Lock()

    def prefix(self, row, version):
        mod = (row["name"], version) in self.modules
        return ("module\n\nimport Foo\n\n" if mod else "import Foo\n\n") + "namespace NS\n\n" + self.mods

    def lakefile_options(self, source, version):
        return ("-Dwarn.sorry=false",) if source == "physlib" else ()

    def compile_project(self, row, declaration, version, *, count=True, timeout=900, lean_args=None, _quiet_prefix_sorry=False):
        with self.lk:
            self.calls.append(("project", row["name"], declaration, version, count, int(timeout), tuple(lean_args or ())))
        core, mods = C.split_modifiers(self.prefix(row, version))
        first = C._first_line(core)
        body = core.rstrip("\n") + "\n\n" + mods + declaration.rstrip() + "\n"
        return self.result(declaration, version, body, first, bool(C._MODULE_LINE.match(core)))

    def compile_putnam(self, header, declaration, version, *, count=True, timeout=600):
        with self.lk:
            self.calls.append(("putnam", hashlib.sha256(header.encode()).hexdigest()[:8], declaration, version, count, int(timeout), ()))
        first = C._first_line(header.rstrip())
        return self.result(declaration, version, header.rstrip() + "\n\n" + declaration.rstrip() + "\n", first, False)

    def result(self, decl, version, body, first, module):
        t = self.truth.get((tag_of(decl), version), {})
        if t.get("timeout"):
            return C.CompileResult(False, None, 3.0, ["timeout"], timed_out=True)
        out, d0 = [], first + 1
        if t.get("lib_sorry"):
            out.append({"severity": "warning", "pos": {"line": 1, "column": 0}, "data": "declaration uses 'sorry'"})
        if t.get("sorry"):
            out.append({"severity": "warning", "pos": {"line": d0, "column": 0}, "data": "declaration uses 'sorry'"})
        if t.get("decl_error"):
            out.append({"severity": "error", "pos": {"line": d0, "column": 4}, "data": "type mismatch"})
        lines, k = body.split("\n"), 0
        for i, l in enumerate(lines, 1):
            if not l.startswith("#print axioms"):
                continue
            if module and not C.prints_in_module(version):
                out.append({"severity": "error", "pos": {"line": i, "column": 0}, "data": "cannot print axioms in a module file here"})
                continue
            axs = t["lists"][k] if t.get("lists") else t.get("axioms", STD)
            k += 1
            if axs is not None:
                out.append({"severity": "information", "pos": {"line": i, "column": 0},
                            "data": f"'NS.x' depends on axioms: [{', '.join(axs)}]" if axs else "'NS.x' does not depend on any axioms"})
        if FS.MARK in body:
            out += self.finer_lines(lines, t, module)
        rc = 1 if any(m["severity"] == "error" for m in out) else 0
        p = subprocess.CompletedProcess(["lean"], rc, "".join(json.dumps(m) + "\n" for m in out), "")
        return C._parse(p, 1.0, first, switch=C._sorry_switch(body, first))

    def finer_lines(self, lines, t, module) -> list:
        """The finer program's output (finer_sorry.PROGRAM): one marker per queried name, then the end line, at the program's line."""
        body = "\n".join(lines)
        nonce = re.search(r'"' + FS.MARK + r' ([0-9a-f]+) "', body).group(1)
        proof_line = int(re.search(r"let proofLine : _root_\.Nat := (\d+)", body).group(1))
        qs = [q.strip().lstrip("`") for q in re.search(r"for q in \(\[(.*?)\] : _root_\.List", body).group(1).split(",")]
        line = next(i for i, l in enumerate(lines, 1) if l.startswith("set_option maxHeartbeats 0 in"))
        f = t.get("finer") or {}
        axs = list(dict.fromkeys(x for l in t["lists"] for x in l)) if t.get("lists") else t.get("axioms", STD)   # the union
        srcs = list(f.get("sources", ["NS.libSorry"] if "sorryAx" in (axs or []) else []))
        own = list(f.get("own", []))
        loc = [s for s in srcs if s.startswith("NS.")]
        ms = [{"v": FS.VERSION, "q": q, "decl": "NS.x", "decl_local": True, "sources": srcs, "own": own, "local": loc, "unranged": [],
               "missing": [], "axioms": list(axs or []), "n_local": 1, "n_frontier": 1, "complete": True, "ms": 1} for q in qs]
        end = {"v": FS.VERSION, "end": True, "markers": len(ms), "unresolved": [], "stored": True, "module": module, "walked": 0,
               "complete": True, "proof_line": proof_line, "lean": "4.34.0", "ms": 2}
        return [{"severity": "information", "pos": {"line": line, "column": 0}, "data": f"{FS.MARK} {nonce} {json.dumps(j)}"}
                for j in ms + [end]]

    @contextlib.contextmanager
    def on(self):
        with mock.patch.object(C, "file_prefix", side_effect=self.prefix), \
                mock.patch.object(C, "lakefile_options", side_effect=self.lakefile_options), \
                mock.patch.object(C, "compile_project", side_effect=self.compile_project), \
                mock.patch.object(C, "compile_putnam", side_effect=self.compile_putnam):
            yield self

    def texts(self) -> list:
        return [c[2] for c in self.calls]


def random_truth(rnd, tags, pins) -> dict:
    t = {}
    for tag in tags:
        for v in pins:
            axs = rnd.choice([STD, STD, STD, STD, [], ["propext"], SORRYAX, ["sorryAx"], STD + ["Lean.ofReduceBool"], None])
            x = {"axioms": axs, "sorry": rnd.random() < 0.1, "lib_sorry": rnd.random() < 0.2, "timeout": rnd.random() < 0.05,
                 "decl_error": rnd.random() < 0.06}
            if rnd.random() < 0.12:
                x["lists"] = [axs or [], rnd.choice([STD, ["sorryAx"], [], SORRYAX])]
            if rnd.random() < 0.3:
                x["finer"] = {"sources": rnd.choice([["NS.libSorry"], ["NS.lib2"], ["NS.libSorry", "Imp.l"], []]),
                              "own": rnd.choice([[], [], ["NS.x"]])}
            t[(tag, v)] = x
    return t


def random_row(rnd) -> dict:
    r = rnd.choice(rows())
    return with_src(r)


def random_modules(rnd, row) -> set:
    if row["source"] == "putnambench":
        return set()
    return {(row["name"], v) for v in newest_first(row["version_info"]) if rnd.random() < 0.5}


# ------------------------------------------------------------------------------------------------------------ stand-in readers
class Readers:
    """Stand-in gate readers: a reading per (text tag, pin) from `table`, a finer reading from `finer`; every call counted."""

    def __init__(self, table: dict, finer: dict | None = None, delay: float = 0.0, raise_on=()):
        self.table, self.finer, self.delay, self.raise_on = table, dict(finer or {}), delay, set(raise_on)
        self.calls, self.fcalls, self.timeouts = [], [], []
        self.lk = threading.Lock()

    def read(self, row, text, pin, timeout):
        with self.lk:
            self.calls.append((tag_of(text), pin))
            self.timeouts.append(timeout)
        if self.delay:
            time.sleep(self.delay)
        if (tag_of(text), pin) in self.raise_on:
            raise RuntimeError("stand-in failure")
        return self.table.get((tag_of(text), pin))

    def fread(self, row, text, pin, timeout):
        with self.lk:
            self.fcalls.append((tag_of(text), pin))
        if self.delay:
            time.sleep(self.delay)
        return self.finer.get((tag_of(text), pin))

    def audit(self, row, text, pins, **kw):
        kw.setdefault("cache", PA.ReadOnce())
        return PA.gate_audit(row, text, pins, reader=self.read, finer_reader=self.fread, **kw)


def fr(sources=(), own=(), axioms=("sorryAx",)) -> dict:
    """A finer reading as axiom_guard.finer_reading returns it (two printed names)."""
    ms = [{"v": FS.VERSION, "q": q, "decl": "NS.x", "decl_local": True, "sources": list(sources), "own": list(own),
           "local": [s for s in sources if s.startswith("NS.")], "unranged": [], "missing": [], "axioms": list(axioms), "n_local": 1,
           "n_frontier": 1, "complete": True, "ms": 1} for q in ("x", "NS.x")]
    return {"markers": ms, "end": {"markers": 2}, "seconds": 1.0}


GOOD = {"axioms": STD, "module": False, "by_construction": False}
SORRY_ONLY = {"axioms": ["sorryAx"], "module": True, "by_construction": False}
OLD_MODULE = {"axioms": None, "module": True, "by_construction": True}   # a `module` file before v4.30: compiled without the print
ROW = with_src(row_of("arklib"), ["v4.34.0", "v4.31.0"])
P1, P2 = "v4.34.0", "v4.31.0"


class DecisionTable(unittest.TestCase):
    def check(self, cand: dict, ref: dict | None = None, finer: dict | None = None, want: str = PA.CLEAN, pins=(P1,), row=ROW,
              text_tag="c"):
        table = {(text_tag, p): cand.get(p, cand.get("*")) for p in pins}
        for p in pins:
            if ref is not None:
                table[("src", p)] = ref.get(p, ref.get("*"))
        rd = Readers(table, finer)
        st, why = rd.audit(row, marked(row, text_tag), list(pins))
        self.assertEqual(st, want, why)
        return st, why, rd

    def test_standard_axioms_on_every_pin_are_clean(self):
        self.check({"*": GOOD}, pins=(P1, P2))
        self.check({"*": dict(GOOD, axioms=[])})

    def test_a_pin_not_read_by_construction_is_skipped_and_its_sorry_message_still_counts(self):
        _st, why, _ = self.check({P1: GOOD, P2: OLD_MODULE}, pins=(P1, P2), want=PA.SKIPPED)
        self.assertIn("sorry message check only on v4.31.0", why)
        self.check({P1: OLD_MODULE}, want=PA.SKIPPED)
        self.check({P1: GOOD, P2: dict(OLD_MODULE, sorry_warning=True)}, pins=(P1, P2), want=PA.SORRY)

    def test_a_forced_print_with_no_list_is_unknown_not_skipped(self):
        self.check({"*": dict(OLD_MODULE, by_construction=False)}, want=PA.UNKNOWN)   # from v4.30 the print must give a list

    def test_evidence_of_sorry(self):
        for bad in (dict(GOOD, sorry_warning=True), dict(GOOD, switch=True), dict(SORRY_ONLY, sorry_warning=True, timed_out=True)):
            self.check({"*": bad}, ref={"*": GOOD}, want=PA.SORRY)

    def test_sorryAx_against_a_standard_reference_is_sorry(self):
        _st, why, rd = self.check({"*": SORRY_ONLY}, ref={"*": GOOD}, want=PA.SORRY)
        self.assertIn("the reference proof reads standard axioms here", why)
        self.assertEqual(rd.calls, [("c", P1), ("src", P1)])

    def test_any_other_axiom_needs_the_reference(self):
        x = dict(GOOD, axioms=STD + ["Lean.ofReduceBool"])
        self.check({"*": x}, ref={"*": GOOD}, want=PA.SORRY)
        self.check({"*": x}, ref={"*": dict(GOOD, axioms=STD + ["Lean.ofReduceBool"])}, want=PA.CLEAN)
        self.check({"*": x}, ref={"*": dict(GOOD, axioms=STD + ["Lean.ofReduceBool"], lists=[STD + ["Lean.ofReduceBool"], STD])},
                   want=PA.SORRY)   # the reference allows only what every print reads

    def test_sorryAx_through_the_allowance_is_decided_by_the_finer_check(self):
        ref = {"*": dict(SORRY_ONLY)}
        same = {("c", P1): fr(["NS.libSorry"]), ("src", P1): fr(["NS.libSorry"])}
        _st, why, rd = self.check({"*": SORRY_ONLY}, ref=ref, finer=same, want=PA.CLEAN)
        self.assertIn("sorry sources as the reference proof", why)
        self.assertEqual(rd.fcalls, [("c", P1), ("src", P1)])
        self.check({"*": SORRY_ONLY}, ref=ref, finer={("c", P1): fr(["NS.lib2"]), ("src", P1): fr(["NS.libSorry"])}, want=PA.SORRY)
        self.check({"*": SORRY_ONLY}, ref=ref, finer={("c", P1): fr(["NS.x"], ["NS.x"]), ("src", P1): fr(["NS.libSorry"])}, want=PA.SORRY)
        self.check({"*": SORRY_ONLY}, ref=ref, finer={("c", P1): fr(["NS.libSorry"]), ("src", P1): fr(["NS.x"], ["NS.x"])}, want=PA.SORRY)

    def test_a_finer_reading_not_available_is_unknown(self):
        ref = {"*": dict(SORRY_ONLY)}
        for f in ({("c", P1): None, ("src", P1): fr(["NS.libSorry"])}, {("c", P1): fr(["NS.libSorry"]), ("src", P1): {"error": "x"}},
                  {("c", P1): {"timed_out": True, "error": "finer reading: the compile timed out"}, ("src", P1): fr(["NS.libSorry"])},
                  {("c", P1): fr(["NS.libSorry"], axioms=STD), ("src", P1): fr(["NS.libSorry"])}):   # other axioms than its reading
            self.check({"*": SORRY_ONLY}, ref=ref, finer=f, want=PA.UNKNOWN)
        # evidence in the finer compile (a sorry message there) is BAD, not a want of reading
        self.check({"*": SORRY_ONLY}, ref=ref, finer={("c", P1): dict(fr(["NS.libSorry"]), sorry_warning=True), ("src", P1): fr(["NS.libSorry"])},
                   want=PA.SORRY)

    def test_the_reference_not_available_is_unknown(self):
        for ref in (None, {"*": {"error": "x"}}, {"*": dict(GOOD, timed_out=True, axioms=None)}, {"*": dict(SORRY_ONLY, sorry_warning=True)},
                    {"*": {"axioms": None}}):
            self.check({"*": SORRY_ONLY}, ref=ref, want=PA.UNKNOWN)
        no_src = dict(ROW, src="")
        self.check({"*": SORRY_ONLY}, row=no_src, want=PA.UNKNOWN)

    def test_not_read_is_unknown(self):
        for x in (None, {"error": "x"}, dict(GOOD, timed_out=True, axioms=None), dict(GOOD, decl_errors=["1:1: e"])):
            self.check({"*": x}, want=PA.UNKNOWN)
        # with an axiom outside the three, a timeout or an error in the declaration is BAD (the guard's rule)
        self.check({"*": dict(SORRY_ONLY, timed_out=True)}, ref={"*": SORRY_ONLY}, want=PA.SORRY)
        self.check({"*": dict(SORRY_ONLY, decl_errors=["1:1: e"])}, ref={"*": SORRY_ONLY}, want=PA.SORRY)

    def test_newest_pin_first_and_bad_returns_at_once(self):
        rd = Readers({("c", P1): dict(GOOD, sorry_warning=True), ("c", P2): GOOD})
        self.assertEqual(rd.audit(ROW, marked(ROW, "c"), [P1, P2])[0], PA.SORRY)
        self.assertEqual(rd.calls, [("c", P1)])
        rd = Readers({("c", P1): {"error": "x"}, ("c", P2): dict(GOOD, sorry_warning=True)})
        self.assertEqual(rd.audit(ROW, marked(ROW, "c"), [P1, P2])[0], PA.SORRY)   # an unknown pin, then a bad one: sorry
        self.assertEqual(rd.calls, [("c", P1), ("c", P2)])

    def test_no_pin_and_a_raising_reader(self):
        self.assertEqual(Readers({}).audit(ROW, marked(ROW, "c"), []), (PA.UNKNOWN, "the row lists no pin"))
        rd = Readers({("c", P1): GOOD}, raise_on={("c", P1)})
        st, why = rd.audit(ROW, marked(ROW, "c"), [P1])
        self.assertEqual(st, PA.UNKNOWN)
        self.assertIn("RuntimeError", why)

    def test_hooks(self):
        """A candidate whose text registers a hook is rejected without a compile; a reference with one allows nothing; an instance
        (a finer hook) blocks only a finer reading."""
        fake = marked(ROW, "c") + "\n@[command_elab Lean.Parser.Command.printAxioms] private def fakePrint : Lean.Elab.Command.CommandElab := fun _ => pure ()\n"
        rd = Readers({("c", P1): GOOD})
        st, why = rd.audit(ROW, fake, [P1])
        self.assertEqual(st, PA.SORRY)
        self.assertTrue(why.startswith("hook check:"), why)
        self.assertEqual(rd.calls, [])
        hooked_ref = dict(ROW, src=ROW["src"] + "\nmacro \"x\" : term => `(1)\n")
        rd = Readers({("c", P1): SORRY_ONLY, ("src", P1): SORRY_ONLY})
        self.assertEqual(rd.audit(hooked_ref, marked(ROW, "c"), [P1])[0], PA.UNKNOWN)
        self.assertEqual(rd.calls, [("c", P1)])   # the reference's text is not compiled
        inst = marked(ROW, "c") + "\ninstance : Inhabited Nat := ⟨0⟩\n"
        rd = Readers({("c", P1): GOOD})
        self.assertEqual(rd.audit(ROW, inst, [P1])[0], PA.CLEAN)
        rd = Readers({("c", P1): SORRY_ONLY, ("src", P1): SORRY_ONLY}, {("c", P1): fr(["NS.libSorry"]), ("src", P1): fr(["NS.libSorry"])})
        self.assertEqual(rd.audit(ROW, inst, [P1])[0], PA.UNKNOWN)
        self.assertEqual(rd.fcalls, [("src", P1)])   # the candidate's finer reading is not taken (finer_hooks)


class Deadline(unittest.TestCase):
    def test_each_compile_gets_at_most_the_time_left_and_no_pin_starts_late(self):
        now = [1000.0]
        rd = Readers({("c", P1): GOOD, ("c", P2): GOOD})
        orig = rd.read

        def slow(row, text, pin, timeout):
            out = orig(row, text, pin, timeout)
            now[0] += 50
            return out
        rd.read = slow
        st, why = rd.audit(ROW, marked(ROW, "c"), [P1, P2], timeout=600, deadline=1052.0, clock=lambda: now[0])
        self.assertEqual(st, PA.UNKNOWN)
        self.assertIn("v4.31.0: the audit deadline was reached", why)
        self.assertEqual(rd.timeouts, [52])
        rd = Readers({("c", P1): GOOD})
        self.assertEqual(rd.audit(ROW, marked(ROW, "c"), [P1], deadline=1003.0, clock=lambda: 1000.0)[0], PA.UNKNOWN)   # < 5 s left
        self.assertEqual(rd.calls, [])
        rd = Readers({("c", P1): GOOD})
        self.assertEqual(rd.audit(ROW, marked(ROW, "c"), [P1])[0], PA.CLEAN)
        self.assertEqual(rd.timeouts, [OPK.AUDIT_TIMEOUT_S])   # no deadline: the published gate's timeout

    def test_a_reference_reading_timed_out_under_a_shortened_timeout_is_not_kept(self):
        cache = PA.ReadOnce()
        rd = Readers({("c", P1): SORRY_ONLY, ("src", P1): dict(GOOD, axioms=None, timed_out=True)})
        self.assertEqual(rd.audit(ROW, marked(ROW, "c"), [P1], cache=cache, deadline=1100.0, clock=lambda: 1000.0)[0], PA.UNKNOWN)
        self.assertEqual(cache.keys(), [])
        self.assertEqual(rd.audit(ROW, marked(ROW, "c"), [P1], cache=cache)[0], PA.UNKNOWN)   # the full timeout: kept
        self.assertEqual(len(cache.keys()), 1)


class Caching(unittest.TestCase):
    def test_the_reference_is_read_once_per_row_and_pin(self):
        table = {(t, p): SORRY_ONLY for t in ("a", "b", "c", "src") for p in (P1, P2)}
        finer = {(t, p): fr(["NS.libSorry"]) for t in ("a", "b", "c", "src") for p in (P1, P2)}
        rd, cache = Readers(table, finer), PA.ReadOnce()
        for t in ("a", "b", "c"):
            self.assertEqual(rd.audit(ROW, marked(ROW, t), [P1, P2], cache=cache)[0], PA.CLEAN)
        self.assertEqual([c for c in rd.calls if c[0] == "src"], [("src", P1), ("src", P2)])
        self.assertEqual([c for c in rd.fcalls if c[0] == "src"], [("src", P1), ("src", P2)])
        self.assertEqual(len([c for c in rd.fcalls if c[0] != "src"]), 6)   # the candidate's own finer reading: per audit
        other = dict(ROW, src=ROW["src"] + "\n-- another reference text\n")
        rd.audit(other, marked(ROW, "a"), [P1], cache=cache)
        self.assertEqual(len([c for c in rd.calls if c[0] == "src"]), 3)   # a new sha: read again
        rd.audit(dict(ROW, name="Other.row"), marked(ROW, "a"), [P1], cache=cache)
        self.assertEqual(len([c for c in rd.calls if c[0] == "src"]), 4)   # another row: read again

    def test_concurrent_audits_take_one_reading(self):
        table = {(t, P1): SORRY_ONLY for t in [f"t{i}" for i in range(8)] + ["src"]}
        finer = {(t, P1): fr(["NS.libSorry"]) for t in [f"t{i}" for i in range(8)] + ["src"]}
        rd, cache, out = Readers(table, finer, delay=0.05), PA.ReadOnce(), {}

        def one(i):
            out[i] = rd.audit(ROW, marked(ROW, f"t{i}"), [P1], cache=cache)[0]
        ts = [threading.Thread(target=one, args=(i,)) for i in range(8)]
        for t in ts:
            t.start()
        for t in ts:
            t.join(30)
        self.assertEqual(set(out.values()), {PA.CLEAN})
        self.assertEqual(rd.calls.count(("src", P1)), 1)
        self.assertEqual(rd.fcalls.count(("src", P1)), 1)

    def test_a_reading_that_raised_is_not_kept(self):
        cache = PA.ReadOnce()
        rd = Readers({("c", P1): SORRY_ONLY, ("src", P1): SORRY_ONLY}, {("c", P1): fr(["NS.libSorry"]), ("src", P1): fr(["NS.libSorry"])},
                     raise_on={("src", P1)})
        self.assertEqual(rd.audit(ROW, marked(ROW, "c"), [P1], cache=cache)[0], PA.UNKNOWN)
        rd.raise_on.clear()
        self.assertEqual(rd.audit(ROW, marked(ROW, "c"), [P1], cache=cache)[0], PA.CLEAN)
        self.assertEqual(rd.calls.count(("src", P1)), 2)

    def test_only_complete_readings_and_evidence_are_kept(self):
        """keep_reading: a reading whose failure more time or another try could change is taken again by the next audit (review
        2026-11-24: one failed reference reading made every later candidate of the row unknown)."""
        kept = [dict(SORRY_ONLY), dict(GOOD, axioms=None, sorry_warning=True), dict(GOOD, axioms=None, switch=True),
                {"hook": "an elaborator", "axioms": None}, dict(GOOD, decl_errors=["12:4: type mismatch"]),
                dict(GOOD, axioms=None, timed_out=True), fr(["NS.libSorry"]),
                {"error": "finer reading: the compile timed out", "timed_out": True}]
        dropped = [None, "text", {"error": "the reading another audit takes did not come in time"},
                   {"error": "finer reading: no marker; not compiled again with Lean's command elaborator imported: 3 s left",
                    "timed_out": False, "program_errors": ["x"]},
                   dict(GOOD, axioms=None, decl_errors=["lean exit -9: Killed"])]
        for r in kept:
            self.assertTrue(PA.keep_reading(r, False), r)
        for r in dropped:
            self.assertFalse(PA.keep_reading(r, False), r)
        self.assertFalse(PA.keep_reading(dict(GOOD, axioms=None, timed_out=True), True))   # a shortened timeout
        self.assertTrue(PA.keep_reading(dict(GOOD, axioms=None, sorry_warning=True, timed_out=True), True))   # evidence first

    def test_a_failed_reference_reading_is_taken_again(self):
        """Three candidates of one row that need the reference: its reading fails twice (a killed compile, then a reader error),
        then comes; the third candidate is decided on it, and the reading is then kept."""
        cache = PA.ReadOnce()
        seq = [dict(GOOD, axioms=None, decl_errors=["lean exit -9: Killed"]), {"error": "finer reading: 2 s left"}, SORRY_ONLY]
        rd = Readers({(t, P1): SORRY_ONLY for t in ("a", "b", "c", "d")},
                     {(t, P1): fr(["NS.libSorry"]) for t in ("a", "b", "c", "d", "src")})
        orig = rd.read

        def read(row, text, pin, timeout):
            return seq.pop(0) if tag_of(text) == "src" else orig(row, text, pin, timeout)
        rd.read = read
        got = [rd.audit(ROW, marked(ROW, t), [P1], cache=cache)[0] for t in ("a", "b", "c", "d")]
        self.assertEqual(got, [PA.UNKNOWN, PA.UNKNOWN, PA.CLEAN, PA.CLEAN])
        self.assertEqual(seq, [])   # three readings of the reference in all; the fourth audit used the kept one

    def test_standard_axioms_never_read_the_reference(self):
        rd = Readers({("c", P1): GOOD, ("c", P2): GOOD, ("src", P1): GOOD})
        rd.audit(ROW, marked(ROW, "c"), [P1, P2])
        self.assertEqual(rd.calls, [("c", P1), ("c", P2)])
        self.assertEqual(rd.fcalls, [])

    def test_the_process_cache_is_an_object_not_a_module_level_container(self):
        """post_fast/pf_worker scopes every empty module-level dict / set / list of harness modules for its speculative threads."""
        self.assertIsInstance(PA.CACHE, PA.ReadOnce)
        self.assertFalse([k for k, v in vars(PA).items() if not k.startswith("__") and isinstance(v, (dict, set, list))])


# ---------------------------------------------------------------------------------------------- the invariant: gate => guard
def random_reading(rnd, by_construction: bool):
    if by_construction:
        return dict(OLD_MODULE, sorry_warning=rnd.random() < 0.2, timed_out=rnd.random() < 0.05,
                    decl_errors=["1:1: e"] if rnd.random() < 0.05 else [])
    if rnd.random() < 0.04:
        return rnd.choice([None, {"error": "x"}])
    l1 = rnd.choice([STD, STD, STD, [], ["sorryAx"], SORRYAX, STD + ["Lean.ofReduceBool"], ["myAxiom", "sorryAx"], None])
    r = {"axioms": l1, "module": rnd.random() < 0.5, "by_construction": False, "sorry_warning": rnd.random() < 0.08,
         "switch": rnd.random() < 0.03, "timed_out": rnd.random() < 0.05, "decl_errors": ["1:1: e"] if rnd.random() < 0.05 else []}
    if l1 is not None and rnd.random() < 0.25:
        l2 = rnd.choice([STD, ["sorryAx"], SORRYAX, l1])
        r["lists"] = [l1, l2]
        r["axioms"] = list(dict.fromkeys(l1 + l2))
    return r


def random_finer(rnd):
    x = rnd.random()
    if x < 0.08:
        return None
    if x < 0.14:
        return rnd.choice([{"error": "finer reading: x"}, {"timed_out": True, "error": "t"}, dict(fr(["NS.libSorry"]), sorry_warning=True)])
    return fr(rnd.choice([["NS.libSorry"], ["NS.lib2"], ["NS.libSorry", "Imp.l"], [], ["NS.x"]]), rnd.choice([[], [], [], ["NS.x"]]),
              axioms=rnd.choice([["sorryAx"], ["sorryAx"], SORRYAX, ["myAxiom", "sorryAx"]]))


class Invariant(unittest.TestCase):
    def test_whatever_the_gate_accepts_the_guard_accepts_on_the_same_readings(self):
        rnd = random.Random(20261124)
        seen = {PA.CLEAN: 0, PA.SKIPPED: 0, PA.SORRY: 0, PA.UNKNOWN: 0}
        for trial in range(4000):
            pins = ["v4.34.0", "v4.31.0", "v4.27.0"][:rnd.randint(1, 3)]
            old = {p: (p == "v4.27.0" and rnd.random() < 0.6) for p in pins}
            table, finer = {}, {}
            for p in pins:
                table[("c", p)] = random_reading(rnd, old[p])
                table[("src", p)] = random_reading(rnd, old[p])
                finer[("c", p)], finer[("src", p)] = random_finer(rnd), random_finer(rnd)
            row = ROW if rnd.random() < 0.95 else dict(ROW, src="")
            rd = Readers(table, finer)
            st, why = rd.audit(row, marked(ROW, "c"), pins)
            seen[st] += 1
            readings = {p: table[("c", p)] for p in pins}
            refs = {p: table[("src", p)] if row["src"] else {"error": "the row has no reference proof"} for p in pins}
            finers = {p: (finer[("c", p)], finer[("src", p)] if row["src"] else {"error": "the row has no reference proof"}) for p in pins}
            verdict, gwhy, states = AG.classify(readings, refs, finers)
            ctx = f"trial {trial}: gate {st} ({why}); guard {verdict} ({gwhy})"
            if st in PA.ACCEPTED:
                self.assertNotEqual(verdict, AG.FAIL, ctx)
            if st == PA.CLEAN:
                self.assertEqual(verdict, AG.PASS, ctx)
            if st == PA.SKIPPED:
                self.assertIn(verdict, (AG.PASS, AG.NOT_READ), ctx)
                if verdict == AG.NOT_READ:
                    self.assertTrue(all(old.values()), ctx)
            if verdict == AG.FAIL:
                self.assertNotIn(st, PA.ACCEPTED, ctx)
            # judged by the guard's rule pin by pin: clean iff every pin reads OK there
            self.assertEqual(st == PA.CLEAN, all(s == AG.OK for s, _ in states.values()), ctx)
            if st == PA.SORRY:
                self.assertEqual(verdict, AG.FAIL, ctx)
        self.assertTrue(all(n > 50 for n in seen.values()), seen)


# ----------------------------------------------------------------------------------------------- the reading through the compiles
class Reading(unittest.TestCase):
    def test_module_files_are_printed_on_every_toolchain_and_not_read_by_construction_before_v4_30(self):
        r = with_src(row_of("strata"), ["v4.31.0", "v4.29.1"])
        w = World(modules={(r["name"], "v4.31.0"), (r["name"], "v4.29.1")})
        with w.on():
            new = PA.gate_reading(r, marked(r, "c"), "v4.31.0", 600)
            old = PA.gate_reading(r, marked(r, "c"), "v4.29.1", 600)
        self.assertIn("#print axioms", w.calls[0][2])
        self.assertIn("#print axioms", w.calls[1][2])   # forced there too, as the guard's forced reading: Lean gives an error, no list
        with w.on():
            guard = AG.forced_reading(r, marked(r, "c"), "v4.29.1", 600)
        self.assertEqual(w.calls[2][2:], w.calls[1][2:])   # the guard's own text and flags
        self.assertEqual((new["axioms"], new["module"], new["by_construction"]), (STD, True, False))
        self.assertEqual((old["axioms"], old["module"], old["by_construction"]), (None, True, True))
        self.assertTrue(AG.structural(old) and AG.structural(guard))
        self.assertEqual(old["print_errors"], 2)   # the two prints' errors are on the print lines, not the declaration's
        self.assertEqual(w.calls[0][6][-1], "-Dwarn.sorry=true")
        self.assertEqual(PA.pin_verdict(old, None)[0], PA.PIN_CONSTRUCTION)
        self.assertEqual(PA.pin_verdict(dict(old, by_construction=False), None)[0], PA.PIN_UNKNOWN)   # from v4.30: no list fails closed

    def test_a_module_file_before_v4_30_that_prints_a_list_is_read(self):
        """The version rule only labels a print with no list; a toolchain that does print is read like any other."""
        r = with_src(row_of("strata"), ["v4.29.1"])
        w = World({("c", "v4.29.1"): {"axioms": ["sorryAx"]}}, modules={(r["name"], "v4.29.1")})
        with w.on(), mock.patch.object(C, "MODULE_PRINT_FROM", (4, 29)):
            self.assertEqual(PA.gate_audit(r, marked(r, "c"), ["v4.29.1"], cache=PA.ReadOnce())[0], PA.SORRY)
        with w.on():   # (Lean as on v4.29.1: an error and no list) not read by construction, the sorry message still read
            self.assertEqual(PA.gate_audit(r, marked(r, "c"), ["v4.29.1"], cache=PA.ReadOnce())[0], PA.SKIPPED)
        w = World({("c", "v4.29.1"): {"axioms": STD, "sorry": True}}, modules={(r["name"], "v4.29.1")})
        with w.on():
            self.assertEqual(PA.gate_audit(r, marked(r, "c"), ["v4.29.1"], cache=PA.ReadOnce())[0], PA.SORRY)

    def test_plain_project_and_putnam_rows_print_as_published(self):
        pub = published()
        for r in (with_src(row_of("cslib"), ["v4.31.0"]), with_src(row_of("putnambench"), ["v4.27.0"])):
            w, wp = World(), World()
            with w.on():
                got = PA.gate_reading(r, marked(r, "c"), "v4.31.0" if r["source"] != "putnambench" else "v4.27.0", 600)
            with wp.on(), published_chain(pub):
                C.audit_axioms(r, marked(r, "c"), "v4.31.0" if r["source"] != "putnambench" else "v4.27.0", timeout=600)
            self.assertEqual(w.calls, wp.calls)
            self.assertFalse(got["module"])
            self.assertEqual(got["axioms"], STD)

    def test_the_union_of_both_prints_and_the_reference_allows_their_intersection(self):
        r = with_src(row_of("cslib"), ["v4.31.0"])
        w = World({("c", "v4.31.0"): {"lists": [STD, SORRYAX]}, ("src", "v4.31.0"): {"lists": [SORRYAX, STD]}})
        with w.on():
            st, why = PA.gate_audit(r, marked(r, "c"), ["v4.31.0"], cache=PA.ReadOnce())
        self.assertEqual(st, PA.SORRY, why)   # the candidate reads sorryAx in one print; the reference's prints differ: it allows
        self.assertEqual(len(w.calls), 2)     # what both read, nothing beyond the three
        w = World({("c", "v4.31.0"): {"lists": [STD, SORRYAX]}, ("src", "v4.31.0"): {"lists": [SORRYAX, SORRYAX]}})
        with w.on():
            st, why = PA.gate_audit(r, marked(r, "c"), ["v4.31.0"], cache=PA.ReadOnce())
        self.assertEqual(st, PA.CLEAN, why)   # both prints of the reference read sorryAx (non-module: the finer program answers)
        self.assertEqual(len(w.calls), 4)

    def test_a_sorry_message_of_the_library_prefix_is_not_the_candidates(self):
        r = with_src(row_of("cslib"), ["v4.31.0"])
        w = World({("c", "v4.31.0"): {"lib_sorry": True}})
        with w.on():
            self.assertEqual(PA.gate_audit(r, marked(r, "c"), ["v4.31.0"], cache=PA.ReadOnce())[0], PA.CLEAN)

    def test_row_25_like_through_the_compiles_with_the_finer_program(self):
        """The reference reads sorryAx (a library lemma proved by sorry): the same lemma passes, another lemma and the value made
        sorry are rejected; each through the real finer_reading and parse, the World answering the program."""
        r = with_src(row_of("arklib"), ["v4.34.0"])
        mods = {(r["name"], "v4.34.0")}
        base = {("src", "v4.34.0"): {"axioms": ["sorryAx"], "finer": {"sources": ["NS.libSorry"]}}}
        for tag, finer, want in (("same", {"sources": ["NS.libSorry"]}, PA.CLEAN), ("other", {"sources": ["NS.lib2"]}, PA.SORRY),
                                 ("own", {"sources": ["NS.x"], "own": ["NS.x"]}, PA.SORRY)):
            w = World({**base, (tag, "v4.34.0"): {"axioms": ["sorryAx"], "finer": finer}}, modules=mods)
            with w.on():
                st, why = PA.gate_audit(r, marked(r, tag), ["v4.34.0"], cache=PA.ReadOnce())
            self.assertEqual(st, want, why)
            self.assertEqual(len(w.calls), 4)   # its reading, the reference's, its finer reading, the reference's
            self.assertEqual(sum(FS.MARK in t for t in w.texts()), 2)


class Row42Chain(unittest.TestCase):
    def test_the_chain_is_cut_at_step_7_where_the_published_gate_let_it_through(self):
        """Held-out row 42's shape: a `module` file, one pin v4.34.0; steps 0-6 read the standard three, steps 7-10 sorryAx alone with
        no Lean message. The new gate rejects 7-10 (the guard sets them back); the published gate reads them `skipped` (adopted)."""
        r = with_src(row_of("arklib"), ["v4.34.0"])
        truth = {(f"s{i}", "v4.34.0"): {"axioms": STD if i < 7 else ["sorryAx"]} for i in range(11)}
        truth[("src", "v4.34.0")] = {"axioms": STD}
        mods = {(r["name"], "v4.34.0")}
        pub = published()
        for i in range(11):
            w = World(truth, mods)
            with w.on():
                st, why = PA.gate_audit(r, marked(r, f"s{i}"), ["v4.34.0"], cache=PA.ReadOnce())
                guard = AG.classify({"v4.34.0": AG.forced_reading(r, marked(r, f"s{i}"), "v4.34.0", 600)},
                                    {"v4.34.0": AG.forced_reading(r, r["src"], "v4.34.0", 600)})[0]
            wp = World(truth, mods)
            with wp.on(), published_chain(pub):
                pst, _ = pub["audit_proof"](r, marked(r, f"s{i}"), ["v4.34.0"], {})
            self.assertEqual(st, PA.CLEAN if i < 7 else PA.SORRY, why)
            self.assertEqual(guard, AG.PASS if i < 7 else AG.FAIL)
            self.assertEqual(pst, PA.SKIPPED)


# ------------------------------------------------------------------------------------------------ the warm-up, the switch, the export
def warm_call() -> str:
    """The one audit_axioms call of post_fast/pf_worker.audit_warm (frozen), as written."""
    tree = ast.parse((ROOT / "post_fast/pf_worker.py").read_text())
    fn = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "audit_warm")
    calls = [n for n in ast.walk(fn) if isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute) and n.func.attr == "audit_axioms"]
    assert len(calls) == 1
    return ast.unparse(calls[0])


class WarmUp(unittest.TestCase):
    CASES = (("strata", "v4.31.0", True), ("strata", "v4.29.1", True), ("cslib", "v4.31.0", False), ("putnambench", "v4.27.0", False))

    def test_the_warm_up_call_is_as_written(self):
        self.assertEqual(warm_call(), "C.audit_axioms(row, decl, v, timeout=OPK.AUDIT_TIMEOUT_S)")
        self.assertIn("_orig_default_audit = P.default_audit", (ROOT / "post_fast/pf_worker.py").read_text())

    def run_mode(self, mode: str | None):
        """For each case: (the warm-up's compile call, the gate's own compile call) in a post-stage process of `mode`."""
        env = {} if mode is None else {OP.AUDIT_ENV: mode}
        out = []
        for source, pin, module in self.CASES:
            r = with_src(row_of(source), [pin])
            w = World(modules={(r["name"], pin)} if module else ())
            with mock.patch.dict(os.environ, env), mock.patch.object(C, "GATE_MODULE_PRINT", False), \
                    mock.patch.object(PA, "CACHE", PA.ReadOnce()), contextlib.redirect_stdout(io.StringIO()):
                if mode is None:
                    os.environ.pop(OP.AUDIT_ENV, None)
                aud = OP.default_audit()
                with w.on():
                    C.audit_axioms(r, marked(r, "c"), pin, timeout=OPK.AUDIT_TIMEOUT_S)   # = audit_warm's call
                    aud(r, marked(r, "c"))
            out.append((w.calls[0], w.calls[1]))
        return out

    def test_the_warm_up_compiles_the_gates_text_in_both_modes(self):
        for mode in (None, "guard", "published"):
            for (warm, gate), (source, pin, module) in zip(self.run_mode(mode), self.CASES):
                self.assertEqual(warm, gate, (mode, source, pin))
                forced = module and mode != "published"   # every toolchain, v4.29.1 included (Lean: an error, no list)
                self.assertEqual("#print axioms" in warm[2], forced or not module, (mode, source, pin))


class Switch(unittest.TestCase):
    def test_audit_mode(self):
        self.assertEqual(OP.audit_mode("published"), ("published", None))
        self.assertEqual(OP.audit_mode(" published "), ("published", None))
        for v in ("", "guard"):
            self.assertEqual(OP.audit_mode(v), ("guard", None))
        for v in ("Published", "off", "0", "publish"):
            mode, warn = OP.audit_mode(v)
            self.assertEqual(mode, "guard")
            self.assertIn("neither published nor guard", warn)

    def test_default_audit_sets_the_flag_and_logs_the_mode(self):
        for env, flag, logged in (({OP.AUDIT_ENV: "published"}, False, ""), ({OP.AUDIT_ENV: "guard"}, True, "gate audit: the export guard's rule"),
                                  ({OP.AUDIT_ENV: "typo"}, True, "WARNING: LRA_POST_AUDIT='typo'")):
            buf = io.StringIO()
            with mock.patch.dict(os.environ, env), mock.patch.object(C, "GATE_MODULE_PRINT", not flag), contextlib.redirect_stdout(buf):
                OP.default_audit()
                self.assertIs(C.GATE_MODULE_PRINT, flag)
            self.assertIn(logged, buf.getvalue())
            if not logged:
                self.assertEqual(buf.getvalue(), "")   # published: no new output

    def test_the_flag_is_off_in_a_fresh_process(self):
        out = subprocess.run([sys.executable, "-B", "-c", "from scorer import compile as C; print(C.GATE_MODULE_PRINT)"], cwd=ROOT,
                             capture_output=True, text=True, timeout=120)
        self.assertEqual(out.stdout.strip(), "False", out.stderr)

    def test_published_restores_the_published_gate_exactly(self):
        """LRA_POST_AUDIT=published: the current default_audit's audit and the published one (executed from its verbatim text, with
        the published audit_proof and audit_axioms) give the same verdicts and make the same compiles, on random tables."""
        self.assertEqual(hashlib.sha256(PUBLISHED.read_bytes()).hexdigest(), PUBLISHED_SHA256)
        pub, rnd = published(), random.Random(7)
        for trial in range(300):
            row = random_row(rnd)
            pins = newest_first(row["version_info"])
            truth = random_truth(rnd, ["c0", "c1", "c2", "src"], pins)
            mods = random_modules(rnd, row)
            texts = [marked(row, t) for t in ("c0", "c1", "c2")]
            w = World(truth, mods)
            with mock.patch.dict(os.environ, {OP.AUDIT_ENV: "published"}), mock.patch.object(C, "GATE_MODULE_PRINT", True), w.on():
                aud = OP.default_audit()
                cur = [aud(row, t) for t in texts]
                self.assertFalse(C.GATE_MODULE_PRINT)
            wp = World(truth, mods)
            with wp.on(), published_chain(pub):
                old = [pub["default_audit"]()(row, t) for t in texts]
            self.assertEqual(cur, old, f"trial {trial}")
            self.assertEqual(w.calls, wp.calls, f"trial {trial}")

    def test_the_new_gate_accepts_nothing_the_published_gate_rejects(self):
        """On the same compiles (one truth per text and pin): every candidate the new gate accepts, the published gate accepts; the new
        one makes no more compiles than the published one for a candidate whose axioms are standard."""
        pub, rnd = published(), random.Random(11)
        stricter = 0
        for trial in range(400):
            row = random_row(rnd)
            pins = newest_first(row["version_info"])
            truth = random_truth(rnd, ["c0", "c1", "src"], pins)
            mods = random_modules(rnd, row)
            for t in ("c0", "c1"):
                w, wp = World(truth, mods), World(truth, mods)
                with w.on():
                    st, why = PA.gate_audit(row, marked(row, t), pins, cache=PA.ReadOnce())
                with wp.on(), published_chain(pub):
                    pst, pwhy = pub["audit_proof"](row, marked(row, t), pins, {})
                ctx = f"trial {trial} {t}: new {st} ({why}); published {pst} ({pwhy})"
                if st in PA.ACCEPTED:
                    self.assertIn(pst, PA.ACCEPTED, ctx)
                elif pst in PA.ACCEPTED:
                    stricter += 1
                if all((truth[(t, v)].get("axioms") or []) and set(truth[(t, v)]["axioms"]) <= set(STD) and not truth[(t, v)].get("lists")
                       for v in pins):
                    self.assertLessEqual(len(w.calls), len(pins), ctx)
                    self.assertLessEqual(len(w.calls), len(wp.calls), ctx)
        self.assertGreater(stricter, 20)


class CompileCounts(unittest.TestCase):
    def test_compiles_per_candidate(self):
        r = with_src(row_of("arklib"), ["v4.34.0", "v4.33.1", "v4.31.0", "v4.30.0"])
        pins = newest_first(r["version_info"])
        mods = {(r["name"], v) for v in pins}
        cache = PA.ReadOnce()
        w = World({(t, v): {"axioms": STD} for t in ("a", "b") for v in pins}, mods)
        with w.on():
            self.assertEqual(PA.gate_audit(r, marked(r, "a"), pins, cache=cache)[0], PA.CLEAN)
        self.assertEqual(len(w.calls), 4)   # one per pin, as the published gate
        x = STD + ["Lean.ofReduceBool"]
        w = World({(t, v): {"axioms": x} for t in ("a", "b", "src") for v in pins}, mods)
        with w.on():
            self.assertEqual(PA.gate_audit(r, marked(r, "a"), pins, cache=cache)[0], PA.CLEAN)
            self.assertEqual(len(w.calls), 8)   # + the reference on each pin
            self.assertEqual(PA.gate_audit(r, marked(r, "b"), pins, cache=cache)[0], PA.CLEAN)
            self.assertEqual(len(w.calls), 12)  # the reference's readings are kept for the process
        w = World({(t, v): {"axioms": ["sorryAx"]} for t in ("a", "b", "src") for v in pins}, mods)
        cache = PA.ReadOnce()
        with w.on():
            self.assertEqual(PA.gate_audit(r, marked(r, "a"), pins, cache=cache)[0], PA.CLEAN)
            self.assertEqual(len(w.calls), 16)  # its reading, the reference's, and both finer readings on each pin
            self.assertEqual(PA.gate_audit(r, marked(r, "b"), pins, cache=cache)[0], PA.CLEAN)
            self.assertEqual(len(w.calls), 24)  # its reading and its finer reading on each pin


class ExportAuditUnchanged(unittest.TestCase):
    def test_the_export_audit_is_the_published_one_whatever_the_flag(self):
        """open_package.audit_export (run.sh's export step) against the published audit_export, audit_proof and audit_axioms on random
        tables, with scorer.compile.GATE_MODULE_PRINT off and on (a post-stage process): the same choices and the same compiles."""
        pub, rnd = published(), random.Random(3)
        for trial in range(300):
            row = random_row(rnd)
            pins = newest_first(row["version_info"])
            truth = random_truth(rnd, ["c0", "c1", "src"], pins)
            mods = random_modules(rnd, row)
            cands = [("proofs.jsonl", marked(row, "c0")), ("picks", marked(row, "c1")), ("seed", row["src"])]
            wp = World(truth, mods)
            with wp.on(), published_chain(pub), contextlib.redirect_stdout(io.StringIO()):
                old = pub["audit_export"](row, cands)
            for flag in (False, True):
                w = World(truth, mods)
                with w.on(), mock.patch.object(C, "GATE_MODULE_PRINT", flag), contextlib.redirect_stdout(io.StringIO()):
                    cur = OPK.audit_export(row, cands)
                self.assertEqual(cur, old, f"trial {trial} flag {flag}")
                self.assertEqual(w.calls, wp.calls, f"trial {trial} flag {flag}")

    def test_the_only_change_to_the_export_audit_is_the_explicit_keyword(self):
        pub_src = ast.parse(PUBLISHED.read_text())
        src = {n.name: ast.unparse(n) for n in pub_src.body if isinstance(n, ast.FunctionDef)}
        cur = {n.name: ast.unparse(n) for n in ast.parse((ROOT / "harness/open_package.py").read_text()).body
               if isinstance(n, ast.FunctionDef) and n.name in ("audit_proof", "audit_export")}
        self.assertEqual(cur["audit_export"], src["audit_export"])
        self.assertEqual(cur["audit_proof"], src["audit_proof"].replace("timeout=tmo()))", "timeout=tmo(), module_print=False))"))


class Fingerprint(unittest.TestCase):
    def test_the_seven_measured_scripts_are_unchanged(self):
        h = "".join(hashlib.sha256((ROOT / "post_fast" / f).read_bytes()).hexdigest() + "\n"
                    for f in ("post_stage.sh", "pf_drive.py", "pf_svc.py", "pf_worker.py", "prefix_backend.py", "snapshot.py", "merge_post.py"))
        self.assertEqual(hashlib.sha256(h.encode()).hexdigest()[:16], "b4ac6d42002767a0")


if __name__ == "__main__":
    unittest.main()
