#!/usr/bin/env python3
"""Tests of the finer sorry check (harness/finer_sorry.py and its place in harness/axiom_guard.py, 2026-11-24).

They start no Lean. The Lean program itself is tested on the library environments by tests/finer_lean/run_fixtures.py. Here: the
program's text, the parser of its lines, the rule (decide), the switch, the guard with stand-in readers (the check on), and the
guard with the check off against the guard as published (tag open-camready-20261125, a copy in tests/data), on random tables.
    python3 -B -m pytest -q -p no:cacheprovider tests/test_finer_sorry.py"""
from __future__ import annotations

import contextlib, hashlib, json, os, random, re, sys, tempfile, threading, time, types, unittest
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

PUBLISHED = ROOT / "tests/data/axiom_guard_published.py.txt"   # final/harness/axiom_guard.py at tag open-camready-20261125 (git blob 40a9b7f7)
PUBLISHED_SHA256 = "14912c75ba360d9939e1833f47a811f2262ed39bd1cf561088568c971e29372d"
STD = ["propext", "Classical.choice", "Quot.sound"]
GOOD = {"axioms": STD}
SORRY = {"axioms": ["sorryAx"]}
NONCE = "0123456789abcdef"


def rows() -> list:
    return [json.loads(l) for l in ROWS_FILE.read_text().splitlines() if l.strip()]


def tmpdir() -> Path:
    return Path(tempfile.mkdtemp(prefix="lra-finer-sorry-"))


def write_jsonl(path: Path, recs: list) -> None:
    path.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in recs))


def proof(row: dict, tag: str) -> str:
    return row["statement"] + f" := by\n  -- mark:{tag}:\n  exact foo\n"


def rec(row: dict, tag: str, score: float, source: str = "post") -> dict:
    return {"name": row["name"], "proof": proof(row, tag), "source": source, "stored_score": score, "tokens": 10, "heartbeats": 100}


def tag_of(text: str) -> str:
    m = re.search(r"-- mark:(\w+):", text)
    return m.group(1) if m else "reference"


# ------------------------------------------------------------------------------------------------------------- program output
def marker(q="X.main", decl="X.main", sources=(), own=(), local=None, axioms=("sorryAx",), complete=True, missing=(), v=FS.VERSION,
           unranged=(), decl_local=True) -> dict:
    return {"v": v, "q": q, "decl": decl, "decl_local": decl_local, "sources": list(sources), "own": list(own),
            "local": list(sources if local is None else local), "unranged": list(unranged), "missing": list(missing),
            "axioms": list(axioms), "n_local": 3, "n_frontier": 5, "complete": complete, "ms": 1}


def end(n=1, unresolved=(), complete=True, error=None, v=FS.VERSION, proof_line=9) -> dict:
    e = {"v": v, "end": True, "markers": n, "unresolved": list(unresolved), "stored": True, "module": False, "walked": 0,
         "complete": complete, "proof_line": proof_line, "lean": "4.31.0", "ms": 2}
    if error:
        e["error"] = error
    return e


def msg(j, line=20, nonce=NONCE, severity="information") -> dict:
    data = j if isinstance(j, str) else f"{FS.MARK} {nonce} {json.dumps(j)}"
    return {"severity": severity, "pos": {"line": line, "column": 0}, "data": data}


def fr(sources=(), own=(), axioms=("sorryAx",), decls=("X.main",), complete=True, missing=(), **kw) -> dict:
    """A finer reading as axiom_guard.finer_reading returns it: one marker per printed name."""
    ms = [marker(q=d, decl=d, sources=sources, own=own, axioms=axioms, complete=complete, missing=missing) for d in decls]
    out = {"markers": ms, "end": end(len(ms), complete=complete), "sorry_warning": False, "switch": False, "timed_out": False,
           "decl_errors": [], "program_errors": [], "seconds": 1.0, "program_ms": 2, "finer_version": FS.VERSION, "lean_import": False}
    out.update(kw)
    return out


class Program(unittest.TestCase):
    def test_the_text(self):
        t = FS.program(["main", "X.main"], NONCE, 9)
        self.assertIn(f'"{FS.MARK} {NONCE} "', t)
        self.assertIn("([`main, `X.main] : _root_.List _root_.Lean.Name)", t)
        self.assertIn("_root_.Lean.realizeGlobalConst", t)   # names resolve as `#print axioms` resolves them, private ones included
        self.assertIn("_root_.Lean.collectAxioms", t)
        self.assertIn("_root_.Lean.findDeclarationRanges?", t)   # OWN: declared by the proof text (program v2)
        self.assertIn("let proofLine : _root_.Nat := 9\n", t)
        self.assertTrue(t.startswith("set_option maxHeartbeats 0 in\n#eval "))   # a proof's own heartbeat setting does not stop it
        self.assertNotIn("@", t.replace("@[", "").replace("(@", ""))   # every placeholder filled
        self.assertEqual(FS.program(["main", "main"], NONCE, 9).count("`main"), 1)
        from scorer.compile import SORRY_SWITCH_RE
        from scorer.forbidden import strip_lean_comments
        self.assertIsNone(SORRY_SWITCH_RE.search(strip_lean_comments(t)))   # the scorer's switch check reads the program's lines too
        self.assertNotRegex(t, r"\bsorry\b")                                  # no sorry of its own
        # the file's scope cannot change what the program resolves (review 2026-11-24): it opens nothing, resolves no name literal
        # (``x), and names every global from the root
        self.assertNotRegex(t, r"(?m)^\s*open\b|\bopen\s+\w+.*\bin\b")
        self.assertNotIn("``", t)
        self.assertIn("`sorryAx", t)
        bare = re.findall(r"(?<![\w.`'])(?:Lean|Std|IO|Json|Name|Nat|String|Array|List|Option|Bool|Unit|Pure|toString|toJson|logInfo|getEnv|"
                          r"collectAxioms|privateToUserName\??|realizeGlobalConst|mkIdent|liftCoreM|findDeclarationRanges\?)\b", t)
        self.assertEqual(bare, [], "identifiers not named from the root")
        self.assertIsNone(FS.hooks(t.replace("#eval", "")))   # (the program registers nothing, its own `#eval` aside)

    def test_bad_input_is_refused(self):
        for n in ("", " main", "a`b", "a\nb", "main\r"):
            with self.assertRaises(ValueError, msg=n):
                FS.program([n], NONCE, 9)
        for nonce in ("", "XYZ", "0123", NONCE.upper(), NONCE + "\n"):
            with self.assertRaises(ValueError, msg=nonce):
                FS.program(["main"], nonce, 9)
        for line in (0, -1, True, "9", None, 9.0):
            with self.assertRaises(ValueError, msg=repr(line)):
                FS.program(["main"], NONCE, line)
        self.assertRegex(FS.new_nonce(), r"\A[0-9a-f]{16}\Z")
        self.assertNotEqual(FS.new_nonce(), FS.new_nonce())

    def test_the_lean_import(self):
        self.assertEqual(FS.with_lean_import("import Foo\n"), "import Lean.Elab.Command\nimport Foo\n")
        core = "/- c -/\n-- x\nmodule\n\npublic import Foo\n"
        self.assertEqual(FS.with_lean_import(core), "/- c -/\n-- x\nmodule\npublic meta import Lean.Elab.Command\n\npublic import Foo\n")
        from scorer import compile as C
        self.assertEqual(FS.with_lean_import(core), C._with_measure_import(core))   # = the scorer's measuring import


class Parse(unittest.TestCase):
    def test_a_reading(self):
        ms = [msg(marker(q="main"), 21), msg(marker(q="X.main"), 22), msg(end(2), 23)]
        got = FS.parse(ms, 20, NONCE)
        self.assertEqual([m["q"] for m in got["markers"]], ["main", "X.main"])
        self.assertEqual(got["end"]["markers"], 2)

    def test_lines_that_are_not_the_programs_are_ignored(self):
        other = [msg(marker(q="forged", sources=[]), 25, nonce="ffffffffffffffff"),   # another nonce
                 msg(marker(q="early"), 19),                                          # before the program's first line
                 msg(marker(q="warn"), 21, severity="warning"),                       # not an information message
                 {"severity": "information", "pos": None, "data": f"{FS.MARK} {NONCE} {{}}"},   # no line
                 msg("X.main depends on axioms: [sorryAx]", 22), "not a message"]
        got = FS.parse(other + [msg(marker(), 21), msg(end(1), 23)], 20, NONCE)
        self.assertEqual([m["q"] for m in got["markers"]], ["X.main"])

    def test_failures(self):
        cases = {
            "no end line: the program did not run": [],
            "no end line (the program did not finish)": [msg(marker(), 21)],
            "two end lines": [msg(marker(), 21), msg(end(1), 22), msg(end(1), 23)],
            "a marker line does not parse": [msg(f"{FS.MARK} {NONCE} {{not json", 21), msg(end(0), 22)],
            "a marker of another version (3)": [msg(marker(v=3), 21), msg(end(1), 22)],
            "the program: a module file before v4.30": [msg(end(0, error="a module file before v4.30: ..."), 21)],
            "the end line's 'markers' is not a int": [msg(dict(end(1), markers="1"), 21)],
            "the end line's 'complete' is not a bool": [msg(dict(end(1), complete=1), 21)],
            "a marker's 'sources' is not a list of names": [msg(dict(marker(), sources=[1]), 21), msg(end(1), 22)],
            "a marker's 'complete' is not a bool": [msg(dict(marker(), complete=None), 21), msg(end(1), 22)],
            "a marker's 'q' is not a str": [msg({k: v for k, v in marker().items() if k != "q"}, 21), msg(end(1), 22)],
            "two markers for X.main -> X.main": [msg(marker(), 21), msg(marker(), 22), msg(end(2), 23)],
            "own, local or unranged sources are not among its sources": [msg(marker(sources=["a"], own=["b"]), 21), msg(end(1), 22)],
            "own, local or unranged sources are not among its sources ": [msg(marker(sources=["a", "I.x"], local=["a"], own=["I.x"]), 21),
                                                                          msg(end(1), 22)],   # an imported source is never OWN
            "own, local or unranged sources are not among its sources  ": [msg(marker(sources=["a"], unranged=["a"]), 21), msg(end(1), 22)],
            "a marker's 'decl_local' is not a bool": [msg(dict(marker(), decl_local=None), 21), msg(end(1), 22)],
            "the end line's 'proof_line' is not a int": [msg(dict(end(1), proof_line="9"), 21)],
            "the program read the proof's first line as 8, not 9": [msg(marker(), 21), msg(end(1, proof_line=8), 22)],
            "the end line counts 2 marker(s), 1 read": [msg(marker(), 21), msg(end(2), 22)],
            "no printed name resolved to a declaration (main, X.main)": [msg(end(0, unresolved=["main", "X.main"]), 21)],
            "a marker of another version (1)": [msg(marker(v=1), 21), msg(end(1), 22)],   # program v1 (OWN by name prefix)
        }
        for want, ms in cases.items():
            got = FS.parse(ms, 20, NONCE, 9)
            self.assertIn("error", got, want)
            self.assertIn(want.strip(), got["error"], (want, got))
        self.assertIn("error", FS.parse(None, 20, NONCE))
        self.assertIn("error", FS.parse([msg(f"{FS.MARK} {NONCE} [1, 2]", 21)], 20, NONCE))
        self.assertNotIn("error", FS.parse([msg(marker(), 21), msg(end(1, proof_line=8), 22)], 20, NONCE))   # proof_line not given


class Rule(unittest.TestCase):
    """decide(proof's finer reading, reference's): OK iff both are available, neither side has an OWN source and the proof's sources
    are among the reference's. Everything else fails closed."""

    def test_the_table(self):
        L, M, own = "Lib.lemmaA", "Lib.lemmaB", "X.main"
        table = [  # proof's sources, proof's OWN, reference's sources, reference's OWN -> OK?
            ([L], [], [L], [], True),            # held-out row 25: the library lemma the reference uses
            ([], [], [L], [], True),             # no source (its axioms read no sorryAx)
            ([L], [], [L, M], [], True),
            ([L, M], [], [L], [], False),        # another sorry'd lemma
            ([M], [], [L], [], False),
            ([own], [own], [L], [], False),      # held-out row 42: its own value is sorry
            ([L, own], [own], [L], [], False),
            ([own + ".go"], [own + ".go"], [L], [], False),   # an auxiliary declaration of its own
            ([L], [], [L, own], [own], False),   # the reference's own declaration rests on sorry: nothing can be told apart
            ([L], [], [own], [own], False),
        ]
        for ps, po, rs, ro, ok in table:
            ax = lambda s: ["sorryAx"] if s else STD   # no source: its axioms read no sorryAx
            got, why, f = FS.decide(fr(ps, po, axioms=ax(ps)), fr(rs, ro, axioms=ax(rs)))
            self.assertEqual(got, ok, (ps, po, rs, ro, why))
            self.assertEqual((f["finer_sources"], f["finer_own"]), (sorted(ps), sorted(po)))
            self.assertEqual((f["finer_reference_sources"], f["finer_reference_own"]), (sorted(rs), sorted(ro)))
            self.assertEqual((f["finer_reading"], f["finer_reference_reading"]), ("read", "read"))
        self.assertIn("its own text rests on sorry (OWN sources ['X.main'])", FS.decide(fr([own], [own]), fr([L]))[1])
        self.assertIn("the reference proof's own text rests on sorry", FS.decide(fr([L]), fr([own], [own]))[1])
        # a library lemma named D.aux is a source like any other when the program does not mark it OWN (program v2: by its range)
        self.assertTrue(FS.decide(fr([own + ".aux"]), fr([own + ".aux"]))[0])
        self.assertIn(f"sorry sources ['{M}'] that the reference proof does not use (it uses ['{L}'])", FS.decide(fr([L, M]), fr([L]))[1])
        self.assertEqual(FS.decide(fr([L]), fr([L]))[1], f"sorry sources as the reference proof: ['{L}'] (the reference's: ['{L}'])")

    def test_fail_closed(self):
        L = "Lib.lemmaA"
        for bad in (None, "not a reading", {"error": "finer reading: no end line"}, fr([L], timed_out=True), fr([L], switch=True),
                    fr([L], sorry_warning=True), fr([L], decl_errors=["5:1: unknown identifier"]), fr([L], markers=[]),
                    {k: v for k, v in fr([L]).items() if k != "markers"}, fr([L], complete=False), fr([L], missing=["X.aux"]),
                    fr([], axioms=["sorryAx"]),    # its axioms read sorryAx but no source: the program missed one
                    dict(fr([L]), markers=[marker(sources=[L], decl_local=False)]),   # the printed name is a constant of another file
                    dict(fr([L]), hook="its text registers the attribute 'command_elab', ...")):   # not compiled: with_hooks
            ok, why, f = FS.decide(bad, fr([L]))
            self.assertFalse(ok, bad)
            self.assertIn("its finer sorry reading is not available", why)
            self.assertIsNone(f["finer_sources"])
            ok, why, f = FS.decide(fr([L]), bad)
            self.assertFalse(ok, bad)
            self.assertIn("the reference proof's finer sorry reading is not available", why)
            self.assertIsNone(f["finer_reference_sources"])
        self.assertEqual(FS.sources_of(None, "proof"), (None, "not read within the time budget"))
        self.assertEqual(FS.sources_of(fr([L], switch=True), "proof")[1], "its text names a way to hide Lean's sorry message")
        self.assertIn("did not finish (fuel)", FS.sources_of(fr([L], complete=False), "proof")[1])
        self.assertIn("a constant of another file", FS.sources_of(dict(fr([L]), markers=[marker(decl_local=False)]), "proof")[1])
        self.assertIn("registers the attribute", FS.sources_of(dict(fr([L]), hook="its text registers the attribute 'x'"), "proof")[1])

    def test_the_finer_compile_must_read_the_axiom_readings_axioms(self):
        L = "Lib.lemmaA"
        self.assertTrue(FS.decide(fr([L]), fr([L]), ["sorryAx"], ["sorryAx"])[0])
        ok, why, _ = FS.decide(fr([L], axioms=STD + ["sorryAx"]), fr([L]), ["sorryAx"], ["sorryAx"])
        self.assertFalse(ok)
        self.assertIn("its finer compile reads the axioms", why)
        self.assertFalse(FS.decide(fr([L]), fr([L]), ["sorryAx"], STD + ["sorryAx"])[0])
        self.assertTrue(FS.decide(fr([L], axioms=STD + ["sorryAx"]), fr([L]), STD + ["sorryAx"], None)[0])   # None: not checked

    def test_two_printed_names(self):
        """The proof side is the union over its markers (each printed name's constant counts against it); the reference side the
        intersection (a name that resolves to another constant never widens what is allowed); OWN the union on both sides."""
        L, M = "Lib.lemmaA", "Lib.lemmaB"
        two = lambda a, b, oa=(), ob=(): dict(fr(), markers=[marker("main", "main", a, oa), marker("X.main", "X.main", b, ob)], end=end(2))
        self.assertEqual(FS.sources_of(two([L], [M]), "proof")[0]["sources"], frozenset({L, M}))
        self.assertEqual(FS.sources_of(two([L], [L, M]), "reference")[0]["sources"], frozenset({L}))
        self.assertFalse(FS.decide(two([L], [M]), fr([L]))[0])              # one name's constant uses M
        self.assertTrue(FS.decide(two([L], [L]), two([L], [L, M]))[0])
        self.assertFalse(FS.decide(fr([M]), two([L], [L, M]))[0])            # M: only one of the reference's names uses it
        self.assertFalse(FS.decide(fr([L]), two([L], ["X.main"], ob=["X.main"]))[0])   # OWN on either name of the reference
        self.assertFalse(FS.decide(two([L], ["main"], ob=["main"]), fr([L]))[0])
        # the reference's OWN is the union over its names, also where its sources' intersection would allow the proof (review
        # 2026-11-24, code finding 4: with the intersection the proof below passed)
        ok, why, f = FS.decide(fr([L]), two([L], [L, "X.main"], ob=["X.main"]))
        self.assertFalse(ok)
        self.assertEqual((f["finer_reference_sources"], f["finer_reference_own"]), ([L], ["X.main"]))
        self.assertIn("the reference proof's own text rests on sorry", why)
        self.assertEqual(FS.sources_of(two([L], [L, "X.main"], oa=(), ob=["X.main"]), "proof")[0]["own"], frozenset({"X.main"}))

    def test_wanting(self):
        for why in FS.EVIDENCE + ("read", None):
            self.assertFalse(FS.wanting(why), why)
        for why in ("not read within the time budget", "finer reading: no end line", "its compile timed out", "no marker"):
            self.assertTrue(FS.wanting(why), why)


# ------------------------------------------------------------------------------------------------------------------ the hooks
# review 2026-11-24 (soundness finding 1): the text below passed the Arena's forbidden list and the option guard, and its handler
# logged the program's lines (nonce included) for a proof resting on another sorry'd lemma; the finer check then read OK
FAKE_EVAL = """open Lean Elab Command in
@[command_elab Lean.Parser.Command.eval] private def fakeEval : CommandElab := fun stx => do
  let some lit := stx.find? (fun s => (s.isStrLit?.map (·.startsWith "LRA-FINER ")).getD false) | throwUnsupportedSyntax
  logInfo (lit.isStrLit?.getD "")

theorem mainT : (1 : Nat) = 1 ∧ True := ⟨libSorry2, trivial⟩
"""
FAKE_PRINT = """open Lean Elab Command in
@[command_elab Lean.Parser.Command.printAxioms] private def fakePrint : CommandElab := fun _ => do
  logInfo "'LRAFix.mainT' depends on axioms: [propext]"

theorem mainT : (1 : Nat) = 1 ∧ True := ⟨libSorry2, trivial⟩
"""
T = "theorem mainT : (1 : Nat) = 1 ∧ True := "


class Hooks(unittest.TestCase):
    def test_the_reviews_attacks(self):
        from harness.option_guard import check_forbidden
        for text in (FAKE_EVAL, FAKE_PRINT):
            self.assertIsNone(check_forbidden(text))   # what the post stage's gate and the candidates' filter read: nothing
            self.assertIn("'command_elab'", FS.hooks(text))
            self.assertIn("'command_elab'", FS.finer_hooks(text))

    def test_texts_with_a_hook(self):
        for text in (
                "open Lean in\nattribute [command_elab Lean.Parser.Command.eval] f\n" + T + "rfl",   # past `^attribute`
                "@[simp, command_elab Lean.Parser.Command.eval] private def f : Unit := ()\n" + T + "rfl",
                "@[aesop safe (rule_sets := [X]), macro Lean.Parser.Command.eval] def f := 1\n" + T + "rfl",   # nested brackets
                '@[foo "]", term_elab X] def f := 1\n' + T + "rfl",                                        # a `]` in a string
                "@[«foo]», tactic X] def f := 1\n" + T + "rfl", "@[«tactic» Lean.Parser.Tactic.x] def f := 1", "@[«init»] def f := 1",
                "@[ local  command_elab X] def f := 1", "@[scoped macro X] def f := 1", "@[-command_elab] def f := 1",
                "@[inline, implemented_by g] def f := 1", "@[csimp] theorem t : @f = @g := rfl", '@[extern "c"] def f := 1',
                "@[builtin_term_elab x] def f := 1", "@[my_parser] def f := 1", "@[init] def f := 1", "@[export lean_f] def f := 1",
                "@[app_unexpander f] def u := 1", "@[delab app.f] def d := 1", "@[command_code_action x] def f := 1",
                "macro_rules | `(#print axioms $x) => `(#check 1)", 'syntax "foo" : command', "elab_rules : command | _ => pure ()",
                'notation "x" => 1', 'infixl:65 " ++ " => f', 'prefix:max "√" => f', 'postfix:max "!" => f', 'infix " ~ " => f',
                'infixr:(max+1) (priority := high) " ^^ " => f', "#eval 1", "# eval 1", "run_cmd pure ()", "run_meta pure ()",
                "theorem t : True := by_elab pure ()", "initialize pure ()", "declare_syntax_cat foo",
                "simproc s (f _) := fun _ => pure .continue", "register_simp_attr my_simp", "eval% 1"):
            self.assertIsNotNone(FS.hooks(text), text)
            self.assertIsNotNone(FS.finer_hooks(text), text)

    def test_texts_that_change_only_the_programs_elaboration(self):
        """Read by finer_hooks (every finer reading), not by hooks (every reading): `#print axioms` is Lean's compiled code, an
        instance cannot change it; the finer program is elaborated in the file and can be changed."""
        for text in ("instance (priority := high) : ToString Lean.Name := ⟨fun _ => \"x\"⟩\n" + T + "⟨libSorry, trivial⟩",
                     "private instance : ToString Lean.Name := ⟨fun _ => \"x\"⟩", "@[instance] private def i : Inhabited Nat := ⟨1⟩",
                     "@[simp, instance 1000] def i : Inhabited Nat := ⟨1⟩", "attribute [local instance] Classical.propDecidable",
                     "attribute [-instance] instBEqName", "deriving instance Repr for Foo", "structure S where x : Nat\n  deriving Repr",
                     "unif_hint (n : Nat) where n =?= 1 ⊢ n + 0 =?= 1",
                     "def Ns._root_.Lean.Name := 1", "def Ns.«_root_».Lean.logInfo := 1", "@[default_instance] def i := 1"):
            self.assertIsNone(FS.hooks(text), text)
            self.assertIsNotNone(FS.finer_hooks(text), text)

    def test_ordinary_proofs_have_no_hook(self):
        for text in (T + "⟨libSorry, trivial⟩", T + "by\n  constructor\n  · simp [foo] at h ⊢\n  · exact trivial",
                     "@[simp] theorem t : 1 = 1 := rfl", "@[simp, elab_as_elim, induction_eliminator] theorem t : 1 = 1 := rfl",
                     "@[local simp] theorem t : 1 = 1 := rfl", "@[simp ←, norm_cast, aesop safe apply, gcongr, macro_inline] theorem t := 1",
                     "attribute [local simp] foo bar in\n" + T + "by simp",
                     "theorem t : xs.foldl (init := 0) f = 0 := by\n  induction xs with\n  | nil => rfl\n  | cons x xs ih => simp [ih]",
                     T + "by\n  intro prefix\n  exact List.prefix_append _ _", T + "by\n  haveI := inferInstance\n  letI : Fact p := ⟨h⟩\n  infer_instance",
                     T + "by exact _root_.trans h1 h2", T + "by\n  -- @[command_elab x] #eval macro instance\n  /- syntax notation -/ rfl",
                     T + "by\n  simp only [Nat.add_def, Set.mem_def]\n  omega", T + "by decide", T + "by\n  exact?",
                     T + "by\n  aesop\n    (add unsafe (by rw [add_comm]))\n    (add unsafe forward [Nat.add_lt_add_right])"):
            self.assertIsNone(FS.hooks(text), text)
            self.assertIsNone(FS.finer_hooks(text), text)

    def test_the_published_proofs_and_references_have_no_hook(self):
        """The 60 final rows' reference proofs: none has a hook, so the hook check changes no reference reading of the final rows."""
        hits = [(r["name"], FS.finer_hooks(r["src"])) for r in rows() if FS.finer_hooks(r.get("src") or "")]
        self.assertEqual(hits, [])


# --------------------------------------------------------------------------------------------------------------- the switch
class Switch(unittest.TestCase):
    def test_values(self):
        self.assertEqual(AG.finer_switch("off"), (False, None))
        self.assertEqual(AG.finer_switch(" off\n"), (False, None))
        for v in ("on", "", " on "):
            self.assertEqual(AG.finer_switch(v), (True, None), v)
        for v in ("OFF", "0", "no", "false"):
            on, warn = AG.finer_switch(v)
            self.assertTrue(on, v)
            self.assertIn("neither on nor off", warn)
        with mock.patch.dict(os.environ, {}, clear=False):
            os.environ.pop(AG.FINER_ENV, None)
            self.assertEqual(AG.finer_switch(), (True, None))
            os.environ[AG.FINER_ENV] = "off"
            self.assertEqual(AG.finer_switch(), (False, None))

    def test_the_rule_with_the_check_off_is_the_published_rule(self):
        """pin_state / classify without `finer` (None: off) are the published functions on every reading pair below."""
        pub = published()
        readings = [None, GOOD, SORRY, {"axioms": []}, {"axioms": STD + ["sorryAx"]}, dict(SORRY, sorry_warning=True), dict(SORRY, switch=True),
                    dict(SORRY, timed_out=True), dict(SORRY, decl_errors=["1:1: e"]), {"axioms": None}, {"axioms": None, "module": True},
                    {"error": "x"}, {"axioms": STD + ["myAxiom"]}, {"axioms": ["sorryAx", "myAxiom"]},
                    {"axioms": STD + ["sorryAx"], "lists": [STD, STD + ["sorryAx"]], "prints_differ": True}]
        for a in readings:
            for b in readings + [None]:
                self.assertEqual(AG.pin_state(a, b), pub.pin_state(a, b), (a, b))
                self.assertEqual(AG.classify({"p": a, "q": GOOD}, {"p": b}), pub.classify({"p": a, "q": GOOD}, {"p": b}), (a, b))
                self.assertEqual(AG.allowance_pins({"p": a}, {"p": b}), pub.allowance_pins({"p": a}, {"p": b}))

    def test_needs_finer(self):
        self.assertTrue(AG.needs_finer(SORRY, SORRY))
        self.assertTrue(AG.needs_finer({"axioms": STD + ["sorryAx"]}, {"axioms": ["sorryAx", "myAxiom"]}))
        for r, ref in ((SORRY, GOOD), (SORRY, None), (GOOD, SORRY), ({"axioms": STD + ["myAxiom"]}, {"axioms": ["myAxiom"]}),
                       (dict(SORRY, sorry_warning=True), SORRY), (dict(SORRY, timed_out=True), SORRY), (None, SORRY)):
            self.assertFalse(AG.needs_finer(r, ref), (r, ref))

    def test_pin_state_with_the_check_on(self):
        L = "Lib.lemmaA"
        self.assertEqual(AG.pin_state(SORRY, SORRY, (fr([L]), fr([L])))[0], AG.OK)
        st, why = AG.pin_state(SORRY, SORRY, (fr(["X.main"], ["X.main"]), fr([L])))
        self.assertEqual(st, AG.BAD)
        self.assertIn("but the finer sorry check fails: its own text rests on sorry (OWN sources", why)
        self.assertEqual(AG.pin_state(SORRY, SORRY, (None, None))[0], AG.BAD)
        self.assertEqual(AG.pin_state(SORRY, GOOD, (fr([L]), fr([L])))[0], AG.BAD)            # the allowance first: unchanged
        self.assertEqual(AG.pin_state(GOOD, SORRY, (None, None)), (AG.OK, "standard axioms"))   # no allowance needed: no finer
        my = {"axioms": STD + ["myAxiom"]}
        self.assertEqual(AG.pin_state(my, my, (None, None))[0], AG.OK)                         # an axiom other than sorryAx: unchanged
        v, why, _ = AG.classify({"a": SORRY, "b": GOOD}, {"a": SORRY}, {"a": (fr([L]), fr([L]))})
        self.assertEqual(v, AG.PASS)
        self.assertIn(f"axioms as the reference proof on a: ['sorryAx'] (sorry sources as the reference proof: ['{L}']", why)
        self.assertEqual(AG.classify({"a": SORRY}, {"a": SORRY}, {})[0], AG.FAIL)                # a pin left out: neither available


# ----------------------------------------------------------------------------------------------------------------- the guard
class Stubs:
    """Stand-in readers keyed by the proof's mark: `axioms` {tag: reading | callable(row, pin)}, `finers` the same for the finer
    readings ("reference" = the row's reference proof). One call log for both, in order."""

    def __init__(self, axioms: dict, finers: dict | None = None, ref=None, ref_finer=None, delay=0.0, finer_delay=0.0):
        self.axioms, self.finers, self.ref, self.ref_finer = axioms, finers or {}, ref, ref_finer
        self.delay, self.finer_delay = delay, finer_delay
        self.calls, self.lock = [], threading.Lock()

    def _get(self, table, default, row, text, pin):
        t = tag_of(text)
        r = table.get(t, default)
        return r(row, pin) if callable(r) else r

    def reader(self, row, text, pin, timeout):
        with self.lock:
            self.calls.append(("axioms", row["name"], tag_of(text), pin))
        if self.delay:
            time.sleep(self.delay)
        return self._get(self.axioms, self.ref if tag_of(text) == "reference" and self.ref is not None else GOOD, row, text, pin)

    def finer(self, row, text, pin, timeout):
        with self.lock:
            self.calls.append(("finer", row["name"], tag_of(text), pin))
        if self.finer_delay:
            time.sleep(self.finer_delay)
        t = tag_of(text)
        r = self.ref_finer if t == "reference" else self.finers.get(t, {"error": "finer reading: no stand-in"})
        return r(row, pin) if callable(r) else r

    def of(self, kind):
        return [c for c in self.calls if c[0] == kind]


class Guard(unittest.TestCase):
    """The guard with the check on: PhysLib rows (two pins each); the reference proofs read sorryAx unless said otherwise."""
    L = "PhysLib.libLemma"

    def setUp(self):
        self.rs = rows()[10:14]
        self.d = tmpdir()
        write_jsonl(self.d / "rows.jsonl", self.rs)
        self.p = self.d / "proofs.jsonl"
        write_jsonl(self.p, [rec(r, f"cur{k}", 70.0 + k) for k, r in enumerate(self.rs)])
        write_jsonl(self.d / "proofs.picks.jsonl", [rec(r, f"picks{k}", 60.0 + k, "agent") for k, r in enumerate(self.rs)])
        write_jsonl(self.d / "proofs.export.jsonl", [rec(r, f"export{k}", 50.0 + k, "agent") for k, r in enumerate(self.rs)])
        self.raw = self.p.read_text().splitlines()
        self.pins = AG.versions_of(self.rs[0])
        AG.STOP.clear()

    def tearDown(self):
        AG.STOP.clear()

    def guard(self, st: Stubs, finer=True, **kw):
        lines = []
        kw.setdefault("budget_s", 30)
        rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=st.reader, finer_reader=st.finer, finer=finer, log=lines.append, **kw)
        return rep, lines

    def line(self, k):
        return json.loads(self.p.read_text().splitlines()[k])

    def test_rows_without_sorry_on_the_reference_get_no_finer_reading(self):
        for ref in (GOOD, {"axioms": []}):
            st = Stubs({"cur0": SORRY, "cur1": {"axioms": STD + ["myAxiom"]}}, ref=ref)
            rep, log = self.guard(st)
            self.assertEqual(st.of("finer"), [])
            self.assertEqual((rep["finer"], rep["finer_readings"], rep["finer_pins_ok"], rep["finer_pins_bad"]), ("on", 0, 0, 0))
            self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"))   # sorryAx against standard axioms: BAD, as before
            self.assertTrue(all(x.get("finer") is None for d in rep["per_row"] for x in d["pins"].values()))
            self.assertNotIn("finer sorry check of", "\n".join(log))

    def test_a_proof_with_the_references_sources_is_kept(self):
        """Held-out row 25's case: the reference proof uses a library lemma proved by sorry; the proof uses the same one."""
        st = Stubs({"cur0": SORRY}, {"cur0": fr([self.L])}, ref=SORRY, ref_finer=fr([self.L]))
        rep, log = self.guard(st)
        self.assertEqual((rep["rc"], rep["replaced"], rep["written"]), (0, [], False))
        self.assertEqual(self.p.read_text().splitlines(), self.raw)
        self.assertEqual(sorted((c[2], c[3]) for c in st.of("finer")), sorted((t, v) for t in ("cur0", "reference") for v in self.pins))
        self.assertEqual((rep["finer_readings"], rep["finer_readings_done"], rep["finer_readings_complete"]), (4, 4, 4))
        self.assertEqual((rep["finer_pins_ok"], rep["finer_pins_bad"]), (2, 0))
        self.assertEqual(rep["passed_by_allowance"], [self.rs[0]["name"]])
        f = rep["per_row"][0]["pins"][self.pins[0]]["finer"]
        self.assertEqual((f["decision"], f["finer_sources"], f["finer_reference_sources"], f["finer_own"]), (AG.OK, [self.L], [self.L], []))
        text = "\n".join(log)
        self.assertIn(f"finer sorry check of its proof on {self.pins[0]}: OK", text)
        self.assertIn(f"its sources ['{self.L}'] (OWN []), the reference proof's ['{self.L}'] (OWN [])", text)
        self.assertIn(f"sorry sources ['{self.L}'], the reference's ['{self.L}']", text)      # the pass line names both sides
        self.assertIn(f"finer sorry check on (LRA_AXIOM_GUARD_FINER; program v{FS.VERSION})", log[0])
        self.assertIn("finer sorry check: 2 pin(s) of the proofs read decided by it (2 OK, 0 BAD), 4 of 4 finer reading(s) complete", log[-1])

    def test_a_proof_whose_own_value_is_sorry_is_set_back(self):
        """Held-out row 42's case, on a row whose reference reads sorryAx: the allowance alone lets it through; the finer check not."""
        own = fr(["PhysLib.main"], ["PhysLib.main"])
        st = Stubs({"cur0": SORRY}, {"cur0": own}, ref=SORRY, ref_finer=fr([self.L]))
        rep, log = self.guard(st)
        self.assertEqual(rep["replaced"], [self.rs[0]["name"]])
        new = self.line(0)
        self.assertEqual(new["proof"], proof(self.rs[0], "picks0"))
        self.assertIn("the finer sorry check fails: its own text rests on sorry (OWN sources ['PhysLib.main'])", new["axiom_guard"])
        self.assertEqual((rep["finer_pins_ok"], rep["finer_pins_bad"], rep["set_back_for_want_of_finer_reading"]), (0, 2, []))
        self.assertIn(f"finer sorry check of its proof on {self.pins[0]}: BAD", "\n".join(log))
        # the same with the check off: the published guard keeps it, and no finer reading is taken
        write_jsonl(self.p, [json.loads(l) for l in self.raw])
        st2 = Stubs({"cur0": SORRY}, {"cur0": own}, ref=SORRY, ref_finer=fr([self.L]))
        rep2, log2 = self.guard(st2, finer=False)
        self.assertEqual((rep2["replaced"], rep2["finer"], st2.of("finer")), ([], "off", []))
        self.assertNotIn("finer_readings", rep2)
        self.assertNotIn("finer sorry check", log2[0])

    def test_a_proof_with_another_sorry_source_is_set_back(self):
        st = Stubs({"cur0": SORRY}, {"cur0": fr([self.L, "PhysLib.other"])}, ref=SORRY, ref_finer=fr([self.L]))
        rep, _ = self.guard(st)
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"))
        self.assertIn("sorry sources ['PhysLib.other'] that the reference proof does not use", self.line(0)["axiom_guard"])

    def test_a_reference_whose_own_declaration_rests_on_sorry_allows_no_sorry(self):
        st = Stubs({"cur0": SORRY}, {"cur0": fr([self.L])}, ref=SORRY, ref_finer=fr(["PhysLib.ref"], ["PhysLib.ref"]))
        rep, _ = self.guard(st)
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"))
        self.assertEqual(rep["set_back_for_want_of_finer_reading"], [])   # evidence, not want
        self.assertIn("the reference proof's own text rests on sorry", self.line(0)["axiom_guard"])

    def test_no_finer_reading_fails_closed_and_is_named(self):
        for finers, ref_finer in (({"cur0": {"error": "finer reading: no end line: the program did not run"}}, fr([self.L])),
                                  ({"cur0": fr([self.L])}, {"error": "finer reading: the compile timed out"}),
                                  ({}, fr([self.L]))):
            write_jsonl(self.p, [json.loads(l) for l in self.raw])
            st = Stubs({"cur0": SORRY}, finers, ref=SORRY, ref_finer=ref_finer)
            rep, log = self.guard(st)
            self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"), finers)
            self.assertEqual(rep["set_back_for_want_of_finer_reading"], [self.rs[0]["name"]])
            self.assertIn("only because a finer sorry reading was not available", log[-1])
            self.assertIn("finer sorry reading is not available", self.line(0)["axiom_guard"])

    def test_a_finer_reader_that_raises(self):
        def boom(row, pin):
            raise RuntimeError("no env")
        st = Stubs({"cur0": SORRY}, {"cur0": boom}, ref=SORRY, ref_finer=fr([self.L]))
        rep, _ = self.guard(st)
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"))
        self.assertIn("RuntimeError: no env", rep["per_row"][0]["pins"][self.pins[0]]["finer"]["finer_reading"])

    def test_a_candidate_that_passes_through_the_allowance_needs_the_finer_check_too(self):
        st = Stubs({"cur0": SORRY, "picks0": SORRY, "export0": SORRY},
                   {"cur0": fr(["PhysLib.main"], ["PhysLib.main"]), "picks0": fr(["PhysLib.other"]), "export0": fr([self.L])},
                   ref=SORRY, ref_finer=fr([self.L]))
        rep, log = self.guard(st)
        new = self.line(0)
        self.assertEqual(new["proof"], proof(self.rs[0], "export0"))
        d = rep["per_row"][0]
        self.assertEqual([c["role"] for c in d["candidates"]], ["proofs.picks.jsonl", "proofs.export.jsonl"])
        self.assertEqual(d["candidates"][0]["finer"][self.pins[0]]["decision"], AG.BAD)
        self.assertEqual(d["candidates"][1]["finer"][self.pins[0]]["decision"], AG.OK)
        self.assertEqual(d["chosen_allowance"], self.pins)
        self.assertIn("finer sorry check of its replacement (the agent stage's export)", "\n".join(log))

    def test_the_reference_proof_as_the_floor(self):
        """No earlier proof passes; the reference proof is the last candidate and passes on its own finer reading (no OWN source)."""
        bad = fr(["PhysLib.main"], ["PhysLib.main"])
        st = Stubs({"cur0": SORRY, "picks0": SORRY, "export0": SORRY}, {"cur0": bad, "picks0": bad, "export0": bad},
                   ref=SORRY, ref_finer=fr([self.L]))
        rep, _ = self.guard(st)
        self.assertEqual(self.line(0)["proof"], self.rs[0]["src"].rstrip() + "\n")
        self.assertEqual(rep["per_row"][0]["chosen_verdict"], AG.PASS)
        self.assertEqual(rep["reference_not_passing"], [])

    def test_finer_readings_come_before_the_candidates(self):
        """One thread: once the reference's reading on the newest pin is in, both finer readings there (the reference's first) are
        read ahead of the candidates, which were queued when the pin read BAD while waiting."""
        st = Stubs({"cur0": SORRY}, {"cur0": fr([self.L])}, ref=SORRY, ref_finer=fr([self.L]), delay=0.05, finer_delay=0.05)
        rep, _ = self.guard(st, jobs=1, budget_s=60)
        calls = [(c[0], c[2], c[3]) for c in st.calls]
        i_ref = calls.index(("axioms", "reference", self.pins[0]))
        i_fr, i_fp = calls.index(("finer", "reference", self.pins[0])), calls.index(("finer", "cur0", self.pins[0]))
        i_cand = min(i for i, c in enumerate(calls) if c[1] in ("picks0", "export0"))
        self.assertLess(i_ref, i_fr)
        self.assertLess(i_fr, i_fp)
        self.assertLess(i_fp, i_cand, calls)
        self.assertEqual(len(calls), len(set(calls)))   # nothing is read twice
        self.assertEqual((rep["rc"], rep["replaced"]), (0, []))

    def test_a_finer_reading_not_read_in_time(self):
        slow = lambda row, pin: time.sleep(4) or fr([self.L])
        st = Stubs({"cur0": SORRY}, {"cur0": slow}, ref=SORRY, ref_finer=fr([self.L]))
        t0 = time.monotonic()
        with mock.patch.object(AG, "GRACE_S", 0.5), mock.patch.object(AG, "MIN_START_S", 0.1):
            rep, log = self.guard(st, budget_s=1.5, jobs=8)
        self.assertLess(time.monotonic() - t0, 4)
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"))
        self.assertEqual(rep["set_back_for_want_of_finer_reading"], [self.rs[0]["name"]])
        self.assertLess(rep["finer_readings_done"], rep["finer_readings"])
        self.assertIn("not read within the time budget", rep["per_row"][0]["pins"][self.pins[0]]["finer"]["finer_reading"])

    def test_a_stop_signal_during_the_finer_readings(self):
        def stop(row, pin):
            AG.STOP.set()
            return fr([self.L])
        st = Stubs({"cur0": SORRY}, {"cur0": stop}, ref=SORRY, ref_finer=fr([self.L]))
        rep, _ = self.guard(st, jobs=1, budget_s=60)
        i = next(i for i, c in enumerate(st.calls) if c[0] == "finer" and c[2] == "cur0")
        self.assertEqual(st.calls[i + 1:], [])           # nothing starts after the stop
        self.assertIn("not started: the guard was stopped", json.dumps(rep))
        # the rows are decided on what was read: row 0's proof, its finer readings on the older pin not started, is not kept (fail
        # closed); it is set back to an earlier proof read before the stop, named as set back for want of a finer reading
        self.assertNotEqual(self.line(0)["proof"], proof(self.rs[0], "cur0"))
        self.assertEqual(rep["set_back_for_want_of_finer_reading"], [self.rs[0]["name"]])

    def test_the_switch_from_the_environment(self):
        st = Stubs({"cur0": SORRY}, {"cur0": fr(["PhysLib.main"], ["PhysLib.main"])}, ref=SORRY, ref_finer=fr([self.L]))
        lines = []
        with mock.patch.dict(os.environ, {AG.FINER_ENV: "off"}):
            rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=st.reader, finer_reader=st.finer, log=lines.append, budget_s=30)
        self.assertEqual((rep["finer"], rep["replaced"], st.of("finer")), ("off", [], []))
        lines = []
        with mock.patch.dict(os.environ, {AG.FINER_ENV: "maybe"}):
            rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=st.reader, finer_reader=st.finer, log=lines.append, budget_s=30)
        self.assertEqual((rep["finer"], rep["replaced"]), ("on", [self.rs[0]["name"]]))
        self.assertIn("LRA_AXIOM_GUARD_FINER='maybe' is neither on nor off: the finer sorry check stays on", lines[0])

    def test_the_cli_passes_the_finer_reader(self):
        st = Stubs({"cur0": SORRY}, {"cur0": fr(["PhysLib.main"], ["PhysLib.main"])}, ref=SORRY, ref_finer=fr([self.L]))
        rp = self.d / "report.json"
        with mock.patch.dict(os.environ, {AG.FINER_ENV: "on"}), mock.patch("builtins.print"):
            rc = AG.main([str(self.p), "--rows", str(self.d / "rows.jsonl"), "--budget", "30", "--report", str(rp)],
                         reader=st.reader, finer_reader=st.finer)
        rep = json.loads(rp.read_text())
        self.assertEqual((rc, rep["finer"], rep["replaced"]), (0, "on", [self.rs[0]["name"]]))
        self.assertTrue(st.of("finer"))

    def hooked(self, k: int, tag: str, hook: str) -> None:
        """Row k's current proof becomes `hook` + its proof text (mark `tag`)."""
        recs = [json.loads(l) for l in self.raw]
        recs[k]["proof"] = hook + proof(self.rs[k], tag)
        write_jsonl(self.p, recs)

    def test_a_text_with_a_hook_reads_bad_without_a_compile(self):
        """Review 2026-11-24 (soundness finding 1): a text that registers a command elaborator can fake `#print axioms` (and the
        program). With the check on it is not compiled and reads BAD on every pin, also on a row whose reference reads no sorryAx;
        with the check off the guard is the published one (the stand-in reads it GOOD, as a faked print would)."""
        self.hooked(1, "cur1", FAKE_PRINT.split("\n\n")[0] + "\n\n")
        st = Stubs({}, ref=GOOD)
        rep, log = self.guard(st)
        self.assertEqual([c for c in st.of("axioms") if c[2] == "cur1"], [])   # never compiled
        self.assertEqual(self.line(1)["proof"], proof(self.rs[1], "picks1"))
        pins = rep["per_row"][1]["pins"]
        self.assertTrue(all(x["state"] == AG.BAD and "'command_elab'" in x["hook"] for x in pins.values()))
        self.assertIn("('command_elab'), which can change what the reading prints", self.line(1)["axiom_guard"])
        self.assertEqual((rep["set_back_for_want_of_finer_reading"], rep["set_back_for_want_of_reference"]), ([], []))
        self.hooked(1, "cur1", FAKE_PRINT.split("\n\n")[0] + "\n\n")
        st2 = Stubs({}, ref=GOOD)
        rep2, _ = self.guard(st2, finer=False)
        self.assertEqual((rep2["replaced"], rep2["finer"]), ([], "off"))
        self.assertTrue([c for c in st2.of("axioms") if c[2] == "cur1"])
        self.assertNotIn("hook", rep2["per_row"][1]["pins"][self.pins[0]])

    def test_a_reference_with_a_hook_allows_nothing(self):
        rows_ = [dict(r) for r in self.rs]
        rows_[0]["src"] = "@[command_elab Lean.Parser.Command.printAxioms] private def f : Unit := ()\n" + rows_[0]["src"]
        write_jsonl(self.d / "rows.jsonl", rows_)
        st = Stubs({"cur0": SORRY, "picks0": SORRY, "export0": SORRY}, {"cur0": fr([self.L])}, ref=SORRY, ref_finer=fr([self.L]))
        rep, _ = self.guard(st)
        self.assertEqual([c for c in st.calls if c[2] == "reference"], [])
        self.assertIn("('command_elab'), which can change what the reading prints", rep["per_row"][0]["pins"][self.pins[0]]["why"])
        self.assertEqual(rep["reference_not_passing"], [self.rs[0]["name"]])   # no proof of the row passes: exit 3
        self.assertEqual(rep["rc"], 3)

    def test_an_instance_in_the_text_needs_no_hook_on_its_axiom_reading_but_has_no_finer_reading(self):
        """An instance cannot change `#print axioms` (Lean's compiled code), so the axiom reading is taken; it can change the finer
        program's elaboration, so the finer reading is not (finer_hooks) and the pin fails closed."""
        self.hooked(0, "cur0", "instance (priority := high) : ToString Lean.Name := ⟨fun _ => \"PhysLib.libLemma\"⟩\n\n")
        st = Stubs({"cur0": SORRY}, {"cur0": fr([self.L])}, ref=SORRY, ref_finer=fr([self.L]))
        rep, _ = self.guard(st)
        self.assertTrue([c for c in st.of("axioms") if c[2] == "cur0"])
        self.assertEqual([c for c in st.of("finer") if c[2] == "cur0"], [])
        f = rep["per_row"][0]["pins"][self.pins[0]]["finer"]
        self.assertEqual(f["decision"], AG.BAD)
        self.assertIn("'instance'", f["finer_reading"])
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"))

    def test_a_stand_in_reader_without_a_finer_one_starts_no_compile(self):
        """Review 2026-11-24 (code finding 3): a guard given a stand-in axiom reader and no finer reader reads no finer reading (the
        check fails closed); it never starts the real finer_reading."""
        st = Stubs({"cur0": SORRY}, ref=SORRY)
        lines = []
        with mock.patch.object(AG, "finer_reading", side_effect=AssertionError("a real compile")):
            rep = AG.guard_file(self.p, self.d / "rows.jsonl", reader=st.reader, finer=True, log=lines.append, budget_s=30)
        f = rep["per_row"][0]["pins"][self.pins[0]]["finer"]
        self.assertIn("no finer reader", f["finer_reading"])
        self.assertEqual(self.line(0)["proof"], proof(self.rs[0], "picks0"))


# ------------------------------------------------------------------------------------------------------- off = the published
def published():
    """The guard as published (tag open-camready-20261125), loaded from its copy under the name axiom_guard_published."""
    src = PUBLISHED.read_bytes()
    assert hashlib.sha256(src).hexdigest() == PUBLISHED_SHA256, "tests/data/axiom_guard_published.py.txt is not the published guard"
    if "axiom_guard_published" in sys.modules:
        return sys.modules["axiom_guard_published"]
    mod = types.ModuleType("axiom_guard_published")
    mod.__file__ = str(ROOT / "harness" / "axiom_guard.py")   # its ROOT: the package
    sys.modules[mod.__name__] = mod
    exec(compile(src, str(PUBLISHED), "exec"), mod.__dict__)
    return mod


KINDS = [GOOD, {"axioms": []}, SORRY, {"axioms": STD + ["sorryAx"]}, {"axioms": ["propext", "sorryAx"]}, dict(SORRY, sorry_warning=True),
         dict(GOOD, sorry_warning=True), dict(SORRY, switch=True), dict(SORRY, timed_out=True), dict(GOOD, timed_out=True),
         dict(SORRY, decl_errors=["5:2: type mismatch"]), dict(GOOD, decl_errors=["5:2: e"]), {"axioms": None},
         {"axioms": None, "module": True, "decl_errors": []}, {"error": "RuntimeError: no env"}, {"axioms": STD + ["myAxiom"]},
         {"axioms": ["sorryAx", "myAxiom"]}, {"axioms": STD + ["sorryAx"], "lists": [STD, STD + ["sorryAx"]], "prints_differ": True},
         {"axioms": STD + ["sorryAx", "myAxiom"], "lists": [["sorryAx", "propext"], ["sorryAx", "myAxiom"] + STD], "prints_differ": True},
         "raise"]


class TableReader:
    """A reader that answers from a fixed table {(row name, tag, pin): kind}; "raise" raises."""

    def __init__(self, table):
        self.table, self.finer_calls = table, []

    def __call__(self, row, text, pin, timeout):
        r = self.table.get((row["name"], tag_of(text), pin), GOOD)
        if r == "raise":
            raise RuntimeError("no env")
        return json.loads(json.dumps(r))

    def finer(self, row, text, pin, timeout):
        self.finer_calls.append((row["name"], tag_of(text), pin))
        r = self.table.get((row["name"], tag_of(text), pin), GOOD)
        return fr(["Lib.x"], axioms=r.get("axioms") or ["sorryAx"])   # the same compile as the axiom reading: its axioms


class SyncReadings:
    """The pool's interface, read one key at a time in the calling thread, each result handed to on_result before the next reading
    starts: the order and the set of readings no longer depend on thread timing (with threads they do, in the published guard too:
    whether a row's earlier proofs are queued depends on whether the reference's reading is in yet)."""

    def __init__(self, reader, jobs, deadline, timeout_s, clock=time.monotonic):
        import heapq, itertools
        self._hq, self.reader, self.timeout_s = heapq, reader, float(timeout_s)
        self.heap, self.seq, self.results, self.queued, self.prio, self.started = [], itertools.count(), {}, set(), {}, set()

    def submit(self, prio, key, row, proof, pin, fn=None):
        if key in self.queued and (key in self.started or key in self.results or prio >= self.prio[key]):
            return
        self.queued.add(key)
        self.prio[key] = prio
        self._hq.heappush(self.heap, (prio, next(self.seq), key, row, proof, pin, fn))

    def drain(self, on_result, stop_at):
        while self.heap:
            _p, _s, key, row, proof, pin, fn = self._hq.heappop(self.heap)
            if key in self.started or key in self.results:
                continue
            self.started.add(key)
            try:
                res = dict((fn or self.reader)(row, proof, pin, self.timeout_s))
            except Exception as e:
                res = {"error": f"{type(e).__name__}: {str(e)[:160]}"}
            res.setdefault("seconds", 0.0)
            self.results[key] = res
            on_result(key)
        return True

    def close(self):
        return dict(self.results)


def norm_log(lines):
    out = []
    for s in lines:
        s = re.sub(r"\d{4}-\d\d-\d\dT\d\d:\d\d:\d\dZ", "T", s)
        out.append(re.sub(r"done in \d+ s", "done in N s", s))
    return out


def norm_rep(rep):
    return {k: v for k, v in rep.items() if k not in ("at", "seconds", "finer", "file")}


class OffIsThePublishedGuard(unittest.TestCase):
    def test_the_copy_is_the_published_file(self):
        self.assertEqual(hashlib.sha256(PUBLISHED.read_bytes()).hexdigest(), PUBLISHED_SHA256)
        git = "blob %d\0" % PUBLISHED.stat().st_size
        self.assertEqual(hashlib.sha1(git.encode() + PUBLISHED.read_bytes()).hexdigest()[:8], "40a9b7f7")

    def setup_dir(self, rs, rnd, variant) -> Path:
        d = tmpdir()
        write_jsonl(d / "rows.jsonl", rs)
        recs = [rec(r, f"cur{k}", 70.0 + k) for k, r in enumerate(rs)]
        if variant == 1:
            recs[0]["proof"] = ""                      # a record without a proof text
        if variant == 2:
            recs[1]["proof"] = rs[1]["src"]            # the proof is the reference proof
        write_jsonl(d / "proofs.jsonl", recs)
        if variant != 3:
            write_jsonl(d / "proofs.picks.jsonl", [rec(r, f"picks{k}", 60.0 + k, "agent") for k, r in enumerate(rs)])
        exp = [rec(r, f"export{k}", 50.0 + k, "agent") for k, r in enumerate(rs)]
        if variant == 4:
            exp[2] = dict(recs[2])                     # not changed by the post stage: read later
        write_jsonl(d / "proofs.export.jsonl", exp)
        return d

    def run_both(self, rs, table, variant, finer_new, sync=True):
        """The published guard and this one (`finer_new`: the check on or off) on the same files and readings. `sync`: both with the
        one-at-a-time pool (SyncReadings), so the comparison is exact; else with their own thread pools (jobs 4)."""
        pub = published()
        out = []
        for g, kw in ((pub, {}), (AG, {"finer": finer_new})):
            d = self.setup_dir(rs, None, variant)
            tr = TableReader(table)
            lines = []
            if g is AG:
                kw["finer_reader"] = tr.finer
            with (mock.patch.object(g, "Readings", SyncReadings) if sync else contextlib.nullcontext()):
                rep = g.guard_file(d / "proofs.jsonl", d / "rows.jsonl", reader=tr, log=lines.append, budget_s=60, jobs=4, **kw)
            lines = [s.replace(str(d), "D") for s in lines]                        # each run has its own folder
            rep = json.loads(json.dumps(rep).replace(json.dumps(str(d))[1:-1], "D"))
            files = {p.name: p.read_bytes().replace(str(d).encode(), b"D") for p in sorted(d.iterdir())}
            out.append((rep, lines, files, tr))
        return out

    @staticmethod
    def table(rs, rnd, ref_kinds=None) -> dict:
        t = {}
        for k, r in enumerate(rs):
            for v in AG.versions_of(r):
                for tag in (f"cur{k}", f"picks{k}", f"export{k}"):
                    t[(r["name"], tag, v)] = rnd.choice(KINDS) if rnd.random() < 0.6 else rnd.choice([GOOD, SORRY])
                t[(r["name"], "reference", v)] = rnd.choice(ref_kinds or KINDS) if rnd.random() < 0.6 or ref_kinds else rnd.choice([GOOD, SORRY])
        return t

    def test_off_on_random_tables(self):
        """The check off: the same report (but its new "finer": "off"), the same log lines, the same files, on 100 random tables."""
        rs = rows()[10:16]
        rnd = random.Random(20261124)
        for trial in range(100):
            variant = trial % 5
            (rp, lp, fp, _), (rn, ln, fn, tn) = self.run_both(rs, self.table(rs, rnd), variant, False)
            self.assertEqual(rn["finer"], "off")
            self.assertEqual(tn.finer_calls, [])
            self.assertEqual(norm_rep(rp), norm_rep(rn), (trial, variant))
            self.assertEqual(norm_log(lp), norm_log(ln), (trial, variant))
            self.assertEqual(fp, fn, (trial, variant))
            self.assertEqual(rp["rc"], rn["rc"])

    def test_off_with_thread_pools(self):
        """The same with both guards' own thread pools: which readings are taken may differ from run to run (in the published guard
        too), the decisions and the files do not."""
        rs = rows()[10:16]
        rnd = random.Random(11)
        for trial in range(25):
            variant = trial % 5
            (rp, lp, fp, _), (rn, ln, fn, tn) = self.run_both(rs, self.table(rs, rnd), variant, False, sync=False)
            self.assertEqual(tn.finer_calls, [])
            dec = lambda rep: [(d["k"], d["verdict"], d["why"], d.get("chosen"), d.get("chosen_why")) for d in rep["per_row"]]
            self.assertEqual(dec(rp), dec(rn), (trial, variant))
            self.assertEqual((rp["rc"], rp["replaced"], rp["written"]), (rn["rc"], rn["replaced"], rn["written"]))
            self.assertEqual(fp, fn, (trial, variant))

    def test_on_without_sorry_allowances_is_the_published_guard(self):
        """The check on, on tables where the reference proofs read no sorryAx (so no proof passes through the allowance with it): no
        finer reading, the same decisions, logs and files (the start line names the check; the report adds its counts)."""
        rs = rows()[10:16]
        rnd = random.Random(7)
        no_sorry_ref = [k for k in KINDS if k == "raise" or "sorryAx" not in (k.get("axioms") or [])]
        for trial in range(50):
            variant = trial % 5
            if variant == 2:
                continue   # a current proof that is the reference proof reads the reference's kinds: the case of the next test
            (rp, lp, fp, _), (rn, ln, fn, tn) = self.run_both(rs, self.table(rs, rnd, no_sorry_ref), variant, True)
            self.assertEqual(tn.finer_calls, [], trial)
            self.assertEqual((rn["finer"], rn["finer_readings"]), ("on", 0))
            extra = ("finer_readings", "finer_readings_done", "finer_readings_complete", "finer_pins_ok", "finer_pins_bad",
                     "set_back_for_want_of_finer_reading")
            rn_ = {k: v for k, v in norm_rep(rn).items() if k not in extra}
            for d in rn_["per_row"]:
                for p in d["pins"].values():
                    self.assertIsNone(p.pop("finer"))
                    self.assertIsNone(p.pop("hook"))
                for c in d.get("candidates", []):
                    self.assertEqual(c.pop("finer"), {})
            self.assertEqual(norm_rep(rp), rn_, trial)
            pl, nl = norm_log(lp), norm_log(ln)
            self.assertEqual(pl[0] + f"; finer sorry check on (LRA_AXIOM_GUARD_FINER; program v{FS.VERSION})", nl[0])
            self.assertEqual(pl[1:-1], nl[1:-1], trial)
            self.assertEqual(re.sub(r"; finer sorry check: [^;]*", "", nl[-1]), pl[-1])
            self.assertEqual(fp, fn, trial)

    def test_on_where_it_decides_only_the_sorry_allowance_changes(self):
        """The check on, random tables, finer readings that always pass (the reference's sources): the same decisions as published."""
        rs = rows()[10:16]
        rnd = random.Random(5)
        for trial in range(40):
            variant = trial % 5
            (rp, lp, fp, _), (rn, ln, fn, tn) = self.run_both(rs, self.table(rs, rnd), variant, True)
            dec = lambda rep: [(d["k"], d["verdict"], d.get("chosen")) for d in rep["per_row"]]
            self.assertEqual(dec(rp), dec(rn), (trial, variant))
            self.assertEqual(fp.keys(), fn.keys())
            self.assertEqual(rn["finer_pins_bad"], 0)


# ----------------------------------------------------------------------------------------------------------- the finer reading
class FinerReading(unittest.TestCase):
    """finer_reading builds the text as forced_reading does, with the program in place of the prints, and reads its lines."""

    def setUp(self):
        AG._FINER_NEEDS_IMPORT.clear()
        AG.STOP.clear()

    def tearDown(self):
        AG._FINER_NEEDS_IMPORT.clear()
        AG.STOP.clear()

    def fake(self, msgs, errors=(), timed_out=False, secs=1.5):
        from scorer.compile import CompileResult
        return CompileResult(not errors, None, secs, list(errors), timed_out=timed_out, messages=msgs)

    @staticmethod
    def proof_line(text) -> int:
        return int(re.search(r"let proofLine : _root_\.Nat := (\d+)\n", text).group(1))

    def answer(self, text, program_line, sources=("Lib.x",)):
        nonce = re.search(rf"{FS.MARK} ([0-9a-f]+) ", text).group(1)
        names = re.search(r"\(\[(.*?)\] : _root_\.List _root_\.Lean\.Name\)", text).group(1).replace("`", "").split(", ")
        ms = [msg(marker(q=n, decl="Lambda.x", sources=sources), program_line + 2, nonce) for n in names]
        return ms + [msg(end(len(names), proof_line=self.proof_line(text)), program_line + 3, nonce)]

    def test_project_row(self):
        from scorer import compile as C
        r = next(x for x in rows() if x["source"] == "strata")
        core = "module\n\nimport Foo\n\nnamespace Lambda\n\n"
        pf = proof(r, "x")
        seen = {}
        pl = C._first_line(core) + 1 + (pf.rstrip() + "\n\n").count("\n")

        def cp(row, text, version, *, count=True, timeout=900, lean_args=None, _quiet_prefix_sorry=False):
            seen.update(text=text, count=count, timeout=timeout, lean_args=lean_args)
            forged = msg(marker(q="forged", sources=[]), pl + 5, "ffffffffffffffff")   # a line the proof could print: another nonce
            return self.fake(self.answer(text, pl) + [forged, {"severity": "warning", "pos": {"line": 2}, "data": "declaration uses 'sorry'"}])
        with mock.patch.object(C, "file_prefix", return_value=core), mock.patch.object(C, "lakefile_options", return_value=("-Dwarn.sorry=false",)), \
                mock.patch.object(C, "compile_project", side_effect=cp):
            got = AG.finer_reading(r, pf, "v4.31.0", 77.9)
        name = C.decl_name(r["statement"], r["name"])
        self.assertFalse(seen["count"])
        self.assertEqual(seen["timeout"], 77)
        self.assertEqual(seen["lean_args"][-1], "-Dwarn.sorry=true")
        self.assertTrue(seen["text"].startswith(pf.rstrip() + "\n\nset_option maxHeartbeats 0 in\n"
                                                "#eval show _root_.Lean.Elab.Command.CommandElabM _root_.Unit from do\n"))
        self.assertIn(f"([`{name}, `{C.qualified_name(name, 'Lambda')}] : _root_.List _root_.Lean.Name)", seen["text"])
        # OWN: what the file declares from its first line after the library file's prefix on (the modifiers, then the proof)
        self.assertEqual(self.proof_line(seen["text"]), C._first_line(core) + 1)
        self.assertNotIn("error", got)
        self.assertEqual([m["q"] for m in got["markers"]], [name, C.qualified_name(name, "Lambda")])
        self.assertEqual((got["module"], got["sorry_warning"], got["lean_import"], got["finer_version"]), (True, False, False, FS.VERSION))
        self.assertEqual(FS.sources_of(got, "proof")[0]["sources"], frozenset({"Lib.x"}))

    def test_the_program_line(self):
        """The program's first line in the compiled file is the line the parser reads from (a marker one line above is ignored)."""
        from scorer import compile as C
        r = next(x for x in rows() if x["source"] == "putnambench")
        pf = proof(r, "x")
        seen = {}

        def cpu(header, text, version, *, count=True, timeout=600):
            body = header.rstrip() + "\n\n" + text.rstrip() + "\n"
            lines = body.split("\n")
            pl = next(i for i, s in enumerate(lines, 1) if s.startswith("set_option maxHeartbeats 0 in"))
            seen["pl"] = pl
            nonce = re.search(rf"{FS.MARK} ([0-9a-f]+) ", text).group(1)
            return self.fake([msg(marker(decl="x"), pl - 1, nonce), msg(end(1, proof_line=self.proof_line(text)), pl, nonce)])
        with mock.patch.object(C, "compile_putnam", side_effect=cpu):
            got = AG.finer_reading(r, pf, "v4.27.0", 60)
        self.assertEqual(got["error"], "finer reading: the end line counts 1 marker(s), 0 read")   # the line above: not read

    def test_the_lean_import_retry(self):
        from scorer import compile as C
        r = next(x for x in rows() if x["source"] == "cslib")
        core = "module\n\npublic import Cslib\n\n"
        pf = proof(r, "x")
        pl = C._first_line(core) + 1 + (pf.rstrip() + "\n\n").count("\n")
        calls = []

        def cp(row, text, version, **kw):
            calls.append(("project", text))
            return self.fake([], errors=[f"{pl}:15: unknown namespace `Command`"])

        def lip(source, version, body, lean_args, timeout, first_line=1, quiet_prefix_sorry=False):
            calls.append(("import", body, timeout, first_line))
            self.assertTrue(body.startswith("module\npublic meta import Lean.Elab.Command\n\npublic import Cslib"))
            return self.fake(self.answer(body, pl + 1), secs=2.0)
        with mock.patch.object(C, "file_prefix", return_value=core), mock.patch.object(C, "lakefile_options", return_value=()), \
                mock.patch.object(C, "compile_project", side_effect=cp), mock.patch.object(C, "_lean_in_project", side_effect=lip):
            got = AG.finer_reading(r, pf, "v4.35.0", 100)
        self.assertEqual([c[0] for c in calls], ["project", "import"])
        self.assertEqual(calls[1][3], pl - 1 - (pf.rstrip() + "\n\n").count("\n") + 1)   # the first line after the longer prefix
        self.assertLessEqual(calls[1][2], 100)
        self.assertNotIn("error", got)
        self.assertTrue(got["lean_import"])
        self.assertEqual(got["seconds"], 3.5)
        self.assertIn("unknown namespace `Command`", got["first_attempt"])
        self.assertEqual(got["end"]["proof_line"], C._first_line(FS.with_lean_import(core)) + 1)
        # the same file again in this run: compiled with the import at once, one compile (review 2026-11-24: on LeanPool every finer
        # reading cost two compiles, the second in what was left of the timeout)
        calls.clear()
        with mock.patch.object(C, "file_prefix", return_value=core), mock.patch.object(C, "lakefile_options", return_value=()), \
                mock.patch.object(C, "compile_project", side_effect=cp), mock.patch.object(C, "_lean_in_project", side_effect=lip):
            got = AG.finer_reading(r, proof(r, "y"), "v4.35.0", 100)
        self.assertEqual([c[0] for c in calls], ["import"])
        self.assertEqual(calls[0][2], 100)
        self.assertNotIn("error", got)
        self.assertNotIn("first_attempt", got)

    def test_no_retry_after_a_stop_or_without_the_time_to_start(self):
        """Review 2026-11-24 (code finding 2): the second compile obeys the pool's rules: none after a stop signal, none with less
        than MIN_START_S left."""
        from scorer import compile as C
        r = next(x for x in rows() if x["source"] == "cslib")
        core = "module\n\npublic import Cslib\n\n"
        pf = proof(r, "x")
        pl = C._first_line(core) + 1 + (pf.rstrip() + "\n\n").count("\n")
        for stop, timeout in ((True, 100), (False, AG.MIN_START_S - 0.5)):
            calls = []
            AG.STOP.clear()

            def cp(row, text, version, **kw):
                calls.append("project")
                if stop:
                    AG.STOP.set()
                return self.fake([], errors=[f"{pl}:15: unknown namespace `Command`"])
            with mock.patch.object(C, "file_prefix", return_value=core), mock.patch.object(C, "lakefile_options", return_value=()), \
                    mock.patch.object(C, "compile_project", side_effect=cp), \
                    mock.patch.object(C, "_lean_in_project", side_effect=AssertionError("a second compile")):
                got = AG.finer_reading(r, pf, "v4.35.0", timeout)
            self.assertEqual(calls, ["project"])
            self.assertIn("not compiled again with Lean's command elaborator imported: "
                          + ("the guard was stopped" if stop else "4 s left"), got["error"])
            self.assertEqual(AG._FINER_NEEDS_IMPORT, set())

    def test_no_retry_after_a_timeout_or_without_a_program_error(self):
        """A timed-out compile is not compiled again, also when it reports an error on the program's lines (review 2026-11-24, code
        finding 5: the case without such an error passed whatever the code did)."""
        from scorer import compile as C
        r = next(x for x in rows() if x["source"] == "putnambench")
        pf = proof(r, "x")
        pl = C._first_line(r["header"].rstrip()) + 1 + (pf.rstrip() + "\n\n").count("\n")
        for res in (self.fake([], errors=["timeout", f"{pl + 3}:4: unknown namespace `Command`"], timed_out=True), self.fake([])):
            calls = []
            with mock.patch.object(C, "compile_putnam", side_effect=lambda *a, **k: calls.append(1) or res):
                got = AG.finer_reading(r, pf, "v4.27.0", 60)
            self.assertEqual(len(calls), 1)
            self.assertIn("error", got)
            self.assertEqual(AG.pin_state(SORRY, SORRY, (got, fr(["Lib.x"])))[0], AG.BAD)
        self.assertTrue(got is not None)
        timed = self.fake([], errors=["timeout", f"{pl + 3}:4: unknown namespace `Command`"], timed_out=True)
        with mock.patch.object(C, "compile_putnam", return_value=timed):
            got = AG.finer_reading(r, pf, "v4.27.0", 60)
        self.assertTrue(got["program_errors"] and got["timed_out"])   # the case a mutant that drops `not timed_out` retries

    def test_a_sorry_message_on_the_declaration(self):
        from scorer import compile as C
        r = next(x for x in rows() if x["source"] == "putnambench")
        pf = proof(r, "x")

        def cpu(header, text, version, **kw):
            first = C._first_line(header.rstrip())
            pl = first + 1 + (pf.rstrip() + "\n\n").count("\n")
            return self.fake(self.answer(text, pl) + [{"severity": "warning", "pos": {"line": first + 2}, "data": "declaration uses 'sorry'"}])
        with mock.patch.object(C, "compile_putnam", side_effect=cpu):
            got = AG.finer_reading(r, pf, "v4.27.0", 60)
        self.assertTrue(got["sorry_warning"])
        self.assertFalse(FS.decide(got, fr(["Lib.x"]))[0])


if __name__ == "__main__":
    unittest.main()
