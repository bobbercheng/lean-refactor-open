#!/usr/bin/env python3
"""Tests of the kernel guard (harness/kernel_guard.py) and of the removal of the kernel-skip op (2026-11-24).

They start no Lean, no model and no network: only text checks, file handling and the tools' own refusals. From this folder's parent:
    python3 -B -m unittest discover -s tests -v
The tests write small files into new folders under the system temp directory (TMPDIR) and leave them there."""
from __future__ import annotations

import hashlib, importlib, importlib.util, json, os, re, subprocess, sys, tempfile, unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
ROWS_FILE = ROOT / "data/official/rows.jsonl"
HBS_FILE = ROOT / "data/official/heartbeats.jsonl"
os.environ.setdefault("LRA_ROWS_FILE", str(ROWS_FILE))   # harness/leantools reads its rows at import
os.environ.setdefault("LRA_HBS_FILE", str(HBS_FILE))

from harness import kernel_guard as KG  # noqa: E402
from scorer import forbidden as ARENA  # noqa: E402

ENV = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
SKIP = "set_option debug.skipKernelTC true in"
# the two shapes of our four submitted kernel-skip proofs (P stands for the row's head predicate)
FORM_UNFOLD = " by\n  unfold P\n  set_option debug.skipKernelTC true in decide +kernel"
FORM_INPLACE = "set_option debug.skipKernelTC true in\n  decide +kernel"


def rows() -> list:
    return [json.loads(l) for l in ROWS_FILE.read_text().splitlines() if l.strip()]


def tainted(row: dict) -> str:
    return row["statement"] + " := by\n  " + FORM_INPLACE


def tmpdir() -> Path:
    return Path(tempfile.mkdtemp(prefix="lra-kernel-guard-"))


def write_jsonl(path: Path, recs: list) -> None:
    path.write_text("".join(json.dumps(r, ensure_ascii=False) + "\n" for r in recs))


def export_like(rs: list, bad: set) -> list:
    """An export's lines for the rows: the reference proof, or a kernel-skip proof for the names in `bad`."""
    return [{"name": r["name"], "proof": (tainted(r) if r["name"] in bad else r["src"].rstrip()) + "\n", "source": "agent",
             "stored_score": 72.19 if r["name"] in bad else 33.33, "tokens": 10, "heartbeats": 83} for r in rs]


class Predicate(unittest.TestCase):
    ACCEPT = [
        "theorem t : 2 + 2 = 4 := by\n  decide +kernel",
        "theorem t : True := by\n  set_option smartUnfolding false in\n  trivial",
        "theorem t : True := by\n  set_option backward.isDefEq.lazyWhnfCore false in\n  trivial",
        "theorem t : True := by\n  set_option backward.isDefEq.lazyProjDelta false in set_option backward.isDefEq.respectTransparency false in trivial",
        "theorem t : True := by\n  set_option maxRecDepth 2000 in\n  trivial",
        "theorem t : True := by\n  open Nat in\n  set_option smartUnfolding false in trivial",
        "theorem t (debug : Nat) : debug = debug := by\n  -- debug this later\n  rfl",
        "theorem t : True := by\n  have debugInfo := Foo.debug.bar\n  trivial",
        "theorem t : True := by\n  set_option trace.Meta.debug true in\n  trivial",
        "theorem t : True := by\n  set_option trace.debug.foo true in\n  trivial",
        "theorem t : True := by\n  exact mydebug.elim (h'debug.trans x?debug.symm)",
    ]
    REJECT = [
        "theorem t : P x :=" + FORM_UNFOLD,
        "theorem t : P x := by\n  simp only [foo]\n  " + FORM_INPLACE,
        "theorem t : P := by set_option debug.skipKernelTC true in decide +kernel",
        "theorem t : P := by\n  set_option   debug.skipKernelTC   true   in\n  decide +kernel",
        "theorem t : P := by\n  set_option\n    debug.skipKernelTC true in decide +kernel",
        "theorem t : P := by\n  set_option\tdebug.skipKernelTC true in decide +kernel",
        "theorem t : P := by\n  SET_OPTION DEBUG.SKIPKERNELTC TRUE IN decide +kernel",
        "theorem t : P := by\n  set_option Debug.SkipKernelTC true in decide +kernel",
        "theorem t : P := by\n  set_option /- why -/ debug.skipKernelTC true in decide +kernel",
        "theorem t : P := by\n  set_option -- why\n    debug.skipKernelTC true in decide +kernel",
        "theorem t : P := by\n  set_option «debug».skipKernelTC true in decide +kernel",
        "theorem t : P := by\n  set_option maxRecDepth 1000 in set_option debug.skipKernelTC true in decide +kernel",
        "theorem t : P := by\n  set_option smartUnfolding false in\n  set_option debug.skipKernelTC true in\n  decide +kernel",
        "theorem t : P := by\n  open Nat in set_option debug.skipKernelTC true in decide +kernel",
        "theorem t : P := by\n  open Nat Foo in\n  open Bar in\n  set_option debug.skipKernelTC true in\n  decide +kernel",
        "theorem t : P := set_option debug.skipKernelTC true in by decide +kernel",
        "theorem t : P := by\n  set_option debug.skipKernelTC false in decide +kernel",
        "theorem t : P := by\n  set_option debug.byAsSorry true in\n  exact foo",
        "theorem t : P := by\n  set_option debug.proofAsSorry true in\n  exact foo",
        "theorem t : P := by\n  set_option debug.moduleNameAtTimeout false in\n  exact foo",
        "theorem t : P := by\n  set_option debug.anythingElse 3 in\n  exact foo",
        "theorem t : P := by\n  -- set_option debug.skipKernelTC true in\n  decide +kernel",
        "theorem t : P := by\n  /- skipKernelTC -/ decide +kernel",
        # a quote that misleads a comment reader must not hide the option
        "theorem t : P := by\n  have c := '\"'\n  set_option /- x -/ debug.skipKernelTC true in decide +kernel",
        "theorem t : P := by\n  have s := \"--\"; set_option debug.skipKernelTC true in decide +kernel",
        # other debug options behind a quote and a comment that mislead a comment reader (the token-level rule reads no comment)
        "theorem t : P := by\n  have c : Char := '\"'\n  set_option /- /- a -/ b -/ debug.byAsSorry true in exact foo",
        "theorem t : P := by\n  have c : Char := '\"'\n  set_option -- /-\n debug.byAsSorry true in exact foo -- -/",
        "theorem t : P := by\n  have «a\"b» := 1\n  set_option /- /- a -/ b -/ debug.proofAsSorry true in exact foo",
        "theorem t : P := by\n  set_option /- /- a -/ b -/ debug.byAsSorry true in exact foo",
        "theorem t : P := by\n  set_option/- a -/debug.byAsSorry true in exact foo",
        "theorem t : P := by\n  set_option«debug».byAsSorry true in exact foo",
        "theorem t : P := by\n  set_option /- a -/ «debug».«byAsSorry» true in exact foo",
        "theorem t : P := by\r\n  set_option\r\n debug.byAsSorry true in exact foo",
    ]

    def test_accepts_normal_proofs_and_elaborator_options(self):
        for t in self.ACCEPT:
            self.assertIsNone(KG.debug_option(t), t)
            self.assertEqual(KG.check_forbidden(t), ARENA.check_forbidden(t), t)

    def test_rejects_every_debug_option_form(self):
        for t in self.REJECT:
            self.assertEqual(KG.debug_option(t), KG.REASON, t)
            self.assertIsNotNone(KG.check_forbidden(t), t)

    def test_the_token_rule_alone_rejects_every_form_in_exact_case(self):
        """The rule that needs no comment handling carries every form whose option name is spelled as Lean reads it."""
        for t in self.REJECT:
            if "debug." in t or "«debug»." in t:
                self.assertIsNotNone(KG._DEBUG_NAME.search(t), t)
        for t in self.ACCEPT:
            self.assertIsNone(KG._DEBUG_NAME.search(t), t)

    def test_a_local_name_debug_with_a_projection_is_rejected_too(self):
        """The documented price of the token-level rule: `debug.` at the start of an identifier is rejected wherever it stands."""
        self.assertEqual(KG.debug_option("theorem t (debug : A ∧ B) : A := by\n  exact debug.1"), KG.REASON)
        self.assertEqual(KG.debug_option("theorem t : P := by\n  -- see debug.byAsSorry\n  exact foo"), KG.REASON)

    def test_time_is_linear_on_a_text_of_the_size_limit(self):
        """Many comment openers without a closer, and the word `debug`: no rule may go quadratic (the predicate runs in the model's
        check tools). 255 KB, under the Arena's size limit; a quadratic rule needs minutes here."""
        import time
        for body in ("/- " * 85000, "set_option " * 23000, "-- /- \n" * 36000, "debug " * 42000):
            t = "theorem t : P := by\n  -- debug\n" + body
            self.assertLess(len(t), ARENA.MAX_PROOF_BYTES)
            t0 = time.monotonic()
            self.assertIsNone(KG.debug_option(t))
            self.assertLess(time.monotonic() - t0, 10.0, body[:12])

    def test_empty_text(self):
        self.assertIsNone(KG.debug_option(""))
        self.assertIsNone(KG.debug_option(None))

    def test_reason_is_one_line_and_says_why(self):
        self.assertNotIn("\n", KG.REASON)
        self.assertIn("disables kernel checking", KG.REASON)
        self.assertIn("not allowed", KG.REASON)

    def test_arena_labels_come_first_and_unchanged(self):
        self.assertEqual(KG.check_forbidden("theorem t : P := by sorry"), "sorry")
        self.assertEqual(KG.check_forbidden("theorem t : P := by native_decide"), "native_decide")
        self.assertEqual(KG.check_forbidden("theorem t : P := by\n  sorry\n  " + FORM_INPLACE), "sorry")
        self.assertEqual(KG.check_forbidden("theorem t : P := by\n  " + FORM_INPLACE), KG.REASON)

    def test_released_reference_proofs_pass_as_before(self):
        rs = rows()
        self.assertEqual(len(rs), 60)
        for r in rs:
            self.assertIsNone(KG.debug_option(r["src"]), r["name"])
            self.assertEqual(KG.check_forbidden(r["src"]), ARENA.check_forbidden(r["src"]), r["name"])

    def test_arena_list_file_is_the_export_copy(self):
        want = json.loads((ROOT / "EXPORT.json").read_text())["files"]["scorer/forbidden.py"]
        self.assertEqual(hashlib.sha256((ROOT / "scorer/forbidden.py").read_bytes()).hexdigest(), want)


class NoKernelSkipOp(unittest.TestCase):
    def test_op_tables(self):
        from harness import open_post as P
        for name in ("V1_ORDER", "V2_OPS", "V3_OPS", "V4_OPS", "V5L_OPS", "V5_OPS", "V2_ORDER", "V3_ORDER", "V4_ORDER", "LANE_OPS", "ORDER"):
            self.assertNotIn("kskip", getattr(P, name), name)
        self.assertNotIn("kskip", P.READS)
        self.assertEqual(P.V1_ORDER, ("implied", "closerprep", "inlineeq"))
        self.assertEqual(len(P.ORDER), 40)
        self.assertEqual(set(P.READS), set(P.ORDER))
        self.assertEqual([m.__name__ for m in P._mods()],
                         ["harness.post.d4_implied", "harness.post.d4_inlineeq", "harness.post.d4_closerprep", "harness.post.d4_measure"])

    def test_no_site_for_a_kernel_checked_decide_closer(self):
        from harness import open_post as P
        st = "theorem t : 2 + 2 = 4"
        self.assertNotIn("kskip", P.sites(st + " := by\n  decide +kernel", st))

    def test_ops_flag_refuses_the_name(self):
        from harness import open_post as P
        before = P.ORDER
        with self.assertRaises(SystemExit):
            P.main(["--rows", "x", "--heartbeats", "x", "--out", "x", "--ops", "kskip"])
        self.assertEqual(P.ORDER, before)

    def test_cli_help_texts(self):
        for cmd in (["harness/open_post.py", "--help"], ["post_fast/pf_drive.py", "--help"], ["harness/open_package.py", "--help"],
                    ["harness/kernel_guard.py", "--help"]):
            r = subprocess.run([sys.executable, "-B", *cmd], cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=120)
            self.assertEqual(r.returncode, 0, (cmd, r.stderr[-300:]))
            self.assertNotIn("kskip", r.stdout, cmd)
            self.assertIn("--debug-rows", r.stdout, cmd)

    def test_no_source_file_names_the_op_as_code(self):
        """No import of the module and no quoted op name in any Python or shell file of the package (comments may say it is removed)."""
        pat = re.compile(r"""["']kskip|\bimport\b[^\n]*\bkskip\b|\bpost\.kskip\b|\bkskip\s+as\b|\bKS\.""")
        hits = []
        for f in sorted(ROOT.rglob("*")):
            if f.suffix not in (".py", ".sh") or "tests" in f.relative_to(ROOT).parts or f.name == "kskip.py" or "runs" in f.relative_to(ROOT).parts:
                continue
            for n, line in enumerate(f.read_text(errors="replace").splitlines(), 1):
                if pat.search(line):
                    hits.append(f"{f.relative_to(ROOT)}:{n}")
        self.assertEqual(hits, [])

    def test_module_file_is_gone(self):
        self.assertFalse((ROOT / "harness/post/kskip.py").exists(),
                         "harness/post/kskip.py is still in the package: nothing imports it, but it must be removed (git rm)")


class EveryGateUsesTheGuard(unittest.TestCase):
    def test_only_the_guard_imports_the_arena_check(self):
        pat = re.compile(r"scorer\.forbidden\s+import[^\n]*\bcheck_forbidden\b|\bforbidden\.check_forbidden\s*\(")
        hits = []
        for f in sorted(ROOT.rglob("*.py")):
            rel = f.relative_to(ROOT)
            if str(rel) in ("harness/kernel_guard.py", "scorer/forbidden.py") or "tests" in rel.parts or "runs" in rel.parts:
                continue
            for n, line in enumerate(f.read_text(errors="replace").splitlines(), 1):
                if pat.search(line):
                    hits.append(f"{rel}:{n}")
        self.assertEqual(hits, [])

    def test_module_level_names_are_the_guard(self):
        for m in ("harness.agent", "harness.leantools", "harness.endstage", "harness.endstage_r10", "harness.workbench",
                  "harness.hb_tool_eval", "harness.funind", "harness.post.argon_haveopt", "harness.post.argon_funind",
                  "harness.post.argon_calcstep", "harness.post.argon_hbsimp"):
            self.assertIs(importlib.import_module(m).check_forbidden, KG.check_forbidden, m)

    def test_agent_stage_closures_call_the_one_name(self):
        """The model's check tools in harness/agent.py are closures of its main function, which a test cannot call without a model
        server. Read from the source instead: the name check_forbidden is bound once in each file, by the import from the guard
        module (no local name hides it), and the functions that compile a candidate call it."""
        import ast
        for rel, n_calls, caller in (("harness/agent.py", 2, "golf_eval"), ("harness/leantools.py", 1, "lean_check"),
                                     ("harness/workbench.py", 1, None)):
            tree = ast.parse((ROOT / rel).read_text())
            binds, calls = [], set()
            for fn in ast.walk(tree):
                if isinstance(fn, ast.ImportFrom) and any((al.asname or al.name) == "check_forbidden" for al in fn.names):
                    binds.append(fn.module)
                elif isinstance(fn, (ast.Assign, ast.AnnAssign, ast.AugAssign, ast.NamedExpr)):
                    tg = fn.targets if isinstance(fn, ast.Assign) else [fn.target]
                    binds += ["assigned" for t in tg for n in ast.walk(t) if isinstance(n, ast.Name) and n.id == "check_forbidden"]
                elif isinstance(fn, (ast.FunctionDef, ast.AsyncFunctionDef)):
                    if fn.name == "check_forbidden" or any(x.arg == "check_forbidden" for x in ast.walk(fn.args) if isinstance(x, ast.arg)):
                        binds.append("defined")
                    own = [n for st in fn.body for n in ast.walk(st)]
                    if any(isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == "check_forbidden" for n in own):
                        calls.add(fn.name)
            self.assertEqual(binds, ["harness.kernel_guard"], rel)
            n = sum(isinstance(x, ast.Call) and isinstance(x.func, ast.Name) and x.func.id == "check_forbidden" for x in ast.walk(tree))
            self.assertEqual(n, n_calls, rel)
            if caller:
                self.assertIn(caller, calls, rel)

    def test_agent_tool_path_tells_the_model_why(self):
        from harness import leantools as LT
        r = rows()[0]
        res = LT.lean_check(r["name"], tainted(r), {"best": {}, "attempts": []}, {}, None)   # refused before any compile
        self.assertEqual(res, {"ok": False, "errors": ["forbidden construct: " + KG.REASON]})

    def test_post_step_gate(self):
        from harness import open_post as P
        r = rows()[0]
        self.assertEqual(P.static_ok(tainted(r), r["statement"]), "forbidden: " + KG.REASON)
        self.assertIsNone(P.static_ok(r["src"].rstrip(), r["statement"]))

    def test_export_picks_and_writer(self):
        from harness import open_package as OP
        r = rows()[0]
        bad = {"proof": tainted(r), "score": 90.0}
        good = {"proof": r["src"].rstrip(), "score": 40.0}
        self.assertFalse(OP.check_forbidden_ok(tainted(r)))
        self.assertTrue(OP.check_forbidden_ok(r["src"]))
        self.assertEqual(OP.export_candidate(r, bad, good)[0], "agent")
        self.assertEqual(OP.export_candidate(r, bad, bad)[0], "seed")
        self.assertEqual(OP.export_candidate(r, good, bad)[0], "end")
        self.assertIsNone(OP.normalized_choice(r, {"status": "improved", "proof": tainted(r)}))
        self.assertEqual(OP.normalized_choice(r, {"status": "improved", "proof": r["src"]}), r["src"].rstrip())
        d = tmpdir()
        with self.assertRaises(KG.DebugOptionError) as cm:
            OP.write_proofs(d, [{"name": r["name"], "proof": tainted(r) + "\n"}])
        self.assertIn(r["name"], str(cm.exception))
        self.assertFalse((d / "proofs.jsonl").exists())
        OP.write_proofs(d, [{"name": r["name"], "proof": r["src"]}])
        self.assertTrue((d / "proofs.jsonl").exists())

    def test_interim_promote(self):
        from infra.orgserver import orgtools as OT
        rs = rows()[:3]
        d = tmpdir()
        (d / "interim").mkdir()
        write_jsonl(d / "interim" / "proofs.jsonl", export_like(rs, {rs[0]["name"]}))
        res = OT.promote(d)
        self.assertTrue(res.startswith("refused (kernel guard)"), res)
        self.assertIn(rs[0]["name"], res)
        self.assertFalse((d / "proofs.jsonl").exists())
        (d / "interim" / "proofs.jsonl").write_text('{"name": "x", "proof": "by set_option debug.skipKernelTC true in decide"\nnot json\n')
        self.assertTrue(OT.promote(d).startswith("refused (kernel guard)"))
        write_jsonl(d / "interim" / "proofs.jsonl", export_like(rs, set()))
        self.assertTrue(OT.promote(d).startswith("promoted"))
        self.assertEqual(KG.debug_rows(KG.read_jsonl(d / "proofs.jsonl")), [])
        self.assertEqual(OT.promote(d), "kept: proofs.jsonl exists (the export ran)")

    def test_promote_does_not_call_a_file_of_the_earlier_version_the_export(self):
        """A proofs.jsonl with a kernel-skip proof is already in OUT (a resumed run of the earlier version): the answer says so."""
        from infra.orgserver import orgtools as OT
        rs = rows()[:3]
        d = tmpdir()
        (d / "interim").mkdir()
        write_jsonl(d / "proofs.jsonl", export_like(rs, {rs[1]["name"]}))
        write_jsonl(d / "interim" / "proofs.jsonl", export_like(rs, set()))
        before = (d / "proofs.jsonl").read_bytes()
        res = OT.promote(d)
        self.assertTrue(res.startswith("kept, but NOT a valid output (kernel guard)"), res)
        self.assertIn(rs[1]["name"], res)
        self.assertEqual((d / "proofs.jsonl").read_bytes(), before)

    def test_end_stage_code_identity_holds_the_guard(self):
        from harness import endstage as ES, endstage_r10 as R10
        for m in (ES, R10):
            self.assertIn("harness/kernel_guard.py", m.CODE_FILES, m.__name__)
            self.assertIn("harness/kernel_guard.py", m.code_identity()["files"], m.__name__)

    def test_interim_export_and_its_promotion(self):
        """infra/orgserver/snapshot.py (the hourly interim file and the one a signal promotes) goes through the export's picks and
        writer: a saved best and an end-stage output that set the option are passed over, and the promoted file holds none."""
        from harness import open_package as OP
        from infra.orgserver import snapshot as SN
        rs = rows()[:3]
        d = tmpdir()
        write_jsonl(d / "rows.jsonl", rs)
        out = d / "final"
        for k, r in enumerate(rs):
            wd = out / "work" / OP.safe(r["name"])
            wd.mkdir(parents=True)
            proof = tainted(r) if k == 1 else r["src"].rstrip()
            (wd / "state.json").write_text(json.dumps({"problem": r["name"], "best": {"score": 72.19 if k == 1 else 40.0, "proof": proof},
                                                       "attempts": [], "runs": []}))
        (out / "end").mkdir()
        write_jsonl(out / "end" / "report.jsonl", [{"problem": rs[0]["name"], "out": {"proof": tainted(rs[0]), "score": 90.0},
                                                    "input_measured": {"ok": True}, "delta": 1.0}])
        import contextlib, io
        with contextlib.redirect_stdout(io.StringIO()) as buf:
            rc = SN.main(["--rows", str(d / "rows.jsonl"), "--heartbeats", str(HBS_FILE), "--out", str(out), "--promote"])
        self.assertEqual(rc, 0, buf.getvalue())
        self.assertIn("promoted", buf.getvalue())
        for f in (out / "interim" / "proofs.jsonl", out / "proofs.jsonl"):
            recs = KG.read_jsonl(f)
            self.assertEqual([r["source"] for r in recs], ["agent", "seed", "agent"], f)
            self.assertEqual(KG.debug_rows(recs), [], f)

    def test_merge(self):
        spec = importlib.util.spec_from_file_location("lra_merge_post", ROOT / "post_fast/merge_post.py")
        MP = importlib.util.module_from_spec(spec); spec.loader.exec_module(MP)
        rs = rows()[:3]
        d = tmpdir()
        write_jsonl(d / "rows.jsonl", rs)
        cur = export_like(rs, set())
        new = export_like(rs, {rs[1]["name"]})          # a higher stored score, but a kernel-skip proof
        self.assertFalse(MP.good(new[1], cur[1], rs[1]))
        write_jsonl(d / "proofs.jsonl", cur); write_jsonl(d / "emit.jsonl", new)
        MP.main(str(d / "emit.jsonl"), str(d / "rows.jsonl"), str(d / "proofs.jsonl"))
        self.assertEqual(KG.debug_rows(KG.read_jsonl(d / "proofs.jsonl")), [])
        write_jsonl(d / "proofs.jsonl", new)             # the file to merge into holds the proof itself: refused, unchanged
        before = (d / "proofs.jsonl").read_bytes()
        with self.assertRaises(SystemExit) as cm:
            MP.main(str(d / "emit.jsonl"), str(d / "rows.jsonl"), str(d / "proofs.jsonl"))
        self.assertIn(rs[1]["name"], str(cm.exception))
        self.assertEqual((d / "proofs.jsonl").read_bytes(), before)


class InputHandling(unittest.TestCase):
    def setUp(self):
        self.rs = rows()[:4]
        self.bad = self.rs[2]["name"]
        self.d = tmpdir()
        write_jsonl(self.d / "rows.jsonl", self.rs)
        self.inp = self.d / "proofs.jsonl"
        write_jsonl(self.inp, export_like(self.rs, {self.bad}))
        self.raw = self.inp.read_text().splitlines()

    def check_replaced(self, path: Path):
        got = path.read_text().splitlines()
        self.assertEqual(len(got), len(self.raw))
        for k, r in enumerate(self.rs):
            if r["name"] != self.bad:
                self.assertEqual(got[k], self.raw[k])    # every other line byte for byte
        rec = json.loads(got[2])
        self.assertEqual((rec["name"], rec["source"], rec["stored_score"]), (self.bad, "seed", 33.33))
        self.assertEqual(rec["proof"], self.rs[2]["src"].rstrip() + "\n")
        self.assertEqual(KG.debug_rows(map(json.loads, got)), [])

    def test_check_input_fail_names_the_rows(self):
        recs = KG.read_jsonl(self.inp)
        with self.assertRaises(KG.DebugOptionError) as cm:
            KG.check_input(recs, {r["name"]: r for r in self.rs}, "fail", "test input")
        self.assertIn(self.bad, str(cm.exception))
        self.assertIn("--debug-rows reference", str(cm.exception))
        with self.assertRaises(KG.DebugOptionError):
            KG.assert_clean(recs, "test output")

    def test_check_input_reference(self):
        recs = KG.read_jsonl(self.inp)
        out, idx = KG.check_input(recs, {r["name"]: r for r in self.rs}, "reference", "test input")
        self.assertEqual(idx, [2])
        self.assertEqual(out[2]["proof"], self.rs[2]["src"].rstrip() + "\n")
        self.assertEqual([out[k] for k in (0, 1, 3)], [recs[k] for k in (0, 1, 3)])
        with self.assertRaises(KG.DebugOptionError):   # no reference proof for the row: never a silent keep
            KG.check_input(recs, {}, "reference", "test input")
        clean, none = KG.check_input(out, {}, "fail", "test input")
        self.assertEqual((clean, none), (out, []))

    def test_cli(self):
        cmd = [sys.executable, "-B", "harness/kernel_guard.py", str(self.inp), "--rows", str(self.d / "rows.jsonl")]
        r = subprocess.run(cmd, cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 2)
        self.assertIn(self.bad, r.stderr)
        self.assertEqual(self.inp.read_text().splitlines(), self.raw)
        r = subprocess.run(cmd + ["--debug-rows", "reference"], cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 0, r.stderr)
        self.assertIn(self.bad, r.stdout)
        self.check_replaced(self.inp)
        self.assertEqual((self.d / "proofs.jsonl.debug-rows").read_text().splitlines(), self.raw)
        r = subprocess.run(cmd, cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 0)

    def test_cli_on_a_file_with_a_line_that_is_not_json(self):
        cmd = [sys.executable, "-B", "harness/kernel_guard.py", str(self.inp), "--rows", str(self.d / "rows.jsonl")]
        self.inp.write_text("".join(l + "\n" for l in self.raw) + "not json\n")
        r = subprocess.run(cmd, cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 2, r.stderr)        # never taken for a clean file
        self.assertIn("does not parse", r.stderr)
        self.inp.write_text("".join(l + "\n" for k, l in enumerate(self.raw) if k != 2) + "not json\n")
        r = subprocess.run(cmd, cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 1, r.stderr)
        self.assertIn("not checked", r.stderr)

    def test_post_step(self):
        from harness import open_post as P
        out = self.d / "post"
        out.mkdir()
        with self.assertRaises(KG.DebugOptionError) as cm:
            P.post_step(self.d / "rows.jsonl", HBS_FILE, out, input_path=self.inp, audit=None, problems=["no such row"])
        self.assertIn(self.bad, str(cm.exception))
        self.assertFalse((out / P.POST_FILE).exists())
        rc = P.main(["--rows", str(self.d / "rows.jsonl"), "--heartbeats", str(HBS_FILE), "--out", str(out), "--input", str(self.inp),
                     "--problems", "no such row"])
        self.assertEqual(rc, 2)
        self.assertFalse((out / P.POST_FILE).exists())
        rep = P.post_step(self.d / "rows.jsonl", HBS_FILE, out, input_path=self.inp, audit=None, problems=["no such row"],
                          debug_rows="reference")    # no row is worked on: nothing compiles
        self.check_replaced(out / P.POST_FILE)
        self.assertEqual(rep["config"]["debug_rows_replaced"], [self.bad])
        self.assertEqual(self.inp.read_text().splitlines(), self.raw)   # the input file is never written

    def test_fast_driver(self):
        cmd = [sys.executable, "-B", "post_fast/pf_drive.py", "--code", str(ROOT), "--rows", str(self.d / "rows.jsonl"), "--heartbeats",
               str(HBS_FILE), "--input", str(self.inp), "--sock", str(self.d / "no.sock"), "--worker", "post_fast/pf_worker.py",
               "--problems", "no such row"]
        o1 = self.d / "pf1"
        r = subprocess.run(cmd + ["--out", str(o1)], cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 2)
        self.assertIn(self.bad, r.stderr)
        self.assertFalse((o1 / "proofs.post.jsonl").exists())
        o2 = self.d / "pf2"
        r = subprocess.run(cmd + ["--out", str(o2), "--debug-rows", "reference"], cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 0, r.stderr[-500:])
        self.check_replaced(o2 / "input.kernel-guard.jsonl")
        self.assertEqual(KG.debug_rows(KG.read_jsonl(o2 / "proofs.post.jsonl")), [])
        self.assertEqual(json.loads((o2 / "summary.json").read_text())["debug_rows_replaced"], [self.bad])

    def test_fast_stage_script(self):
        out = self.d / "run"
        out.mkdir()
        (out / "proofs.jsonl").write_text("".join(l + "\n" for l in self.raw))
        cmd = ["bash", "post_fast/post_stage.sh", str(out), str(self.d / "rows.jsonl"), str(HBS_FILE), str(self.d / "work"), "0"]
        r = subprocess.run(cmd, cwd=ROOT, env=ENV, capture_output=True, text=True, timeout=120)   # job end 0: the stage itself is skipped
        self.assertEqual(r.returncode, 2)
        self.assertIn(self.bad, r.stdout + r.stderr)
        self.assertIn("refused (kernel guard)", r.stdout)
        self.assertEqual((out / "proofs.jsonl").read_text().splitlines(), self.raw)
        r = subprocess.run(cmd, cwd=ROOT, env=dict(ENV, LRA_DEBUG_ROWS="reference"), capture_output=True, text=True, timeout=120)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.check_replaced(out / "proofs.jsonl")
        self.assertEqual((out / "proofs.jsonl.debug-rows").read_text().splitlines(), self.raw)

    def test_driver_start(self):
        from harness import open_package as OP
        rs = {r["name"]: r for r in self.rs}
        names = [r["name"] for r in self.rs]
        out = self.d / "final"
        wd = out / "work" / OP.safe(self.bad)
        wd.mkdir(parents=True)
        state = {"problem": self.bad, "best": {"score": 72.19, "proof": tainted(self.rs[2]), "tokens": 10, "heartbeats": 83},
                 "attempts": [{"sha": "x", "ok": True, "score": 72.19}], "runs": [{"run_id": "r1"}]}
        (wd / "state.json").write_text(json.dumps(state))
        (wd / "best.lean").write_text(tainted(self.rs[2]) + "\n")

        class A:
            rows = str(self.d / "rows.jsonl")
            debug_rows = "fail"
        with self.assertRaises(SystemExit) as cm:
            OP.kernel_guard_start(A, names, rs, out)
        self.assertIn(self.bad, str(cm.exception))
        self.assertEqual(cm.exception.code, OP.KERNEL_GUARD_RC)   # run.sh stops the job on this code instead of restarting the driver
        self.assertIn(f'"$RC" = {OP.KERNEL_GUARD_RC} ]', (ROOT / "run.sh").read_text())
        self.assertEqual(json.loads((wd / "state.json").read_text()), state)
        with self.assertRaises(SystemExit) as cm:   # the command line: refused before any stage
            OP.main(["export", "--rows", str(self.d / "rows.jsonl"), "--heartbeats", str(HBS_FILE), "--out", str(out), "--no-audit"])
        self.assertIn(self.bad, str(cm.exception))
        self.assertFalse((out / "proofs.jsonl").exists())
        A.debug_rows = "reference"
        self.assertEqual(OP.kernel_guard_start(A, names, rs, out), [self.bad])
        st = json.loads((wd / "state.json").read_text())
        self.assertEqual(st["best"], {"score": 33.33, "proof": None, "tokens": self.rs[2]["proof_length"], "heartbeats": None})
        self.assertEqual(st["attempts"], state["attempts"])
        self.assertEqual(json.loads((wd / "state.json.debug-rows").read_text()), state)
        self.assertEqual((wd / "best.lean").read_text(), self.rs[2]["src"].rstrip() + "\n")
        self.assertEqual(OP.kernel_guard_start(A, names, rs, out), [])
        # the export itself (no audit: nothing compiles): an end-stage output that sets the option is passed over for the agent best
        w0 = out / "work" / OP.safe(names[0])
        w0.mkdir(parents=True)
        (w0 / "state.json").write_text(json.dumps({"problem": names[0], "best": {"score": 40.0, "proof": self.rs[0]["src"].rstrip()},
                                                   "attempts": [], "runs": []}))
        (out / "end").mkdir()
        write_jsonl(out / "end" / "report.jsonl", [{"problem": names[0], "out": {"proof": tainted(self.rs[0]), "score": 90.0},
                                                    "input_measured": {"ok": True}, "delta": 1.0}])
        self.assertEqual(OP.end_outputs(out)[names[0]]["score"], 90.0)
        self.assertEqual(OP.main(["export", "--rows", str(self.d / "rows.jsonl"), "--heartbeats", str(HBS_FILE), "--out", str(out),
                                  "--no-audit", "--debug-rows", "reference"]), 0)
        recs = KG.read_jsonl(out / "proofs.jsonl")
        self.assertEqual([r["source"] for r in recs], ["agent", "seed", "seed", "seed"])
        self.assertEqual(KG.debug_rows(recs), [])
        seeded = dict(rs, **{self.bad: dict(rs[self.bad], src=tainted(self.rs[2]))})   # a rows file whose reference sets the option
        with self.assertRaises(SystemExit) as cm:
            OP.kernel_guard_start(A, names, seeded, out)
        self.assertIn(self.bad, str(cm.exception))


class RunScript(unittest.TestCase):
    """run.sh needs a set-up node, so its kernel-guard lines are cut out of the file and run here with stand-ins for the job around
    them (the log helpers, the Python and the paths). The lines run are the shipped ones."""
    STUBS = ('set -u\nlra_log() { echo "$*"; }\nlra_die() { echo "FAILED: $*"; exit 1; }\nstop_all() { :; }\n'
             'fail() { echo "CHECK FAILED: $*"; }\nLOGD=$OUT/logs; mkdir -p "$LOGD"\n')

    def setUp(self):
        self.sh = (ROOT / "run.sh").read_text()
        self.rs = rows()[:3]
        self.d = tmpdir()
        write_jsonl(self.d / "rows.jsonl", self.rs)
        self.out = self.d / "final"
        (self.out / "interim").mkdir(parents=True)

    def block(self, first: str, last: str) -> str:
        """The lines of run.sh from the one that starts with `first` to the next one that starts with `last`."""
        ls = self.sh.splitlines()
        i = [k for k, l in enumerate(ls) if l.startswith(first)]
        self.assertEqual(len(i), 1, first)
        j = next(k for k in range(i[0], len(ls)) if ls[k].startswith(last))
        return "\n".join(ls[i[0]:j + 1]) + "\n"

    def run_lines(self, body: str, **env):
        e = dict(ENV, PY=sys.executable, ROWS=str(self.d / "rows.jsonl"), OUT=str(self.out), START="1700000000", RC="0", **env)
        return subprocess.run(["bash", "-c", self.STUBS + body], cwd=ROOT, env=e, capture_output=True, text=True, timeout=120)

    def test_a_file_of_the_earlier_version_is_moved_aside_and_never_done(self):
        kg = self.block("kg_file() {", "kg_file() {")
        aside = self.block('for f in "$OUT/proofs.jsonl" "$OUT/interim/proofs.jsonl"; do', "done")
        end = self.block("KRC=0;", 'exit "$RC"')
        self.assertLess(self.sh.index(aside), self.sh.index("while :; do"))            # before the driver starts
        self.assertLess(self.sh.index("bash post_fast/post_stage.sh"), self.sh.index(end))   # after the post stage
        bad = self.rs[1]["name"]
        stale = export_like(self.rs, {bad})
        # 1. a resumed OUT with both files of the earlier version; the job then reaches no export and no clean interim file
        write_jsonl(self.out / "proofs.jsonl", stale)
        write_jsonl(self.out / "interim" / "proofs.jsonl", stale)
        r = self.run_lines(kg + aside + end)
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn("FAILED: no proofs file", r.stdout)
        self.assertNotIn("DONE", r.stdout)
        self.assertFalse((self.out / "proofs.jsonl").exists())
        self.assertFalse((self.out / "interim" / "proofs.jsonl").exists())
        for f in (self.out / "proofs.jsonl.debug-rows.1700000000", self.out / "interim" / "proofs.jsonl.debug-rows.1700000000"):
            self.assertEqual(KG.debug_rows(KG.read_jsonl(f)), [bad])                    # kept beside, not lost
        self.assertIn(bad, (self.out / "logs" / "kernel_guard.log").read_text())
        # 2. the same OUT, and this job's clean interim file is promoted afterwards: that is the output
        write_jsonl(self.out / "proofs.jsonl", stale)
        from infra.orgserver import orgtools as OT
        r = self.run_lines(kg + aside)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        write_jsonl(self.out / "interim" / "proofs.jsonl", export_like(self.rs, set()))
        self.assertTrue(OT.promote(self.out).startswith("promoted"))
        r = self.run_lines(kg + end)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("DONE", r.stdout)
        # 3. a clean file is left alone
        before = (self.out / "proofs.jsonl").read_bytes()
        r = self.run_lines(kg + aside + end)
        self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
        self.assertIn("DONE", r.stdout)
        self.assertEqual((self.out / "proofs.jsonl").read_bytes(), before)
        # 4. such a file at the end, however it got there: FAILED with exit code 4, never DONE
        write_jsonl(self.out / "proofs.jsonl", stale)
        r = self.run_lines(kg + end)
        self.assertEqual(r.returncode, 4, r.stdout + r.stderr)
        self.assertIn("FAILED (kernel guard)", r.stdout)
        self.assertNotIn("DONE", r.stdout)

    def test_export_mode_never_ends_well_on_such_a_file(self):
        kg = self.block("kg_file() {", "kg_file() {")
        chk = self.block('  if [ "$DRY" != 1 ] && [ -f "$OUT/proofs.jsonl" ]; then', "  fi")
        self.assertIn("RC=4", chk)
        self.assertLess(self.sh.index("harness/open_package.py export"), self.sh.index(chk))
        self.assertLess(self.sh.index(chk), self.sh.index("# ---", self.sh.index(chk)))
        write_jsonl(self.out / "proofs.jsonl", export_like(self.rs, {self.rs[0]["name"]}))
        r = self.run_lines(kg + chk + 'echo "rc $RC"\n', DRY="0")
        self.assertIn("FAILED (kernel guard)", r.stdout)
        self.assertIn("rc 4", r.stdout)
        write_jsonl(self.out / "proofs.jsonl", export_like(self.rs, set()))
        r = self.run_lines(kg + chk + 'echo "rc $RC"\n', DRY="0")
        self.assertEqual(r.stdout.strip(), "rc 0")

    def test_the_flag_is_passed_on_and_checked_before_anything_starts(self):
        case = self.block('case "${LRA_DEBUG_ROWS:-fail}" in', 'case "${LRA_DEBUG_ROWS:-fail}" in')
        self.assertLess(self.sh.index(case), self.sh.index('\nif [ "$MODE" = check ]; then\n'))   # `run.sh check` reports it too
        for v in ("1", "Reference", "yes", "fail reference"):
            r = self.run_lines(case, LRA_DEBUG_ROWS=v)
            self.assertIn("CHECK FAILED: LRA_DEBUG_ROWS must be fail or reference", r.stdout, v)
        for env in ({}, {"LRA_DEBUG_ROWS": ""}, {"LRA_DEBUG_ROWS": "fail"}, {"LRA_DEBUG_ROWS": "reference"}):
            r = self.run_lines(case, **env)
            self.assertEqual((r.returncode, r.stdout), (0, ""), env)
        extra = self.block('[ -z "${LRA_DEBUG_ROWS:-}" ] || EXTRA+=(--debug-rows', '[ -z "${LRA_DEBUG_ROWS:-}" ] || EXTRA+=(--debug-rows')
        r = self.run_lines("EXTRA=()\n" + extra + 'echo "${EXTRA[*]-}"\n', LRA_DEBUG_ROWS="reference")
        self.assertEqual(r.stdout.strip(), "--debug-rows reference")
        r = self.run_lines("EXTRA=()\n" + extra + 'echo "${EXTRA[*]-}"\n')
        self.assertEqual(r.stdout.strip(), "")
        self.assertIn('snapshot.py --rows "$ROWS" --heartbeats "$HBS" --out "$OUT" "$@" -- ${EXTRA[@]+"${EXTRA[@]}"}', self.sh)


if __name__ == "__main__":
    unittest.main()
