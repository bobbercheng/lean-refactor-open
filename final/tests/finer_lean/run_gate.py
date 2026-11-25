#!/usr/bin/env python3
"""Lean check of the post stage's gate audit (harness/post_audit.py, 2026-11-24) on the library environments, run on demand.

Each fixture (FIXTURES: a library prefix, a candidate, the row's reference proof) is audited, in each environment as a plain file
and, where the library has `module` files, as a `module` file, by the new gate (post_audit.gate_audit, its own readers: the forced
axiom print through scorer.compile.audit_axioms, the reference's reading, the finer readings) and by the gate as published
(open_package.audit_proof with scorer.compile.GATE_MODULE_PRINT off: the skip in `module` files). The package's own compile path is
used, with one change: the compiled file (exactly the text scorer.compile builds) is written to --out, outside the environment, and
compiled there with `lake env lean` from the environment's folder (scorer.compile._lean_in_project and compile_putnam replaced;
file_prefix returns the fixture's prefix). Nothing is written into the environments.

    python3 tests/finer_lean/run_gate.py --envs /path/to/envs --out DIR [--only cslib-v4.31.0,...] [--fixtures G1,G3] [--jobs 2]
                                         [--wrap "systemd-run --user --scope ... --"] [--json OUT]
exit 0: every verdict as expected; 1: some verdict differs; 2: nothing ran."""
from __future__ import annotations

import argparse, json, os, shlex, subprocess, sys, threading, time, uuid
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from unittest import mock

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness import open_package as OPK  # noqa: E402
from harness import post_audit as PA  # noqa: E402
from harness import finer_sorry as FS  # noqa: E402
from scorer import compile as C  # noqa: E402

MOD_HEAD = "module\n\npublic import {imp}\n\npublic section"
ENVS = {   # environment -> the row's source, the plain file's header, the `module` file's header (where the library is built as modules)
    "cslib-v4.31.0": {"source": "cslib", "plain": "import Cslib", "module": MOD_HEAD.format(imp="Cslib")},
    "cslib-v4.30.0": {"source": "cslib", "module": MOD_HEAD.format(imp="Cslib")},   # the first toolchain whose module files print
    "physlib-v4.32.0": {"source": "physlib", "plain": "import Physlib.QFT.PerturbationTheory.WickContraction.Perm",
                        "module": MOD_HEAD.format(imp="Physlib.QFT.PerturbationTheory.WickContraction.Perm")},
    "leanpool-v4.35.0-rc3": {"source": "leanpool", "module": MOD_HEAD.format(imp="LeanPool")},
    "strata-v4.29.1": {"source": "strata", "module": MOD_HEAD.format(imp="Strata.Languages.Laurel.ResolutionProps")},
    "strata-v4.27.0": {"source": "strata", "module": MOD_HEAD.format(imp="Strata.SimpleAPI")},   # the final rows' oldest Strata pin
    "mathlib-v4.27.0": {"source": "putnambench", "plain": "import Mathlib"},
}
LIB = "theorem libSorry : (1 : Nat) = 1 := sorry\n\ntheorem libSorry2 : (2 : Nat) = 2 := sorry\n"
S = "theorem mainT : (1 : Nat) = 1 ∧ True"
S2 = "theorem mainT : (1 : Nat) = 1 ∧ (2 : Nat) = 2"
HOOK = ("\n\n@[command_elab Lean.Parser.Command.printAxioms] private def fakePrint : Lean.Elab.Command.CommandElab := "
        "fun _ => pure ()\n")
# id: (what, library prefix, candidate, reference proof, new gate's verdict, the published gate's (plain, module from v4.30));
# a `module` file before v4.30: both gates read only the sorry message there ("skipped" unless the candidate shows one); the new
# gate compiles the print there too (Lean: an error, no list), and "skipped" needs that reading to be axiom_guard.structural
FIXTURES = {
    "G1": ("clean proof", "", S + " := ⟨rfl, trivial⟩", S + " := by exact ⟨rfl, trivial⟩", "clean", ("clean", "skipped")),
    "G2": ("uses a library lemma proved by sorry (no message on its lines); the reference does not", LIB,
           S + " := ⟨libSorry, trivial⟩", S + " := ⟨rfl, trivial⟩", "sorry", ("sorry", "skipped")),
    "G3": ("its own value is sorryAx with NO Lean message (the library prefix turns warn.sorry off: row 42's observable)",
           LIB + "\nset_option warn.sorry false\n", S + " := ⟨sorryAx _ true, trivial⟩", S + " := ⟨rfl, trivial⟩", "sorry",
           ("sorry", "skipped")),
    "G3m": ("its own value is `sorryAx _ true` (Lean's sorry message)", LIB, S + " := ⟨sorryAx _ true, trivial⟩",
            S + " := ⟨rfl, trivial⟩", "sorry", ("sorry", "sorry")),
    "G4": ("G3's declaration, sound", LIB + "\nset_option warn.sorry false\n", S + " := ⟨rfl, trivial⟩", S + " := ⟨rfl, trivial⟩",
           "clean", ("clean", "skipped")),
    "G5": ("the reference uses libSorry; so does the candidate (finer check: same source)", LIB, S + " := by exact ⟨libSorry, trivial⟩",
           S + " := ⟨libSorry, trivial⟩", "clean", ("clean", "skipped")),
    "G6": ("the reference uses libSorry; the candidate also libSorry2 (finer check: a new source)", LIB, S2 + " := ⟨libSorry, libSorry2⟩",
           S2 + " := ⟨libSorry, rfl⟩", "sorry", ("clean", "skipped")),
    "G7": ("a hook that can fake #print axioms (not compiled by the new gate)", "", S + " := ⟨rfl, trivial⟩" + HOOK,
           S + " := ⟨rfl, trivial⟩", "sorry", None),
}


class Runner:
    """The compile layer: the body scorer.compile builds, written to --out and compiled with `lake env lean` in the environment."""

    def __init__(self, envs: Path, out: Path, wrap: list):
        self.envs, self.out, self.wrap = envs, out, wrap
        self.log: list = []
        self.lk = threading.Lock()
        self.local = threading.local()

    def env_dir(self, source: str, version: str) -> Path:
        return self.envs / ("mathlib-" + version if source == "putnambench" else f"{C.PROJECT_DIRS.get(source, source)}-{version}")

    def lean(self, env_dir: Path, body: str, lean_args, timeout: int, first_line: int, quiet_prefix_sorry=False) -> C.CompileResult:
        f = self.out / f"g_{uuid.uuid4().hex[:12]}.lean"
        f.write_text(body)
        elan = Path(os.environ.get("ELAN_HOME") or Path.home() / ".elan") / "bin"
        env = dict(os.environ, PATH=f"{elan}:{os.environ.get('PATH', '')}")
        cmd = ["timeout", str(min(900, int(timeout) + 30))] + self.wrap + ["lake", "env", "lean", "--json",
                                                                            f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}", *lean_args, str(f)]
        t0 = time.time()
        try:
            p = subprocess.run(cmd, cwd=env_dir, env=env, capture_output=True, text=True, timeout=int(timeout) + 60)
            if p.returncode == 124:
                raise subprocess.TimeoutExpired(cmd, timeout)
        except subprocess.TimeoutExpired:
            r = C.CompileResult(False, None, time.time() - t0, ["timeout"], timed_out=True)
        else:
            r = C._parse(p, time.time() - t0, first_line, sorry_blind=C._warn_sorry_off(lean_args), switch=C._sorry_switch(body, first_line),
                         quiet_prefix_sorry=quiet_prefix_sorry)
        kind = "finer" if FS.MARK in body else "print" if "#print axioms" in body else "plain"
        with self.lk:
            self.log.append({"case": getattr(self.local, "case", None), "gate": getattr(self.local, "gate", None), "kind": kind,
                             "file": f.name, "seconds": round(r.seconds, 1), "ok": r.ok, "timed_out": r.timed_out})
        return r

    def lean_in_project(self, source, version, body, lean_args, timeout, first_line=1, quiet_prefix_sorry=False):
        return self.lean(self.env_dir(source, version), body, lean_args, timeout, first_line, quiet_prefix_sorry)

    def compile_putnam(self, header, declaration, version, *, count=True, timeout=600):
        assert not count, "the audits compile unmeasured"
        first = C._first_line(header.rstrip())
        return self.lean(self.env_dir("putnambench", version), header.rstrip() + "\n\n" + declaration.rstrip() + "\n", (), timeout, first)


def case_row(env: str, variant: str, fid: str) -> tuple[dict, str]:
    """(the row, its file prefix) of one case."""
    e, (_what, lib, _cand, ref, _w, _p) = ENVS[env], FIXTURES[fid]
    version = env.split("-", 1)[1]
    prefix = e[variant] + "\n\nnamespace LRAFix\n\n" + (lib + "\n" if lib else "")
    stmt = ref.split(" :=", 1)[0]
    row = {"name": f"gate/{env}/{variant}/{fid}", "source": e["source"], "statement": stmt, "src": ref, "file_path": "LRAGate.lean",
           "version_info": [{version: "local"}], "header": prefix if e["source"] == "putnambench" else ""}
    return row, prefix


def run_case(runner: Runner, env: str, variant: str, fid: str) -> dict:
    row, _prefix = case_row(env, variant, fid)
    version = env.split("-", 1)[1]
    _what, _lib, cand, _ref, want_new, want_pub = FIXTURES[fid]
    if variant == "module" and not C.prints_in_module(version):
        want_new = "sorry" if fid in ("G3m", "G7") else "skipped"
        want_pub = None if want_pub is None else (None, "sorry" if fid == "G3m" else "skipped")
    out = {"env": env, "variant": variant, "fixture": fid, "version": version, "want_new": want_new}
    runner.local.case = row["name"]
    runner.local.gate = "new"
    n0, t0 = len(runner.log), time.time()
    with mock.patch.object(C, "GATE_MODULE_PRINT", True):
        st, why = PA.gate_audit(row, cand, [version], cache=PA.ReadOnce())
    out.update(new=st, new_why=why[:240], new_s=round(time.time() - t0, 1), new_compiles=len([x for x in runner.log[n0:] if x["case"] == row["name"]]))
    if want_pub is not None:
        runner.local.gate = "published"
        want = want_pub[0] if variant == "plain" else want_pub[1]
        n0, t0 = len(runner.log), time.time()
        with mock.patch.object(C, "GATE_MODULE_PRINT", False):
            pst, pwhy = OPK.audit_proof(row, cand, [version], {})
        out.update(want_published=want, published=pst, published_why=pwhy[:240], published_s=round(time.time() - t0, 1),
                   published_compiles=len([x for x in runner.log[n0:] if x["case"] == row["name"] and x["gate"] == "published"]))
    out["ok"] = out["new"] == want_new and (want_pub is None or out["published"] == out["want_published"])
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--envs", required=True, help="the folder of the library environments (read only)")
    ap.add_argument("--out", required=True, help="a folder outside the environments for the compiled files")
    ap.add_argument("--only", default=None, help="comma-separated environments")
    ap.add_argument("--fixtures", default=None, help="comma-separated fixture ids")
    ap.add_argument("--jobs", type=int, default=2, help="cases at once (each runs its compiles one after the other)")
    ap.add_argument("--wrap", default="", help="a command prefix for every Lean launch (e.g. a systemd-run scope)")
    ap.add_argument("--json", default=None)
    a = ap.parse_args(argv)
    out = Path(a.out).resolve()
    out.mkdir(parents=True, exist_ok=True)
    envs = Path(a.envs).resolve()
    if out == envs or envs in out.parents:
        raise SystemExit("--out must be outside the environments")
    runner = Runner(envs, out, shlex.split(a.wrap))
    only = a.only.split(",") if a.only else list(ENVS)
    fids = a.fixtures.split(",") if a.fixtures else list(FIXTURES)
    cases = [(e, v, f) for e in only if (envs / e).is_dir() for v in ("plain", "module") if v in ENVS[e] for f in fids]
    if not cases:
        print("nothing to run")
        return 2
    prefixes = {case_row(e, v, f)[0]["name"]: case_row(e, v, f)[1] for e, v, f in cases}
    with mock.patch.object(C, "file_prefix", side_effect=lambda row, version: prefixes[row["name"]]), \
            mock.patch.object(C, "project_env_dir", side_effect=runner.env_dir), \
            mock.patch.object(C, "_lean_in_project", side_effect=runner.lean_in_project), \
            mock.patch.object(C, "compile_putnam", side_effect=runner.compile_putnam), \
            mock.patch.dict(os.environ, OPK.SORRY_GUARD_ENV):
        t0 = time.time()
        with ThreadPoolExecutor(max(1, min(2, a.jobs))) as ex:
            res = list(ex.map(lambda c: run_case(runner, *c), cases))
    print(f"{'env':22} {'file':6} {'fx':4} {'want':8} {'new gate':8} {'s':>6} {'n':>2} | {'want':8} {'published':9} {'s':>6} {'n':>2}  ok")
    for r in res:
        print(f"{r['env']:22} {r['variant']:6} {r['fixture']:4} {r['want_new']:8} {r['new']:8} {r['new_s']:6.1f} {r['new_compiles']:2d} | "
              + (f"{r['want_published']:8} {r['published']:9} {r['published_s']:6.1f} {r['published_compiles']:2d}" if "published" in r
                 else f"{'-':8} {'-':9} {'':6} {'':2}") + f"  {'OK' if r['ok'] else 'DIFFERS'}")
    bad = [r for r in res if not r["ok"]]
    for r in bad:
        print(f"DIFFERS {r['env']} {r['variant']} {r['fixture']}: new {r['new']} ({r['new_why']}); published {r.get('published')} ({r.get('published_why')})")
    secs = [x["seconds"] for x in runner.log]
    print(f"{len(res)} cases, {len(res) - len(bad)} as expected; {len(runner.log)} compiles, {min(secs or [0]):.1f}-{max(secs or [0]):.1f} s each; "
          f"{time.time() - t0:.0f} s in all")
    if a.json:
        Path(a.json).write_text(json.dumps({"cases": res, "compiles": runner.log}, indent=1, ensure_ascii=False))
    return 0 if not bad else 1


if __name__ == "__main__":
    raise SystemExit(main())
