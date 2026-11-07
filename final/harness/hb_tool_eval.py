"""Offline, worktree-local evaluator for the opt-in heartbeat tool.




"""
from __future__ import annotations

from contextlib import contextmanager
import fcntl
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import threading
import time
import uuid

from probe.verify_candidates import newest_first
from scorer import compile as compiler
from scorer.forbidden import check_forbidden
from scorer.score import compat_pct, hb_pct_local, len_pct, problem_score
from scorer.tokenize import count_tokens, split_declaration

ROOT = Path(__file__).resolve().parents[1]


SLOTS_DEFAULT = 3
                                                                                                                                     
                                                                                                                                    
                                                                                                                                   
                                                                                                                                  
                                                                                                                     
_LOCAL_SLOTS: dict = {}
_LOCAL_SLOTS_LOCK = threading.Lock()
_LOCAL_SLOTS_WARNED: set = set()


def lock_dir(scratch: Path, env=None) -> Path:
    """Where the slot / memory-gate lock files of `scratch` live: $LRA_LOCK_DIR/s-<sha of scratch> when set, else the scratch."""
    env = os.environ if env is None else env
    base = env.get("LRA_LOCK_DIR")
    if not base:
        return scratch
    import hashlib
    return Path(base).expanduser().resolve() / ("s-" + hashlib.sha256(str(scratch).encode()).hexdigest()[:16])


def local_slots(key: str, n: int, error: OSError) -> threading.BoundedSemaphore:
    """The in-process fallback slot group for `key` (n slots), created on the first flock failure (logged once per key)."""
    with _LOCAL_SLOTS_LOCK:
        if key not in _LOCAL_SLOTS_WARNED:
            _LOCAL_SLOTS_WARNED.add(key)
            import sys
            print(f"[hb_tool_eval] flock unavailable on {key} ({error}); compile slots fall back to an in-process semaphore of {n}",
                  file=sys.stderr, flush=True)
        return _LOCAL_SLOTS.setdefault((key, n), threading.BoundedSemaphore(n))


def compile_slots(env=None) -> int:
    """Physical compiles at once per scratch directory: $LRA_HBTOOL_SLOTS (a positive integer), else SLOTS_DEFAULT (3)."""
    env = os.environ if env is None else env
    try:
        n = int(env.get("LRA_HBTOOL_SLOTS") or SLOTS_DEFAULT)
    except ValueError:
        n = SLOTS_DEFAULT
    return max(1, n)


def load_dataset(rows_path, heartbeats_path) -> tuple[dict, dict]:
    """Read explicit JSONL datasets without changing the pipeline's global rows."""
    rows = {r["name"]: r for line in Path(rows_path).read_text().splitlines()
            if line.strip() for r in [json.loads(line)]}
    heartbeats = {r["name"]: r["heartbeat"]
                  for line in Path(heartbeats_path).read_text().splitlines()
                  if line.strip() for r in [json.loads(line)]}
    return rows, heartbeats


class BoundEvaluator:
    def __init__(self, evaluator: "Evaluator", name: str, versions=None):
        self.evaluator, self.name = evaluator, name
        self.versions = list(versions or evaluator.versions(name))

    def __call__(self, declaration: str, full: bool = False) -> dict:
        return self.evaluator.evaluate(self.name, declaration, self.versions, full)

    def cost(self, full: bool = False) -> int:
        return self.evaluator.cost(self.name, self.versions, full)


class Evaluator:
    """One problem's compile budget; separate instances may share the slot gate.





"""

    def __init__(self, rows: dict, heartbeats: dict, *, max_compiles: int = 60,
                 scratch_root=None, toolchains=None, timeout: int = 900):
        self.rows, self.heartbeats = rows, heartbeats
        self.max_compiles, self.timeout = max_compiles, timeout
                                                                                                                                   
                                                                                                                                
        self.scratch = Path(scratch_root or os.environ.get("LRA_HBTOOL_SCRATCH") or ROOT / "probe/hbtool/.scratch").resolve()
        if not self.scratch.is_relative_to(ROOT):
            raise ValueError("scratch directory must be inside this worktree")
        self.scratch.mkdir(parents=True, exist_ok=True)
        self.lockdir = lock_dir(self.scratch)                                              
        self.lockdir.mkdir(parents=True, exist_ok=True)
        self.toolchains = Path(toolchains).expanduser().resolve() if toolchains else None
        self.compiles = 0
                                                                                                                                      
                                                                                                                         
        self.slot_wait_s = 0.0
        self._count_lock = threading.Lock()
        self._needs_import: set[tuple] = set()
        self._runtime_cache: dict[tuple, tuple] = {}
                                                                              
                                                                               
        spec = importlib.util.spec_from_file_location("_hb_tool_memgate", ROOT / "scorer/memgate.py")
        self._gate = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(self._gate)
        self._gate.LOCK = self.lockdir / "lra-memgate.lock"
        self._gate.LEDGER = self._gate.LOCK.with_suffix(".json")

    def versions(self, name: str) -> list[str]:
        return newest_first(self.rows[name]["version_info"])

    def bound(self, name: str, versions=None) -> BoundEvaluator:
        return BoundEvaluator(self, name, versions)

    def cost(self, name: str, versions=None, full: bool = False) -> int:
        versions = versions or self.versions(name)
        row = self.rows[name]
        primary = 1
        if row["source"] != "putnambench":
            core, _ = compiler.split_modifiers(compiler.file_prefix(row, versions[0]))
            attached = bool(compiler._ATTACHED_IN.search(core))
            key = (row["source"], versions[0], row["file_path"])
            if compiler._with_measure_import(core):
                primary = 2 if key in self._needs_import else 3
            else:
                primary += attached
        return primary + (len(versions) - 1 if full else 0)

    @contextmanager
    def _slot(self):
                                                                                                                               
                                                                                                                                           
                                                                                                  
        handles = [open(self.lockdir / f"compile-slot-{i}.lock", "a+") for i in range(compile_slots())]
        acquired = None
        sem, sem_held = None, False                                                                                   
        t0 = time.monotonic()
        try:
            while acquired is None and sem is None:
                for handle in handles:
                    try:
                        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    except BlockingIOError:
                        continue
                    except OSError as error:                                                                         
                        sem = local_slots(str(self.lockdir), len(handles), error)
                        break
                    acquired = handle
                    break
                if acquired is None and sem is None:
                    time.sleep(0.1)
            if sem is not None:
                sem.acquire(); sem_held = True
            with self._count_lock:
                self.slot_wait_s += time.monotonic() - t0
            yield
        finally:
            if acquired is not None:
                fcntl.flock(acquired, fcntl.LOCK_UN)
            if sem_held:
                sem.release()
            for handle in handles:
                handle.close()

    def _runtime(self, row: dict, version: str) -> tuple[Path, dict]:
        key = (row["source"], version)
        if key in self._runtime_cache:
            return self._runtime_cache[key]
        wd = (compiler.env_dir(version) if row["source"] == "putnambench"
              else compiler.project_env_dir(row["source"], version)).resolve()
        if not wd.is_dir():
            raise FileNotFoundError(f"prepared environment is missing: {wd}")
        pin = (wd / "lean-toolchain").read_text().strip()
        roots = [self.toolchains] if self.toolchains else []
        if os.environ.get("ELAN_HOME"):
            roots.append(Path(os.environ["ELAN_HOME"]) / "toolchains")
        roots.append(Path.home() / ".elan/toolchains")
                                                                             
                                                                        
        roots.extend(p / ".elan/toolchains" for p in wd.parents)
        installed = pin.replace("/", "--").replace(":", "---")
        binary = next((r / installed / "bin/lean" for r in roots
                       if r and (r / installed / "bin/lean").is_file()), None)
        if binary is None:
            raise FileNotFoundError(f"installed toolchain unavailable: {pin}; pass toolchains=")
        binary = binary.resolve()
        libraries = [wd / ".lake/build/lib/lean"]
        manifest_path = wd / "lake-manifest.json"
        manifest = json.loads(manifest_path.read_text()) if manifest_path.exists() else {}
        packages = wd / manifest.get("packagesDir", ".lake/packages")
        if packages.is_dir():
            libraries.extend(p / ".lake/build/lib/lean" for p in sorted(packages.iterdir()))
                                                                          
                                                                               
        for package in manifest.get("packages", []):
            if package.get("subDir"):
                name = str(package["name"]).removeprefix("«").removesuffix("»")
                libraries.append(packages / name / package["subDir"] / ".lake/build/lib/lean")
        libraries = list(dict.fromkeys(p.resolve() for p in libraries if p.is_dir()))
        if not libraries:
            raise FileNotFoundError(f"built Lean libraries are missing: {wd}")
                                                                               
                                                                        
        env = dict(os.environ, LEAN_PATH=os.pathsep.join(str(p) for p in libraries),
                   LEAN_SYSROOT=str(binary.parent.parent))
        self._runtime_cache[key] = binary, env
        return binary, env

    def _run(self, row: dict, version: str, body: str, lean_args=(),
             first_line: int = 1, quiet_prefix_sorry: bool = False):
        binary, env = self._runtime(row, version)
        with self._count_lock:
            if self.compiles >= self.max_compiles:
                return compiler.CompileResult(False, None, 0, ["compile budget exhausted"])
            self.compiles += 1
        path = self.scratch / f"c_{uuid.uuid4().hex}.lean"
        path.write_text(body)
        start = time.monotonic()
        try:
            with self._slot():
                result = self._gate.run_lean(
                    [str(binary), "--json", f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}",
                     *lean_args, str(path)], cwd=self.scratch, env=env,
                    capture_output=True, text=True, timeout=self.timeout)
        except subprocess.TimeoutExpired:
            return compiler.CompileResult(False, None, time.monotonic() - start,
                                          ["timeout"], timed_out=True)
        finally:
            path.unlink(missing_ok=True)
        return compiler._parse(result, time.monotonic() - start, first_line,
                               sorry_blind=compiler._warn_sorry_off(lean_args),
                               switch=compiler._sorry_switch(body, first_line),
                               quiet_prefix_sorry=quiet_prefix_sorry)

    def _compile(self, row: dict, declaration: str, version: str, count=True):
        if row["source"] == "putnambench":
            header = row["header"].rstrip()
            measure = compiler.MEASURE_ELAB + "set_option Elab.async false in\narena_measure\n" if count else ""
            return self._run(row, version, header + "\n\n" + measure + declaration.rstrip() + "\n",
                             first_line=compiler._first_line(header))
        core, modifiers = compiler.split_modifiers(compiler.file_prefix(row, version))
        lean_args = compiler.lakefile_options(row["source"], version)
        quiet = False
        if compiler.force_warn_sorry() and compiler._warn_sorry_off(lean_args):
            lean_args, quiet = compiler._with_warn_sorry(lean_args), True
        plain_body = core.rstrip("\n") + "\n\n" + modifiers + declaration.rstrip() + "\n"

        def plain():
            return self._run(row, version, plain_body, lean_args,
                             compiler._first_line(core), quiet)

        if not count:
            return plain()
        key = (row["source"], version, row["file_path"])
        mcore = (compiler._with_measure_import(core) or core) if key in self._needs_import else core

        def measured(prefix):
            body = (prefix.rstrip("\n") + "\n\n" + compiler.MEASURE_ELAB +
                    "set_option Elab.async false in\narena_measure\n" + modifiers + declaration.rstrip() + "\n")
            return self._run(row, version, body, lean_args, compiler._first_line(prefix), quiet)

        result = measured(mcore)
        if compiler._measure_failed(result, mcore) and mcore is core and compiler._with_measure_import(core):
            mcore = compiler._with_measure_import(core)
            retry = measured(mcore)
            retry.seconds += result.seconds
            result = retry
            if not compiler._measure_failed(result, mcore):
                self._needs_import.add(key)
        if compiler._measure_failed(result, mcore):
            unmeasured = plain()
            unmeasured.seconds += result.seconds
            unmeasured.hb_blind = True
            return unmeasured
        if result.ok and compiler._ATTACHED_IN.search(core):
            unmeasured = plain()
            result.seconds += unmeasured.seconds
            if not unmeasured.ok:
                result.ok, result.timed_out = False, unmeasured.timed_out
                result.errors = [f"(with preceding in modifier) {e}" for e in unmeasured.errors]
        return result

    def evaluate(self, name: str, declaration: str, versions=None, full: bool = False) -> dict:
        row = self.rows[name]
        versions = list(versions or self.versions(name))
        body = split_declaration(declaration.rstrip(), row["statement"])
        if body is None:
            return {"ok": False, "error": "statement differs", "compiles": 0}
        forbidden = check_forbidden(body)
        if forbidden:
            return {"ok": False, "error": f"forbidden: {forbidden}", "compiles": 0}
        start = self.compiles
        try:
            result = self._compile(row, declaration, versions[0])
            out = {"ok": result.ok, "tokens": count_tokens(body), "heartbeats": result.heartbeats,
                   "error": result.errors[0] if result.errors else None,
                   "errors": result.errors, "messages": result.messages, "toolchains": versions,
                   "hb_blind": result.hb_blind, "timed_out": result.timed_out}
            if result.ok:
                L = len_pct(row["proof_length"], out["tokens"])
                H = hb_pct_local(name, result.heartbeats, self.heartbeats.get(name))
                compatibility = {versions[0]: True}
                if full:
                    for version in versions[1:]:
                        compatibility[version] = self._compile(row, declaration, version, count=False).ok
                Z = compat_pct(compatibility) if full else 100.0
                out.update(L=round(L, 2), H=round(H, 2), Z=Z, compat=compatibility,
                           score=problem_score(True, L, H, Z))
        except (OSError, ValueError) as error:
            out = {"ok": False, "error": f"environment: {error}", "toolchains": versions}
        out["compiles"] = self.compiles - start
        return out
