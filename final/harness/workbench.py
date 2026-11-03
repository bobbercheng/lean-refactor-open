#!/usr/bin/env python3
"""One warm Lean process per row: load the row's file prefix once, then check batches of candidate declarations in it (b63 build step 1,

































































"""
from __future__ import annotations

import atexit, json, os, queue, re, signal, subprocess, sys, threading, time, uuid, weakref
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scorer import compile as C              
from scorer.forbidden import check_forbidden, strip_lean_comments              
from scorer.score import hb_pct_local, len_pct              
from scorer.tokenize import count_tokens, split_declaration              
from probe.verify_candidates import newest_first              

MEASURE_HEAD = "set_option Elab.async false in\narena_measure\n"                                                          
SERVE_CMD = "lra_wb_serve"
TIMEOUT_S = 300.0                                                       
LOAD_TIMEOUT_S = 900.0                               
DRAIN_S = 0.25                                                                                                           

                                                                                                                                         
                                                                                                                                        
                                                                                                                                       
                                                           
                                                                                                                                   
                                                                                                                                         
                                                                                                                                   
                                                                                                                     
                                                                                                                                     
                                                                                                                              
                                                                                                                                            
                                                                                                                              
                                                                                                                                     
                      
BOOT_ELAB = r'''{meta}unsafe def lraWbBootU (code req resp : String) (workers : Nat) : Lean.Elab.Command.CommandElabM Unit := do
  let ctx ← read
  let st0 ← get
  Lean.withoutModifyingEnv do
    let stx ← Lean.ofExcept (Lean.Parser.runParserCategory (← Lean.getEnv) `command code)
    Lean.Elab.Command.elabCommand stx
    let n ← Lean.resolveGlobalConstNoOverload (Lean.mkIdent `lraWbServeMain)
    let f ← Lean.evalConst (Lean.Elab.Command.Context → Lean.Elab.Command.State → String → String → Nat → IO Unit) n
    Lean.Elab.Command.liftIO (f ctx st0 req resp workers)

@[implemented_by lraWbBootU] {meta}opaque lraWbBoot (code req resp : String) (workers : Nat) : Lean.Elab.Command.CommandElabM Unit

elab "lra_wb_serve " code:str req:str resp:str workers:num : command =>
  lraWbBoot code.getString req.getString resp.getString workers.getNat

'''

SERVE_MAIN = r'''set_option Elab.async false in
{meta}def _root_.lraWbServeMain (ctx : Lean.Elab.Command.Context) (st0 : Lean.Elab.Command.State) (reqPath respPath : String)
    (workers0 : Nat) : IO Unit := do
  let workers := Nat.max 1 workers0
  let reqH ← IO.FS.Handle.mk reqPath IO.FS.Mode.read
  let respH ← IO.FS.Handle.mk respPath IO.FS.Mode.write
  let send : String → IO Unit := fun s => do
    respH.putStrLn s
    respH.flush
  let watch ← IO.mkRef (#[] : Array (Nat × IO.CancelToken))
  let stop ← IO.mkRef false
  let busy ← IO.mkRef (0 : Nat)
  let dog ← IO.asTask (prio := Task.Priority.dedicated) do
    while !(← stop.get) do
      IO.sleep 20
      let now ← IO.monoMsNow
      let all ← watch.modifyGet fun a => (a, #[])
      let mut keep : Array (Nat × IO.CancelToken) := #[]
      for e in all do
        if e.1 ≤ now then
          e.2.set
        else
          keep := keep.push e
      watch.modify (· ++ keep)
  send (Lean.Json.compress (Lean.Json.mkObj [("ready", Lean.toJson true), ("lean", Lean.toJson Lean.versionString),
    ("workers", Lean.toJson workers)]))
  let mut tasks : Array (Task (Except IO.Error Unit)) := #[]
  repeat
    let line ← reqH.getLine
    if line.isEmpty then break
    let j? := (Lean.Json.parse line).toOption
    if j?.isNone then
      send (Lean.Json.compress (Lean.Json.mkObj [("error", Lean.toJson "bad request")]))
      continue
    let j := j?.getD Lean.Json.null
    let rid : Nat := (j.getObjValAs? Nat "id").toOption.getD 0
    let text : String := (j.getObjValAs? String "text").toOption.getD ""
    let tmo : Nat := (j.getObjValAs? Nat "timeout_ms").toOption.getD 300000
    let fname : String := (j.getObjValAs? String "file").toOption.getD ctx.fileName
    while (← busy.get) ≥ workers do
      IO.sleep 2
    busy.modify (· + 1)
    let tk ← IO.CancelToken.new
    let dl := (← IO.monoMsNow) + tmo
    watch.modify (·.push (dl, tk))
    let inputCtx := Lean.Parser.mkInputContext text fname
    let job : Lean.Elab.Command.CommandElabM (Array Lean.Json) := do
      let mut mps : Lean.Parser.ModuleParserState := {}
      let mut out : Array Lean.Json := #[]
      repeat
        let st ← get
        let scope := st.scopes.head!
        let pmctx : Lean.Parser.ParserModuleContext :=
          { env := st.env, options := scope.opts, currNamespace := scope.currNamespace, openDecls := scope.openDecls }
        let parsed := Lean.Parser.parseCommand inputCtx pmctx mps {}
        let cmd := parsed.1
        mps := parsed.2.1
        for m in parsed.2.2.unreported do
          unless m.isSilent do out := out.push (← m.toJson)
        if Lean.Parser.isTerminalCommand cmd then break
        let pos := cmd.getPos?.getD 0
        modify fun s => { s with messages := {}, traceState := {}, snapshotTasks := #[] }
        let iso ← IO.FS.withIsolatedStreams (isolateStderr := Lean.Core.stderrAsMessages.get scope.opts) <|
          withReader (fun c => { c with cmdPos := pos }) <|
            Lean.Elab.Command.withLoggingExceptions (Lean.Elab.getResetInfoTrees *> Lean.Elab.Command.elabCommandTopLevel cmd)
        let output := iso.1
        let st ← get
        let mut log := st.messages
        if !output.isEmpty then
          log := log.add { fileName := fname, severity := Lean.MessageSeverity.information, pos := inputCtx.fileMap.toPosition pos,
                           data := output }
        for m in log.unreported do
          unless m.isSilent do out := out.push (← m.toJson)
        let tree := Lean.Language.SnapshotTree.mk { diagnostics := Lean.Language.Snapshot.Diagnostics.empty } st.snapshotTasks
        for s in tree.getAll do
          for m in s.diagnostics.msgLog.unreported do
            unless m.isSilent do out := out.push (← m.toJson)
      return out
    let ctx' : Lean.Elab.Command.Context :=
      { ctx with
        fileName := fname, fileMap := inputCtx.fileMap, currRecDepth := 0, cmdPos := 0,
        macroStack := [], quotContext? := none, currMacroScope := Lean.firstFrontendMacroScope, ref := Lean.Syntax.missing,
        snap? := none, cancelTk? := some tk, suppressElabErrors := false }
    let st' : Lean.Elab.Command.State := { st0 with messages := {}, traceState := {}, snapshotTasks := #[] }
    let io : IO Unit := do
      try
        let t0 ← IO.monoMsNow
        let r ← ((job.run ctx').run' st').toBaseIO
        let ms := (← IO.monoMsNow) - t0
        let timedOut ← tk.isSet
        let msgs? := r.toOption
        let fields : List (String × Lean.Json) :=
          if msgs?.isSome then [("msgs", Lean.toJson (msgs?.getD #[]))]
          else [("msgs", Lean.toJson (#[] : Array Lean.Json)), ("exception", Lean.toJson true)]
        send (Lean.Json.compress (Lean.Json.mkObj ([("id", Lean.toJson rid), ("ms", Lean.toJson ms),
          ("timedOut", Lean.toJson timedOut)] ++ fields)))
      finally
        busy.modify (· - 1)
    tasks := tasks.push (← IO.asTask (prio := Task.Priority.dedicated) io)
  for t in tasks do
    discard <| IO.wait t
  stop.set true
  discard <| IO.wait dog
'''


def lean_string(s: str) -> str:
    """`s` as a Lean string literal."""
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n").replace("\t", "\\t") + '"'


def serve_text(module: bool, req: str, resp: str, workers: int) -> str:
    """BOOT_ELAB and the serve command (with SERVE_MAIN inside) for a file whose head ends with MEASURE_ELAB."""
    meta = "meta " if module else ""
    return (BOOT_ELAB.replace("{meta}", meta) + f"{SERVE_CMD} " + lean_string(SERVE_MAIN.replace("{meta}", meta))
            + f' "{req}" "{resp}" {int(workers)}\n')

                                                                                                                                       
                                                                                                                                      
                                                                                                                                    
                                                                              
WARM_CACHE_TACTICS = re.compile(r"(?<![\w.'])(exact\?|apply\?|rw\?\??|rw_search|hint|library_search|try\?)(?![\w'])")
_NEEDS_IMPORT: set = set()                                                                                                                
_LIVE: "weakref.WeakSet[Workbench]" = weakref.WeakSet()


class WorkbenchError(RuntimeError):
    """The process could not be started (environment missing, the prefix cannot define the serve command, load timeout)."""


def _close_all() -> None:
    for wb in list(_LIVE):
        try:
            wb.close()
        except Exception:                
            pass


atexit.register(_close_all)


class Layout:
    """The row's measured layout on one pin (module docstring, "file" / "candidate")."""

    def __init__(self, row: dict, version: str, need_import: bool = False):
        self.row, self.version = row, version
        self.putnam = row["source"] == "putnambench"
        if self.putnam:
            self.core, self.modifiers, self.lean_args, self.quiet = row["header"].rstrip(), "", (), False
            self.attached, self.in_lines, self.module = False, [], False
        else:
            core, self.modifiers = C.split_modifiers(C.file_prefix(row, version))
            lean_args, quiet = C.lakefile_options(row["source"], version), False
            if C.force_warn_sorry() and C._warn_sorry_off(lean_args):
                lean_args, quiet = C._with_warn_sorry(lean_args), True
            self.lean_args, self.quiet = tuple(lean_args), quiet
            self.attached = bool(C._ATTACHED_IN.search(core))
            from harness.batch_screen import strip_in_tail
            self.in_lines = strip_in_tail(core)[1] if self.attached else []
            self.module = bool(C._MODULE_LINE.match(core))
            self.plain_core = core
            if need_import and C._with_measure_import(core):
                core = C._with_measure_import(core)
            self.core = core
        self.need_import = need_import
                                                                                                                               
        self.head = self.core.rstrip("\n") + "\n\n" + C.MEASURE_ELAB
        self.first_line = C._first_line(self.core)
        self.chunk_line0 = self.head.count("\n")                                                                 
        self.serve_line = self.chunk_line0 + 1                                                                                        
        if not self.putnam:
            pc = self.plain_core.rstrip("\n")
            self.plain_first_line = C._first_line(self.plain_core)
            self.plain_line0 = pc.count("\n") + 1 - len(self.in_lines)

    def measured(self, decl: str, max_heartbeats: int | None = None) -> tuple[str, int]:
        """(request text, line offset): the meter's measured tail, optionally under a maxHeartbeats bound (one line before it)."""
        pre = f"set_option maxHeartbeats {int(max_heartbeats)} in\n" if max_heartbeats else ""
        return pre + MEASURE_HEAD + self.modifiers + decl.rstrip() + "\n", self.chunk_line0 - pre.count("\n")

    def measured_body(self, decl: str) -> str:
        return self.head + MEASURE_HEAD + self.modifiers + decl.rstrip() + "\n"

    def plain(self, decl: str) -> tuple[str, int]:
        """(request text, line offset): the meter's unmeasured validity check with the core's `… in` lines attached to the declaration."""
        return "\n".join(self.in_lines) + "\n\n" + self.modifiers + decl.rstrip() + "\n", self.plain_line0

    def plain_body(self, decl: str) -> str:
        return self.plain_core.rstrip("\n") + "\n\n" + self.modifiers + decl.rstrip() + "\n"


class _Proc:
    """One running Lean process: pipes, reader threads, the frontend's prefix messages."""

    def __init__(self, cmd: list, env: dict, cwd: Path, path: Path, text: str, rq_r: int, rq_w: int, rs_r: int, rs_w: int):
        self.path = path
        path.write_text(text)
        self.p = subprocess.Popen(cmd, cwd=cwd, env=env, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                  pass_fds=(rq_r, rs_w), start_new_session=True)
        os.close(rq_r)
        os.close(rs_w)
        self.req = os.fdopen(rq_w, "w", encoding="utf-8", newline="\n")
        self.resp = os.fdopen(rs_r, "r", encoding="utf-8", newline="\n")
        self.q: queue.Queue = queue.Queue()
        self.front: list = []                                                          
        self.front_t = time.monotonic()
        self.err_tail = ""
        self.lock = threading.Lock()
        self.dead = False
        self.readers = [threading.Thread(target=f, daemon=True) for f in (self._read_resp, self._read_out, self._read_err)]
        for t in self.readers:
            t.start()

    def _read_resp(self):
        try:
            for line in self.resp:
                line = line.strip()
                if not line:
                    continue
                try:
                    self.q.put(json.loads(line))
                except json.JSONDecodeError:
                    self.q.put({"error": f"bad response: {line[:200]}"})
        except (OSError, ValueError):
            pass
        self.q.put(None)

    def _read_out(self):
        try:
            for raw in self.p.stdout:
                line = raw.decode("utf-8", "replace").strip()
                if line.startswith("{"):
                    try:
                        m = json.loads(line)
                    except json.JSONDecodeError:
                        continue
                    with self.lock:
                        self.front.append((line, m))
                        self.front_t = time.monotonic()
        except (OSError, ValueError):
            pass

    def _read_err(self):
        try:
            for raw in self.p.stderr:
                with self.lock:
                    self.err_tail = (self.err_tail + raw.decode("utf-8", "replace"))[-8000:]
        except (OSError, ValueError):
            pass

    def send(self, obj: dict) -> bool:
        try:
            self.req.write(json.dumps(obj, ensure_ascii=False) + "\n")
            self.req.flush()
            return True
        except (OSError, ValueError):
            return False

    def rss_mb(self) -> tuple[float | None, float | None]:
        """(VmRSS, VmHWM) of the Lean process in MB."""
        try:
            txt = Path(f"/proc/{self.p.pid}/status").read_text()
        except OSError:
            return None, None
        out = {}
        for k in ("VmRSS", "VmHWM"):
            m = re.search(rf"^{k}:\s+(\d+) kB", txt, re.M)
            out[k] = int(m.group(1)) / 1024 if m else None
        return out["VmRSS"], out["VmHWM"]

    def kill(self, graceful: float = 0.0):
        if self.dead:
            return
        self.dead = True
        try:
            self.req.close()
        except (OSError, ValueError):
            pass
        if graceful > 0:
            try:
                self.p.wait(timeout=graceful)
            except subprocess.TimeoutExpired:
                pass
        if self.p.poll() is None:
            try:
                os.killpg(self.p.pid, signal.SIGKILL)
            except (ProcessLookupError, PermissionError):
                pass
        try:
            self.p.wait(timeout=30)
        except subprocess.TimeoutExpired:
            pass
        for f in (self.resp, self.p.stdout, self.p.stderr):
            try:
                f.close()
            except (OSError, ValueError, AttributeError):
                pass
        self.path.unlink(missing_ok=True)


class Workbench:
    """Module docstring. Not thread-safe: one caller thread at a time (calls are serialised by a lock)."""

    def __init__(self, row: dict, version: str | None = None, *, heartbeats: dict | None = None, workers: int = 2,
                 timeout: float = TIMEOUT_S, grace: float | None = None, scratch=None, max_rss_mb: float | None = None,
                 load_timeout: float = LOAD_TIMEOUT_S, attached_check: bool = True, log=None, start: bool = True):
        self.row, self.name, self.statement = row, row["name"], row["statement"]
        self.version = version or newest_first(row["version_info"])[0]
        self.heartbeats = heartbeats or {}
        self.ref_hb = self.heartbeats.get(self.name)
        self.workers = max(1, int(workers))
        self.timeout, self.grace = float(timeout), grace
        self.max_rss_mb = max_rss_mb
        self.load_timeout = float(load_timeout)
        self.attached_check = attached_check
        self.log = log or (lambda *a, **k: None)
        from harness.hb_tool_eval import Evaluator
        self.scratch = Path(scratch or os.environ.get("LRA_HBTOOL_SCRATCH") or ROOT / "probe/hbtool/.scratch").resolve()
        self._ev = Evaluator({self.name: row}, self.heartbeats, scratch_root=self.scratch)
        self._lock = threading.RLock()
        self._proc: _Proc | None = None
        self._gate = None
        self._lay: Layout | None = None
        self._rid = 0
        self.prefix_lines: list = []                                                                              
        self.prefix_errors: list = []
        self.load_s: float | None = None
        self.loads: list = []                                   
        self.restarts = 0
        self.peak_rss_mb = 0.0
        self.counts = {"checked": 0, "ok": 0, "fail": 0, "timeout": 0, "crash": 0, "rejected": 0, "unknown": 0, "attached_checks": 0}
        self.lean = None
        _LIVE.add(self)
        if start:
            self.start()

                                                                                                                                 
    def __enter__(self):
        if self._proc is None:
            self.start()
        return self

    def __exit__(self, *exc):
        self.close()
        return False

    def info(self) -> dict:
        return {"name": self.name, "pin": self.version, "lean": self.lean, "workers": self.workers, "load_s": self.load_s, "loads": self.loads,
                "restarts": self.restarts, "peak_rss_mb": round(self.peak_rss_mb, 1), "need_import": bool(self._lay and self._lay.need_import),
                "attached": bool(self._lay and self._lay.attached), "prefix_errors": len(self.prefix_errors), "counts": dict(self.counts)}

    @property
    def decl_line0(self) -> int | None:
        """The meter file's line just before the declaration's first line (an error reported at meter-file line L is on line
"""
        lay = self._lay
        return None if lay is None else lay.chunk_line0 + MEASURE_HEAD.count("\n") + lay.modifiers.count("\n")

    def _layout(self, need_import: bool) -> Layout:
        return Layout(self.row, self.version, need_import)

    def start(self) -> dict:
        with self._lock:
            if self._proc is not None:
                return self.info()
            if self.loads:
                self.restarts += 1                                                                                   
            key = (self.row["source"], self.version, self.row.get("file_path"))
            lay = self._layout(key in _NEEDS_IMPORT)
            try:
                self._spawn(lay)
            except WorkbenchError as e:
                if lay.module and not lay.need_import and getattr(e, "measure_failed", False):
                    lay = self._layout(True)
                    self._spawn(lay)
                    _NEEDS_IMPORT.add(key)
                else:
                    raise
            return self.info()

    def _spawn(self, lay: Layout) -> None:
        from scorer import memgate
        if getattr(memgate, "admission_closed", lambda: False)():                                                                            
                                                                                                                                           
                                                                                                                                       
                                                                                                                                 
            raise WorkbenchError("compile admission is closed (the process is ending): no Lean started")
        binary, env = self._ev._runtime(self.row, self.version)
        rq_r, rq_w = os.pipe()
        rs_r, rs_w = os.pipe()
        text = lay.head + serve_text(lay.module, f"/dev/fd/{rq_r}", f"/dev/fd/{rs_w}", self.workers)
        path = self.scratch / f"c_{uuid.uuid4().hex}.lean"
        cmd = [str(binary), "--json", f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}", *lay.lean_args, str(path)]
        if self._gate is None:
            try:
                self._gate = memgate.acquire(label=f"workbench {path.name}")
            except subprocess.TimeoutExpired as e:
                for fd in (rq_r, rq_w, rs_r, rs_w):
                    os.close(fd)
                raise WorkbenchError(f"the memory gate gave up: {e}") from e
        t0 = time.monotonic()
        try:
            proc = _Proc(cmd, env, self.scratch, path, text, rq_r, rq_w, rs_r, rs_w)
        except OSError as e:
            for fd in (rq_r, rq_w, rs_r, rs_w):
                try:
                    os.close(fd)
                except OSError:
                    pass
            self._release_gate()
            raise WorkbenchError(f"cannot start lean: {e}") from e
        try:
            first = proc.q.get(timeout=self.load_timeout)
        except queue.Empty:
            first = "timeout"
        if not isinstance(first, dict) or not first.get("ready"):
            if first != "timeout":
                try:
                    proc.p.wait(timeout=30)                                                                  
                except subprocess.TimeoutExpired:
                    pass
            if proc.p.poll() is not None:
                for t in proc.readers:
                    t.join(timeout=10)
            proc.kill()
            with proc.lock:
                msgs = [m for _, m in proc.front if m.get("severity") == "error"]
            why = "load timeout" if first == "timeout" else f"no ready, exit {proc.p.returncode}, {str(first)[:200]}"
            err = WorkbenchError(f"workbench did not start on {self.version} ({why}): "
                                 + "; ".join(f"{(m.get('pos') or {}).get('line')}: {str(m.get('data'))[:200]}" for m in msgs[:3])
                                 + (f" stderr: {proc.err_tail[-300:]}" if proc.err_tail.strip() else ""))
            err.measure_failed = any((m.get("pos") or {}).get("line", 0) > lay.first_line for m in msgs)
            self._release_gate()
            raise err
                                                                                                            
        t_end = time.monotonic() + 4.0
        while time.monotonic() < t_end:
            with proc.lock:
                quiet = time.monotonic() - proc.front_t
            if quiet >= DRAIN_S:
                break
            time.sleep(0.05)
        self._proc, self._lay, self.lean = proc, lay, first.get("lean")
        self._absorb_prefix()
        self.load_s = round(time.monotonic() - t0, 2)
        self.loads.append(self.load_s)
        self._note_rss()
        self.log(f"[workbench] {self.name} @ {self.version}: ready in {self.load_s}s (lean {self.lean}, workers {self.workers}"
                 f"{', +measure import' if lay.need_import else ''})")

    def _absorb_prefix(self):
        proc, lay = self._proc, self._lay
        with proc.lock:
            front = list(proc.front)
        lines = [(l, m) for l, m in front if ((m.get("pos") or {}).get("line") or 0) < lay.serve_line]
        self.prefix_lines = [l for l, _ in lines]
        self.prefix_errors = [m for _, m in lines if m.get("severity") == "error"]

    def _release_gate(self):
        if self._gate is not None:
            from scorer import memgate
            try:
                memgate.release(self._gate)
            except Exception:                
                pass
            self._gate = None

    def _note_rss(self) -> float | None:
        if self._proc is None:
            return None
        rss, hwm = self._proc.rss_mb()
        for v in (rss, hwm):
            if v:
                self.peak_rss_mb = max(self.peak_rss_mb, v)
        return rss

    def _restart(self, why: str) -> bool:
        self.log(f"[workbench] {self.name}: restart ({why})")
        if self._proc is not None:
            self._proc.kill()
            self._proc = None
        self.restarts += 1
        try:
            self._spawn(self._lay or self._layout(False))
            return True
        except WorkbenchError as e:
            self.log(f"[workbench] {self.name}: restart failed: {e}")
            return False

    def close(self) -> None:
        with self._lock:
            if self._proc is not None:
                self._proc.kill(graceful=3.0)
                self._proc = None
            self._release_gate()

    def __del__(self):
        try:
            self.close()
        except Exception:                
            pass

                                                                                                                                  
    def metrics(self, tokens: int, heartbeats: int, Z: float = 100.0) -> dict:
        """harness/endstage.Meter.metrics: L, H and the unrounded score."""
        L = len_pct(self.row["proof_length"], tokens)
        H = hb_pct_local(self.name, heartbeats, self.ref_hb)
        return {"L": L, "H": H, "score_exact": (L + H + Z) / 3.0}

    def _precheck(self, decl: str) -> tuple[str | None, int | None]:
        body = split_declaration(decl, self.statement)
        if body is None:
            return "statement differs", None
        bad = check_forbidden(body)
        return (f"forbidden: {bad}" if bad else None), count_tokens(body)

    def _parse(self, resp: dict, offset: int, body: str, first_line: int) -> C.CompileResult:
        """scorer.compile._parse over the prefix's messages and the candidate's messages at the meter file's line numbers."""
        lines = list(self.prefix_lines)
        err = False
        for m in resp.get("msgs") or []:
            m = dict(m)
            for k in ("pos", "endPos"):
                if isinstance(m.get(k), dict) and isinstance(m[k].get("line"), int):
                    m[k] = dict(m[k], line=m[k]["line"] + offset)
            err = err or m.get("severity") == "error"
            lines.append(json.dumps(m, ensure_ascii=False))
        if resp.get("exception"):
            err = True
            lines.append(json.dumps({"severity": "error", "pos": {"line": first_line, "column": 0},
                                     "data": "workbench: uncaught exception while elaborating the candidate"}))
        err = err or bool(self.prefix_errors)
        fake = subprocess.CompletedProcess([], 1 if err else 0, "\n".join(lines) + "\n", "")
        lay = self._lay
        return C._parse(fake, float(resp.get("ms") or 0) / 1000.0, first_line, sorry_blind=C._warn_sorry_off(lay.lean_args),
                        switch=C._sorry_switch(body, first_line), quiet_prefix_sorry=lay.quiet)

    def check(self, decls: list[str], *, timeout: float | None = None, max_heartbeats: int | None = None,
              messages: bool = False) -> list[dict]:
        """One reading per declaration, in order (module docstring, "reading"). messages=True: each reading also carries the

"""
        with self._lock:
            if self._proc is None:
                self.start()
            to = float(timeout or self.timeout)
            grace = self.grace if self.grace is not None else max(15.0, 0.25 * to)
            out: list = [None] * len(decls)
            jobs = deque()
            for i, d in enumerate(decls):
                d = (d or "").strip()
                why, tokens = self._precheck(d)
                if why:
                    out[i] = {"status": "rejected", "ok": False, "compiled": None, "tokens": tokens, "heartbeats": None, "error": why,
                              "errors": [why], "meter": "workbench", "pin": self.version}
                    continue
                text, off = self._lay.measured(d, max_heartbeats)
                jobs.append({"i": i, "decl": d, "tokens": tokens, "kind": "measured", "text": text, "off": off, "solo": False,
                             "messages": bool(messages)})
            results = self._run(jobs, to, grace)
            follow = deque()
            for i, job, resp in results:
                r = self._reading(job, resp)
                out[i] = r
                if (self.attached_check and self._lay.attached and r["status"] == "ok"):
                    text, off = self._lay.plain(job["decl"])
                    follow.append(dict(job, kind="plain", text=text, off=off, solo=False))
            if follow:
                for i, job, resp in self._run(follow, to, grace):
                    self.counts["attached_checks"] += 1
                    out[i] = self._attach(out[i], job, resp)
            for r in out:
                self.counts["checked"] += 1
                self.counts[r["status"]] = self.counts.get(r["status"], 0) + 1
            return out

    def measure(self, decl: str, **kw) -> dict:
        return self.check([decl], **kw)[0]

    def paired(self, incumbent: str, decls: list[str], *, meter_hb: int | None = None, **kw) -> dict:
        """The screening protocol (module docstring, "warm"): read the incumbent, read it again (warm), then the candidates. Each ok





"""
        first = self.measure(incumbent, **kw)
        warm = self.measure(incumbent, **kw)
        out = {"incumbent": first, "incumbent_warm": warm, "offset": None, "readings": []}
        if warm.get("status") != "ok" or warm.get("heartbeats") is None:
            out["readings"] = self.check(decls, **kw)
            return out
        base = meter_hb if meter_hb is not None else first.get("heartbeats")
        off = (base - warm["heartbeats"]) if base is not None else 0
        out["offset"] = off
        rs = self.check(decls, **kw)
        for r in rs:
            if r.get("status") == "ok" and r.get("heartbeats") is not None:
                r["d_heartbeats"] = r["heartbeats"] - warm["heartbeats"]
                r["heartbeats_est"] = r["heartbeats"] + off
                r.update(self.metrics(r["tokens"], r["heartbeats_est"]))
        out["readings"] = rs
        return out

    def _reading(self, job: dict, resp: dict | None) -> dict:
        base = {"meter": "workbench", "pin": self.version, "tokens": job["tokens"]}
        if resp is None or resp.get("_status") in ("crash", "unknown", "hard_timeout"):
            st = (resp or {}).get("_status", "unknown")
            status = "timeout" if st == "hard_timeout" else st
            why = {"crash": "the Lean process died on this candidate (alone)", "unknown": "workbench unavailable",
                   "timeout": "timeout (hard deadline; process restarted)"}[status]
            return dict(base, status=status, ok=False, compiled=None, heartbeats=None, error=why, errors=[why],
                        timed_out=status == "timeout", wall=(resp or {}).get("_wall"))
        lay = self._lay
        res = self._parse(resp, job["off"], lay.measured_body(job["decl"]), lay.first_line)
        timed = bool(resp.get("timedOut"))
        ok = bool(res.ok) and res.heartbeats is not None and not timed
        r = dict(base, ok=ok, compiled=bool(res.ok) and not timed, heartbeats=res.heartbeats,
                 error=("timeout" if timed else (res.errors[0][:300] if res.errors else None)), errors=res.errors,
                 warnings=res.warnings, timed_out=timed, seconds=round(float(resp.get("ms") or 0) / 1000.0, 3), wall=resp.get("_wall"))
        if res.ok and res.heartbeats is None and not timed:
            r["error"] = "compiled without a heartbeat reading"
        r["status"] = "ok" if ok else ("timeout" if timed else "fail")
        if WARM_CACHE_TACTICS.search(strip_lean_comments(job["decl"])):
            r["warm_cache_risk"] = True
        if job.get("messages"):
            d0 = self.decl_line0 or 0
            r["messages"] = [dict(m, decl_line=m["pos"]["line"] + job["off"] - d0) for m in (resp.get("msgs") or [])
                             if isinstance(m, dict) and isinstance((m.get("pos") or {}).get("line"), int)]
        if ok:
            r.update(self.metrics(job["tokens"], res.heartbeats), Z=100.0, Z_assumed=True)
        return r

    def _attach(self, r: dict, job: dict, resp: dict | None) -> dict:
        """The meter's second check: a failure there fails the reading (errors prefixed as hb_tool_eval does)."""
        if resp is None or resp.get("_status"):
            r = dict(r, attached_check="unknown")
            return r
        lay = self._lay
        res = self._parse(resp, job["off"], lay.plain_body(job["decl"]), lay.plain_first_line)
        timed = bool(resp.get("timedOut"))
        if res.ok and not timed:
            return dict(r, attached_check="ok")
        errs = [f"(with preceding in modifier) {e}" for e in (res.errors or ["timeout"])]
        out = dict(r, ok=False, compiled=False, status="timeout" if timed else "fail", errors=errs, error=errs[0][:300],
                   timed_out=timed, attached_check="fail")
        for k in ("L", "H", "score_exact", "Z", "Z_assumed"):
            out.pop(k, None)
        return out

    def _run(self, jobs: deque, to: float, grace: float) -> list:
        """Send jobs (at most `workers` in flight; one at a time for suspects after a crash), collect responses; restart on a hard
"""
        done: list = []
        inflight: dict = {}                             
        recycle = False
        while jobs or inflight:
            proc = self._proc
            if proc is None:
                if not self._restart("not running"):
                    for job, _ in list(inflight.values()) + [(j, 0) for j in jobs]:
                        done.append((job["i"], job, {"_status": "unknown"}))
                    return done
                proc = self._proc
            solo = any(j["solo"] for j in jobs) or any(j["solo"] for j, _ in inflight.values())
            cap = 1 if solo else self.workers
            while jobs and len(inflight) < cap and not recycle:
                job = jobs[0]
                if inflight and job["solo"]:
                    break
                self._rid += 1
                if not proc.send({"id": self._rid, "text": job["text"], "timeout_ms": int(to * 1000), "file": str(proc.path)}):
                    break
                jobs.popleft()
                inflight[self._rid] = (job, time.monotonic())
            if recycle and not inflight:
                recycle = False
                if not self._restart(f"rss above {self.max_rss_mb} MB"):
                    continue
                continue
            now = time.monotonic()
            nearest = min((t + to + grace for _, t in inflight.values()), default=now + 1.0)
            try:
                msg = proc.q.get(timeout=max(0.05, min(1.0, nearest - now)))
            except queue.Empty:
                msg = "tick"
            if msg == "tick":
                now = time.monotonic()
                over = [rid for rid, (_, t) in inflight.items() if now > t + to + grace]
                if over:
                    for rid in over:
                        job, t = inflight.pop(rid)
                        done.append((job["i"], job, {"_status": "hard_timeout", "_wall": round(now - t, 3)}))
                    for rid, (job, _) in list(inflight.items()):
                        jobs.appendleft(job)
                    inflight.clear()
                    self._restart("hard timeout")
                continue
            if msg is None:                              
                if inflight:
                    if len(inflight) == 1:                                        
                        rid, (job, t) = next(iter(inflight.items()))
                        done.append((job["i"], job, {"_status": "crash", "_wall": round(time.monotonic() - t, 3)}))
                    else:
                        for rid, (job, _) in list(inflight.items()):
                            jobs.appendleft(dict(job, solo=True))
                    inflight.clear()
                self._proc.kill()
                self._proc = None
                if jobs and not self._restart("process died"):
                    for job in jobs:
                        done.append((job["i"], job, {"_status": "unknown"}))
                    return done
                continue
            rid = msg.get("id")
            if rid not in inflight:
                continue
            job, t = inflight.pop(rid)
            msg["_wall"] = round(time.monotonic() - t, 3)
            done.append((job["i"], job, msg))
            rss = self._note_rss()
            if self.max_rss_mb and rss and rss > self.max_rss_mb and (jobs or inflight):
                recycle = True
        return done


                                                                                                                                    
def _load_jsonl(path) -> list:
    return [json.loads(l) for l in Path(path).read_text().splitlines() if l.strip()]


def main(argv=None) -> int:
    import argparse
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--rows", required=True)
    ap.add_argument("--name", required=True)
    ap.add_argument("--heartbeats")
    ap.add_argument("--decls", required=True, help="JSON: a list of declarations or {key: declaration}")
    ap.add_argument("--version")
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--timeout", type=float, default=TIMEOUT_S)
    ap.add_argument("--max-heartbeats", type=int)
    a = ap.parse_args(argv)
    rows = {r["name"]: r for r in _load_jsonl(a.rows)}
    hbs = {r["name"]: r["heartbeat"] for r in _load_jsonl(a.heartbeats)} if a.heartbeats else {}
    d = json.loads(Path(a.decls).read_text())
    keys, decls = (list(d.keys()), list(d.values())) if isinstance(d, dict) else (list(range(len(d))), list(d))
    with Workbench(rows[a.name], a.version, heartbeats=hbs, workers=a.workers, timeout=a.timeout,
                   log=lambda s: print(s, file=sys.stderr, flush=True)) as wb:
        t0 = time.monotonic()
        rs = wb.check(decls, max_heartbeats=a.max_heartbeats)
        wall = time.monotonic() - t0
        for k, r in zip(keys, rs):
            print(json.dumps({"key": k, **{x: r.get(x) for x in ("status", "tokens", "heartbeats", "seconds", "wall", "error")}},
                             ensure_ascii=False))
        print(json.dumps({"info": wb.info(), "batch_wall_s": round(wall, 2)}), flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
