"""prefix_backend (postfast, 2026-11-05; post-hoc measurement tooling, not what produced any upload): prefix-reuse compile servers.

Every compile body the evaluator builds is <file prefix> + blank line + <candidate part> (scorer/compile.py: `_first_line` is the blank
line). The prefix (imports + every declaration before the candidate) is the same for every candidate of a (row, pin), and elaborating it
is most of a compile (ArkLib 2.5 of 3.2 s, PhysLib 18 of 26 s, PutnamBench 2.9 of 5.2 s).

One server per (lean binary, LEAN_PATH, LEAN_SYSROOT, lean args incl. -M, sha256 of the prefix) elaborates the prefix once, exactly as
`lean --json <args> file` would (prefix_server/driver.lean.in, one rendering per toolchain API group, compiled per toolchain with
`lean -c` + gcc and linked against the toolchain's own shared libraries, as bin/lean is), then serves requests by fork(): the child
elaborates the rest of the file from the post-prefix state with the stock frontend functions and writes the JSON message stream a
fresh `lean --json` prints (prefix messages included, same order) plus a sentinel with the exit status; the parent never elaborates a
candidate, so no request can see another's state (measured: a long-lived in-process server drifts, e.g. nlinarith 1284 -> 1269
heartbeats on its 2nd request; a process-global cache of interpreted code, not reset by re-import or new threads; fork fixes it).
The last K=2 prefix commands are re-parsed against each request's text, so a candidate that changes how the prefix's last command
parses (`set_option ... in` before the theorem, a leading comment) resumes from before that command.
Validated 2026-11-05 on VM2 (prefix_validate.py): 9 rows x 2 pins, 8 toolchains v4.26-v4.35-rc3, export proofs x3 per server, a broken
candidate, an options probe: raw stdout identical to a fresh compile of the same file (same module name), heartbeats identical.
Memory per server = what a fresh compile of the prefix holds (private 0.13-1.5 GB; olean mmaps shared through the page cache); a child
adds only its own allocations (copy-on-write).

Two front ends share one Pool:
  install(HE, C, ...)  for fast_post.py: wraps the CURRENT HE.Evaluator._run (fast_post's patched one); eligible compiles go to a
                       server, everything else runs the wrapped _run unchanged;
  run(req)             for pf_svc.py --backend: a Lean launch request -> result dict, or None ("not handled": the service compiles fresh).
  fast_post_prefix.py  runs fast_post.py unchanged with install() hooked in right after fast_post's own _run patch.
Falls back to the fresh compile on: unknown toolchain, lean args other than -M / -D, no C compiler, a prefix that does not end in the
blank line, server start failure (twice per key -> fresh for that key for good), a lost child (crash, no sentinel), pool full.
A timed-out request kills its child (SIGKILL, pid checked to still be the server's child); a server that stops answering is killed;
idle servers are evicted least-recently-used beyond the caps; servers exit when the Python process goes (stdin EOF), their children
with them (PR_SET_PDEATHSIG).

Environment knobs (install() keyword arguments override): LRA_PREFIX_DISABLE=1, LRA_PREFIX_ROOT (build + server dirs), LRA_PREFIX_MAX_SERVERS
(default 48), LRA_PREFIX_MAX_ANON_MB (sum of the servers' private memory, default 40% of MemTotal), LRA_PREFIX_START_TIMEOUT (s, default 900),
LRA_PREFIX_CHARGE (default 1: a request is charged the server's measured header + prefix time, in its reported seconds and against its
timeout, so time-dependent gates and timeouts see fresh-compile-equivalent numbers; 0: real request time only), LRA_PREFIX_MODE
(native | dynlib; default native, dynlib = `lean --run` of the driver, used automatically when the native build fails).
"""
from __future__ import annotations

import atexit, hashlib, json, os, re, select, shutil, signal, subprocess, sys, threading, time, uuid
from collections import Counter, OrderedDict
from pathlib import Path

HERE = Path(__file__).resolve().parent / "prefix_server"
# ---------------------------------------------------------------------------------------------------------- driver rendering
# Toolchain API groups (checked against each toolchain's sources, 2026-11-05):
#   v4.26: processHeaderCore without `package?`; `module` keyword check by hand; -D via typed KVMap.insert;
#   v4.27: + `package?` argument, Language.Lean.setOption; v4.30: Options.set (Options no longer a KVMap);
#   v4.31: + headerStx? / origHeaderStx?; v4.33+: doElab / parseCmd take the previous commands (`cmds`, module linters at EOF).
GROUPS = {"v4.26.0": "G26", "v4.27.0": "G27", "v4.30.0": "G30", "v4.31.0": "G31",
          "v4.33.1": "G33", "v4.34.0": "G33", "v4.34.1": "G33", "v4.35.0-rc3": "G33"}
K = 2   # prefix commands re-parsed against each request's text (a candidate can only change how the LAST one parses: `... in`)
_SET_KNOWN_26 = '''    match decl.defValue with
    | .ofBool _ =>
      if val == "true" then return KVMap.insert opts name (.ofBool true)
      else if val == "false" then return KVMap.insert opts name (.ofBool false)
      else throw <| .userError s!"invalid -D parameter, invalid configuration option '{name}' value, it must be true/false"
    | .ofNat _ => return KVMap.insert opts name (.ofNat val.toNat!)
    | .ofString _ => return KVMap.insert opts name (.ofString val)
    | _ => throw <| .userError s!"invalid -D parameter, configuration option '{name}' cannot be set in the command line"'''
_SET_KNOWN = "    Language.Lean.setOption opts decl name val"
_UNK_KV = "    return KVMap.insert opts name (.ofString val)"
_UNK_SET = "    return opts.set name val"
_MAX_KV = "  KVMap.insert opts `max_memory (.ofNat n)"
_MAX_SET = "  opts.set `max_memory n"
_PH_26 = '''  if mainModuleName.getRoot ∈ [`Init, `Std, `Lean, `Lake, `LakeMain] then
    hopts := Language.Lean.experimental.module.setIfNotSet hopts true
  if !trimmed.raw[0].isNone && !Language.Lean.experimental.module.get hopts then
    throw <| IO.Error.userError "`module` keyword is experimental and not enabled here"
  let (headerEnv, msgLog) ← Elab.processHeaderCore (leakEnv := true)
    trimmed.startPos trimmed.imports trimmed.isModule opts .empty ictx trustLevel #[] mainModuleName {}'''
_PH_27 = '''  let (headerEnv, msgLog) ← Elab.processHeaderCore (leakEnv := true)
    trimmed.startPos trimmed.imports trimmed.isModule opts .empty ictx trustLevel #[] mainModuleName none {}'''
_PH_31 = _PH_27 + "\n    (headerStx? := trimmed) (origHeaderStx? := origStx)"
_DO_OLD = "doElabP stx st beginPos bundle cancelTk"
_DO_NEW = "doElabP stx cmds st beginPos bundle cancelTk"
_RQ_OLD = "      let t ← processCommands ictx ps st"
_RQ_NEW = '''      let prom ← IO.Promise.new
      let tk ← IO.CancelToken.new
      ((parseCmdP none ps st prom true tk cmds).run none |>.run { ictx with } : BaseIO Unit)
      let t := prom.result!'''
_SNIP = {
    "G26": dict(SET_KNOWN=_SET_KNOWN_26, SET_UNKNOWN=_UNK_KV, SET_MAXMEM=_MAX_KV, PROCESS_HEADER=_PH_26, DOELAB=_DO_OLD, REQUEST=_RQ_OLD),
    "G27": dict(SET_KNOWN=_SET_KNOWN, SET_UNKNOWN=_UNK_KV, SET_MAXMEM=_MAX_KV, PROCESS_HEADER=_PH_27, DOELAB=_DO_OLD, REQUEST=_RQ_OLD),
    "G30": dict(SET_KNOWN=_SET_KNOWN, SET_UNKNOWN=_UNK_SET, SET_MAXMEM=_MAX_SET, PROCESS_HEADER=_PH_27, DOELAB=_DO_OLD, REQUEST=_RQ_OLD),
    "G31": dict(SET_KNOWN=_SET_KNOWN, SET_UNKNOWN=_UNK_SET, SET_MAXMEM=_MAX_SET, PROCESS_HEADER=_PH_31, DOELAB=_DO_OLD, REQUEST=_RQ_OLD),
    "G33": dict(SET_KNOWN=_SET_KNOWN, SET_UNKNOWN=_UNK_SET, SET_MAXMEM=_MAX_SET, PROCESS_HEADER=_PH_31, DOELAB=_DO_NEW, REQUEST=_RQ_NEW),
}
MEASURE_MARK = '\n\nopen Lean Elab Command in\nelab "arena_measure " cmd:command : command => do\n'   # scorer/compile.py MEASURE_ELAB


def render(group: str) -> str:
    s = (HERE / "driver.lean.in").read_text().replace("@@GROUP@@", group).replace("@@K@@", str(K))
    for k, v in _SNIP[group].items():
        s = s.replace("@@" + k + "@@", v)
    if "@@" in s:
        raise RuntimeError(f"unrendered placeholder near {s[s.index('@@') - 40:s.index('@@') + 40]!r}")
    return s


def toolchain_version(binary: Path) -> str:
    name = Path(binary).resolve().parent.parent.name     # leanprover--lean4---v4.27.0
    return name.split("---")[-1] if "---" in name else name


class ServerError(Exception):
    """The server path cannot answer this compile: run it fresh."""


class CompileTimeout(Exception):
    pass


def _env_int(name, default):
    try:
        return int(os.environ.get(name, "") or default)
    except ValueError:
        return default


def _meminfo_mb(key="MemTotal") -> int:
    try:
        with open("/proc/meminfo") as f:
            for line in f:
                if line.startswith(key + ":"):
                    return int(line.split()[1]) // 1024
    except OSError:
        pass
    return 0


def proc_mem_mb(pid: int, rollup: bool = False) -> dict:
    """VmRSS / RssAnon / RssFile (/proc/pid/status) and, with rollup, Pss / Pss_Anon / Pss_File / Shared_Clean (smaps_rollup), in MB."""
    out = {}
    try:
        with open(f"/proc/{pid}/status") as f:
            for line in f:
                k, _, v = line.partition(":")
                if k in ("VmRSS", "RssAnon", "RssFile", "VmHWM"):
                    out[k] = int(v.split()[0]) // 1024
        if rollup:
            with open(f"/proc/{pid}/smaps_rollup") as f:
                for line in f:
                    k, _, v = line.partition(":")
                    if k in ("Pss", "Pss_Anon", "Pss_File", "Shared_Clean", "Shared_Dirty", "Private_Dirty"):
                        out[k] = int(v.split()[0]) // 1024
    except (OSError, ValueError, IndexError):
        pass
    return out


class _Sampler:
    """Peak memory of a running child (validation only: Pool.sample_children)."""

    def __init__(self, pid: int):
        self.pid, self.peak, self.ev = pid, {}, threading.Event()
        self.th = threading.Thread(target=self._loop, daemon=True)
        self.th.start()

    def _loop(self):
        while not self.ev.is_set():
            m = proc_mem_mb(self.pid, rollup=True)
            for k, v in m.items():
                self.peak[k] = max(v, self.peak.get(k, 0))
            self.ev.wait(0.25)

    def stop(self):
        self.ev.set()
        self.th.join(2)


class _Lines:
    """Line reader with deadlines over a pipe fd (the server's stdout)."""

    def __init__(self, fd: int):
        self.fd, self.buf = fd, b""
        # selfix (POST-HOC 2026-11-05): poll(), not select(): select() raises "filedescriptor out of range" for fd >= 1024
        # (FD_SETSIZE), which a host with 60 rows reaches; every such server start failed and its compiles ran fresh.
        self.po = select.poll()
        self.po.register(fd, select.POLLIN | select.POLLHUP | select.POLLERR)

    def readline(self, deadline: float) -> str:
        while b"\n" not in self.buf:
            left = deadline - time.monotonic()
            if left <= 0:
                raise TimeoutError("server did not answer in time")
            r = self.po.poll(max(1, int(min(left, 5.0) * 1000)))
            if r:
                b = os.read(self.fd, 65536)
                if not b:
                    raise EOFError("server closed its stdout")
                self.buf += b
        line, _, self.buf = self.buf.partition(b"\n")
        return line.decode("utf-8", "replace")


# ---------------------------------------------------------------------------------------------------------- builds
class Builds:
    """Per toolchain, built once: (group, mode, command prefix). mode "native": driver.lean compiled with `lean -c` and linked against
    the toolchain's shared libraries (the libraries bin/lean uses), one Lean environment per server; mode "dynlib" (if the native
    build fails): `lean --load-dynlib=psrv.so -M<mb> --run driver.lean` (the driver's own `import Lean` adds ~1.7 GB private memory per
    server). None when the toolchain is not in GROUPS or nothing builds (those compiles run fresh). LRA_PREFIX_MODE=dynlib forces it."""

    def __init__(self, root: Path, log):
        self.root, self.log, self.lock, self.done = root, log, threading.Lock(), {}

    def _run(self, cmd, cwd, env=None, timeout=600):
        p = subprocess.run([str(c) for c in cmd], cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
        if p.returncode != 0:
            raise RuntimeError(f"{Path(str(cmd[0])).name} exit {p.returncode}: {(p.stdout + p.stderr)[-600:]}")

    def get(self, binary: Path):
        binary = Path(binary).resolve()
        tc = binary.parent.parent
        group = GROUPS.get(toolchain_version(binary))
        if group is None:
            return None
        with self.lock:
            if tc.name in self.done:
                return self.done[tc.name]
            res, d = None, self.root / "build" / tc.name
            try:
                d.mkdir(parents=True, exist_ok=True)
                tag = uuid.uuid4().hex[:8]
                drv = d / "driver.lean"
                tmp = d / f"driver.{tag}.tmp"
                tmp.write_text(render(group))
                tmp.replace(drv)
                cc = os.environ.get("CC") or shutil.which("gcc") or shutil.which("cc")
                if not cc:
                    raise RuntimeError("no C compiler (gcc/cc)")
                inc, lib = tc / "include", tc / "lib" / "lean"
                env = {k: v for k, v in os.environ.items() if k not in ("LEAN_PATH", "LEAN_SYSROOT")}
                if os.environ.get("LRA_PREFIX_MODE", "native") == "native":
                    try:
                        t0 = time.monotonic()
                        self._run([binary, "-c", f"driver.{tag}.c", "driver.lean"], d, env)
                        self._run([cc, "-O2", "-fPIC", "-I", inc, "-c", f"driver.{tag}.c", "-o", f"driver.{tag}.o"], d)
                        self._run([cc, "-O2", "-fPIC", "-DPSRV_NATIVE", "-I", inc, "-c", HERE / "psrv.c", "-o", f"psrv_native.{tag}.o"], d)
                        libs = [f"-l{n}" for n in ("Init_shared", "leanshared_2", "leanshared_1", "leanshared") if (lib / f"lib{n}.so").is_file()]
                        self._run([cc, "-o", f"driver.{tag}", f"driver.{tag}.o", f"psrv_native.{tag}.o", "-L", lib, *libs, f"-Wl,-rpath,{lib}",
                                   "-lpthread", "-ldl", "-lm"], d)
                        (d / f"driver.{tag}").replace(d / "driver")
                        res = (group, "native", [str(d / "driver")])
                        self.log(f"prefix: native driver for {tc.name} built in {time.monotonic() - t0:.1f}s")
                    except Exception as e:  # noqa: BLE001
                        self.log(f"prefix: native driver build for {tc.name} failed ({type(e).__name__}: {str(e)[:300]}); using --run")
                if res is None:
                    tso = d / f"psrv.{tag}.so"
                    self._run([cc, "-O2", "-shared", "-fPIC", "-I", inc, "-o", tso, HERE / "psrv.c"], d)
                    tso.replace(d / "psrv.so")
                    res = (group, "dynlib", [str(binary), f"--load-dynlib={d / 'psrv.so'}", "-M{mem}", "--run", str(drv)])
            except Exception as e:  # noqa: BLE001
                self.log(f"prefix: build for {tc.name} failed ({type(e).__name__}: {str(e)[:300]}); fresh compiles for it")
                res = None
            self.done[tc.name] = res
            return res


# ---------------------------------------------------------------------------------------------------------- one server
class Server:
    def __init__(self, pool: "Pool", plan: dict):
        self.pool, self.key, self.plan = pool, plan["key"], plan
        self.lock = threading.Lock()          # one request line / reply at a time on the server's pipes
        self.ready = threading.Event()
        self.error: BaseException | None = None
        self.proc: subprocess.Popen | None = None
        self.inflight = self.uses = 0
        self.dead = False
        self.charge_s = self.ready_s = self.header_s = self.prefix_s = 0.0
        self.ncmds = 0
        self.mem: dict = {}

    def start(self, timeout: float) -> None:
        group, self.mode, cmd = self.plan["build"]
        self.dir = self.pool.root / "srv" / f"s_{uuid.uuid4().hex[:12]}"
        self.dir.mkdir(parents=True, exist_ok=True)
        self.pf = self.dir / f"c_{uuid.uuid4().hex}.lean"      # a fresh compile's name shape: same main-module name length
        self.pf.write_text(self.plan["prefix"])
        self.pf_json = json.dumps(str(self.pf))
        self.group = group
        t0 = time.monotonic()
        with open(self.dir / "stderr.log", "w") as err:
            self.proc = subprocess.Popen([c.replace("{mem}", self.plan["mem"]) for c in cmd],
                                         cwd=self.dir, env=self.plan["env"], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=err,
                                         start_new_session=True)
        self.out = _Lines(self.proc.stdout.fileno())
        try:
            self._send({"prefix": str(self.pf), "args": self.plan["args"]})
            rep = json.loads(self.out.readline(t0 + timeout))
        except (OSError, TimeoutError, EOFError, ValueError) as e:
            self.kill()
            raise ServerError(f"start: {type(e).__name__}: {e}"[:300])
        if rep.get("__psrv__") != "ready":
            self.kill()
            raise ServerError(f"start: {rep.get('error', rep)}"[:400])
        self.ready_s = time.monotonic() - t0
        self.header_s, self.prefix_s = rep.get("header_ms", 0) / 1000.0, rep.get("prefix_ms", 0) / 1000.0
        self.charge_s = self.header_s + self.prefix_s
        self.ncmds = rep.get("n", 0)
        self.mem = proc_mem_mb(self.proc.pid)

    def _send(self, obj) -> None:
        self.proc.stdin.write((json.dumps(obj) + "\n").encode())
        self.proc.stdin.flush()

    def _child_alive(self, pid: int) -> bool:
        """pid is still OUR server's child (never signal a recycled pid)."""
        try:
            with open(f"/proc/{pid}/stat") as f:
                st = f.read()
            return int(st.rsplit(")", 1)[1].split()[1]) == self.proc.pid
        except (OSError, ValueError, IndexError):
            return False

    def _kill_child(self, pid: int) -> None:
        if self._child_alive(pid):
            try:
                os.kill(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass

    def request(self, path: Path, file_name: str, timeout: float):
        """-> (stdout text as `lean --json` prints it for file_name, exit code, seconds). CompileTimeout: the compile timed out (the
        child is killed); ServerError: no answer (run it fresh)."""
        rid = uuid.uuid4().hex[:12]
        fifo = self.dir / f"r_{rid}.fifo"
        os.mkfifo(fifo, 0o600)
        fd = os.open(fifo, os.O_RDONLY | os.O_NONBLOCK)
        t0, sampler = time.monotonic(), None
        try:
            with self.lock:
                if self.dead:
                    raise ServerError("server closed")
                try:
                    self._send({"id": rid, "path": str(path), "fileName": file_name, "fifo": str(fifo)})
                    rep = json.loads(self.out.readline(time.monotonic() + 120))
                except (OSError, TimeoutError, EOFError, ValueError) as e:
                    self.kill()
                    raise ServerError(f"request: {type(e).__name__}: {e}"[:300])
            if rep.get("__psrv__") != "forked" or rep.get("id") != rid:
                raise ServerError(f"request: {rep}"[:300])
            pid = int(rep["pid"])
            sampler = _Sampler(pid) if self.pool.sample_children else None
            buf = bytearray()
            po = select.poll()
            po.register(fd, select.POLLIN | select.POLLHUP)
            deadline, connected, last_check = t0 + timeout, False, t0
            while True:
                now = time.monotonic()
                if now >= deadline:
                    self._kill_child(pid)
                    raise CompileTimeout()
                ev = po.poll(max(1, min(1000, int((deadline - now) * 1000))))
                if ev:
                    try:
                        b = os.read(fd, 1 << 20)
                    except BlockingIOError:
                        continue
                    if b:
                        buf += b
                        connected = True
                        continue
                    break                                  # end of file: the child closed (exited)
                if not connected and now - last_check >= 2.0:
                    last_check = now
                    if not self._child_alive(pid):          # died before opening the FIFO
                        raise ServerError("request: the child exited without output")
        finally:
            os.close(fd)
            try:
                fifo.unlink()
            except OSError:
                pass
            if sampler is not None:
                sampler.stop()
        secs = time.monotonic() - t0
        text = buf.decode("utf-8", "replace")
        k = text.rfind('\n{"__psrv__":"exit","code":')
        if k >= 0 and text.endswith("}\n"):
            # the child left through exit() (runAndReport's `maxErrors` stop): what it printed, and lean's exit status
            sent = dict(json.loads(text[k + 1:]), resume=None, n=self.ncmds)
            out = text[:k]
        else:
            body, _, last = text.rstrip("\n").rpartition("\n")
            if not last.startswith('{"__psrv__"'):
                self._keep_lost(rid, path, text)
                raise ServerError("request: no sentinel (the child crashed or was killed)")
            try:
                sent = json.loads(last)
            except ValueError:
                raise ServerError("request: bad sentinel")
            if sent.get("__psrv__") != "done":
                raise ServerError(f"request: {sent.get('error', sent)}"[:300])
            out = body + "\n" if body else ""
        if sampler is not None:
            sent["child_mem"] = sampler.peak
        # cached prefix messages carry the prefix file's name; a fresh compile names the compiled file
        out = out.replace('"fileName":' + self.pf_json, '"fileName":' + json.dumps(file_name))
        return out, int(sent["code"] if "code" in sent else sent.get("exit", 1)), secs, sent

    def _keep_lost(self, rid: str, path: Path, text: str) -> None:
        """Diagnostics for a request that ended without a sentinel: its file and output, in the server directory."""
        try:
            (self.dir / f"lost_{rid}.lean").write_text(Path(path).read_text())
            (self.dir / f"lost_{rid}.out").write_text(text[-200000:])
        except OSError:
            pass

    def kill(self) -> None:
        self.dead = True
        if self.proc is not None and self.proc.poll() is None:
            try:
                self.proc.kill()
            except ProcessLookupError:
                pass
            try:
                self.proc.wait(10)
            except subprocess.TimeoutExpired:
                pass

    def close(self) -> None:
        with self.lock:
            self.dead = True
            if self.proc is None:
                return
            try:
                self.proc.stdin.close()
                self.proc.wait(20)
            except (OSError, subprocess.TimeoutExpired):
                self.kill()


# ---------------------------------------------------------------------------------------------------------- the pool
class Pool:
    def __init__(self, root: Path, max_servers: int, max_anon_mb: int, start_timeout: float, charge_prefix: bool, log):
        self.root, self.max_servers, self.max_anon_mb = Path(root), max_servers, max_anon_mb
        self.start_timeout, self.charge_prefix, self.log = start_timeout, charge_prefix, log
        self.root.mkdir(parents=True, exist_ok=True)
        self.builds = Builds(self.root, log)
        self.lock = threading.Lock()
        self.servers: OrderedDict = OrderedDict()
        self.failed: Counter = Counter()
        self.cores: dict = {}          # run(req) mode: known prefixes per (binary, LEAN_PATH, args) for unmeasured bodies
        self.counts: Counter = Counter()
        self.secs: Counter = Counter()
        self.enabled = True
        self.sample_children = False
        self.tl = threading.local()    # .last: the last server answer of this thread (validation / diagnostics)

    def stat(self, k, n=1):
        with self.lock:
            self.counts[k] += n

    # ---- what a compile needs
    def plan(self, binary, env: dict, lean_args, mem: str, body: str, first_line: int | None):
        """(plan, None) or (None, reason)."""
        if not self.enabled:
            return None, "disabled"
        build = self.builds.get(Path(binary))
        if build is None:
            return None, "toolchain"
        args = [["M", str(mem)]]
        for a in lean_args:
            m = re.fullmatch(r"-D([^=\s]+)=(.*)", a, re.S)
            if not m:
                return None, "args"
            args.append(["D", m.group(1), m.group(2)])
        if first_line is None:
            prefix = self._detect_prefix(binary, env, args, body)
            if prefix is None:
                return None, "prefix"
        else:
            lines = body.split("\n")
            if first_line < 2 or first_line >= len(lines) or lines[first_line - 1] != "":
                return None, "prefix"
            prefix = "\n".join(lines[:first_line]) + "\n"
        if not prefix.strip():
            return None, "prefix"
        key = (str(binary), env.get("LEAN_PATH", ""), env.get("LEAN_SYSROOT", ""), json.dumps(args), hashlib.sha256(prefix.encode()).hexdigest())
        if self.failed[key] >= 2:
            return None, "failed"
        return dict(key=key, binary=Path(binary), env=dict(env), args=args, mem=str(mem), prefix=prefix, build=build), None

    def _detect_prefix(self, binary, env, args, body):
        ck = (str(binary), env.get("LEAN_PATH", ""), json.dumps(args))
        i = body.find(MEASURE_MARK)
        if i >= 0:
            prefix = body[:i + 2]
            with self.lock:
                self.cores.setdefault(ck, set()).add(prefix)
            return prefix
        with self.lock:
            known = [p for p in self.cores.get(ck, ()) if body.startswith(p)]
        return max(known, key=len) if known else None

    # ---- servers
    def _anon_total(self) -> int:
        return sum(s.mem.get("RssAnon", 0) for s in self.servers.values() if s.ready.is_set() and not s.dead)

    def _fits(self) -> bool:
        return len(self.servers) < self.max_servers and self._anon_total() < self.max_anon_mb

    def _make_room(self) -> bool:
        """Under self.lock: evict least recently used idle servers until a new one fits; False if it cannot (the compile runs fresh)."""
        for k in list(self.servers):
            if self._fits():
                return True
            s = self.servers[k]
            if s.inflight == 0 and s.ready.is_set():
                del self.servers[k]
                self.counts["evicted"] += 1
                threading.Thread(target=s.close, daemon=True).start()
        return self._fits()

    def server(self, plan, slot=None, gate=None):
        """(ready server with inflight += 1, seconds this call waited for it, started here?). ServerError when unavailable."""
        key, t0 = plan["key"], time.monotonic()
        with self.lock:
            srv = self.servers.get(key)
            if srv is not None and srv.dead:
                del self.servers[key]
                srv = None
            if srv is not None:
                self.servers.move_to_end(key)
                srv.inflight += 1
                starter = False
            else:
                if not self._make_room():
                    self.counts["fallback_pool_full"] += 1
                    raise ServerError("pool full")
                srv = Server(self, plan)
                srv.inflight += 1
                self.servers[key] = srv
                starter = True
        if starter:
            try:
                self._start(srv, slot, gate)
            except BaseException as e:
                srv.error = e
                with self.lock:
                    if self.servers.get(key) is srv:
                        del self.servers[key]
                    self.failed[key] += 1
                    self.counts["start_failed"] += 1
                    srv.inflight -= 1
                srv.ready.set()
                self.log(f"prefix: server start failed ({toolchain_version(plan['binary'])}, {key[4][:10]}): {str(e)[:300]}")
                raise ServerError(f"start failed: {e}") from None
            srv.ready.set()
            with self.lock:
                self.counts["started"] += 1
                self.secs["start_s"] += srv.ready_s
            self.log(f"prefix: server up {toolchain_version(plan['binary'])} ({srv.mode}) {key[4][:10]} pid {srv.proc.pid}: {srv.ncmds} commands, "
                     f"header {srv.header_s:.1f}s + prefix {srv.prefix_s:.1f}s (ready {srv.ready_s:.1f}s), "
                     f"rss {srv.mem.get('VmRSS')} MB anon {srv.mem.get('RssAnon')} MB; {len(self.servers)} servers")
        else:
            if not srv.ready.wait(self.start_timeout + 120) or srv.error is not None or srv.dead:
                with self.lock:
                    srv.inflight -= 1
                raise ServerError("server start failed (another request started it)")
        return srv, time.monotonic() - t0, starter

    def _start(self, srv: Server, slot, gate) -> None:
        if slot is None:
            srv.start(self.start_timeout)
            return
        with slot():
            token = gate.acquire(label="prefix-server") if gate is not None else None
            try:
                srv.start(self.start_timeout)
            finally:
                if token is not None:
                    gate.release(token)

    def done(self, srv: Server) -> None:
        with self.lock:
            srv.inflight -= 1
            srv.uses += 1

    def compile(self, plan, path: Path, file_name: str, timeout: float, slot=None, gate=None):
        """-> (CompletedProcess or None for a timeout, extra seconds to charge). ServerError: run it fresh."""
        srv, waited, started = self.server(plan, slot, gate)
        try:
            charge = srv.charge_s if self.charge_prefix else 0.0
            extra = 0.0 if started else max(0.0, charge - waited)
            remaining = timeout - charge if timeout is not None else 10 ** 6
            ctx = slot() if slot is not None else _null()
            with ctx:
                if remaining <= 0:            # a fresh compile would spend the whole timeout in the prefix
                    self.stat("timeout")
                    return None, min(extra, timeout)
                token = gate.acquire(label=path.name) if gate is not None else None   # TimeoutExpired: the caller's timeout
                try:
                    out, code, secs, sent = srv.request(path, file_name, remaining)
                except CompileTimeout:
                    self.stat("timeout")
                    return None, extra
                except ServerError as e:
                    with self.lock:
                        self.counts["lost"] += 1
                    self.log(f"prefix: request failed on {toolchain_version(plan['binary'])} {plan['key'][4][:10]}: {str(e)[:200]}")
                    raise
                finally:
                    if token is not None:
                        gate.release(token)
            with self.lock:
                self.counts["requests"] += 1
                self.counts["resumed_early"] += int(sent.get("resume") not in (None, srv.ncmds))
                self.counts["child_exit"] += int("code" in sent)
                self.secs["request_s"] += secs
                self.secs["charged_s"] += extra
            self.tl.last = dict(server=srv, text=out, exit=code, seconds=secs, sentinel=sent, started=started, waited=waited)
            return subprocess.CompletedProcess([str(plan["binary"]), "--json", file_name], code, out, ""), extra
        finally:
            self.done(srv)

    def summary(self) -> dict:
        with self.lock:
            servers = [dict(version=toolchain_version(s.plan["binary"]), mode=s.mode, prefix=s.key[4][:10], uses=s.uses, ready_s=round(s.ready_s, 2),
                            header_s=s.header_s, prefix_s=s.prefix_s, commands=s.ncmds, rss_mb=s.mem.get("VmRSS"),
                            anon_mb=s.mem.get("RssAnon")) for s in self.servers.values() if s.ready.is_set() and not s.dead]
            return dict(counts=dict(self.counts), seconds={k: round(v, 1) for k, v in self.secs.items()}, servers=servers)

    def close(self) -> None:
        with self.lock:
            servers, self.servers = list(self.servers.values()), OrderedDict()
        for s in servers:
            s.close()


class _null:
    def __enter__(self):
        return self

    def __exit__(self, *a):
        return False


def make_pool(root=None, max_servers=None, max_anon_mb=None, start_timeout=None, charge_prefix=None, log=None) -> Pool:
    root = Path(root or os.environ.get("LRA_PREFIX_ROOT") or Path(os.environ.get("LRA_HBTOOL_SCRATCH", "/tmp")) / "prefix-servers")
    pool = Pool(root,
                max_servers if max_servers is not None else _env_int("LRA_PREFIX_MAX_SERVERS", 48),
                max_anon_mb if max_anon_mb is not None else _env_int("LRA_PREFIX_MAX_ANON_MB", max(4096, int(0.4 * _meminfo_mb()))),
                start_timeout if start_timeout is not None else _env_int("LRA_PREFIX_START_TIMEOUT", 900),
                bool(charge_prefix if charge_prefix is not None else _env_int("LRA_PREFIX_CHARGE", 1)),
                log or (lambda m: print(m, file=sys.stderr, flush=True)))
    atexit.register(pool.close)
    return pool


# ---------------------------------------------------------------------------------------------------------- fast_post front end
def install(HE, C, *, TL=None, log=None, **kw):
    """Wrap HE.Evaluator._run (call AFTER fast_post patched it). Returns the Pool (pool.summary() for stats), or None when disabled.
    Accounting as fast_post's _run: TL.phys += 1 per physical compile; compiles += 1 (budget-checked only when TL.ev_to is None, as
    the original Evaluator._run); timeout = TL.ev_to, else self.timeout; self._slot() around the request, self._gate (memory gate) per
    request and per server start. A server error undoes the accounting and runs the wrapped _run (the fresh compile)."""
    if os.environ.get("LRA_PREFIX_DISABLE") == "1":
        return None
    main = sys.modules.get("__main__")
    TL = TL if TL is not None else getattr(main, "TL", None)
    if TL is None:
        TL = threading.local()
    log = log or getattr(main, "log", None)
    pool = make_pool(log=log, **kw)
    inner = HE.Evaluator._run

    def _run(self, row, version, body, lean_args=(), first_line=1, quiet_prefix_sorry=False):
        try:
            binary, env = self._runtime(row, version)
            plan, why = pool.plan(binary, env, lean_args, os.environ.get("LRA_LEAN_MEMORY_MB", "16000"), body, first_line)
        except Exception as e:  # noqa: BLE001
            plan, why = None, f"plan_{type(e).__name__}"
        if plan is None:
            pool.stat("fresh_" + why)
            return inner(self, row, version, body, lean_args, first_line, quiet_prefix_sorry)
        t_ev = getattr(TL, "ev_to", None)
        timeout = t_ev if t_ev is not None else self.timeout
        with self._count_lock:
            if t_ev is None and self.compiles >= self.max_compiles:
                return C.CompileResult(False, None, 0, ["compile budget exhausted"])
            self.compiles += 1
        TL.phys = getattr(TL, "phys", 0) + 1
        path = self.scratch / f"c_{uuid.uuid4().hex}.lean"
        path.write_text(body)
        start = time.monotonic()
        try:
            res, extra = pool.compile(plan, path, str(path), timeout, slot=self._slot, gate=self._gate)
        except ServerError:
            with self._count_lock:
                self.compiles -= 1
            TL.phys -= 1
            path.unlink(missing_ok=True)
            pool.stat("fresh_server_error")
            return inner(self, row, version, body, lean_args, first_line, quiet_prefix_sorry)
        except subprocess.TimeoutExpired:          # the memory gate gave up: a timed-out compile, as fast_post reports it
            return C.CompileResult(False, None, time.monotonic() - start, ["timeout"], timed_out=True)
        finally:
            path.unlink(missing_ok=True)
        secs = time.monotonic() - start + extra
        if res is None:
            return C.CompileResult(False, None, secs, ["timeout"], timed_out=True)
        return C._parse(res, secs, first_line, sorry_blind=C._warn_sorry_off(lean_args), switch=C._sorry_switch(body, first_line),
                        quiet_prefix_sorry=quiet_prefix_sorry)

    _run.prefix_pool = pool
    HE.Evaluator._run = _run
    pool.log(f"prefix: backend installed (root {pool.root}, max servers {pool.max_servers}, max anon {pool.max_anon_mb} MB, "
             f"charge prefix {pool.charge_prefix})")
    return pool


# ---------------------------------------------------------------------------------------------------------- pf_svc.py front end
_POOL = None
_PLOCK = threading.Lock()


def run(req: dict):
    """pf_svc.py --backend: {"cmd": [lean, "--json", "-M<mb>", -D..., file], "file_index", "cwd", "env", "content", "timeout", "lake"} ->
    {"stdout", "stderr", "returncode", "seconds", "timed_out"} or None (not handled: the service compiles fresh). Called inside the
    service's slot; the first request of a prefix starts its server (seconds include the start)."""
    global _POOL
    if os.environ.get("LRA_PREFIX_DISABLE") == "1" or req.get("lake"):
        return None
    cmd, fi = list(req["cmd"]), int(req["file_index"])
    if fi != len(cmd) - 1 or Path(cmd[0]).name != "lean" or "--json" not in cmd[1:fi]:
        return None
    mem, dargs = None, []
    for a in cmd[1:fi]:
        if a == "--json":
            continue
        if a.startswith("-M") and a[2:].isdigit():
            mem = a[2:]
        elif a.startswith("-D"):
            dargs.append(a)
        else:
            return None
    if mem is None:
        return None
    with _PLOCK:
        if _POOL is None:
            _POOL = make_pool()
    pool = _POOL
    env, content, file_name = dict(req.get("env") or os.environ), req["content"], cmd[fi]
    cwd = Path(req.get("cwd") or os.getcwd())
    fpath = Path(file_name) if Path(file_name).is_absolute() else cwd / file_name
    if fpath.parent.resolve() != cwd.resolve():      # main module name = the file's path relative to cwd: keep it c_<hex>
        return None
    plan, why = pool.plan(Path(cmd[0]), env, dargs, mem, content, None)
    if plan is None:
        pool.stat("fresh_" + why)
        return None
    if int(req.get("draw") or 0) > 0:   # postfast: a repeat draw of a text already measured: a server of its own (its own random module
        plan = dict(plan, key=tuple(plan["key"]) + (f"draw{int(req['draw'])}",))   # name), so its heartbeats are an independent draw
        pool.stat("draw_server_request")
    own = None
    if not fpath.is_file() or fpath.read_text() != content:
        own = pool.root / "req" / f"c_{uuid.uuid4().hex}.lean"
        own.parent.mkdir(parents=True, exist_ok=True)
        own.write_text(content)
    t0 = time.monotonic()
    try:
        res, extra = pool.compile(plan, own or fpath, file_name, req.get("timeout"))
    except ServerError:
        pool.stat("fresh_server_error")
        return None
    finally:
        if own is not None:
            own.unlink(missing_ok=True)
    secs = time.monotonic() - t0 + extra
    if res is None:
        return {"timed_out": True, "seconds": secs, "stdout": "", "stderr": "", "returncode": None, "prefix": True}
    return {"stdout": res.stdout, "stderr": "", "returncode": res.returncode, "seconds": secs, "timed_out": False, "prefix": True}


def stats() -> dict:
    return _POOL.summary() if _POOL is not None else {}


def shutdown() -> int:
    """pf_svc.py's termination handler (SIGTERM / SIGINT; the service exits right after, without atexit): SIGKILL every pooled
    server's process group now (servers run in sessions of their own), waiting for no server lock and no process. -> servers
    signalled. Not called while the service runs."""
    pool = _POOL
    if pool is None:
        return 0
    got = pool.lock.acquire(timeout=2.0)
    try:
        servers = list(pool.servers.values())
    except RuntimeError:   # mutated while copied without the lock
        servers = []
    finally:
        if got:
            pool.lock.release()
    n = 0
    for s in servers:
        s.dead = True
        proc = s.proc
        if proc is None or proc.returncode is not None:
            continue
        try:
            os.killpg(proc.pid, signal.SIGKILL)
            n += 1
        except (ProcessLookupError, PermissionError):
            pass
    return n
