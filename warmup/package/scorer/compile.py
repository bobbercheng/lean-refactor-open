"""Compile a candidate declaration in a prepared environment and measure











"""
from __future__ import annotations

import json, os, re, subprocess, sys, time, uuid
from dataclasses import dataclass, field
from pathlib import Path
from scorer.memgate import run_lean              

ROOT = Path(__file__).resolve().parents[1]
ELAN_BIN = Path.home() / ".elan/bin"
USED_RE = re.compile(r"ARENA_HB (\d+)")
MEASURE_ELAB = """open Lean Elab Command in
elab "arena_measure " cmd:command : command => do
  let t0 ← IO.getNumHeartbeats
  elabCommand cmd
  let t1 ← IO.getNumHeartbeats
  logInfo m!"ARENA_HB {(t1 - t0) / 1000}"

"""


@dataclass
class CompileResult:
    ok: bool
    heartbeats: int | None
    seconds: float
    errors: list[str] = field(default_factory=list)
    warnings: int = 0
    timed_out: bool = False
    raw: str = ""
    messages: list = field(default_factory=list)
    hb_blind: bool = False                                                                                               
    sorry_blind: bool = False                                                                                                                   
                                                                                                                                                   


                                                                                                                                            
                                                                                                                                            
                                                                                                                                         
                                                                                                                                      
                                                                                                                                            
                                                                                                                                     
SORRY_WARN_RE = re.compile(r"\bdeclaration uses\b.*\bsorry", re.DOTALL)
SORRY_ERR = "the declaration depends on sorryAx"                                                                                 
                                                                                                                                           
                                                                                                                                            
                                                                                                                                         
                                                                                                                                   
SORRY_SWITCH_RE = re.compile(r"\bwarn\.sorry\b|#guard_msgs\b")
SORRY_SWITCH_ERR = "can hide Lean's sorry warning"                                                                 


def _is_sorry_msg(m: dict) -> bool:
    return m.get("kind") == "hasSorry" or bool(SORRY_WARN_RE.search(str(m.get("data", ""))))


def _msg_line(m: dict, default: int) -> int:
    """A message's line; `default` when the message has no position (Lean always gives one: theoretical)."""
    return (m.get("pos") or {}).get("line") or default


def _sorry_switch(body: str, first_line: int) -> str | None:
    """The error for a candidate (body lines from `first_line` on) that names a way to hide the sorry warning, else None."""
    from scorer.forbidden import strip_lean_comments
    m = SORRY_SWITCH_RE.search(strip_lean_comments("\n".join(body.split("\n")[first_line - 1:])))
    return None if not m else (f"the declaration uses `{m.group(0)}`, which {SORRY_SWITCH_ERR}; the scorer counts it as an error "
                               "(a candidate may not change warn.sorry or filter messages)")


def _parse(p, secs: float, first_line: int = 1, sorry_blind: bool = False, switch: str | None = None,
           quiet_prefix_sorry: bool = False) -> CompileResult:
    """CompileResult from a finished `lean --json` process: errors (pos-prefixed), warning count, ARENA_HB heartbeats, every message;


"""
    errors, warnings, hb, messages = [], 0, None, []
    for line in p.stdout.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            m = json.loads(line)
        except json.JSONDecodeError:
            continue
        messages.append(m)
        sev, data = m.get("severity"), m.get("data", "")
        pos = m.get("pos") or {}
        is_sorry, in_cand = _is_sorry_msg(m), _msg_line(m, first_line) >= first_line
        if sev == "error":
            errors.append(f"{pos.get('line')}:{pos.get('column')}: {data}")
        elif sev == "warning" and not (quiet_prefix_sorry and is_sorry and not in_cand):
            warnings += 1
        if sev != "error" and is_sorry and in_cand:
            errors.append(f"{pos.get('line')}:{pos.get('column')}: {SORRY_ERR} (Lean {sev}: {data}); the scorer counts it as an error: a sorry "
                          "produced by a tactic or macro (e.g. `stop`) is still a sorry")
        if sev == "information":
            mm = USED_RE.search(data)
            if mm:
                hb = int(mm.group(1))
    if switch:
        errors.append(switch)
    ok = p.returncode == 0 and not errors
    if p.returncode != 0 and not errors:
        errors.append(f"lean exit {p.returncode}: {p.stderr[-500:]}")
    return CompileResult(ok, hb, secs, errors, warnings, raw=p.stdout[-4000:], messages=messages, sorry_blind=sorry_blind)


def _first_line(head: str) -> int:
    """Line number of the blank line after `head` (header or file prefix) in a body built as head.rstrip("

"""
    return head.rstrip("\n").count("\n") + 2


def env_dir(version: str, source: str = "putnambench") -> Path:
    if source == "putnambench":
        return ROOT / "envs" / f"mathlib-{version}"
    raise NotImplementedError(f"env for {source}")


def compile_putnam(header: str, declaration: str, version: str, *, count: bool = True,
                   timeout: int = 600) -> CompileResult:
    wd = env_dir(version)
    scratch = wd / "LRAScratch"
    scratch.mkdir(exist_ok=True)
    f = scratch / f"c_{uuid.uuid4().hex[:12]}.lean"
    if count:
        text = header.rstrip() + "\n\n" + MEASURE_ELAB + "set_option Elab.async false in\narena_measure\n" + declaration.rstrip() + "\n"
    else:
        text = header.rstrip() + "\n\n" + declaration.rstrip() + "\n"
    f.write_text(text)
    env = dict(os.environ, PATH=f"{ELAN_BIN}:{os.environ.get('PATH','')}")
    t0 = time.time()
    try:
        p = run_lean(["lake", "env", "lean", "--json", f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}", str(f.relative_to(wd))], cwd=wd, env=env,
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as e:
        f.unlink(missing_ok=True)
        return CompileResult(False, None, time.time() - t0, ["timeout"], timed_out=True,
                             raw=(e.stdout or b"")[:2000] if isinstance(e.stdout, bytes) else str(e.stdout)[:2000])
    secs = time.time() - t0
    f.unlink(missing_ok=True)
    first = _first_line(header.rstrip())
    return _parse(p, secs, first, switch=_sorry_switch(text, first))


                                                                             
                                                                        
                                                                       
                                                                         
                                                                         
                                                                       
                                                           
                                                                             

PROJECT_DIRS = {"strata": "strata", "cslib": "cslib", "physlib": "physlib", "arklib": "arklib",
                "leanpool": "leanpool"}                                                                                                                          


def project_env_dir(source: str, version: str) -> Path:
    return ROOT / "envs" / f"{PROJECT_DIRS[source]}-{version}"


def _ws_regex(text: str) -> re.Pattern:
    """Regex matching `text` with any whitespace run allowed where it has one."""
    parts = [re.escape(t) for t in text.split()]
    return re.compile(r"\s+".join(parts))


def locate(source: str, version: str, file_path: str, statement: str, src: str) -> tuple[str, int]:
    """Find the reference declaration in the file at the pinned commit and




"""
    text = (project_env_dir(source, version) / file_path).read_text()
    needle = src.rstrip("\n")
    i = text.find(needle)
    if i >= 0 and text.find(needle, i + 1) < 0:
        return text[:i], text[:i].count("\n") + 1
    hits = [m.start() for m in _ws_regex(statement).finditer(text)]
                                                                         
    hits = [h for h in hits if re.match(r"\s*:=", text[_ws_regex(statement).match(text, h).end():])]
    if len(hits) != 1:
        raise ValueError(f"statement found {len(hits)} times in {file_path} @ {version}")
    return text[:hits[0]], text[:hits[0]].count("\n") + 1


def file_prefix(row: dict, version: str) -> str:
    return locate(row["source"], version, row["file_path"], row["statement"], row["src"])[0]


                                                                                                                                       
                                                                                                                                          
                                                                                                                                 
                                                                                                                                    
                                                                                                                                 
                                                                                                                           
_MODIFIER_TAIL = re.compile(
    r"((?:/--(?:(?!-/).)*-/\s*|@\[[^\]\n]*\]\s*|(?:private|protected|noncomputable|nonrec|partial|unsafe|public|meta|scoped|local|open\s+[\w.\s]+?\s+in)\s+)*)\Z",
    re.DOTALL)
                                                                                                                                 
                                                                                                                                    
_ATTACHED_IN = re.compile(r"(?:^|\n)[ \t]*(?:omit|include|unseal|variable|set_option(?![ \t]+(?:weak\.)?(?:linter|pp)\.))\b[^\n]*\bin[ \t]*\n?\s*\Z")

                                                                                                                                     
                                                                                                                                 
                                                                                                        
SEMANTIC_OPTIONS = {"autoImplicit", "relaxedAutoImplicit", "warningAsError", "experimental.module", "warn.sorry", "says.verify",
                    "maxSynthPendingDepth", "maxHeartbeats", "maxRecDepth", "synthInstance.maxHeartbeats", "synthInstance.maxSize"}


def _semantic(key: str) -> bool:
    key = key.removeprefix("weak.")
    return key in SEMANTIC_OPTIONS or key.startswith("backward.")


def _fmt(v) -> str:
    return ("true" if v else "false") if isinstance(v, bool) else str(v)


def lakefile_options(source: str, version: str) -> tuple[str, ...]:
    """-D flags for the semantic options in this pin's lakefile (top-level leanOptions, every lean_lib's leanOptions and moreLeanArgs)."""
    wd = project_env_dir(source, version); flags: list[str] = []
    toml_f, lean_f = wd / "lakefile.toml", wd / "lakefile.lean"
    if toml_f.exists():
        import tomllib
        d = tomllib.loads(toml_f.read_text())
        tables = [d.get("leanOptions") or {}] + [lib.get("leanOptions") or {} for lib in d.get("lean_lib", [])]
        def flat(t, pre=""):
            for k, v in t.items():
                yield from (flat(v, f"{pre}{k}.") if isinstance(v, dict) else [(f"{pre}{k}", v)])
        for t in tables:
            flags += [f"-D{k}={_fmt(v)}" for k, v in flat(t) if _semantic(k)]
        for lib in d.get("lean_lib", []):
            flags += [a for a in lib.get("moreLeanArgs", []) if a.startswith("-D") and _semantic(a[2:].split("=")[0])]
    elif lean_f.exists():                                                                             
        t = lean_f.read_text()
        for k, v in re.findall(r"⟨`([\w.]+),\s*(?:\.ofNat\s+|\.ofBool\s+|\.ofString\s+)?\(?([\w.\"]+)\)?\s*⟩", t):
            if _semantic(k):
                flags.append(f"-D{k}={v.strip(chr(34))}")
        flags += [a for a in re.findall(r'"(-D[\w.]+=[^"]+)"', t) if _semantic(a[2:].split("=")[0])]
    return tuple(dict.fromkeys(flags))                              


def split_modifiers(prefix: str) -> tuple[str, str]:
    """Split the file prefix into (core, trailing declaration modifiers).

"""
    m = _MODIFIER_TAIL.search(prefix)
    if not m or not m.group(1):
        return prefix, ""
    return prefix[: m.start(1)], m.group(1)


def _measure_lines(core: str) -> range:
    """Line numbers of MEASURE_ELAB (the elab definition, not the `arena_measure` call, where the declaration's own errors can land)
"""
    start = core.rstrip("\n").count("\n") + 3
    return range(start, start + MEASURE_ELAB.count("\n"))


                                                                                                                               
                                                                                                                                  
                                                                                                                                      
_MODULE_LINE = re.compile(r"\A(?:\s+|--[^\n]*\n|/-(?:(?!-/).)*-/)*module[ \t]*\n", re.DOTALL)
MEASURE_IMPORT = "public meta import Lean.Elab.Command\n"
_NEEDS_IMPORT: set = set()
_BLIND_WARNED: set = set()


def _with_measure_import(core: str) -> str | None:
    m = _MODULE_LINE.match(core)
    return core[: m.end()] + MEASURE_IMPORT + core[m.end():] if m else None


def _measure_failed(res: CompileResult, core: str) -> bool:
    span = _measure_lines(core)
    return not res.ok and any((m.get("pos") or {}).get("line") in span for m in res.messages if m.get("severity") == "error")


def _without_warn_sorry(lean_args) -> tuple:
    return tuple(a for a in lean_args or () if not a.startswith(("-Dwarn.sorry=", "-Dweak.warn.sorry=")))


def _with_warn_sorry(lean_args) -> tuple:
    """`lean_args` with every warn.sorry flag replaced by a final -Dwarn.sorry=true."""
    return _without_warn_sorry(lean_args) + ("-Dwarn.sorry=true",)


def force_warn_sorry() -> bool:
    """LRA_FORCE_WARN_SORRY=1: compile_project's default lean_args get -Dwarn.sorry=true on pins whose lakefile turns it off (PhysLib), so


"""
    return os.environ.get("LRA_FORCE_WARN_SORRY", "") == "1"


def compile_project(row: dict, declaration: str, version: str, *, count: bool = True,
                    timeout: int = 900, lean_args: tuple | None = None, _quiet_prefix_sorry: bool = False) -> CompileResult:
    """`lean_args`: extra flags for `lean`. None (default, 2026-10-12) = the pin's semantic lakefile options (lakefile_options), which





"""
    source = row["source"]
    if lean_args is None:
        lean_args = lakefile_options(source, version)
        if force_warn_sorry() and _warn_sorry_off(lean_args):
            lean_args, _quiet_prefix_sorry = _with_warn_sorry(lean_args), True
    core, modifiers = split_modifiers(file_prefix(row, version))
    if not count:
        return _lean_in_project(source, version, core.rstrip("\n") + "\n\n" + modifiers + declaration.rstrip() + "\n", lean_args, timeout,
                                first_line=_first_line(core), quiet_prefix_sorry=_quiet_prefix_sorry)
    key = (source, version, row["file_path"])
    measured = lambda c: _lean_in_project(source, version, c.rstrip("\n") + "\n\n" + MEASURE_ELAB + "set_option Elab.async false in\n"
                                          "arena_measure\n" + modifiers + declaration.rstrip() + "\n", lean_args, timeout,
                                          first_line=_first_line(c), quiet_prefix_sorry=_quiet_prefix_sorry)
    mcore = (_with_measure_import(core) or core) if key in _NEEDS_IMPORT else core
    res = measured(mcore)
    if _measure_failed(res, mcore) and mcore is core and _with_measure_import(core):
        mcore = _with_measure_import(core)
        retry = measured(mcore)
        retry.seconds += res.seconds
        res = retry
        if not _measure_failed(res, mcore):
            _NEEDS_IMPORT.add(key)
    if _measure_failed(res, mcore):
        plain = compile_project(row, declaration, version, count=False, timeout=timeout, lean_args=lean_args,
                                _quiet_prefix_sorry=_quiet_prefix_sorry)
        plain.seconds += res.seconds
        plain.hb_blind = True
        if (source, version, row["file_path"]) not in _BLIND_WARNED:
            _BLIND_WARNED.add((source, version, row["file_path"]))
            print(f"WARNING scorer.compile: arena_measure cannot be defined in this {source} @ {version} file ({res.errors[0][:120]}); "
                  "heartbeats unavailable there (hb_blind), validity from the unmeasured compile", file=sys.stderr, flush=True)
        return plain
    if res.ok and _ATTACHED_IN.search(core):
        plain = compile_project(row, declaration, version, count=False, timeout=timeout, lean_args=lean_args,
                                _quiet_prefix_sorry=_quiet_prefix_sorry)
        res.seconds += plain.seconds
        if not plain.ok:
            res.ok, res.timed_out = False, plain.timed_out
            res.errors = [f"(with the preceding `… in` modifier applied to the declaration, as in the file) {e}" for e in plain.errors]
    return res


def _lean_in_project(source: str, version: str, body: str, lean_args: tuple, timeout: int, first_line: int = 1,
                     quiet_prefix_sorry: bool = False) -> CompileResult:
    """`first_line`: the body's first line after the file prefix; sorry warnings before it belong to the project's own declarations."""
    wd = project_env_dir(source, version)
    scratch_dir = wd / "LRAScratch"
    scratch_dir.mkdir(exist_ok=True)
    f = scratch_dir / f"c_{uuid.uuid4().hex[:12]}.lean"
    f.write_text(body)
    env = dict(os.environ, PATH=f"{ELAN_BIN}:{os.environ.get('PATH','')}")
    t0 = time.time()
    try:
        p = run_lean(["lake", "env", "lean", "--json", f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}", *lean_args, str(f.relative_to(wd))], cwd=wd, env=env,
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        f.unlink(missing_ok=True)
        return CompileResult(False, None, time.time() - t0, ["timeout"], timed_out=True)
    secs = time.time() - t0
    f.unlink(missing_ok=True)
    return _parse(p, secs, first_line, sorry_blind=_warn_sorry_off(lean_args), switch=_sorry_switch(body, first_line),
                  quiet_prefix_sorry=quiet_prefix_sorry)


def _warn_sorry_off(lean_args) -> bool:
    """The last warn.sorry flag in `lean_args` turns the sorry warning off."""
    vals = [a.split("=", 1)[1].strip().lower() for a in lean_args or () if a.startswith(("-Dwarn.sorry=", "-Dweak.warn.sorry="))]
    return bool(vals) and vals[-1] == "false"


                                                                             
                                                                                                                                           
                                                                                                                                       
                                                                                                                                          
                                                                                                                               
                                                                                                                             
                                                                                                                                         
                                                                                                                            
                                                                                                                                    
                                                                                                                                       
                                              
                                                                             

AXIOM_ALLOW = frozenset({"propext", "Classical.choice", "Quot.sound"})
_DECL_KW = re.compile(r"(?:^|(?<=[\s\]]))(theorem|lemma|def|abbrev|instance|example)\b")
_DECL_NAME = re.compile(r"\s+((?:«[^»]*»|[^\s(){}\[\]⦃:,«])+)")
_INST_PRIO = re.compile(r"\s*\(\s*priority\s*:=[^)]*\)")
_STR_LIT = re.compile(r'"(?:\\.|[^"\\])*"')
_AXIOMS_RE = re.compile(r"depends on axioms:\s*\[(.*?)\]", re.DOTALL)
_SCOPE_CMD = re.compile(r"^(?:(?:noncomputable|public)[ \t]+)?(namespace|section|end)\b[ \t]*([^\s]*)", re.M)


def _code_only(text: str) -> str:
    """`text` without comments and docstrings, with string literals and `@[…]` attribute lists (bracket-balanced) blanked."""
    from scorer.forbidden import strip_lean_comments
    s, out, i = _STR_LIT.sub(" ", strip_lean_comments(text)), [], 0
    while (j := s.find("@[", i)) >= 0:
        out.append(s[i:j])
        depth, k = 0, j + 1
        while k < len(s):
            depth += {"[": 1, "]": -1}.get(s[k], 0)
            k += 1
            if depth == 0:
                break
        out.append(" ")
        i = k
    return "".join(out) + s[i:]


def _declared(statement: str) -> list[tuple[str, str | None]]:
    """(keyword, name or None) for every declaration keyword in the statement, in order; `foo.{u}` gives `foo`."""
    s, out = _code_only(statement), []
    for k in _DECL_KW.finditer(s):
        kw, pos = k.group(1), k.end()
        if kw == "example":
            out.append((kw, None)); continue
        if kw == "instance":
            pm = _INST_PRIO.match(s, pos)
            pos = pm.end() if pm else pos
        m = _DECL_NAME.match(s, pos)
        out.append((kw, (m.group(1).rstrip(".") or None) if m else None))
    return out


def decl_name(statement: str, row_name: str | None = None) -> str | None:
    """The declared name in a row statement (comments, docstrings, attributes and strings ignored; `open … in` and modifiers may precede

"""
    found = _declared(statement)
    if row_name:
        for _, n in found:
            if n and (row_name == n.removeprefix("_root_.") or row_name.endswith("." + n.removeprefix("_root_."))):
                return n
    thms = [n for kw, n in found if kw in ("theorem", "lemma") and n]
    return thms[-1] if thms else (found[0][1] if found else None)


def current_namespace(prefix: str) -> str:
    """The namespace open at the end of `prefix` (namespace / section / end commands at column 0, comments ignored)."""
    from scorer.forbidden import strip_lean_comments
    stack: list[tuple[str, str]] = []
    for m in _SCOPE_CMD.finditer(strip_lean_comments(prefix)):
        kw, parts = m.group(1), [p for p in m.group(2).split(".") if p]
        if kw == "end":
            del stack[len(stack) - min(len(stack), max(1, len(parts))):]
        else:
            stack += [(kw, p) for p in parts] or [(kw, "")]
    return ".".join(p for kw, p in stack if kw == "namespace")


def qualified_name(name: str, namespace: str) -> str:
    return name.removeprefix("_root_.") if name.startswith("_root_.") or not namespace else f"{namespace}.{name}"


def parse_axioms(messages: list, first_line: int = 1) -> list[str] | None:
    """Axiom names from the last `#print axioms` message at or after `first_line` ([] = 'does not depend on any axioms'), None if none."""
    out = None
    for m in messages:
        if _msg_line(m, first_line) < first_line:
            continue
        d = str(m.get("data", ""))
        if "does not depend on any axioms" in d:
            out = []
        else:
            mm = _AXIOMS_RE.search(d)
            if mm:
                out = [a.strip() for a in mm.group(1).split(",") if a.strip()]
    return out


def _err_line(e: str) -> int | None:
    m = re.match(r"(\d+):", e)
    return int(m.group(1)) if m else None


@dataclass
class AxiomAudit:
    name: str | None
    axioms: list | None                                                                                              
    skipped: str | None = None                                                                                        
    compile: CompileResult | None = None
    first_line: int = 1                                                                                                              
    print_line: int | None = None                                                                  

    @property
    def extra(self) -> list:
        return [a for a in self.axioms or [] if a not in AXIOM_ALLOW]

    @property
    def sorry_warning(self) -> bool:
        """Direct sorry: Lean's sorry message on the candidate's lines, at any severity (warningAsError pins report it as an error)."""
        c = self.compile
        return c is not None and any(_is_sorry_msg(m) and _msg_line(m, self.first_line) >= self.first_line
                                     and (self.print_line is None or _msg_line(m, self.first_line) < self.print_line) for m in c.messages)

    @property
    def sorry(self) -> bool:
        """Direct sorry, or sorryAx among the axioms (which may also come transitively from a sorried project declaration)."""
        return self.sorry_warning or "sorryAx" in (self.axioms or [])

    @property
    def switch(self) -> bool:
        """The candidate names a way to hide the sorry warning (_sorry_switch)."""
        return self.compile is not None and any(SORRY_SWITCH_ERR in e for e in self.compile.errors)

    @property
    def print_errors(self) -> list:
        """Errors on the `#print axioms` lines: the name did not resolve there (one of the two forms may fail harmlessly)."""
        if self.compile is None or self.print_line is None:
            return []
        return [e for e in self.compile.errors if (_err_line(e) or 0) >= self.print_line]

    @property
    def decl_errors(self) -> list:
        """The declaration's own errors: not the sorry error / message, not the switch error, not on the `#print axioms` lines."""
        if self.compile is None:
            return []
        pe = set(self.print_errors)
        return [e for e in self.compile.errors if e not in pe and SORRY_ERR not in e and SORRY_SWITCH_ERR not in e
                and not SORRY_WARN_RE.search(e)]


def audit_axioms(row: dict, decl: str, version: str, *, axioms: bool = True, timeout: int = 900) -> AxiomAudit:
    """Compile `decl` + `#print axioms <name>` (unmeasured, warn.sorry on) for the row at `version` and return the audit: the axiom list



"""
    name = decl_name(row["statement"], row.get("name"))
    if row["source"] == "putnambench":
        core, mods = row["header"].rstrip(), ""
        run = lambda text: compile_putnam(row["header"], text, version, count=False, timeout=timeout)
        skip = None
    else:
        core, mods = split_modifiers(file_prefix(row, version))
        args = _with_warn_sorry(lakefile_options(row["source"], version))
        run = lambda text: compile_project(row, text, version, count=False, timeout=timeout, lean_args=args)
        skip = "module" if _MODULE_LINE.match(core) else None
    first = _first_line(core)
    skip = skip or (None if name else "no-name") or (None if axioms else "off")
    if skip:
        return AxiomAudit(name, None, skip, run(decl), first)
    head = decl.rstrip() + "\n\n"
    names = list(dict.fromkeys([name, qualified_name(name, current_namespace(core))]))
    print_line = first + 1 + (mods + head).count("\n")
    r = run(head + "".join(f"set_option pp.fullNames true in\n#print axioms {n}\n" for n in names))
    return AxiomAudit(name, parse_axioms(r.messages, print_line), None, r, first, print_line)
