"""Compile a candidate declaration in a prepared environment and measure
heartbeats. Putnam (self-contained) path for now: header + declaration is
written to a scratch file inside the Mathlib worktree and run with
`lake env lean --json`.

Heartbeats: Mathlib's `#count_heartbeats in` is pathologically slow on some
declarations (15+ min vs 7 s plain compile on putnam_1964_a4, Oct 6), so we
inject a tiny measuring command (`arena_measure`) that reads
`IO.getNumHeartbeats` around `elabCommand`, under `set_option Elab.async
false` so the work stays on the counting thread. Calibration on the three
PutnamBench references (newest toolchain): +0.05%, +0.07%, +0.8% vs
`benchmark_heartbeats.jsonl`. Tracked in STATUS.md.
"""
from __future__ import annotations

import json, os, re, subprocess, time, uuid
from dataclasses import dataclass, field
from pathlib import Path
from scorer.memgate import run_lean  # noqa: E402

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
        if sev == "error":
            errors.append(f"{m.get('pos',{}).get('line')}:{m.get('pos',{}).get('column')}: {data}")
        elif sev == "warning":
            warnings += 1
        if sev == "information":
            mm = USED_RE.search(data)
            if mm:
                hb = int(mm.group(1))
    ok = p.returncode == 0 and not errors
    if p.returncode != 0 and not errors:
        errors.append(f"lean exit {p.returncode}: {p.stderr[-500:]}")
    return CompileResult(ok, hb, secs, errors, warnings, raw=p.stdout[-4000:], messages=messages)


# ---------------------------------------------------------------------------
# Project-resident problems (Strata, CSLib, PhysLib, ArkLib): the worker
# compiles the declaration in place inside the repository at the pinned
# commit. We replicate that by writing a scratch module that contains the
# original file's prefix (everything before `start_line`) followed by the
# candidate declaration, and compiling it with `lake env lean` from the
# project root so imports resolve against the built oleans.
# ---------------------------------------------------------------------------

PROJECT_DIRS = {"strata": "strata", "cslib": "cslib", "physlib": "physlib", "arklib": "arklib"}


def project_env_dir(source: str, version: str) -> Path:
    return ROOT / "envs" / f"{PROJECT_DIRS[source]}-{version}"


def _ws_regex(text: str) -> re.Pattern:
    """Regex matching `text` with any whitespace run allowed where it has one."""
    parts = [re.escape(t) for t in text.split()]
    return re.compile(r"\s+".join(parts))


def locate(source: str, version: str, file_path: str, statement: str, src: str) -> tuple[str, int]:
    """Find the reference declaration in the file at the pinned commit and
    return (prefix_text, line_number). The benchmark's start_line/end_line are
    unreliable (the CallElimCorrect rows point at other declarations) and the
    proof text can differ by whitespace across commits (ArkLib at v4.30.0),
    so we match the *statement* with whitespace-tolerant search, preferring an
    exact match of the whole declaration when one exists."""
    text = (project_env_dir(source, version) / file_path).read_text()
    needle = src.rstrip("\n")
    i = text.find(needle)
    if i >= 0 and text.find(needle, i + 1) < 0:
        return text[:i], text[:i].count("\n") + 1
    hits = [m.start() for m in _ws_regex(statement).finditer(text)]
    # the statement must be followed by `:=` to be the declaration itself
    hits = [h for h in hits if re.match(r"\s*:=", text[_ws_regex(statement).match(text, h).end():])]
    if len(hits) != 1:
        raise ValueError(f"statement found {len(hits)} times in {file_path} @ {version}")
    return text[:hits[0]], text[:hits[0]].count("\n") + 1


def file_prefix(row: dict, version: str) -> str:
    return locate(row["source"], version, row["file_path"], row["statement"], row["src"])[0]


_MODIFIER_TAIL = re.compile(
    r"((?:/--(?:(?!-/).)*-/\s*|@\[[^\]\n]*\]\s*|(?:private|protected|noncomputable|nonrec|partial|unsafe|public|meta|scoped|local|open\s+[\w.\s]+?\s+in)\s+)*)\Z",
    re.DOTALL)


def split_modifiers(prefix: str) -> tuple[str, str]:
    """Split the file prefix into (core, trailing declaration modifiers).
    Docstrings and attributes immediately before the declaration belong to
    it syntactically, so the measuring command must be inserted before them."""
    m = _MODIFIER_TAIL.search(prefix)
    if not m or not m.group(1):
        return prefix, ""
    return prefix[: m.start(1)], m.group(1)


def compile_project(row: dict, declaration: str, version: str, *, count: bool = True,
                    timeout: int = 900) -> CompileResult:
    source, fp = row["source"], row["file_path"]
    wd = project_env_dir(source, version)
    prefix = file_prefix(row, version)
    core, modifiers = split_modifiers(prefix)
    scratch_dir = wd / "LRAScratch"
    scratch_dir.mkdir(exist_ok=True)
    f = scratch_dir / f"c_{uuid.uuid4().hex[:12]}.lean"
    if count:
        body = (core.rstrip("\n") + "\n\n" + MEASURE_ELAB + "set_option Elab.async false in\narena_measure\n"
                + modifiers + declaration.rstrip() + "\n")
    else:
        body = core.rstrip("\n") + "\n\n" + modifiers + declaration.rstrip() + "\n"
    f.write_text(body)
    env = dict(os.environ, PATH=f"{ELAN_BIN}:{os.environ.get('PATH','')}")
    t0 = time.time()
    try:
        p = run_lean(["lake", "env", "lean", "--json", f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}", str(f.relative_to(wd))], cwd=wd, env=env,
                           capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        f.unlink(missing_ok=True)
        return CompileResult(False, None, time.time() - t0, ["timeout"], timed_out=True)
    secs = time.time() - t0
    f.unlink(missing_ok=True)
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
        if sev == "error":
            errors.append(f"{m.get('pos',{}).get('line')}:{m.get('pos',{}).get('column')}: {data}")
        elif sev == "warning":
            warnings += 1
        if sev == "information":
            mm = USED_RE.search(data)
            if mm:
                hb = int(mm.group(1))
    ok = p.returncode == 0 and not errors
    if p.returncode != 0 and not errors:
        errors.append(f"lean exit {p.returncode}: {p.stderr[-500:]}")
    return CompileResult(ok, hb, secs, errors, warnings, raw=p.stdout[-4000:], messages=messages)
