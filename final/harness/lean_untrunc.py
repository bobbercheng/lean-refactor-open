"""Untruncated Lean runner for the goal map, skeleton and profile tools (moved out of harness/mine.py, 2026-10-30).




"""
from __future__ import annotations

import json, os, subprocess, sys, uuid
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.leantools import ROWS              
from scorer.compile import ELAN_BIN, env_dir, project_env_dir, file_prefix              
from scorer.memgate import run_lean              
from probe.verify_candidates import newest_first              


def lean_run(name: str, code: str, timeout: int = 600, options: list[str] | None = None) -> list[dict]:
    """Compile `code` after the problem's header; return ALL messages as {severity, line (relative to code), data}.

"""
    row = ROWS[name]; primary = newest_first(row["version_info"])[0]
    if row["source"] == "putnambench":
        wd = env_dir(primary); head = row["header"].rstrip() + "\n\n"
    else:
        wd = project_env_dir(row["source"], primary); head = file_prefix(row, primary).rstrip("\n") + "\n\n"
    scratch = wd / "LRAScratch"; scratch.mkdir(exist_ok=True)
    f = scratch / f"m_{uuid.uuid4().hex[:10]}.lean"; f.write_text(head + code.rstrip() + "\n")
    env = dict(os.environ, PATH=f"{ELAN_BIN}:{os.environ.get('PATH','')}")
    try:
        pr = run_lean(["lake", "env", "lean", "--json", f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}", *[f"-Dweak.{o}" for o in (options or [])], str(f.relative_to(wd))], cwd=wd, env=env, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        f.unlink(missing_ok=True); return [{"severity": "error", "line": 0, "data": "timeout"}]
    f.unlink(missing_ok=True)
    off = head.count("\n"); out = []
    for line in pr.stdout.splitlines():
        if line.startswith("{"):
            try:
                m = json.loads(line)
            except json.JSONDecodeError:
                continue
            out.append({"severity": m.get("severity"), "line": (m.get("pos") or {}).get("line", 0) - off, "data": str(m.get("data", ""))})
    if pr.returncode != 0 and not any(m["severity"] == "error" for m in out):
        out.append({"severity": "error", "line": 0, "data": f"exit {pr.returncode}: {pr.stderr[:300]}"})
    return out
