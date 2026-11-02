"""Write envs/manifest.json: one entry per (project, version) worktree with
commit, toolchain, build-dir size, and whether the benchmark modules' oleans
exist. Run after builds; cheap enough to run every session."""
from __future__ import annotations

import json, subprocess, time
from pathlib import Path

ENVS = Path(__file__).resolve().parent
ROOT = ENVS.parent
rows = [json.loads(l) for l in (ROOT / "data/benchmark_warmup.jsonl").open() if l.strip()]
needed: dict[str, set[str]] = {}
for r in rows:
    for pair in r["version_info"]:
        v = list(pair)[0]
        key = f"mathlib-{v}" if r["source"] == "putnambench" else f"{r['source']}-{v}"
        if r["source"] != "putnambench":
            needed.setdefault(key, set()).add(r["file_path"].removesuffix(".lean"))
        else:
            needed.setdefault(key, set())


def du(p: Path) -> str:
    try:
        return subprocess.run(["du", "-sh", str(p)], capture_output=True, text=True).stdout.split()[0]
    except Exception:
        return "?"


def head(p: Path) -> str:
    try:
        return subprocess.run(["git", "rev-parse", "HEAD"], cwd=p, capture_output=True, text=True).stdout.strip()
    except Exception:
        return "?"


man = {}
for key, mods in sorted(needed.items()):
    d = ENVS / key
    entry = {"exists": d.is_dir()}
    if d.is_dir():
        entry.update({"commit": head(d), "toolchain": (d / "lean-toolchain").read_text().strip() if (d / "lean-toolchain").exists() else "?",
                      "lake_dir_size": du(d / ".lake") if (d / ".lake").exists() else "none"})
        if key.startswith("mathlib-"):
            entry["ok"] = (d / ".lake/build/lib/lean/Mathlib.olean").exists()
        else:
            oleans = {m: (d / ".lake/build/lib/lean" / (m + ".olean")).exists() for m in sorted(mods)}
            entry["modules"] = oleans
            entry["ok"] = all(oleans.values())
    man[key] = entry
man["_generated"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
(ENVS / "manifest.json").write_text(json.dumps(man, indent=1))
for k, e in man.items():
    if k.startswith("_"):
        continue
    print(f"{k:22s} exists={e['exists']} ok={e.get('ok')} size={e.get('lake_dir_size')} {e.get('toolchain','')}")
