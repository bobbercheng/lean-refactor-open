#!/usr/bin/env python3
"""The Lean environments a rows file needs, in the format of infra/vast/harness_envs.json (read by infra/vast/harness_setup.sh):



"""
from __future__ import annotations

import argparse, json, sys
from pathlib import Path

URLS = {"strata": "https://github.com/strata-org/Strata", "physlib": "https://github.com/leanprover-community/physlib",
        "cslib": "https://github.com/leanprover/cslib", "arklib": "https://github.com/Verified-zkEVM/ArkLib",
        "putnambench": "https://github.com/leanprover-community/mathlib4",
        "leanpool": "https://github.com/LeanPool/lean-pool"}                                                                                    
NO_CACHE = {"strata"}                                                   
REPO = {"putnambench": "mathlib4"}
ENV_PREFIX = {"putnambench": "mathlib"}


def envs(rows: list[dict], urls: dict, no_cache: set) -> dict:
    out: dict = {}
    for r in rows:
        src = r["source"]
        if src not in urls and (r.get("url") or "").startswith("http"):                                                        
            urls = dict(urls, **{src: r["url"]})
        if src not in urls:
            raise SystemExit(f"source {src!r} ({r['name']}): no repository URL; pass --url {src}=<git url>")
        mod = None if src == "putnambench" else r["file_path"].removesuffix(".lean").replace("/", ".")
        for vi in r["version_info"]:
            for ver, commit in vi.items():
                key = f"{ENV_PREFIX.get(src, src)}-{ver}"
                e = out.setdefault(key, {"repo": REPO.get(src, src), "url": urls[src], "commit": commit, "modules": [], "cache": src not in no_cache})
                if e["commit"] != commit:
                    raise SystemExit(f"{key}: two commits ({e['commit']} and {commit}) for one toolchain")
                if mod and mod not in e["modules"]:
                    e["modules"].append(mod)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rows", required=True); ap.add_argument("--out", required=True)
    ap.add_argument("--url", action="append", default=[], metavar="SOURCE=URL"); ap.add_argument("--no-cache", action="append", default=[])
    a = ap.parse_args()
    urls = dict(URLS, **dict(x.split("=", 1) for x in a.url))
    rows = [json.loads(l) for l in Path(a.rows).read_text().splitlines() if l.strip()]
    d = envs(rows, urls, NO_CACHE | set(a.no_cache))
    Path(a.out).write_text(json.dumps(d, indent=1) + "\n")
    print(f"{len(d)} environment(s) for {len(rows)} row(s) -> {a.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
