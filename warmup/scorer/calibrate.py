"""Measure every reference proof's heartbeats locally on its primary (newest)
toolchain and write data/reference_heartbeats_local.json. Scorers use the
ratio hb_candidate / hb_reference_local so the small constant offset between
our counter and the organizers' cancels."""
from __future__ import annotations

import json, sys, time
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from scorer.compile import compile_putnam, compile_project  # noqa: E402
from probe.verify_candidates import newest_first  # noqa: E402

OUT = ROOT / "data/reference_heartbeats_local.json"


def main() -> None:
    rows = {json.loads(l)["name"]: json.loads(l) for l in (ROOT / "data/benchmark_warmup.jsonl").open() if l.strip()}
    official = {json.loads(l)["name"]: json.loads(l)["heartbeat"] for l in (ROOT / "data/benchmark_heartbeats.jsonl").open() if l.strip()}

    def one(name):
        r = rows[name]; v = newest_first(r["version_info"])[0]
        res = compile_putnam(r["header"], r["src"], v) if r["source"] == "putnambench" else compile_project(r, r["src"], v)
        return name, {"toolchain": v, "heartbeats_local": res.heartbeats, "heartbeats_official": official.get(name),
                      "ok": res.ok, "compile_seconds": round(res.seconds, 1)}

    with ThreadPoolExecutor(8) as ex:
        out = dict(ex.map(one, list(rows)))
    out["_measured_at"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
    OUT.write_text(json.dumps(out, indent=1))
    for n, e in out.items():
        if n.startswith("_"):
            continue
        off = (e["heartbeats_local"] - e["heartbeats_official"]) / e["heartbeats_official"] * 100 if e["heartbeats_local"] and e["heartbeats_official"] else None
        print(f"{n[:45]:45s} {e['toolchain']:12s} local={e['heartbeats_local']} official={e['heartbeats_official']} off={off:+.2f}% ok={e['ok']}")


if __name__ == "__main__":
    main()
