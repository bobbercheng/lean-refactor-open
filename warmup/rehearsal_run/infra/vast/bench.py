#!/usr/bin/env python3
"""Throughput benchmark against the self-hosted server (through the tunnel): N concurrent 2k-token generations.
Usage: python3 infra/vast/bench.py [--url http://localhost:8000/v1] [--n 3] [--max-tokens 2000] [--effort low]
Appends a line to accounting/a100_poc.md."""
import argparse, concurrent.futures as cf, json, pathlib, time
import requests
KEY_FILE = pathlib.Path("~/.config/vexorium/vllm_api_key").expanduser()
HEADERS = {"Authorization": "Bearer " + KEY_FILE.read_text().strip()} if KEY_FILE.exists() else {}

ap = argparse.ArgumentParser()
ap.add_argument("--url", default="http://localhost:8000/v1"); ap.add_argument("--n", type=int, default=3)
ap.add_argument("--max-tokens", type=int, default=2000); ap.add_argument("--effort", default="low"); ap.add_argument("--model", default="glm-5.3-flash")
a = ap.parse_args()

def one(i: int):
    t = time.time()
    r = requests.post(a.url + "/chat/completions", headers=HEADERS, json={"model": a.model, "max_tokens": a.max_tokens, "reasoning_effort": a.effort,
                      "messages": [{"role": "user", "content": f"Write a {a.max_tokens // 2}-word essay (topic {i}) on the design of Lean 4 tactics."}]}, timeout=1800).json()
    u = r.get("usage") or {}; m = (r.get("choices") or [{}])[0].get("message") or {}
    return u.get("completion_tokens", 0), time.time() - t, len(m.get("reasoning_content") or ""), (r.get("choices") or [{}])[0].get("finish_reason")

t0 = time.time()
with cf.ThreadPoolExecutor(a.n) as ex:
    res = list(ex.map(one, range(a.n)))
wall = time.time() - t0
lines = [f"{c} tok in {s:.1f}s = {c / s:.1f} tok/s per stream (reasoning chars {rc}, finish {fr})" for c, s, rc, fr in res]
agg = sum(c for c, _, _, _ in res) / wall
print("\n".join(lines)); print(f"aggregate {agg:.1f} tok/s over {wall:.1f}s wall at concurrency {a.n}")
out = pathlib.Path("accounting/a100_poc.md"); out.parent.mkdir(exist_ok=True)
with out.open("a") as f:
    f.write(f"- {time.strftime('%Y-%m-%dT%H:%M UTC', time.gmtime())} bench n={a.n} max_tokens={a.max_tokens} effort={a.effort}: " + "; ".join(lines) + f"; aggregate {agg:.1f} tok/s\n")
