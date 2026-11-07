#!/usr/bin/env python3
"""DEV ONLY ($0 dry run of the open package, docs/open_package_readme.md "Dry run"): a scripted OpenAI-compatible /v1/chat/completions















"""
from __future__ import annotations

import argparse, hashlib, http.server, json, os, re, threading, time

LOG = None
LOCK = threading.Lock()
                                                                                                                           
                                                                                                        
SORRY = os.environ.get("LRA_FAKE_SORRY_PROOFS", "") == "1"
TURN_S = float(os.environ.get("LRA_FAKE_TURN_S", "0") or 0)                                                                    


def step(body: dict) -> dict:
    msgs = body.get("messages") or []
    k = sum(1 for m in msgs if m.get("role") == "assistant")
    opening = next((m.get("content") for m in msgs if m.get("role") == "user"), "") or ""
    if isinstance(opening, list):
        opening = " ".join(str(x.get("text", "")) for x in opening if isinstance(x, dict))
    ref = re.search(r"original\.lean \(the REFERENCE proof\):\n```lean\n(.*?)\n```", opening, re.S)
    ref = ref.group(1) if ref else ""
    if k == 0:
        return {"tool": "lean_check", "args": {"path": "candidate.lean"}}
    if k == 1:
        return {"tool": "lean_goals", "args": {"path": "candidate.lean", "depth": 1}}
    if k == 2 and ":= by" in ref:
        return {"tool": "lean_skeleton", "args": {"content": ref[:ref.index(":= by")] + ":= by\n  all_goals sorry"}}
    if k == 3:
        return {"tool": "lean_profile", "args": {"path": "candidate.lean"}}
    if k == 4 and ref:
        alt = re.sub(r"\n\s*\n", "\n", ref, count=1)
        vs = [{"label": "ref", "content": ref}, {"label": "alt", "content": alt}]
        if SORRY and ":= by" in ref:                                                                                                   
            head = ref[:ref.index(":= by")] + ":= by\n  "
            vs += [{"label": "stop", "content": head + "stop\n  simp"},                                                    
                   {"label": "impossible", "content": head + "exfalso; impossible by simp"}]
        return {"tool": "lean_check_variants", "args": {"variants": vs}}
    if k == 5:
        return {"tool": "write_file", "args": {"path": "notes.md", "content": "# Notes\n- dry run: the reference compiles\n"}}
    if k == 6:
        return {"tool": "lean_search", "args": {"path": "candidate.lean"}}
    return {"tool": "finish", "args": {"summary": "dry run"}}


T0 = time.time()


def fake_kv(now: float | None = None) -> float:
    """LRA_FAKE_KV (module docstring): the KV cache use reported at `now`."""
    spec = os.environ.get("LRA_FAKE_KV", "0.10").strip()
    if ":" not in spec:
        return float(spec)
    t = (time.time() if now is None else now) - T0; kv = 0.0
    for part in spec.split(","):
        s, v = part.split(":")
        if t >= float(s):
            kv = float(v)
    return kv


def metrics_page(now: float | None = None) -> str:
    lab = '{engine="0",model_name="glm-5.3-flash"}'
    return ("# HELP vllm:kv_cache_usage_perc KV-cache usage. 1 means 100 percent usage.\n# TYPE vllm:kv_cache_usage_perc gauge\n"
            f"vllm:kv_cache_usage_perc{lab} {fake_kv(now)}\nvllm:num_requests_running{lab} 0.0\nvllm:num_requests_waiting{lab} 0.0\n"
            f"vllm:num_preemptions_total{lab} 0.0\n")


class H(http.server.BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, code: int, obj: dict):
        out = json.dumps(obj).encode()
        self.send_response(code); self.send_header("Content-Type", "application/json"); self.send_header("Content-Length", str(len(out)))
        self.end_headers(); self.wfile.write(out)

    def do_GET(self):
        if self.path.split("?")[0] == "/metrics" and os.environ.get("LRA_FAKE_METRICS", "on") != "off":                          
            out = metrics_page().encode()
            self.send_response(200); self.send_header("Content-Type", "text/plain; version=0.0.4"); self.send_header("Content-Length", str(len(out)))
            self.end_headers(); self.wfile.write(out); return
        self._send(200, {"data": [{"id": "glm-5.3-flash", "object": "model"}]})

    def do_POST(self):
        body = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
        s = step(body)
        if TURN_S > 0:
            time.sleep(TURN_S)
        msgs = body.get("messages") or []
        sysm = next((m.get("content") for m in msgs if m.get("role") == "system"), "")
        last_user = next((m for m in reversed(msgs) if m.get("role") in ("user", "tool")), {})
        if LOG:
            with LOCK, open(LOG, "a") as fh:
                fh.write(json.dumps({"system_sha256": hashlib.sha256(str(sysm).encode()).hexdigest()[:16], "system_chars": len(str(sysm)),
                                     "tools": [t.get("function", {}).get("name") for t in body.get("tools") or []],
                                     "turn": sum(1 for m in msgs if m.get("role") == "assistant"), "step": s["tool"],
                                     "last": str(last_user.get("content"))[:300]}) + "\n")
        msg = {"role": "assistant", "content": None, "reasoning_content": "dry run step",
               "tool_calls": [{"id": f"call_{len(msgs)}", "type": "function", "function": {"name": s["tool"], "arguments": json.dumps(s["args"])}}]}
        self._send(200, {"choices": [{"message": msg, "finish_reason": "tool_calls"}],
                         "usage": {"prompt_tokens": 1000, "completion_tokens": 50}})


def main() -> int:
    global LOG
    ap = argparse.ArgumentParser()
    ap.add_argument("--port", type=int, default=18471)
    ap.add_argument("--log", default=None)
    a = ap.parse_args()
    LOG = a.log
    http.server.ThreadingHTTPServer(("127.0.0.1", a.port), H).serve_forever()
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
