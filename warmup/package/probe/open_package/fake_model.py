#!/usr/bin/env python3
"""DEV ONLY ($0 dry run of the open package, docs/open_package_readme.md "Dry run"): a scripted OpenAI-compatible /v1/chat/completions






















"""
from __future__ import annotations

import argparse, hashlib, http.server, json, os, re, threading, time

LOG = None
LOCK = threading.Lock()
                                                                                                                           
                                                                                                        
SORRY = os.environ.get("LRA_FAKE_SORRY_PROOFS", "") == "1"
BLIND = os.environ.get("LRA_FAKE_BLIND", "")                                                                                        
_REF = re.compile(r"original\.lean \(the REFERENCE proof\):\n```lean\n(.*?)\n```", re.S)
_BLIND_STMT = re.compile(r"candidate\.lean \(the statement; the body is yours to write\):\n```lean\n(.*?)\s*:= by\n\s*sorry\n```", re.S)


def _text(c) -> str:
    return " ".join(str(x.get("text", "")) for x in c if isinstance(x, dict)) if isinstance(c, list) else str(c or "")
STYLE = os.environ.get("LRA_FAKE_STYLE", "rewrites")
_RW_CUR = re.compile(r"(?:BEST SO FAR|CURRENT PROOF) \([^\n]*\n```lean\n(.*?)\n```", re.S)                                       
_RW_FAIL = re.compile(r"FAILING REWRITE:\n```lean\n(.*?)\n```", re.S)                                                            
RW_BROKEN = "exact dry_run_no_such_lemma"


def is_style(body: dict) -> bool:
    return any(m.get("role") == "system" and "proof golfer" in str(m.get("content")) for m in body.get("messages") or [])


def style_proofs(body: dict) -> list:
    """The style step's answer (module docstring) on the proof its prompt shows."""
    t = next((str(m.get("content")) for m in body.get("messages") or [] if m.get("role") == "user"), "")
    m = _RW_FAIL.search(t)
    if m:
        return [{"label": "fix", "strategy": "drop the broken line", "declaration": "\n".join(l for l in m.group(1).split("\n") if RW_BROKEN not in l)}]
    m = _RW_CUR.search(t)
    if not m:
        return []
    base = m.group(1)
    hyg = re.sub(r":=\s*by\s*\n", ":= by unhygienic\n", base, count=1) if "unhygienic" not in base and ":= by" in base else base
    out = [{"label": "c0", "strategy": "unchanged", "declaration": base},
           {"label": "c1", "strategy": "unhygienic", "declaration": hyg},
           {"label": "c2", "strategy": "broken", "declaration": base.rstrip() + "\n  " + RW_BROKEN},
           {"label": "c3", "strategy": "retyped statement", "declaration": base.replace(" :", "  :", 1)}]
    dep = "\n".join(l for l in base.split("\n") if l.strip() != "skip")
    if dep != base:
        out.insert(0, {"label": "c4", "strategy": "padding removed", "declaration": dep})
    return out[:4]


def hostile_proofs(body: dict) -> list:
    """LRA_FAKE_STYLE=hostile (module docstring): cheating rewrites of the proof the prompt shows; none may ever be accepted."""
    t = next((str(m.get("content")) for m in body.get("messages") or [] if m.get("role") == "user"), "")
    m = _RW_FAIL.search(t) or _RW_CUR.search(t)
    if not m or ":= by" not in m.group(1):
        return []
    base = m.group(1)
    head = base[:base.index(":= by") + len(":= by")] + "\n  "
    if _RW_FAIL.search(t):                                                                                    
        orig = re.search(r"ORIGINAL VERIFIED PROOF[^\n]*\n```lean\n(.*?)\n```", t, re.S)
        return [{"label": "aux", "declaration": (orig.group(1) if orig else base).rstrip() + "\n\ntheorem style_hostile_aux : True := trivial"}]
    return [{"label": "stop", "declaration": head + "stop\n  simp"}, {"label": "impossible", "declaration": head + "exfalso; impossible by simp"},
            {"label": "sorry", "declaration": head + "sorry"}, {"label": "native", "declaration": head + "native_decide"}]


def step(body: dict) -> dict:
    msgs = body.get("messages") or []
    k = sum(1 for m in msgs if m.get("role") == "assistant")
    opening = next((m.get("content") for m in msgs if m.get("role") == "user"), "") or ""
    if isinstance(opening, list):
        opening = " ".join(str(x.get("text", "")) for x in opening if isinstance(x, dict))
    ref = re.search(r"original\.lean \(the REFERENCE proof\):\n```lean\n(.*?)\n```", opening, re.S)
    ref = ref.group(1) if ref else ""
    if "BLIND START" in opening:                                                                                                 
        shown = [m_.group(1) for m_ in (_REF.search(_text(m.get("content"))) for m in msgs if m.get("role") == "user") if m_]
        ref = shown[-1] if shown else ""
        st = _BLIND_STMT.search(opening)
        if k == 0 and st:
            return {"tool": "lean_skeleton", "args": {"content": st.group(1) + " := by\n  all_goals sorry"}}
        if k == 1:
            return {"tool": "lean_check", "args": {"path": "candidate.lean"}}
        if k == 2 and BLIND == "peek" and st:
            nm = re.search(r"\b(?:theorem|lemma)\s+(\S+)", st.group(1))
            return {"tool": "shell", "args": {"command": f"grep -rn {nm.group(1) if nm else 'x'} . | head -3"}}
        if k == 2:
            return {"tool": "lean_goals", "args": {"path": "candidate.lean", "depth": 1}}
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


class H(http.server.BaseHTTPRequestHandler):
    def log_message(self, *a):
        pass

    def _send(self, code: int, obj: dict):
        out = json.dumps(obj).encode()
        self.send_response(code); self.send_header("Content-Type", "application/json"); self.send_header("Content-Length", str(len(out)))
        self.end_headers(); self.wfile.write(out)

    def do_GET(self):
        self._send(200, {"data": [{"id": "glm-5.3-flash", "object": "model"}]})

    def do_POST(self):
        body = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
        if is_style(body):
            return self.style(body)
        s = step(body)
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


    def style(self, body: dict):
        if LOG:
            with LOCK, open(LOG, "a") as fh:
                fh.write(json.dumps({"style": STYLE, "step": "submit_proofs", "max_tokens": body.get("max_tokens"),
                                     "chat_template_kwargs": body.get("chat_template_kwargs"), "reasoning_effort": body.get("reasoning_effort"),
                                     "tools": [t.get("function", {}).get("name") for t in body.get("tools") or []]}) + "\n")
        if STYLE == "hang":
            time.sleep(float(os.environ.get("LRA_FAKE_HANG_S", "3600")))
            return self._send(500, {"error": {"message": "fake server held the request", "code": 500}})
        if STYLE == "error":
            return self._send(500, {"error": {"message": "fake server error", "code": 500}})
        if STYLE == "empty":
            msg = {"role": "assistant", "content": None, "reasoning_content": "thinking " * 50}
            return self._send(200, {"choices": [{"message": msg, "finish_reason": "length"}], "usage": {"prompt_tokens": 3000, "completion_tokens": 7000}})
        if STYLE == "junk":
            msg = {"role": "assistant", "content": "\t\t\t \n" * 2000}
            return self._send(200, {"choices": [{"message": msg, "finish_reason": "stop"}], "usage": {"prompt_tokens": 3000, "completion_tokens": 7000}})
        props = hostile_proofs(body) if STYLE == "hostile" else style_proofs(body)
        call = {"id": "call_style", "type": "function", "function": {"name": "submit_proofs", "arguments": json.dumps({"proofs": props})}}
        msg = {"role": "assistant", "content": None, "reasoning_content": "style rehearsal", "tool_calls": [call]}
        self._send(200, {"choices": [{"message": msg, "finish_reason": "tool_calls"}], "usage": {"prompt_tokens": 3000, "completion_tokens": 300}})


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
