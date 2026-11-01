"""Deterministic self-test of the agent harness with a scripted fake model (cycle 46, 2026-10-08).

Live smoke runs could not verify harness changes: a 3-turn z.ai run took the short-polish path and never wrote candidate.lean, and
turn-0 truncations ate the budget. This test starts a local OpenAI-compatible server that replays a fixed script of model responses,
runs harness/agent.py against it (--endpoint openai, scratch work root, model name `fake-selftest` so nothing is attributable to
GLM), records every request the harness sends, and asserts on what the model would have seen. No API calls, no bank writes: the
run directory is moved into the scratch root afterwards.

    python3 harness/selftest.py            # prints PASS/FAIL per check, exit 1 on any failure

Checks:
  opening_move     the first request ends with the OPENING MOVE line (runs longer than 10 turns)
  trunc_handback   a capped no-tool turn is answered with the tail of the cut reasoning (z.ai path: --no-budget-forcing)
  auto_check       writing candidate.lean returns an automatic lean_check result in the same tool result
  dup_note         writing it again unchanged returns the duplicate note, not a second compile
  finish_guard     an early finish is refused while a third of the budget remains
  noop_delete      a tactic left after the goal is closed (\"No goals\") is deleted by the auto-check and reported
  rw_repair        a failed rewrite (wrong rule direction) in a written candidate is repaired by the auto-check and reported
  text_end_guard   a turn that ends with text only (no tool call) is refused like an early finish while a third of the budget remains
  compat_why       a variant that compiles on the primary toolchain but not on an older one is reported with the errors there and
                   the names that do exist there (fixture: a real a4 candidate that fails on v4.26.0 and v4.25.0)
  closed_lessons   (--closed-lessons) the first message carries the three habits from the closed lines, and only with the flag
  from_reference_guard  (--from-reference on a workspace with three flat runs at ~70, adaptive turns on) the run stays a restart:
                   no FRESH START, no structural brief or effort raise, the strategy brief kept, the --turns budget as given,
                   and the notes in the opening message (a warm restart)
  variant_scores   (--variant-scores) a compiling variant that is not a new best shows its provisional score and vs_best, not null
  error_lines      (--relative-error-lines) a failing line is reported as `line k `<text>`` of the declaration, not the scratch file's line
  simp_prune       (--simp-prune) an unused lemma added to a `simp only [...]` list of the a4 best is dropped by the write's auto-check
  upstream_digest  a project problem's first message carries the precomputed upstream version of the theorem (CCS congr_choice:
                   simplified upstream), so the model need not search git history for it
  nothink_markup   (z.ai path) the retry's tool call arrives as GLM template markup in text: parsed and executed
  nothink_rescue   (z.ai path, Anthropic API) a capped thinking turn is re-asked once with thinking disabled and the cut reasoning
                   appended to the last user message; the rescued tool call is executed (auto-check result reaches the next request)
"""
from __future__ import annotations

import http.server, json, os, pathlib, shutil, socket, subprocess, sys, tempfile, threading, time

ROOT = pathlib.Path(__file__).resolve().parents[1]
PROBLEM = "putnam_1964_b2"
REASONING_TAIL = "PLANNED-EDIT-MARKER: V1 drops the have, V2 swaps the closer"


def script(candidate: str) -> list[dict]:
    return [
        {"length": True, "reasoning": "x " * 2000 + REASONING_TAIL},                              # turn 0: capped while thinking
        {"tool": "write_file", "args": {"path": "candidate.lean", "content": candidate}},          # turn 1: new candidate -> auto check
        {"tool": "write_file", "args": {"path": "candidate.lean", "content": candidate}},          # turn 2: same text -> duplicate note
        {"tool": "finish", "args": {}},                                                             # turn 3: early finish -> refused
    ]


class Fake(http.server.BaseHTTPRequestHandler):
    steps: list[dict] = []; seen: list[dict] = []

    def log_message(self, *a):   # quiet
        pass

    def do_POST(self):
        body = json.loads(self.rfile.read(int(self.headers["Content-Length"])))
        Fake.seen.append(body)
        step = Fake.steps[min(len(Fake.seen) - 1, len(Fake.steps) - 1)]
        if self.path.endswith("/messages"):
            return self.anthropic(body, step)
        msg: dict = {"role": "assistant", "content": None}
        if "text" in step:
            msg["content"] = step["text"]; fr = "stop"
        elif step.get("length"):
            msg["reasoning_content"] = step["reasoning"]; fr = "length"
        else:
            msg["tool_calls"] = [{"id": f"call_{len(Fake.seen)}", "type": "function",
                                  "function": {"name": step["tool"], "arguments": json.dumps(step["args"])}}]; fr = "tool_calls"
        out = json.dumps({"choices": [{"message": msg, "finish_reason": fr}], "usage": {"prompt_tokens": 1000, "completion_tokens": 100}}).encode()
        self.send_response(200); self.send_header("Content-Type", "application/json"); self.send_header("Content-Length", str(len(out)))
        self.end_headers(); self.wfile.write(out)

    def anthropic(self, body: dict, step: dict):
        """Anthropic Messages API (what the z.ai code path speaks): JSON for create(), SSE for stream()."""
        if step.get("length"):
            blocks = [{"type": "thinking", "thinking": step["reasoning"], "signature": ""}]; stop = "max_tokens"
        elif "text" in step:
            blocks = [{"type": "text", "text": step["text"]}]; stop = "end_turn"
        else:
            blocks = [{"type": "tool_use", "id": f"toolu_{len(Fake.seen)}", "name": step["tool"], "input": step["args"]}]; stop = "tool_use"
        msg = {"id": f"msg_{len(Fake.seen)}", "type": "message", "role": "assistant", "model": "fake", "content": blocks,
               "stop_reason": stop, "stop_sequence": None, "usage": {"input_tokens": 1000, "output_tokens": 100}}
        if not body.get("stream"):
            out = json.dumps(msg).encode()
            self.send_response(200); self.send_header("Content-Type", "application/json"); self.send_header("Content-Length", str(len(out)))
            self.end_headers(); self.wfile.write(out); return
        ev = [("message_start", {"type": "message_start", "message": {**msg, "content": [], "stop_reason": None,
                                                                         "usage": {"input_tokens": 1000, "output_tokens": 0}}})]
        for i, b in enumerate(blocks):
            if b["type"] == "text":
                ev += [("content_block_start", {"type": "content_block_start", "index": i, "content_block": {"type": "text", "text": ""}}),
                       ("content_block_delta", {"type": "content_block_delta", "index": i, "delta": {"type": "text_delta", "text": b["text"]}})]
            elif b["type"] == "thinking":
                ev += [("content_block_start", {"type": "content_block_start", "index": i, "content_block": {"type": "thinking", "thinking": "", "signature": ""}}),
                       ("content_block_delta", {"type": "content_block_delta", "index": i, "delta": {"type": "thinking_delta", "thinking": b["thinking"]}})]
            else:
                ev += [("content_block_start", {"type": "content_block_start", "index": i, "content_block": {**b, "input": {}}}),
                       ("content_block_delta", {"type": "content_block_delta", "index": i, "delta": {"type": "input_json_delta", "partial_json": json.dumps(b["input"])}})]
            ev.append(("content_block_stop", {"type": "content_block_stop", "index": i}))
        ev += [("message_delta", {"type": "message_delta", "delta": {"stop_reason": stop, "stop_sequence": None}, "usage": {"output_tokens": 100}}),
               ("message_stop", {"type": "message_stop"})]
        self.send_response(200); self.send_header("Content-Type", "text/event-stream"); self.end_headers()
        for name, data in ev:
            self.wfile.write(f"event: {name}\ndata: {json.dumps(data)}\n\n".encode()); self.wfile.flush()


def text_of(m: dict) -> str:
    c = m.get("content")
    return c if isinstance(c, str) else json.dumps(c, ensure_ascii=False)


def run_agent(port: int, scratch: pathlib.Path, zai: bool, extra: tuple = ()) -> tuple[subprocess.CompletedProcess, float]:
    run_id = f"selftest-{'zai' if zai else 'oai'}-{time.strftime('%m%d-%H%M%S')}"
    cmd = [sys.executable, "harness/agent.py", "--problems", PROBLEM, "--turns", "12", "--no-adaptive-turns", "--workers", "1",
           "--max-tokens", "4000", "--model", "fake-selftest", "--reasoning-effort", "low", "--max-api-retries", "1",
           "--run-id", run_id, "--work-root", str(scratch / f"work-{run_id}"), *extra]
    env = dict(os.environ)
    if zai:
        env["LRA_SELFTEST_ANTHROPIC_URL"] = f"http://127.0.0.1:{port}"
    else:
        cmd += ["--endpoint", "openai", "--base-url", f"http://127.0.0.1:{port}/v1", "--api-model", "fake", "--no-budget-forcing"]
    t0 = time.time()
    pr = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True, timeout=1800, env=env)
    run_dir = ROOT / "probe/runs" / run_id
    if run_dir.exists():
        shutil.move(str(run_dir), str(scratch / run_id))   # keep fake records out of the bank import
    return pr, time.time() - t0


def last_user_text(req: dict) -> str:
    return text_of(req["messages"][-1]) if req.get("messages") else ""


def main() -> int:
    global PROBLEM
    best = (ROOT / f"harness/work/{PROBLEM}/best.lean")
    candidate = best.read_text().rstrip() + "\n\n"   # same proof, new bytes: a new sha, so it is compiled, not a duplicate
    with socket.socket() as s:
        s.bind(("127.0.0.1", 0)); port = s.getsockname()[1]
    srv = http.server.ThreadingHTTPServer(("127.0.0.1", port), Fake)
    threading.Thread(target=srv.serve_forever, daemon=True).start()
    scratch = pathlib.Path(tempfile.mkdtemp(prefix="lra-selftest-"))

    # run 1: self-hosted (OpenAI) path without budget forcing
    Fake.steps = script(candidate); Fake.seen = []
    pr1, sec1 = run_agent(port, scratch, zai=False)
    reqs = Fake.seen
    first_user = next((text_of(m) for m in reqs[0]["messages"] if m["role"] == "user"), "") if reqs else ""
    last_new = lambda i: last_user_text(reqs[i]) if i < len(reqs) else ""
    checks = {
        "opening_move": "OPENING MOVE" in first_user,
        "trunc_handback": REASONING_TAIL in last_new(1) and "Do not rewrite the current best unchanged" in last_new(1),
        "auto_check": "auto lean_check of candidate.lean" in last_new(2),
        "dup_note": "byte-identical to an attempt already checked" in last_new(3) and "auto lean_check" not in last_new(3),
        "finish_guard": "finish rejected" in last_new(4),
    }
    oai_reqs = reqs

    # run 2: z.ai (Anthropic) path: capped thinking turn -> no-thinking rescue -> rescued write is executed
    Fake.steps = [{"length": True, "reasoning": "x " * 2000 + REASONING_TAIL},
                  {"tool": "write_file", "args": {"path": "candidate.lean", "content": candidate}},
                  {"tool": "finish", "args": {}}]
    Fake.seen = []
    OAI_ONLY = os.environ.get("LRA_SELFTEST_OAI_ONLY") == "1"   # 2026-10-09: replication without the Anthropic SDK runs only the OpenAI path
    pr2, sec2 = run_agent(port, scratch, zai=True) if not OAI_ONLY else (pr1, 0.0)
    z = Fake.seen

    # run 3: z.ai path, the no-thinking retry answers with GLM template markup in plain text instead of a tool_use block
    markup = ("<tool_call>write_file<arg_key>path</arg_key><arg_value>candidate.lean</arg_value>"
              f"<arg_key>content</arg_key><arg_value>{candidate}</arg_value></tool_call>")
    Fake.steps = [{"length": True, "reasoning": "x " * 2000 + REASONING_TAIL}, {"text": markup}, {"tool": "finish", "args": {}}]
    Fake.seen = []
    if not OAI_ONLY:
        pr3, sec3 = run_agent(port, scratch, zai=True)
        z3 = Fake.seen
        checks["nothink_markup"] = len(z3) > 2 and "auto lean_check of candidate.lean" in last_user_text(z3[2])

    # run 4: OpenAI path, the model ends its first turn with plain text (gpt-oss in the second-model screen): the run must continue
    Fake.steps = [{"text": "I think the proof is already optimal."}, {"tool": "finish", "args": {}}]
    Fake.seen = []
    pr4, sec4 = run_agent(port, scratch, zai=False)
    z4 = Fake.seen
    checks["text_end_guard"] = len(z4) > 1 and "You ended your turn without a tool call" in last_user_text(z4[1])

    # run 5: a candidate whose rewrite rule has the wrong direction (putnam_1964_a4 best with `← key (n - i)` reversed): the write's
    # auto-check must repair it (reversed rule / simp_rw / erw / simp only) and report it (cycle 53)
    a4 = (ROOT / "harness/work/putnam_1964_a4/best.lean").read_text()
    broken = a4.replace("← key (n - i)", "key (n - i)", 1)
    if broken != a4:
        PROBLEM, saved = "putnam_1964_a4", PROBLEM
        Fake.steps = [{"tool": "write_file", "args": {"path": "candidate.lean", "content": broken}}, {"tool": "finish", "args": {}}]
        Fake.seen = []
        pr5, sec5 = run_agent(port, scratch, zai=False)
        PROBLEM = saved
        z5 = Fake.seen
        checks["rw_repair"] = len(z5) > 1 and "failed rewrite repaired" in last_user_text(z5[1])
    else:
        checks["rw_repair"] = False
    # run 6: a superfluous tactic after the goal is closed ("No goals to be solved"): the auto-check must delete the no-op line (cycle 54)
    b2 = (ROOT / f"harness/work/{PROBLEM}/best.lean").read_text().rstrip()
    indent = next((l[:len(l) - len(l.lstrip())] for l in reversed(b2.split("\n")) if l.strip() and l.startswith(" ")), "  ")
    Fake.steps = [{"tool": "write_file", "args": {"path": "candidate.lean", "content": b2 + "\n" + indent + "rfl\n"}}, {"tool": "finish", "args": {}}]
    Fake.seen = []
    pr6, sec6 = run_agent(port, scratch, zai=False)
    z6 = Fake.seen
    checks["noop_delete"] = len(z6) > 1 and "deleted no-op line" in last_user_text(z6[1])

    # run 6b (--relative-error-lines, cycle 76): a failing line inserted after `classical` in the b2 best. The write's auto-check must
    # report it as `line k `<text>`` of the declaration, not as the scratch file's line (head lines + k).
    _ls = b2.split("\n"); _k = next((i for i, l in enumerate(_ls) if l.strip() == "classical"), 0) + 2   # 1-based line of the insert
    _bad = "\n".join(_ls[:_k - 1] + [indent + "have hx : (1 : ℕ) = 2 := rfl"] + _ls[_k - 1:])
    Fake.steps = [{"tool": "write_file", "args": {"path": "candidate.lean", "content": _bad + "\n"}}, {"tool": "finish", "args": {}}]
    Fake.seen = []
    pr6b, sec6b = run_agent(port, scratch, zai=False, extra=("--relative-error-lines",))
    z6b = Fake.seen
    sys.path.insert(0, str(ROOT))   # this script runs with harness/ as its import root
    from harness.leantools import head_line_count as _hlc6b, ROWS as _R6b
    from probe.verify_candidates import newest_first as _nf6b
    _raw6b = _hlc6b(_R6b[PROBLEM], _nf6b(_R6b[PROBLEM]["version_info"])[0]) + _k
    _t6b = last_user_text(z6b[1]) if len(z6b) > 1 else ""
    checks["error_lines"] = f"line {_k} `have hx" in _t6b and f"{_raw6b}:" not in _t6b

    # run 6d (--closed-lessons, cycle 80): the first message carries the three habits only with the flag
    Fake.steps = [{"tool": "finish", "args": {}}, {"tool": "finish", "args": {}}]
    Fake.seen = []
    pr6d, sec6d = run_agent(port, scratch, zai=False, extra=("--closed-lessons",))
    z6d = Fake.seen
    _f6d = next((text_of(m) for m in z6d[0]["messages"] if m["role"] == "user"), "") if z6d else ""
    checks["closed_lessons"] = "THREE HABITS OF THE STRONGEST PROVERS" in _f6d and "THREE HABITS" not in first_user

    # run 6e (BFS deep dive, 2026-10-09): a --from-reference restart on a workspace with history (three flat runs at ~70, like the A100
    # copies harness/exp_variants.sh uses) must stay a restart: the adaptive rules must not turn it into a FRESH START or a 6-turn polish,
    # structural mode must not add its brief and effort raise, the strategy brief stays, and the budget is --turns as given.
    _w6e = scratch / "work-6e"; (_w6e / PROBLEM).mkdir(parents=True, exist_ok=True)
    _att6e = [{"run_id": f"st-r{i}", "ok": True, "score": s, "sha": f"s{i}", "t": f"2026-10-0{i + 1}T00:00:00"} for i, s in enumerate((69.8, 69.9, 70.0))]
    (_w6e / PROBLEM / "notes.md").write_text("# Notes (yours to keep; persisted across runs)\n- NOTES-6E-MARKER: lemma names from earlier runs\n")
    (_w6e / PROBLEM / "state.json").write_text(json.dumps({"problem": PROBLEM, "best": {"score": 70.0, "proof": None, "tokens": 1, "heartbeats": None},
                                                            "attempts": _att6e, "runs": [{"run_id": f"st-r{i}"} for i in range(3)]}))
    Fake.steps = [{"tool": "finish", "args": {}}, {"tool": "finish", "args": {}}]
    Fake.seen = []
    pr6e, sec6e = run_agent(port, scratch, zai=False, extra=("--adaptive-turns", "--from-reference", "--brief", "restructure", "--work-root", str(_w6e)))
    _f6e = next((text_of(m) for m in Fake.seen[0]["messages"] if m["role"] == "user"), "") if Fake.seen else ""
    checks["from_reference_guard"] = ("scout brief: restructure" in pr6e.stdout and "FRESH START" not in pr6e.stdout and "structural mode" not in pr6e.stdout
                                      and "SCOUT RUN" in _f6e and "STRUCTURAL PASS" not in _f6e and "You have 12 tool turns" in _f6e
                                      and "NOTES-6E-MARKER" in _f6e)   # warm: the notes reach the opening message

    # run 6c (--variant-scores, cycle 78): a batch of the b2 best (a new best in the scratch workspace) and the same proof with a second
    # `classical` (compiles, not above the new best). Row b must carry a numeric provisional score and a negative vs_best, not score null.
    _b2c = "\n".join(_ls[:_k - 1] + [indent + "classical"] + _ls[_k - 1:])
    Fake.steps = [{"tool": "lean_check_variants", "args": {"variants": [{"label": "a", "content": b2 + "\n"}, {"label": "b", "content": _b2c + "\n"}]}},
                  {"tool": "finish", "args": {}}]
    Fake.seen = []
    pr6c, sec6c = run_agent(port, scratch, zai=False, extra=("--variant-scores",))
    z6c = Fake.seen
    try:
        _rows6c = {r_["label"]: r_ for r_ in json.loads(last_user_text(z6c[1]))["variants"]}
        checks["variant_scores"] = (isinstance(_rows6c["b"].get("score"), (int, float)) and _rows6c["b"].get("vs_best", 1) < 0
                                    and "provisional" in str(_rows6c["b"].get("score_kind")) and (_rows6c["a"].get("vs_best") or 0) > 0)
    except Exception:  # noqa: BLE001
        checks["variant_scores"] = False

    # run 7: a variant that compiles on the primary toolchain but not on the older ones (a real fresh-zai-p1 a4 candidate: `.not_finite`
    # does not resolve on v4.26.0/v4.25.0): the batch result must say why, per variant (cycle 56)
    fixture = (ROOT / "harness/selftest_fixtures/a4_fails_v426.lean").read_text()
    PROBLEM, saved = "putnam_1964_a4", PROBLEM
    Fake.steps = [{"tool": "lean_check_variants", "args": {"variants": [{"label": "V1", "content": fixture}]}}, {"tool": "finish", "args": {}}]
    Fake.seen = []
    pr7, sec7 = run_agent(port, scratch, zai=False)
    PROBLEM = saved
    z7 = Fake.seen
    r7 = last_user_text(z7[1]) if len(z7) > 1 else ""
    checks["compat_why"] = "compat_failures" in r7 and "v4.26.0" in r7 and "not_finite" in r7 and "did_you_mean_here" in r7

    # run 8: a project problem whose proof was later simplified upstream (CCS bisimilarity_congr_choice: 180 tokens at cslib HEAD vs 251):
    # the first message must carry the precomputed upstream version, so the model does not dig through git log for it (cycle 57)
    PROBLEM, saved = "Cslib.CCS.bisimilarity_congr_choice", PROBLEM
    Fake.steps = [{"tool": "finish", "args": {}}]
    Fake.seen = []
    pr8, sec8 = run_agent(port, scratch, zai=False)
    PROBLEM = saved
    z8 = Fake.seen
    f8 = next((text_of(m) for m in z8[0]["messages"] if m["role"] == "user"), "") if z8 else ""
    checks["upstream_digest"] = "UPSTREAM (precomputed" in f8 and "bisimilarity_congr_choice` at upstream HEAD" in f8 and "```lean" in f8.split("UPSTREAM (precomputed", 1)[-1]

    # run 9 (--simp-prune): the a4 best with an unused lemma added to its `simp only [...]` list: the write's auto-check must drop it (cycle 58)
    a4b = (ROOT / "harness/work/putnam_1964_a4/best.lean").read_text()
    padded = a4b.replace("simp only [Prod.mk.injEq]", "simp only [Prod.mk.injEq, List.length_nil]", 1)
    if padded != a4b:
        PROBLEM, saved = "putnam_1964_a4", PROBLEM
        Fake.steps = [{"tool": "write_file", "args": {"path": "candidate.lean", "content": padded}}, {"tool": "finish", "args": {}}]
        Fake.seen = []
        pr9, sec9 = run_agent(port, scratch, zai=False, extra=("--simp-prune",))
        PROBLEM = saved
        z9 = Fake.seen
        checks["simp_prune"] = len(z9) > 1 and "auto_pruned" in last_user_text(z9[1]) and "dropped 1 unused lemma" in last_user_text(z9[1])
    else:
        checks["simp_prune"] = False

    srv.shutdown(); srv.server_close()   # after the LAST run: a shut-down but still bound socket accepts connections and never answers
    rescue = z[1] if len(z) > 1 else {}
    if not OAI_ONLY:
      checks["nothink_rescue"] = (bool(z) and z[0].get("stream") is True and rescue.get("stream") in (None, False)
                                and rescue.get("thinking") == {"type": "disabled"} and REASONING_TAIL in last_user_text(rescue)
                                and len(z) > 2 and "auto lean_check of candidate.lean" in last_user_text(z[2]))

    for k, ok in checks.items():
        print(f"{'PASS' if ok else 'FAIL'}  {k}")
    print(f"oai: requests={len(oai_reqs)} rc={pr1.returncode} {sec1:.0f}s | zai: requests={len(z)} rc={pr2.returncode} {sec2:.0f}s | scratch={scratch}")
    if not all(checks.values()):
        for pr in (pr1, pr4, pr6, pr6b, pr6c, pr6d, pr6e, pr7, pr8) + ((pr2, pr3) if not OAI_ONLY else ()) + ((pr5,) if 'pr5' in locals() else ()):
            print(pr.stdout[-1500:], pr.stderr[-1500:], sep="\n")
        for i in range(min(4, len(z))):
            print(f"--- zai request {i} stream={z[i].get('stream')} thinking={z[i].get('thinking')} last message:\n{last_user_text(z[i])[:400]}")
    return 0 if all(checks.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
