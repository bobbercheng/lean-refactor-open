"""Agentic refactoring harness: the model gets a workspace and tools
(read_file, write_file, lean_check, finish) and iterates until its turn
budget runs out. Every compiling lean_check result is scored and recorded, so
the harness keeps the best candidate even if the model never calls finish.

Runs against the z.ai Anthropic-compatible endpoint (dev-only) or any
Anthropic-compatible server (self-served vLLM with an Anthropic shim later).
"""
from __future__ import annotations

import argparse, json, os, re, sys, time, hashlib, pathlib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
try:   # the Anthropic SDK serves only the z.ai / OpenRouter / self-test endpoints; replication runs --endpoint openai without it
    import anthropic  # noqa: E402
    from llm.zai_client import _key, BASE_URL  # noqa: E402
except ImportError:   # 2026-10-09: the organizers replicate on their own server, so everything not essential is optional
    import types

    def _no_sdk(*_a, **_k):
        raise SystemExit("the anthropic package is needed only for --endpoint zai/openrouter: pip install anthropic, or use --endpoint openai")
    anthropic = types.SimpleNamespace(Anthropic=_no_sdk, RateLimitError=type("RateLimitError", (Exception,), {}),
                                      APIStatusError=type("APIStatusError", (Exception,), {}))   # `except anthropic.X` clauses still evaluate
    _key, BASE_URL = _no_sdk, None
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402
from scorer.forbidden import check_forbidden  # noqa: E402
from scorer.compile import compile_putnam, compile_project, file_prefix  # noqa: E402
from scorer.score import len_pct, hb_pct_local, compat_pct, problem_score  # noqa: E402
from probe.verify_candidates import newest_first  # noqa: E402
from harness.leantools import digest_error  # noqa: E402

TOOLS = [
    {"name": "read_file", "description": "Read a file in the workspace. Files: original.lean (the reference declaration, compiles), context.lean (imports/header or the surrounding file prefix the declaration lives in — large, read ranges), candidate.lean (your current attempt). Optional start/end line numbers (1-based, inclusive).",
     "input_schema": {"type": "object", "properties": {"path": {"type": "string"}, "start": {"type": "integer"}, "end": {"type": "integer"}}, "required": ["path"]}},
    {"name": "write_file", "description": "Write a file in the workspace (normally candidate.lean with the COMPLETE declaration: the statement byte-for-byte as in original.lean, then `:=` and your proof). Writing candidate.lean also runs lean_check on it and returns the result, so no separate lean_check is needed.",
     "input_schema": {"type": "object", "properties": {"path": {"type": "string"}, "content": {"type": "string"}}, "required": ["path", "content"]}},
    {"name": "lean_check", "description": "Compile the full declaration in a workspace file (default candidate.lean) inside the real project environment on the primary toolchain. Returns ok, errors (line:col relative to the declaration), warnings, heartbeats, token count, and the predicted score vs the reference. If it compiles and improves, also reports compatibility on the other toolchains. Each call costs a few seconds; use it often.",
     "input_schema": {"type": "object", "properties": {"path": {"type": "string"}}}},
    {"name": "lean_run", "description": "Run a scratch Lean snippet in the problem's real environment (same imports/context as the declaration) and return the compiler messages. Use it to discover lemma names and tactics: e.g. `#check Finset.sum_ite_eq'`, `example : <goal> := by exact?`, `example ... := by simp?`, `#print axioms`. The snippet is appended after the context; do not repeat the imports. Each run costs a few seconds.",
     "input_schema": {"type": "object", "properties": {"code": {"type": "string"}}, "required": ["code"]}},
    {"name": "shell", "description": "Run a shell command (bash) in the workspace for exploration: grep/rg the project's Lean sources and Mathlib for lemma names and proof idioms, `git log -p`/`git show` on the problem's file in the project clone to find how the same proof was later simplified upstream, ls/cat/head/sed -n to read other files, or `lake env lean` on a scratch file. Timeout 120 s, output truncated. No network, no writes outside the workspace, no rm/mv/git checkout/lake build.",
     "input_schema": {"type": "object", "properties": {"command": {"type": "string"}}, "required": ["command"]}},
    {"name": "finish", "description": "Stop when you believe the best candidate has been checked (the harness keeps the best compiling candidate it has seen). Accepted only after at least 5 lean_checks in this run or in the last 3 turns; earlier calls are rejected with guidance.",
     "input_schema": {"type": "object", "properties": {"summary": {"type": "string"}}}},
]

SYSTEM = """You are a Lean 4 proof engineer working in a small workspace with tools. Goal: produce a proof of the SAME theorem that scores higher than the reference on
  score = mean(length_reduction%, heartbeat_reduction%, compatibility%),
where length = token count of the proof body (every bracket/operator is a token, dotted names are one token, comments don't count), heartbeats = elaboration cost, compatibility = fraction of listed toolchains on which it compiles unchanged.

Workflow (R3, operator 2026-10-08): REWRITE FIRST. Read original.lean (and context.lean if you need surrounding definitions) for its mathematical plan, then write your own proof of that plan top-down: outline it with `sorry` holes, check the outline with lean_skeleton (it returns each hole's goal), fill one hole at a time, then lean_check the complete candidate. EDIT incrementally (change one thing, lean_check, keep what compiles) only when the problem is too hard to write fresh, or to polish a proof that already compiles; if edits stall (about 8 checks without a new best), start a NEW rewrite with a different architecture instead of more edits. The harness remembers the best compiling candidate; a failed check costs nothing but a turn, so check early and often (every 1–2 turns). A rewrite built hole by hole does not fail all at once; never write a large proof blind and check it only at the end. lean_check returns linter_hints: tactics that do nothing and unused simp arguments are free deletions — do those first. Use lean_run to find lemma names and closing tactics (`example : <goal> := by exact?`, `simp?`, `#check`), and shell (grep/rg over the sources, `git log -p` on the file to see how upstream later simplified this proof) when you need real names or idioms rather than guesses; inside lean_run snippets `sorry` IS allowed, so you can test a proof skeleton with `sorry` placeholders and read the remaining goals. Never put sorry/admit/axiom/native_decide in candidate.lean, never add auxiliary declarations, `open`, or `set_option` outside the proof. CLOSERS: AUTOMATION FIRST (`grind` with lemma hints, forward hints `grind [→ lemma]` for lemmas concluding ∃ or a constructor, `simp`, `omega`, `aesop`, `solve_by_elim`, `linear_combination`): it is robust, while hand-written terms are the most common failure (wrong hypothesis, argument order). Once the proof compiles, replace an automation call by an explicit term only where the `axis` in lean_check says the heartbeats saved are worth more than the tokens added, and keep the swap only if it compiles and scores higher; on small proofs one `grind` costs ~200 heartbeats, so count calls. When out of ideas or budget, call finish."""


_CLAIM_RE = re.compile(r"\b(unavoidable|impossible|cannot|can't|does not exist|doesn't exist|never|not needed|no longer needed|floor|minimal|tight|must|required|only way|no way|dead end|confirmed negative)\b", re.I)


def degenerate_tail(raw: str, window: int = 2000) -> bool:
    """True when a tool call's raw arguments END in degenerate repetition (2026-10-11 warm-up Sol run: all 26 tool calls cut at the
    output cap were this: 20 whitespace runs `\\t\\t\\t \\n` of varying length, 6 a short line like `\\n  all_goals sorry` repeated hundreds of
    times; no legitimate long write). Whitespace-only tail (escaped or not), or a unit of <= 40 chars repeated >= 20 times (<= 5% mismatches)."""
    tail = raw[-window:]
    if len(tail) < 200:
        return False
    if len(re.sub(r"(\\[tnr]|\s)+", "", tail)) < 0.1 * len(tail):
        return True
    return any(len(tail) >= 20 * k and sum(a != b for a, b in zip(tail, tail[k:])) <= 0.05 * (len(tail) - k) for k in range(1, 41))


def unverified_claims(notes: str, limit: int = 8) -> list[str]:
    """Negative / absolute claims in notes.md without a `[tested: …]` tag (cycle 36). Section headers ("What FAILED (do not retry)") and hard
    submission rules (statement byte-identical, forbidden constructs) are skipped: those are not hypotheses."""
    out = []
    for line in notes.splitlines():
        s = line.strip(" -*#>\t")
        if not (30 <= len(s) <= 220) or not _CLAIM_RE.search(s) or re.search(r"\[tested", s, re.I):
            continue
        if re.search(r"statement|byte-for-byte|forbidden|sorry|axiom|native_decide", s, re.I):
            continue
        if s not in out:
            out.append(s)
    return out[:limit]


class Workspace:
    """Per-problem persistent workspace (keyed by problem, not by run):
    original.lean, context.lean, candidate.lean (working copy), best.lean,
    notes.md (model-owned memory), state.json (best record + attempt history)."""

    def __init__(self, root: Path, row: dict, version: str, fresh: bool = False):
        self.root = root; self.row = row; self.version = version
        root.mkdir(parents=True, exist_ok=True)
        (root / "original.lean").write_text(row["src"].rstrip() + "\n")
        ctx = row["header"] if row["source"] == "putnambench" else file_prefix(row, version)
        (root / "context.lean").write_text(ctx)
        self.state_path = root / "state.json"
        if fresh or not self.state_path.exists():
            if fresh and self.state_path.exists():
                self.state_path.unlink()   # otherwise save()'s merge-with-disk resurrects the old runs/attempts (A100 POC: aborted runs gave fresh problems 6-turn budgets)
            self.state = {"problem": row["name"], "best": {"score": 33.33, "proof": None, "tokens": row["proof_length"], "heartbeats": None}, "attempts": [], "runs": []}
            (root / "candidate.lean").write_text(row["src"].rstrip() + "\n")
            if not (root / "notes.md").exists() or fresh:
                (root / "notes.md").write_text("# Notes (yours to keep; persisted across runs)\n")
        else:
            self.state = json.loads(self.state_path.read_text())
            best = self.state["best"].get("proof")
            (root / "candidate.lean").write_text((best or row["src"]).rstrip() + "\n")
        self.save()

    def save(self) -> None:
        # merge with whatever another concurrent run wrote: keep the higher best, union attempts by sha
        try:
            disk = json.loads(self.state_path.read_text())
            if (disk.get("best") or {}).get("score", 0) > (self.state.get("best") or {}).get("score", 0):
                self.state["best"] = disk["best"]
            seen = {(a.get("sha"), a.get("run_id")) for a in self.state.get("attempts", [])}
            for a in disk.get("attempts", []):
                if (a.get("sha"), a.get("run_id")) not in seen:
                    self.state.setdefault("attempts", []).append(a)
            self.state["attempts"] = sorted(self.state["attempts"], key=lambda a: a.get("t", ""))[-200:]
            known = {r.get("run_id") for r in self.state.get("runs", [])}
            self.state.setdefault("runs", []).extend(r for r in disk.get("runs", []) if r.get("run_id") not in known)
        except Exception:  # noqa: BLE001
            pass
        self.state_path.write_text(json.dumps(self.state, ensure_ascii=False, indent=1))
        if self.state["best"].get("proof"):
            (self.root / "best.lean").write_text(self.state["best"]["proof"].rstrip() + "\n")

    def record_attempt(self, rec: dict) -> None:
        rec["t"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        self.state["attempts"].append(rec)
        self.state["attempts"] = self.state["attempts"][-200:]
        self.save()

    def digest(self, n: int = 8) -> str:
        b = self.state["best"]; at = self.state["attempts"]
        lines = [f"Prior work on this problem: {len(at)} checked attempts over {len(self.state['runs'])} earlier run(s). Best so far: score {b['score']} (tokens {b.get('tokens')}, heartbeats {b.get('heartbeats')}); candidate.lean holds it."]
        if at:
            lines.append("Most recent attempts (tokens, heartbeats, outcome):")
            for a in at[-n:]:
                lines.append(f"  - tok={a.get('tokens')} hb={a.get('heartbeats')} {'OK score=' + str(a.get('score')) if a.get('ok') else 'FAIL: ' + str(a.get('error', ''))[:140]}")
        wins = sorted((self.state.get("ledger") or {}).get("wins", []), key=lambda w: -w.get("d_score", 0))[:6]
        if wins:
            lines.append("WINNING EDITS from earlier runs (harness log, verbatim; the current best may have lost some after a restructure: "
                         "check each and re-apply what still fits):")
            for w in wins:
                lines.append(f"  [{w.get('run_id')} check {w.get('check')}: {w.get('d_score'):+} score, {w.get('d_tokens'):+} tokens, {w.get('d_heartbeats'):+} hb]\n"
                             + "\n".join("    " + l for l in (w.get("diff") or "").splitlines()[:12]))
        dead = (self.state.get("ledger") or {}).get("dead_names") or []
        if dead:   # harness/discover.py: unknown in this line's earlier compiles and never in one of its compiling proofs
            lines.append("NAMES THAT DO NOT EXIST in this environment (unknown in earlier runs' compiles; do not use them): "
                         + ", ".join(f"`{n}`" for n in dead[:15]))
        notes = (self.root / "notes.md").read_text().strip()
        if len(notes.splitlines()) > 1:
            lines.append("Your notes.md from earlier runs:\n" + notes[:3000])
            claims = unverified_claims(notes)
            if claims:
                lines.append("UNVERIFIED CLAIMS in these notes (cycle 36: the panel review found claims of this kind wrong on six problems: "
                             "'unavoidable', 'is the floor', 'grind never fires forward', 'set needed', 'a failed apply costs ~110 hb', 'tight'; each "
                             "blocked the move that later won). Treat them as hypotheses, not facts: if one blocks your most promising idea, test it with "
                             "one cheap check first, and write the result back as `[tested: <what you ran> -> <result>]`:\n"
                             + "\n".join("  ? " + c for c in claims))
        return "\n".join(lines)

    def path(self, p: str) -> Path:
        return self.root / Path(p).name


def run_problem(name: str, args, rows, hbs, out_dir: Path) -> dict:
    row = rows[name]; versions = newest_first(row["version_info"]); primary = versions[0]
    ws = Workspace(ROOT / args.work_root / re.sub(r"[^A-Za-z0-9_.-]", "_", name), row, primary, fresh=args.fresh)
    ws.state["runs"].append({"run_id": args.run_id, "model": args.model, "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}); ws.save()
    if args.endpoint == "openrouter":
        # Replication rung 2 (2026-10-06): same harness, GLM-5.3-Flash served by OpenRouter providers pinned to a
        # quantization (nvfp4 = Modal/CoreWeave). OpenRouter exposes an Anthropic-compatible Messages endpoint, so only the
        # base URL, key, model id and routing body differ.
        cl = anthropic.Anthropic(api_key=Path("~/.config/vexorium/openrouter_api_key").expanduser().read_text().strip(),
                                 base_url="https://openrouter.ai/api", timeout=1800, max_retries=0)  # SDK appends /v1/messages
        api_model = args.model if "/" in args.model else "z-ai/" + args.model
        extra_body = {"reasoning_effort": args.reasoning_effort, "reasoning": {"effort": args.reasoning_effort},
                      "provider": {"quantizations": [args.quant], "allow_fallbacks": False}}
        prov_model = f"{args.model}-{args.quant}@openrouter"
    elif args.endpoint == "openai":
        # Self-hosted rung (vLLM / SGLang OpenAI-compatible server, or any /chat/completions endpoint): llm/openai_compat.py
        # converts the Anthropic-shaped history + tools and returns a Message-like object; provenance names the serving.
        from llm import openai_compat as _oai
        cl = None
        _kp = Path(args.api_key_file).expanduser() if args.api_key_file else None
        _oai_key = _kp.read_text().strip() if _kp and _kp.exists() else "EMPTY"
        api_model = args.api_model or args.model
        # "default" sends no effort field: GLM's chat template maps only low/high and treats anything else (or nothing) as
        # max; z.ai/OpenRouter at "low" think ~3k chars per turn, this server at template "Low" thinks ~0-300, so "default"
        # is the comparable setting for self-hosted runs.
        # Same field as z.ai: vLLM's chat completions forward the top-level `reasoning_effort` into the chat-template kwargs
        # (build_chat_params in vllm-backport v0.13.1 and upstream), so the GLM template renders "Reasoning Effort: Low/High/Max"
        # from it. (An earlier claim that it was ignored came from /tokenize, which uses a different request class.)
        extra_body = {} if args.reasoning_effort == "default" else {"reasoning_effort": args.reasoning_effort}
        if args.extra_body_json:
            extra_body.update(json.loads(args.extra_body_json))
        prov_model = f"{args.model}-{args.serving_tag}@openai" if args.serving_tag else f"{args.model}@openai"
        if args.model_preset:
            _pr = MODEL_PRESETS[args.model_preset]
            extra_body = {"usage": {"include": True}}
            if args.model_preset != "deepseek-v4.1-flash" and args.reasoning_effort != "default":
                extra_body["reasoning"] = {"effort": args.reasoning_effort}
            prov_model = f"{args.model_preset}@{'clinepass' if 'cline' in _pr['base_url'] else 'openrouter'}"
    else:
        # LRA_SELFTEST_ANTHROPIC_URL: harness/selftest.py points the z.ai code path at its scripted fake server (never set in real runs)
        cl = anthropic.Anthropic(api_key=_key() if not os.environ.get("LRA_SELFTEST_ANTHROPIC_URL") else "selftest",
                                 base_url=os.environ.get("LRA_SELFTEST_ANTHROPIC_URL") or BASE_URL, timeout=1800, max_retries=0)
        api_model = args.model
        extra_body = {"reasoning_effort": args.reasoning_effort}
        prov_model = args.model + "@z.ai"
    # Bank sync (cycle 12): other runs of the SAME model/serving (e.g. the fresh z.ai control) can hold a better compiling
    # candidate than this state's best — Electromagnetism 61.6 fresh vs 57.4 resumed. Main line only (harness/work), never the
    # replication roots (their measurement must stay independent), and only records with this run's exact provenance model,
    # so OpenRouter proofs never seed the z.ai line.
    synced_note = ""
    if args.bank_sync and args.work_root.rstrip("/") == "harness/work":
        try:
            from bank.store import load_all as _bank_all
            _c = [r for r in _bank_all(name) if (r.get("provenance") or {}).get("model") == prov_model and (r.get("provenance") or {}).get("mode") == "agent" and r.get("score") and r.get("proof")]
            if _c:
                _top = max(_c, key=lambda r: float(r["score"]))
                if float(_top["score"]) > float(ws.state["best"].get("score") or 33.33) + 1e-9:
                    ws.state["best"] = {"score": float(_top["score"]), "proof": _top["proof"], "tokens": _top.get("tokens"), "heartbeats": _top.get("heartbeats"), "L": _top.get("L"), "H": _top.get("H"), "Z": _top.get("Z"), "compat": _top.get("compat")}
                    (ws.root / "candidate.lean").write_text(_top["proof"].rstrip() + "\n"); ws.save()
                    synced_note = (f"\n\nNOTE: another run of this same model ({(_top.get('provenance') or {}).get('run_id')}) found a better compiling candidate "
                                   f"(score {_top['score']}, {_top.get('tokens')} tokens, {_top.get('heartbeats')} heartbeats); candidate.lean now holds it. Continue from it.")
                    print(f"{name[:18]:18s} bank-sync: best {_top['score']} from {(_top.get('provenance') or {}).get('run_id')}", flush=True)
        except Exception as _e:  # noqa: BLE001
            print(f"{name[:18]:18s} bank-sync skipped: {_e}", flush=True)
    ver_f = (out_dir / "verified.jsonl").open("a"); log_f = (out_dir / "turns.jsonl").open("a")
    # Full trajectory (2026-10-06): every message exactly as sent/received — opening prompt, nudges,
    # assistant thinking/text/tool_use inputs, and the tool results the model saw — one JSON line per message, plus
    # per-turn meta lines (cap, stop reason, usage). probe/runs/<run>/trajectories/<problem>.jsonl ; replayable.
    traj_dir = out_dir / "trajectories"; traj_dir.mkdir(exist_ok=True)
    traj_f = (traj_dir / (re.sub(r"[^A-Za-z0-9_.-]", "_", name) + ".jsonl")).open("a")
    traj_logged = 0

    def flush_traj(extra: dict | None = None) -> None:
        nonlocal traj_logged
        for i in range(traj_logged, len(msgs)):
            traj_f.write(json.dumps({"type": "message", "i": i, "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), **msgs[i]}, ensure_ascii=False) + "\n")
        traj_logged = len(msgs)
        if extra:
            traj_f.write(json.dumps({"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), **extra}, ensure_ascii=False) + "\n")
        traj_f.flush()
    # adaptive budget: spend turns where headroom is (near-ceiling problems get a short pass, hard ones a long one)
    fresh_start = False; heartbeat_first = False
    if args.adaptive_turns and not args.from_reference:   # a restart from the reference takes --turns as given (no polish cut, no second fresh start)
        b0 = float(ws.state["best"].get("score") or 33.33)
        # Cycle 10: budget follows headroom and stagnation. Near-ceiling problems that did not move in their last two
        # runs (InitsUpdatesComm 83.8 for passes 6-8, the Putnam rows) get a 10-turn polish; mid problems (45-70:
        # Electromagnetism, SKI, Wick, fiberwise, Fsub) get 50 instead of 40.
        runs_prev = [r.get("run_id") for r in ws.state.get("runs", [])[:-1] if not _is_scout(r)]   # runs before this one, scouts excluded (cycle 27)
        recent = set(runs_prev[-2:])
        older_best = max([float(a.get("score") or 0) for a in ws.state.get("attempts", []) if a.get("ok") and a.get("run_id") not in recent] or [33.33])
        stagnant = len(runs_prev) >= 2 and (b0 - older_best) < 0.5
        args_turns = (10 if stagnant else 20) if b0 >= 80 else (60 if b0 < 45 else (50 if b0 < 70 else 40))
        # Cycle 14 "two strikes": a problem whose last two runs each gained < 0.5 (substOldPostSubset: 80 structural turns for +0.01;
        # variational 19 turns, 2 failed checks; InitsUpdatesComm) gets a 6-turn polish this pass, whatever its score. Pass 10 spent
        # ~120 of ~450 turns on such problems. The bank sync keeps lifting them from the control line meanwhile.
        if len(runs_prev) >= 2:
            def _best_excl(excl):
                return max([float(a.get("score") or 0) for a in ws.state.get("attempts", []) if a.get("ok") and a.get("run_id") not in excl] or [33.33])
            _r1, _r2 = runs_prev[-1], runs_prev[-2]
            _b_before_r1 = _best_excl({_r1, args.run_id}); _b_before_r2 = _best_excl({_r1, _r2, args.run_id})
            if (b0 - _b_before_r1) < 0.5 and (_b_before_r1 - _b_before_r2) < 0.5:
                _fresh_prev = sum(1 for r in ws.state.get("runs", [])[:-1] if r.get("mode") == "fresh")   # scouts are tagged scout, never fresh
                if b0 < 85 and _fresh_prev >= 2:
                    # Cycle 22: two fresh starts already missed on this problem (extractedOldExprInVars: 3 fresh starts, 30 checks, 0 compiled;
                    # Fsub/SKI: 2 each, compiled but never beat the best). A third restart is waste; go structural on the stored best
                    # with a heartbeat-first brief (policy order: direct shape > search burden > clarity > brevity).
                    args_turns = 40; heartbeat_first = True
                    print(f"{name[:18]:18s} two flat runs and {_fresh_prev} fresh starts missed: structural on the best, heartbeat-first, 40 turns", flush=True)
                elif b0 < 85:
                    ws.state["runs"][-1]["mode"] = "fresh"; ws.save()
                    # Cycle 18 anchoring escape: pass 13 gave 8 such problems a 6-turn high-effort polish and every one gained 0
                    # (most never reached a check). Fresh runs found better skeletons than the resumed line (A100 substOldPostSubset
                    # 80.4 vs 75.1; OpenRouter fold_advances 86.5 vs 85.2; z.ai control Electromagnetism 61.6 vs 57.4). Restart from
                    # the reference with a full budget; the stored best is kept unless beaten.
                    fresh_start = True; args_turns = 40
                    print(f"{name[:18]:18s} two flat runs ({_b_before_r2:.2f} -> {_b_before_r1:.2f} -> {b0:.2f}): FRESH START from the reference, 40 turns", flush=True)
                else:
                    args_turns = min(args_turns, 6)
                    print(f"{name[:18]:18s} two flat runs ({_b_before_r2:.2f} -> {_b_before_r1:.2f} -> {b0:.2f}): 6-turn polish", flush=True)
    else:
        args_turns = args.turns
    if not args.upstream_history:   # R2 compliance switch: no hint to read later upstream versions of the proof
        for _n in ("SYSTEM", "SYSTEM_BASE"):
            globals()[_n] = re.sub(r",?\s*`git log -p` on the file[^,;)]*", "", globals()[_n])
    toolchains = ", ".join(versions)
    msgs = [{"role": "user", "content": f"Problem `{name}` from the {row['source']} corpus. Reference proof body: {row['proof_length']} tokens, {hbs.get(name)} heartbeats. Toolchains: {toolchains}. "
                                         f"Workspace files: original.lean, context.lean ({'imports/header' if row['source']=='putnambench' else 'surrounding file prefix, ' + str((ws.root/'context.lean').read_text().count(chr(10))) + ' lines'}), candidate.lean. "
                                         + (f"Project sources (read-only) for grep/git: {ROOT / 'envs' / (row['source'] + '-' + primary)} ; the problem's file is {row['file_path']} ; full git history of the project (newer commits may contain a simplified version of this very proof — `git -C {ROOT / 'envs' / (row['source'] + '.git-main')} log -p --follow -- {row['file_path']} | head -400`) is in {ROOT / 'envs' / (row['source'] + '.git-main')}. "
                                            if row['source'] != 'putnambench' else f"Mathlib sources (read-only) for grep: {ROOT / 'envs' / ('mathlib-' + primary) / 'Mathlib'}. ")
                                         + f"You have {args_turns} tool turns. Keep durable insights (what worked, what failed and why, lemma names that exist) in notes.md so later runs can continue.\n\n" + ws.digest()
                                         + ("\n\nBoth original.lean and candidate.lean are shown below: no need to read_file them, start working." if not ws.state["attempts"] else "\n\nContinue from candidate.lean (your best so far, shown below; no need to read_file it); notes.md is summarised above.")}]
    # Cycle 40: in 97 of 105 main-line runs (92%) turn 0 only read_file'd candidate.lean / original.lean. Show both up front instead.
    for _fn, _lbl in (("original.lean", "original.lean (the REFERENCE proof)"), ("candidate.lean", "candidate.lean (your current best)")):
        try:
            _txt = (ws.root / _fn).read_text().rstrip()
            if args.lean_io and _fn == "candidate.lean" and _txt == (ws.root / "original.lean").read_text().rstrip():
                msgs[0]["content"] += "\n\ncandidate.lean: identical to original.lean (the reference above)."   # --lean-io: no second copy
                continue
            if _txt:
                msgs[0]["content"] += f"\n\n{_lbl}:\n```lean\n{_txt[:12000]}\n```" + ("\n(truncated: read_file for the rest)" if len(_txt) > 12000 else "")
        except OSError:
            pass
    if args.upstream_history:   # cycle 57: the git-history lookup done once by the harness (798 model git calls in 568 trajectories)
        try:
            from harness.leantools import upstream_digest as _ud
            _up = _ud(row, primary)
            if _up:
                msgs[0]["content"] += "\n\n" + _up
        except Exception:  # noqa: BLE001
            pass
    best = dict(ws.state["best"])
    if synced_note:
        msgs[0]["content"] += synced_note
    # 2026-10-13 --heartbeat-first (off by default; harness/cards.py HB_REWRITES): the HEARTBEAT_FIRST card with the technique cards and the
    # heartbeat-aware wording of the cards / scout / structural / heartbeat briefs, while the stored best's H points left >= its L points left
    # (always before a measured best). The system prompt's axis-conditional closer wording is set once in main().
    _hbf = False
    if getattr(args, "heartbeat_first", False):
        from harness import cards as _cards
        _hbf = _cards.gate(name, row, ws.state, hbs.get(name), log=lambda s: print(f"{name[:18]:18s} {s}", flush=True))
        ws.state["runs"][-1]["heartbeat_first"] = _hbf; ws.save()
    _hbw = (lambda s: _cards.heartbeat_aware(s)) if _hbf else (lambda s: s)
    # Per-repo automation briefs (research 2026-10-07, counts from our local envs): what each target repository's own automation
    # supports, so closers and hints match the project instead of generic Mathlib habits. Length experiment only (--length-tools).
    try:   # Tier 2 technique cards (panel R1): playbook v1 rules for the proof patterns detected in this problem
        from harness import cards as _cards
        _ctx = (ws.root / "context.lean").read_text() if (ws.root / "context.lean").exists() else ""
        _cur = (ws.root / "candidate.lean").read_text() if (ws.root / "candidate.lean").exists() else (ws.state["best"].get("proof") or row["src"])
        msgs[0]["content"] += "\n\n" + _cards.cards_for(row["statement"], _cur, _ctx, heartbeat_first=_hbf)
        print(f"{name[:18]:18s} technique cards: {', '.join(_cards.select(row['statement'], _cur, _ctx)) or 'token rules only'}", flush=True)
    except Exception as _e:  # noqa: BLE001
        print(f"{name[:18]:18s} technique cards failed: {_e}", flush=True)
    _cl0 = len(msgs[0]["content"])   # 2026-10-13 --heartbeat-first: the closed-lessons literal stays as prompt_v2.drift_nodes reads it; spliced below
    if args.closed_lessons:   # cycle 80: general habits mined from the Opus 5.5 / GPT Astra lines (docs/closed_line_lessons.md); off until a z.ai A/B
        msgs[0]["content"] += ("\n\nFIVE HABITS OF THE STRONGEST PROVERS (general, not about this problem):\n"
            "1. Let simp prove side conditions: `simp (disch := omega) only [h]` for arithmetic side goals, or put the lemmas that prove them into the "
            "same `simp only [...]` list (with `(maxDischargeDepth := 4)` if they nest), instead of `h 0 (by decide)` arguments or a typed `have` per "
            "side condition. Flash proofs carry such hand-written side proofs; the strongest provers almost never do.\n"
            "2. Write each piece once: when cases or steps repeat the same tactic run, close them together (`all_goals`, `<;>`, `case A | B => tac`) "
            "instead of repeating it; about a fifth of the tokens in Flash's best proofs sit in repeated runs. `<;> first | A | B` is shorter as "
            "`any_goals A` then `all_goals B` (2 tokens fewer).\n"
            "3. For a goal about a recursive definition `f`, try `fun_induction f` (its cases come split by `f`'s equations) instead of `induction x` "
            "followed by `unfold f` / `split`; first drop hypotheses the goal does not need (`rintro -`), so the induction hypotheses stay simple.\n"
            "4. Before expensive closers, run a cheap reducible pre-pass: `any_goals with_reducible apply Or.inl` (or `with_reducible exact h`) closes "
            "the syntactically easy goals and fails fast on the rest; closers that fail at default transparency cost many heartbeats.\n"
            "5. On simple or-splits and membership-in-append goals, a syntactic closer (`refine Or.imp ?_ ?_`, the `List.mem_append` lemmas) "
            "costs about 30 heartbeats per goal against about 110 for `grind`.")
    if _hbf:   # review 2026-10-13: habit 2's `any_goals A` advice made axis-conditional (cards.HB_REWRITES R13); only the text appended just above
        msgs[0]["content"] = msgs[0]["content"][:_cl0] + _hbw(msgs[0]["content"][_cl0:])
    try:   # Tier 1 lemma search pre-pass (panel R1; insight-recall benchmark 9/12 at top 10): library leads for the current proof
        from harness import lemma_search as _ls
        _cur2 = (ws.root / "candidate.lean").read_text() if (ws.root / "candidate.lean").exists() else (ws.state["best"].get("proof") or row["src"])
        _lr = _ls.search(name, _cur2.rstrip(), top=10, probes=True, budget=120.0)
        _sg = _lr.get("suggestions") or []
        if _sg:
            msgs[0]["content"] += ("\n\nLIBRARY LEADS for the current proof (lemma search: exact? at each goal, names ranked by match with the goal and statement, "
                                   "same-file lemmas the reference does not use, @[simp]/@[grind]/@[to_fun] lemmas, induction principles). Leads, not answers: "
                                   "check a lead's signature against the goal (lean_goals) before building on it; lean_search re-runs it after a restructure.\n"
                                   + "\n".join(f"  - {s_.get('name')} [{s_.get('source')}{', line ' + str(s_['line']) if s_.get('line') else ''}]: "
                                                f"{(s_.get('signature') or '')[:180]}  -- {(s_.get('why') or '')[:140]}" for s_ in _sg[:10]))
        print(f"{name[:18]:18s} library leads: {len(_sg)} ({_lr.get('runtime_s')} s, {_lr.get('compiles')} compiles)", flush=True)
    except Exception as _e:  # noqa: BLE001
        print(f"{name[:18]:18s} lemma search failed: {_e}", flush=True)
    REPO_BRIEFS = {
        "strata": "REPO AUTOMATION (Strata): NO Mathlib, NO Batteries, NO Aesop — only core tactics (grind, simp, omega, decide, cases/induction, "
                  "rfl, exact?) plus Strata's own macros (elim_err, split_contra, solve_beq, term_by_mem). Never write aesop/linarith/positivity/fun_prop/norm_num here.",
        "cslib": "REPO AUTOMATION (CSLib): built around grind — 583 `@[grind]` annotations, ~2,200 grind uses. First try `grind` with the "
                 "constructors/lemmas your proof already names as hints, e.g. `grind [→ Foo.bar, Baz.qux]`; `all_goals grind [...]` after induction/cases.",
        "physlib": "REPO AUTOMATION (PhysLib): built around simp and fun_prop (211 `@[fun_prop]` lemmas; no grind annotations). Differentiability/"
                   "continuity side goals → `fun_prop`; algebra → `simp [defs]`/`ring`; prefer `simp_all`/`simp only [...]` over long rw chains.",
        "arklib": "REPO AUTOMATION (ArkLib): omega-heavy (~1,600 uses), plus simp and aesop. Index/arithmetic side goals → `omega`; "
                  "structural goals → `simp_all`/`aesop`.",
        "putnambench": "REPO AUTOMATION (PutnamBench): full Mathlib + Aesop; nlinarith/positivity/norm_num/field_simp/ring for real-analysis "
                       "inequalities, `decide`/`omega` for finite/integer facts, `exact?` for library lemmas.",
    }
    if args.length_tools and row["source"] in REPO_BRIEFS:
        msgs[0]["content"] += "\n\n" + _hbw(REPO_BRIEFS[row["source"]])
    SCOUT_BRIEFS = {
        "automation": ("SCOUT A — AUTOMATION FIRST. Aim for the shortest proof by delegating to decision procedures: `simp_all`, `simp only [...] at *`, `grind`, `omega`, "
                       "`decide`, `aesop`, `norm_num`, `positivity`, `linarith`/`nlinarith`, `fun_prop`, `ext <;> simp`. Try `by grind` / `by simp_all` / `by omega` on the whole goal "
                       "first, then on each case after ONE `cases`/`induction` with `<;>` or `all_goals`. Batch the closers with lean_check_variants. `simp only` beats `simp` on heartbeats when both compile."),
        "direct": ("SCOUT B — DIRECT / TERM MODE. Find the library lemma that closes the goal (`exact?`, `apply?`, `rw?` through lean_run; grep the project sources), then write the proof "
                   "as a term: `exact lemma a b`, anonymous constructors `⟨_, _⟩`, `fun` abstractions, `‹_›` for hypotheses, `.symm`/`.trans`/`.mp` chains, `by simpa using`. "
                   "Avoid tactic blocks except a single closer. Batch alternative lemma applications with lean_check_variants."),
        "restructure": ("SCOUT C — RESTRUCTURE. Change the proof architecture, not the spelling: a different induction/cases variable or order, symmetric cases merged, a stronger "
                        "intermediate statement via `suffices`/`have` so the cases collapse, `match`/`nomatch`/`nofun` for impossible cases, `obtain`/`rcases` patterns instead of nested "
                        "cases, `calc` collapsed to `_` steps. Batch 2-4 architectures with lean_check_variants and keep the one with the fewest tokens, then cut heartbeats."),
    }
    if args.from_reference:
        ws.state["runs"][-1]["mode"] = "scout"; ws.save()
        (ws.root / "candidate.lean").write_text(row["src"].rstrip() + "\n")
        msgs[0]["content"] += ("\n\nSCOUT RUN: candidate.lean holds the ORIGINAL reference proof. Produce a compiling candidate of your own architecture early (within 4 checks), "
                               "then shorten it; everything that compiles is scored and banked, and the stored best is kept unless you beat it.")
        # 2026-10-10 (GPT Astra's fresh starts: 4 of 5 beat the union with the best proof hidden but its size given): a blind target
        if float(best.get("score") or 33.33) > 33.34 and best.get("tokens"):
            msgs[0]["content"] += (f" BLIND TARGET: the stored best has {best.get('tokens')} tokens and {best.get('heartbeats') or '?'} heartbeats "
                                   f"(score {best.get('score')}); a structurally different proof that beats it is the goal.")
    if args.term_card:   # 2026-10-11 (DeepSeek→Sol lesson, docs: fiberwise DeepSeek 199 tok/1741 hb term vs Sol 249/3002 tactics)
        msgs[0]["content"] += ("\n\nTERM-MODE FINISH AND PROBE-BEFORE-COMMIT (general practices, measured on another model):\n"
            "1. Search the library for a theorem matching the WHOLE statement first (lean_search; `exact?` in lean_run): a single library "
            "lemma often closes the problem outright.\n"
            "2. Once a tactic proof compiles, try ONE variant that collapses it into a single term: chain with `.elim`, `.trans`, `.trans_eq`, "
            "`.trans_lt`, `.imp`, anonymous `fun … =>`; drop `unfold`/`dsimp`/`classical` and `simp … at` on hypotheses (let definitional "
            "unfolding happen inside the term). On algebraic/inequality chains a term proof often cuts BOTH tokens and heartbeats.\n"
            "3. Probe before you commit: test sub-terms and lemma fits in lean_run (`example : <goal> := <term>`; sorry allowed, no check "
            "spent) and only then write the full candidate.")
        print(f"{name[:18]:18s} term-mode card", flush=True)
    if args.brief_dir:   # 2026-10-10: per-problem facts-only KNOWLEDGE BRIEF (landmarks, levers, failed lists — never proofs)
        _bf = ROOT / args.brief_dir / (re.sub(r"[^A-Za-z0-9_.-]", "_", name) + ".md")
        if _bf.exists():
            msgs[0]["content"] += "\n\n" + _bf.read_text()
            print(f"{name[:18]:18s} knowledge brief: {_bf.name}", flush=True)
    if args.brief != "none":
        msgs[0]["content"] += "\n\n" + _hbw(SCOUT_BRIEFS[args.brief])
        print(f"{name[:18]:18s} scout brief: {args.brief}", flush=True)
    if args_turns <= 10:   # cycle 38: short polish runs must check, not bookkeep
        msgs[0]["content"] += (f"\n\nSHORT POLISH RUN: only {args_turns} turns. Spend them on checks. Your FIRST action: one lean_check_variants call with 3-6 "
                               "independent single-edit variants of candidate.lean (re-apply WINNING EDITS the best lost, try LIBRARY LEADS, delete a `have`/`set`, "
                               "swap a closer, token micro-rules). Do not re-read notes or reorganise them; write notes.md only in your final turn.")
    hardtail_target = None
    hardtail_batches = 0   # lean_check_variants calls with >= 3 full variants (protocol step 4)
    forced_turns = 0       # turns on which the hard-tail run was restricted to the step-4 tools
    if args.strategy == "hardtail":
        # 2026-10-07: the hard tail (worst for every model, flat after many passes) needs a different strategy, not more passes.
        # Protocol: see the goals, search the library for the routine steps, then change the ARCHITECTURE under a numeric token target.
        _bt = int(ws.state["best"].get("tokens") or row["proof_length"])
        hardtail_target = max(10, int(_bt * 0.7))
        msgs[0]["content"] += (
            f"\n\nHARD-TAIL STRATEGY RUN. This problem has stayed near its current best ({ws.state['best'].get('score')}, {_bt} tokens) for many passes: "
            "local edits of the current proof are exhausted. Do NOT polish it. Follow this protocol:\n"
            "1. MAP: the goal before every step of candidate.lean is listed below (GOAL MAP); call lean_goals for more (other files, from_line).\n"
            "2. PLAN in notes.md (short): for each step, its goal in a few words and whether it is the essential idea or routine (a case that "
            "follows from a constructor, a library lemma, or simplification). Note cases that look alike: they can share one tactic.\n"
            "3. LEMMA SEARCH for the 2-3 most expensive routine steps: with lean_run, state the goal as `example (hyps…) : goal := by exact?` "
            "(also `apply?`, `rw?`, `simp?`, `grind`) and keep the lemma names / closers that work.\n"
            f"4. RESTRUCTURE: write 3-5 FULL candidates with a DIFFERENT architecture, each at most {hardtail_target} tokens (70% of the current best), "
            "and send them in ONE lean_check_variants call. Architectures to try: one `induction`/`cases` with `<;>` and a shared closer "
            "(`<;> grind [lemmas]`, `<;> simp_all`, `<;> aesop`, `<;> first | exact … | …`); a helper `have` that generalises the repeated case; "
            "a term-mode proof from the lemmas found in step 3; a different induction variable or `generalizing` set.\n"
            "5. Iterate on the best NEW architecture (errors → fix with lean_goals/lean_run). Polish only once a new architecture compiles.")
        print(f"{name[:18]:18s} hard-tail strategy: target <= {hardtail_target} tokens (best {_bt})", flush=True)
        try:   # protocol step 1 done by the harness: the model sees the goals before its first turn
            from harness import goals as _goals
            _cand = (ws.root / "candidate.lean").read_text() if (ws.root / "candidate.lean").exists() else ws.state["best"].get("proof") or ""
            _gm = _goals.goal_map(name, _cand, depth=2, total=7000)
            if not _gm.get("steps") or "Showing steps" in (_gm.get("note") or ""):
                _gm = _goals.goal_map(name, _cand, depth=1, total=7000) if not _gm.get("steps") else _gm
            if _gm.get("steps"):
                msgs[0]["content"] += ("\n\nGOAL MAP of candidate.lean (step 1 already done; lean_goals gives more, e.g. from_line=…):\n"
                                       + "\n".join(f"line {s_['line']} `{s_['tactic']}` [{s_['n_goals']} goal(s)]\n{s_['goals']}" for s_ in _gm["steps"])
                                       + (f"\n({_gm['note']})" if _gm.get("note") else ""))
                print(f"{name[:18]:18s} hard-tail goal map: {len(_gm['steps'])} steps in the opening message", flush=True)
        except Exception as _e:  # noqa: BLE001
            print(f"{name[:18]:18s} hard-tail goal map failed: {_e}", flush=True)
    if fresh_start:
        (ws.root / "candidate.lean").write_text(row["src"].rstrip() + "\n")
        msgs[0]["content"] += (f"\n\nFRESH START: the last two runs could not improve the stored best (score {best['score']}; {best.get('tokens')} tokens, "
                               f"{best.get('heartbeats') or '?'} heartbeats: the target to beat); it is anchored to one proof "
                               "skeleton. candidate.lean now holds the ORIGINAL reference proof, not the best. Ignore the old approach: read the statement, "
                               "think about the shortest overall proof strategy (induction + `simp only [defs] at *` + `grind`/`omega`, a direct lemma via "
                               "`exact?`, a different case split), write it, lean_check, iterate. The stored best is kept unless you beat it, so bold "
                               "rewrites cost nothing. notes.md still has the lemma names and pitfalls from earlier runs. "
                               "Build the new proof IN STAGES: the reference compiles, so replace one block at a time and lean_check after each, keeping a "
                               "compiling candidate in hand at all times (a whole new proof written in one shot took 10-25 turns to compile in earlier runs "
                               "and left no time to shorten it). Aim for a first compiling check within your first 6 checks.")
    # stuck-problem strategy switch: ≥2 earlier runs and still at the reference → local edits have failed; prescribe a different approach
    if len([r for r in ws.state.get("runs", []) if not _is_scout(r)]) >= 3 and float(ws.state["best"].get("score") or 33.33) < 50:
        msgs[0]["content"] += ("\n\nSTRATEGY CHANGE: earlier runs made local edits to this proof and gained little or nothing. Do not repeat that. Instead: "
                               "(1) read the whole proof and list its 3–4 most expensive or longest steps (big `simp`/`simp_all`/`omega`/`nlinarith`/`norm_num` calls, long `have` chains); "
                               "(2) for each, state the exact goal at that point with lean_run (copy the surrounding context, put `sorry` after it, read the goal from the error), then ask `exact?`, `apply?`, `simp?` or `rw?` on that goal to find a direct closer; "
                               "(3) replace one step at a time with the closer found, lean_check after each. If a `have` is only used once, inline it. "
                               "Also check the project's git history for a later simplification of this very declaration (see the shell hint above). Aim for a compiling candidate within your first 8 turns.")
    # Structural pass (cycle 11, from docs/gap_analysis_opus_vs_flash.md): the Opus/Fable lead is proof LENGTH, won by deleting
    # scaffolding and collapsing calc chains — exactly what the incremental policy discourages. Once local edits slow down
    # (gain over the last two runs < 3 points) on a problem in [50, 85), prescribe structural cuts from the current best.
    _runs_prev = [r.get("run_id") for r in ws.state.get("runs", [])[:-1] if not _is_scout(r)]
    _b = float(ws.state["best"].get("score") or 33.33)
    _older = max([float(a.get("score") or 0) for a in ws.state.get("attempts", []) if a.get("ok") and a.get("run_id") not in set(_runs_prev[-2:])] or [33.33])
    # Cycle 13: keep structural mode on while it pays. Pass 9 gained +3..+6.5 on six problems under the recipe, but the
    # plateau trigger alone would hand them back to micro-edits next pass. If the previous run was structural and gained
    # >= 1 point, stay structural.
    _nonscout = [r for r in ws.state["runs"][:-1] if not _is_scout(r)]
    _last = _nonscout[-1] if _nonscout else {}
    _before_last = max([float(a.get("score") or 0) for a in ws.state.get("attempts", []) if a.get("ok") and a.get("run_id") not in (_last.get("run_id"), args.run_id)] or [33.33])
    _keep = _last.get("mode") == "structural" and (_b - _before_last) >= 1.0
    # 2026-10-09 BFS deep dive: a --from-reference restart on a workspace with history (the variant test copies the A100 line) would
    # otherwise also get the structural brief ("cut from the current best") and the effort raise, contradicting its own restart.
    if args.strategy != "hardtail" and not fresh_start and not args.from_reference and len(_runs_prev) >= 2 and 50 <= _b < 85 and ((_b - _older) < 3.0 or _keep or heartbeat_first):   # a fresh start gets its own brief, not the structural one; hard-tail runs have their own protocol (smoke 2026-10-07: the structural brief's one-cut-at-a-time advice won, and its effort raise cost an 8k-token no-tool turn)
        ws.state["runs"][-1]["mode"] = "structural"; ws.save()
        # Cycle 17: structural rewrites need more thinking. The self-hosted A100 run at the template's max effort found a
        # 40-token `induction … all_goals simp only [...] at * … all_goals grind only` proof of substOldPostSubset on its
        # first pass, where three structural passes at low effort left the main line at 164 tokens. Hosted endpoints
        # take the effort label, so raise it to "high" for structural-mode problems only (the escalating cap absorbs it).
        # Same logic on every endpoint (2026-10-07): the label travels in the same field everywhere. The A100's response
        # to "high" is unmeasured at scale (n=2-4 per label, spread 0-3.7k chars within one label) — open item, not a code branch.
        if args.reasoning_effort == "low":
            extra_body["reasoning_effort"] = "high"
        print(f"{name[:18]:18s} structural mode ({'kept: last run gained %.2f' % (_b - _before_last) if _keep else 'plateau'}; effort {(extra_body.get('chat_template_kwargs') or {}).get('reasoning_effort') or extra_body.get('reasoning_effort') or args.reasoning_effort})", flush=True)
        msgs[0]["content"] += _hbw("\n\nSTRUCTURAL PASS (aligned with R3, cycle 39): editing has stalled on this proof (gain over the last two runs < 3 points), so the next "
                               "gain needs a NEW ARCHITECTURE, not more edits of the current one. Rewrite top-down: outline the proof with `sorry` holes, check it with "
                               "lean_skeleton, fill one hole at a time, then lean_check. Aim the new outline at what the old one wastes: "
                               "(1) no scaffolding: no `let`/`set`/`have` used once or not at all (each `set` costs ~165 hb); destructure directly; "
                               "(2) no long `calc`: rewrite the goal directly or use `_` for intermediate right-hand sides, pass side goals inline as arguments; "
                               "(3) one shared AUTOMATION closer for alike cases (`induction x <;> grind [hints]`, `all_goals simp only [...]`, `case'` + `first | …`) "
                               "instead of a hand-written term per case; "
                               "(4) LIBRARY LEADS first: a lemma that matches a block's conclusion replaces the block; "
                               "(5) no `show`/`change`/`unfold`/`dsimp` lines that only restate the goal. Keep every compiling improvement; several attempts will fail.")
    if heartbeat_first:
        msgs[0]["content"] += _hbw("\n\nHEARTBEAT FIRST: on this proof the length axis has stalled; the heartbeat axis is where points remain. Prefer, in order: "
                               "a more direct proof shape (term-mode `exact`/anonymous constructors over tactic blocks), lower search burden (`simp only [...]`/"
                               "`rw` over `simp`/`omega`/`grind`/`aesop` where both compile, `exact lemma args` over `apply`+goals), then clarity, then brevity. "
                               "Keep the candidate compiling after every edit; lean_check reports heartbeats — a cut that raises heartbeats is not a win.")
    # 2026-10-10 union push (docs/break_90_results.md): on problems where both closed lines' resumed passes had stalled, a review that named
    # concrete levers, then one budgeted batch of compiles, beat their bests on 10 of 15. Same trigger as structural mode (gain over the last two
    # runs < 3), any score band; off until a z.ai A/B.
    if args.lever_review and args.strategy != "hardtail" and not fresh_start and not args.from_reference and len(_runs_prev) >= 2 and (_b - _older) < 3.0:
        msgs[0]["content"] += _hbw(LEVER_REVIEW)   # 2026-10-13: identity unless --heartbeat-first's gate passed (HB_REWRITES R14)
        print(f"{name[:18]:18s} lever review first (gain over the last two runs {_b - _older:.2f})", flush=True)
    THINK_NUDGE = ("THINK LONGER before each tool call: in your thinking, enumerate at least three distinct proof strategies for the current goal, "
                   "estimate the token/heartbeat payoff and the risk of each, and only then choose one. A short think here wastes a check.")
    _is_structural = (ws.state["runs"][-1].get("mode") == "structural")
    think_prompt_on = args.think_prompt == "all" or (args.think_prompt == "structural" and (_is_structural or fresh_start))
    if think_prompt_on:
        msgs[0]["content"] += "\n\n" + THINK_NUDGE
        print(f"{name[:18]:18s} think-prompt on ({args.think_prompt})", flush=True)
    if getattr(args, "failed_moves", False):   # 2026-10-13 --failed-moves (off by default; docs/opus_pass2_deep_dive.md §3): REFUTED MOVES from
        # state.json attempts, against candidate.lean as this session starts (after a from-reference / fresh-start reset, so a move on lines the
        # reset removed is not listed); the runs[] entry records how many were shown (A/B audit)
        try:
            from harness import cc_levers as _LVfm
            _fm_base = (ws.root / "candidate.lean").read_text() if (ws.root / "candidate.lean").exists() else (ws.state["best"].get("proof") or row["src"])
            _LVfm.void_stale(ws.state, ws.state["best"].get("proof"))   # review 2026-10-13: a best seen only at a session start also voids
            _fm, ws.state["runs"][-1]["failed_moves"] = _LVfm.failed_moves_render(ws.state, base=_fm_base); ws.save()   # review: rows shown
            if _fm:
                msgs[0]["content"] += "\n\n" + _fm
                print(f"{name[:18]:18s} refuted moves: {ws.state['runs'][-1]['failed_moves']}", flush=True)
        except Exception as _e:  # noqa: BLE001
            print(f"{name[:18]:18s} refuted moves failed: {_e}", flush=True)
    try:  # free deletions first: compile the current candidate once and surface the linter's hints up front
        from harness.leantools import lean_check as _lc
        _state_probe = {"best": {"score": 33.33, "proof": None}, "attempts": []}
        _pre = _lc(name, (ws.root / "candidate.lean").read_text(), _state_probe, {"run_id": args.run_id, "kind": "probe"}, None)
        if _pre.get("linter_hints"):
            msgs[0]["content"] += "\n\nLinter hints on the current candidate (free deletions, do these first):\n" + "\n".join("  - " + h for h in _pre["linter_hints"])
    except Exception as _e:  # noqa: BLE001
        pass
    checks = 0; tool_calls = 0; total_out = 0
    sig_cache = {}   # cycle 28: #check signatures looked up this run

    def comp(decl, version, count=True):
        return compile_putnam(row["header"], decl, version, count=count, timeout=900) if row["source"] == "putnambench" else compile_project(row, decl, version, count=count, timeout=900)

    def lean_mine(path: str) -> str:
        from harness import mine as _mine
        src = ws.path(path or "candidate.lean")
        if not src.exists():
            return json.dumps({"ok": False, "errors": [f"{src.name} not found"]})
        decl = src.read_text()
        res = _mine.mine(name, decl, jobs=4, log=lambda *_: None)
        if res.get("error"):
            return json.dumps({"ok": False, "errors": [res["error"]]})
        out = {"base_tokens": res["base_tokens"], "blocks": res["blocks"],
               "block_hits": {f"block {int(k) + 1}": {"closer": v[0], "tokens_saved": v[1]} for k, v in res["block_hits"].items()},
               "tail_cuts": [{"from_body_line": k + 1, "tokens_saved": s} for k, s in res["suffix_ok"]], "whole_proof_closers": res["whole_ok"]}
        if res.get("best"):
            (ws.root / "mined.lean").write_text(res["best"]["proof"].rstrip() + "\n")
            chk = json.loads(lean_check("mined.lean"))
            out["mined"] = {"how": res["best"]["how"], "tokens": chk.get("tokens"), "score": chk.get("score") or chk.get("predicted_score_if_compatible"), "ok": chk.get("ok")}
            if chk.get("new_best"):
                (ws.root / "candidate.lean").write_text(res["best"]["proof"].rstrip() + "\n")
                out["note"] = "mined.lean beats the stored best; copied to candidate.lean"
        else:
            out["note"] = "no compiling cut found; the remaining length needs a different proof shape"
        return json.dumps(out, ensure_ascii=False)

    def lean_check_variants(variants) -> str:
        nonlocal hardtail_batches
        variants = [v for v in (variants or []) if isinstance(v, dict) and (v.get("content") or "").strip()][:6]
        over = {}
        if hardtail_target:
            # Cycle 35 (hard-tail smoke 3): the forced batch held 4 local edits of the old proof (263-277 tokens vs target 203), all compiled
            # and failed. Reject variants > 115% of the target before compiling: they are not new architectures.
            for k, v in enumerate(variants):
                _b = split_declaration(v["content"].rstrip(), row["statement"])
                _n = count_tokens(_b) if _b is not None else None
                if _n is not None and _n > hardtail_target * 1.15:
                    over[k] = _n
        if len(variants) - len(over) >= 3:
            hardtail_batches += 1
        if not variants:
            return json.dumps({"ok": False, "errors": ["give 1-6 variants, each {label, content} with the FULL candidate text (statement + proof)"]})
        before = float(ws.state["best"].get("score") or 33.33)
        rows = []; best_k = None; best_s = -1.0; sigs_all = {}; dym_all: dict = {}; cf_all: dict = {}
        for k, v in enumerate(variants):  # sequential: lean_check mutates shared state; the saving is in LLM turns, not compile time
            p = ws.root / f"variant_{k + 1}.lean"; p.write_text(v["content"].rstrip() + "\n")   # workspace root: ws.path() resolves basenames only
            if k in over:
                rows.append({"label": v.get("label") or f"v{k + 1}", "ok": False, "score": None, "tokens": over[k], "heartbeats": None,
                             "error": f"not compiled: {over[k]} tokens is over the hard-tail target ({hardtail_target}); this is an edit of the old proof, not a new architecture",
                             "note": None})
                continue
            _b0 = float(ws.state["best"].get("score") or 33.33)   # the best just before this variant's check (cycle 78 vs_best)
            try:
                r = json.loads(lean_check(p.name))
            except Exception as e:  # noqa: BLE001
                r = {"ok": False, "errors": [str(e)[:200]]}
            s = r.get("score")
            _vs = {}
            if args.variant_scores:   # cycle 78: compiling rows carried score null unless they beat the best (106 of 137 in A100 p6-p7),
                # so the model recomputed L/H by hand and the "not above the stored best" note never fired; give each compiling row its
                # provisional score (local heartbeats, compatibility assumed) and its distance to the best, and fill duplicates from prior
                if r.get("unchanged") and isinstance(r.get("prior"), dict):
                    r = {**r, **{k_: r["prior"].get(k_) for k_ in ("tokens", "heartbeats") if r.get(k_) is None}}
                    s = r["prior"].get("score")
                elif s is None and r.get("ok") and r.get("predicted_score_if_compatible") is not None:
                    s = r["predicted_score_if_compatible"]; _vs["score_kind"] = "provisional (compatibility not checked: not above the best)"
                if isinstance(s, (int, float)):
                    _vs["vs_best"] = round(float(s) - _b0, 2)
            rows.append({"label": v.get("label") or f"v{k + 1}", "ok": bool(r.get("ok")), "score": s, "tokens": r.get("tokens"), "heartbeats": r.get("heartbeats"),
                         "error": ((r.get("errors") or [None])[0] or None), "note": r.get("note") or r.get("auto_fixed"), **_vs})
            for c_, sig_ in (r.get("signatures") or {}).items():   # cycle 30: the assist was dropped here (0 of 17 mismatches surfaced in pass 1)
                sigs_all.setdefault(c_, sig_)
            for n_, c_ in (r.get("did_you_mean") or {}).items():
                dym_all.setdefault(n_, c_)
            if r.get("compat_failures") and len(cf_all) < 2:   # cycle 56: variant rows carried no compatibility result at all
                cf_all[rows[-1]["label"]] = {"compat": r.get("compat"), "failures": r["compat_failures"], "note": r.get("compat_note")}
            if r.get("ok") and isinstance(s, (int, float)) and s > best_s:
                best_s, best_k = float(s), k
        out = {"variants": rows, "best_variant": rows[best_k]["label"] if best_k is not None else None}
        _rep = next((r_["note"] for r_ in rows if r_.get("note") and "same error has now failed" in r_["note"]), None)
        if _rep:   # cycle 33: the repeated-error nudge sat inside a variant row; lean_check_variants is the most used check tool
            out["repeated_error"] = _rep
        if dym_all:
            out["did_you_mean"] = dict(list(dym_all.items())[:4])
        if cf_all:
            out["compat_failures"] = cf_all
        if sigs_all:
            out["signatures"] = dict(list(sigs_all.items())[:3])
            out["signature_note"] = "application/type mismatch in some variants: `signatures` holds the exact signature of each applied constant — match its argument order before retrying"
        if best_k is not None and best_s > before:
            (ws.root / "candidate.lean").write_text((ws.root / f"variant_{best_k + 1}.lean").read_text().rstrip() + "\n")   # cycle 49: the file holds any auto-fix
            out["note"] = f"best variant {rows[best_k]['label']} ({best_s}) beats the previous best ({before}); copied to candidate.lean"
        elif best_k is not None:
            out["note"] = f"best compiling variant {rows[best_k]['label']} scores {best_s}, not above the stored best {before}; candidate.lean unchanged"
        return json.dumps(out, ensure_ascii=False)

    def lean_search(path: str, probes: bool = False) -> str:
        from harness import lemma_search as _ls
        src = ws.path(path or "candidate.lean")
        if not src.exists():
            return json.dumps({"ok": False, "errors": [f"{src.name} not found"]})
        r_ = _ls.search(name, src.read_text().rstrip(), top=10, probes=bool(probes), budget=150.0)
        return json.dumps({"suggestions": [{k: s_.get(k) for k in ("name", "signature", "source", "line", "why")} for s_ in (r_.get("suggestions") or [])[:10]],
                           "runtime_s": r_.get("runtime_s")}, ensure_ascii=False)[:9000]

    def lean_skeleton(path: str = "", content: str = "") -> str:
        from harness import goals as _goals
        draft = content or (ws.path(path).read_text() if path and ws.path(path).exists() else "")
        if not draft.strip():
            return json.dumps({"ok": False, "errors": ["give `content` (the draft with sorry holes) or a `path` to it"]})
        if split_declaration(draft.rstrip(), row["statement"]) is None:
            return json.dumps({"ok": False, "errors": ["statement differs from the reference statement (must be byte-for-byte identical, followed by :=)"]})
        return json.dumps(_goals.skeleton_check(name, draft.rstrip()), ensure_ascii=False)

    def lean_profile(path: str) -> str:
        from harness import profile as _prof
        src = ws.path(path or "candidate.lean")
        if not src.exists():
            return json.dumps({"ok": False, "errors": [f"{src.name} not found"]})
        decl = src.read_text().rstrip()
        sha = hashlib.sha256(decl.encode()).hexdigest()[:12]
        cache = ws.state.setdefault("profile_cache", {})
        if sha not in cache:
            cache[sha] = _prof.profile(name, decl, max_cuts=12)
            if len(cache) > 6:
                cache.pop(next(iter(cache)))
        res = cache[sha]
        if res.get("floor"):
            ws.state["hb_floor"] = res["floor"]   # every later lean_check reports heartbeat points left against the real floor
        ws.save()
        return json.dumps(res, ensure_ascii=False)

    def lean_goals(path: str, depth: int = 1, from_line: int = 0) -> str:
        from harness import goals as _goals
        src = ws.path(path or "candidate.lean")
        if not src.exists():
            return json.dumps({"ok": False, "errors": [f"{src.name} not found"]})
        return json.dumps(_goals.goal_map(name, src.read_text(), depth=2 if int(depth or 1) >= 2 else 1, from_line=int(from_line or 0)), ensure_ascii=False)

    def lean_run(code: str) -> str:
        import os, subprocess, uuid
        from scorer.compile import ELAN_BIN, env_dir, project_env_dir
        if row["source"] == "putnambench":
            wd = env_dir(primary); head = row["header"].rstrip() + "\n\n"
        else:
            wd = project_env_dir(row["source"], primary); head = file_prefix(row, primary).rstrip("\n") + "\n\n"
        scratch = wd / "LRAScratch"; scratch.mkdir(exist_ok=True)
        f = scratch / f"s_{uuid.uuid4().hex[:10]}.lean"; f.write_text(head + code.rstrip() + "\n")
        env = dict(os.environ, PATH=f"{ELAN_BIN}:{os.environ.get('PATH','')}")
        try:
            from scorer.memgate import run_lean
            pr = run_lean(["lake", "env", "lean", "--json", f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}", str(f.relative_to(wd))], cwd=wd, env=env, capture_output=True, text=True, timeout=300)
        except subprocess.TimeoutExpired:
            f.unlink(missing_ok=True); return "error: timed out after 300s"
        f.unlink(missing_ok=True)
        off = head.count("\n")
        out = []
        for line in pr.stdout.splitlines():
            if not line.startswith("{"):
                continue
            try:
                m = json.loads(line)
            except json.JSONDecodeError:
                continue
            ln = (m.get("pos") or {}).get("line", 0) - off
            if ln < 1:
                continue  # messages from the context itself
            out.append(f"[{m.get('severity')}] line {ln}: {m.get('data','')}")
        return ("\n".join(out) if out else f"(no messages; exit {pr.returncode})")[:12000]

    _DENY = re.compile(r"(^|[;&|]\s*)(rm|mv|chmod|chown|sudo|pip|pip3|curl|wget|ssh|scp|nc|ncat|lake\s+build|lake\s+update|lake\s+exe\s+cache|git\s+(checkout|reset|clean|commit|push|pull|stash|rebase|merge|worktree))\b")

    _LEMMA_GREP = re.compile(r"\b(grep|rg)\b.*(\b(theorem|lemma)\b|\.lake/packages|Mathlib/)")

    def shell(command: str) -> str:
        import os, subprocess
        if not args.upstream_history and re.search(r"\bgit\s+(log|show|diff|blame)\b", command):
            return "error: repository history is not available in this run (--no-upstream-history)"
        if _DENY.search(command) or re.search(r"https?://", command):
            return "error: command not permitted (no network, no writes outside the workspace, no rm/mv/git checkout/lake build)"
        for m in re.finditer(r">\s*([^\s;&|]+)", command):  # redirects must stay inside the workspace
            if m.group(1).strip("'\"") in ("/dev/null", "/dev/stdout", "/dev/stderr"):
                continue   # cycle 41: `2>/dev/null` was rejected 21-26 times per pass (a wasted turn each)
            target = Path(m.group(1)).expanduser()
            if (target.is_absolute() and not str(target.resolve()).startswith(str(ws.root.resolve()))) or (not target.is_absolute() and ".." in target.parts):
                return (f"error: redirect target {m.group(1)} is outside the workspace (only workspace files and /dev/null are allowed; "
                        "grep/sed/git output needs no redirect, it is returned to you)")
        env = dict(os.environ, PATH=f"{Path.home()}/.elan/bin:{os.environ.get('PATH','')}")
        try:
            pr = subprocess.run(["bash", "-lc", command], cwd=ws.root, env=env, capture_output=True, text=True, timeout=120)
        except subprocess.TimeoutExpired:
            return "error: command timed out after 120s"
        out = (pr.stdout or "") + (("\n[stderr]\n" + pr.stderr) if pr.stderr else "")
        return f"exit code: {pr.returncode}\n{out}"[:12000]

    def _cand_sha() -> str | None:
        try:
            return hashlib.sha256(ws.path("candidate.lean").read_text().rstrip().encode()).hexdigest()[:12]
        except OSError:
            return None

    # Cycle 76 (--relative-error-lines, off by default): compile errors carried the scratch file's line numbers (context prefix, the
    # 9-line measure block, then the declaration) though the lean_check description promises declaration-relative ones. In A100
    # passes 5-7 all 465 failing compiles showed shifted positions and the model chased wrong lines (SKI, fiberwise, EM). Relabel
    # `N:C:` as `line n `<that line>`, col C:` of the compiled declaration (candidate or variant), quoting the line so it can be found
    # without counting. Applied after digest_error, which cuts its head at the first `name : `. Compat compiles have no measure block.
    _rel_on = bool(getattr(args, "relative_error_lines", False))
    if _rel_on:
        from harness.leantools import head_line_count as _hlc_rel
        from scorer.compile import MEASURE_ELAB as _ME_rel
        _rel_meas = (_ME_rel + "set_option Elab.async false in\narena_measure\n").count("\n")
        _rel_head = _hlc_rel(row, primary)

    def _rel(e, text, head=None):
        if not _rel_on or not e:
            return e
        m_ = re.match(r"(\d+):(\d+):\s*", e); hd = _rel_head if head is None else head
        if not m_ or int(m_.group(1)) <= hd:
            return e
        n_ = int(m_.group(1)) - hd; ln_ = (text or "").split("\n")
        src_ = ln_[n_ - 1].strip()[:60] if 0 < n_ <= len(ln_) else ""
        return f"line {n_}" + (f" `{src_}`" if src_ else "") + f", col {m_.group(2)}: " + e[m_.end():]

    def _dup_note() -> str:
        """Cycle 34: the duplicate guard in lean_check fired 34 times in POC 2 pass 1, each a wasted turn, mostly right after the model
        rewrote (11) or shell-restored (8) candidate.lean to text it had already checked. Say so at write time, with the earlier
        result, so the model does not spend the next turn re-checking it."""
        sha = _cand_sha()
        if sha is None:
            return ""
        prior = next((a for a in reversed(ws.state["attempts"]) if a.get("sha") == sha), None)
        if prior is None:
            return ""
        _ct = (ws.root / "candidate.lean").read_text().rstrip() if _rel_on and (ws.root / "candidate.lean").exists() else ""
        res = f"compiled, score {prior.get('score')}" if prior.get("ok") else f"failed: {_rel(prior.get('error') or '', _ct)[:120]}"
        return (f"\nNOTE: candidate.lean is now byte-identical to an attempt already checked ({res}). Do not lean_check it again; "
                "edit it first (or move on to a new idea).")

    hardtail_local = 0   # consecutive hard-tail checks that are still local edits (>= 90% of the starting best's tokens)
    stall_checks = 0     # R3: consecutive checks without a new best in this run
    forced_turns_bf = 0  # budget-forcing rescues in this run

    def lean_check(path: str) -> str:
        nonlocal checks, best, hardtail_local, stall_checks
        decl = ws.path(path or "candidate.lean").read_text().rstrip()
        # Duplicate guard: 24 of 134 compiles in pass 5 re-checked a byte-identical candidate (often the inherited best).
        # Return the earlier result instead of compiling, and do not count it as a check.
        sha = hashlib.sha256(decl.encode()).hexdigest()[:12]
        prior = next((a for a in reversed(ws.state["attempts"]) if a.get("sha") == sha), None)
        if prior is not None:
            return json.dumps({"ok": bool(prior.get("ok")), "unchanged": True,
                               "note": "candidate.lean is byte-identical to an attempt already checked (result below); nothing was compiled and this does not count as a check. Edit the candidate before checking again.",
                               "prior": {k: (_rel(prior.get(k), decl) if k == "error" else prior.get(k)) for k in ("tokens", "heartbeats", "ok", "error", "score", "run_id") if prior.get(k) is not None}})
        checks += 1
        body = split_declaration(decl, row["statement"])
        if body is None:
            return json.dumps({"ok": False, "errors": ["statement differs from the reference statement (must be byte-for-byte identical, followed by :=)"]})
        bad = check_forbidden(decl)
        if bad:
            return json.dumps({"ok": False, "errors": [f"forbidden construct: {bad}"]})
        toks = count_tokens(body); r = comp(decl, primary); _autofix = None
        if not r.ok:   # cycle 49: drop local hypotheses from grind lists (newer Lean rejects them) and recompile once
            from harness.leantools import fix_redundant_grind as _frg
            _fixed, _names = _frg(decl, r.errors)
            if _fixed:
                _r2 = comp(_fixed, primary)
                if _r2.ok:
                    decl, r = _fixed, _r2; body = split_declaration(decl, row["statement"]) or body; toks = count_tokens(body)
                    sha = hashlib.sha256(decl.encode()).hexdigest()[:12]
                    ws.path(path or "candidate.lean").write_text(decl + "\n")
                    _autofix = f"removed redundant grind parameter(s) {', '.join(_names)} from candidate.lean (grind uses local hypotheses automatically)"
        if not r.ok and not _autofix:   # cycle 54: delete no-op lines ("made no progress" / "No goals"), up to 3 rounds
            from harness.leantools import noop_line_deletion as _nld, head_line_count as _hlc0
            _cur, _done, _errs = decl, [], r.errors
            for _round in range(3):
                _d = _nld(_cur, _errs, _hlc0(row, primary))
                if not _d:
                    break
                _cur = _d[1]; _done.append(_d[0]); _r2 = comp(_cur, primary); _errs = _r2.errors
                if _r2.ok:
                    decl, r = _cur, _r2; body = split_declaration(decl, row["statement"]) or body; toks = count_tokens(body)
                    sha = hashlib.sha256(decl.encode()).hexdigest()[:12]
                    ws.path(path or "candidate.lean").write_text(decl + "\n")
                    _autofix = "; ".join(_done) + " (in candidate.lean)"
                    break
        if not r.ok and not _autofix:   # cycle 53: failed rewrite -> reversed rule / simp_rw / erw / simp only, first that compiles
            from harness.leantools import rw_alternatives as _rwa, head_line_count as _hlc
            for _how, _cand in _rwa(decl, r.errors, _hlc(row, primary)):
                _r2 = comp(_cand, primary)
                if _r2.ok:
                    decl, r = _cand, _r2; body = split_declaration(decl, row["statement"]) or body; toks = count_tokens(body)
                    sha = hashlib.sha256(decl.encode()).hexdigest()[:12]
                    ws.path(path or "candidate.lean").write_text(decl + "\n")
                    _autofix = f"failed rewrite repaired in candidate.lean: {_how}"
                    break
        _rec = {"sha": sha, "tokens": toks, "heartbeats": r.heartbeats, "ok": r.ok,
                "error": (digest_error(r.errors[0], 300) if r.errors else None), "run_id": args.run_id}
        if not r.ok and getattr(args, "failed_moves", False):   # 2026-10-13 --failed-moves: the failed edit against the closer of best / reference
            try:                                                 # ({} = a rewrite, no move); off: the record is byte-identical to before
                from harness import cc_levers as _LVfm         # review 2026-10-13: the tool call (one batch = one refutation), the error's
                from harness.leantools import head_line_count as _hlcfm   # line relative to the declaration (< 1: environment), stale moves voided
                _rec["move"] = _LVfm.record_move(ws.state, [("best", best.get("proof")), ("ref", row["src"])], decl, call=f"{args.run_id}:{tool_calls}",
                                                 eline=_LVfm.error_line(r.errors[0] if r.errors else None, _hlcfm(row, primary)))
            except Exception:  # noqa: BLE001
                pass
        ws.record_attempt(_rec)
        # linter hints relative to the declaration: unused tactics / simp args are direct deletion targets
        from scorer.compile import file_prefix as _fp, split_modifiers as _sm, MEASURE_ELAB as _ME
        if row["source"] == "putnambench":
            head_lines = (row["header"].rstrip() + "\n\n" + _ME + "set_option Elab.async false in\narena_measure\n").count("\n")
        else:
            core, mods = _sm(_fp(row, primary)); head_lines = (core.rstrip("\n") + "\n\n" + _ME + "set_option Elab.async false in\narena_measure\n" + mods).count("\n")
        hints = []
        for m in r.messages:
            if m.get("severity") != "warning":
                continue
            d = str(m.get("data", "")); ln = (m.get("pos") or {}).get("line", 0) - head_lines
            if ln < 1:
                continue
            if "does nothing" in d or "unused" in d.lower() or "would suffice" in d:
                hints.append(f"line {ln}: " + re.sub(r"\s+", " ", d.split("Note:")[0]).strip()[:140])
        hints = list(dict.fromkeys(hints))[:12]
        res = {"ok": r.ok, "tokens": toks, "ref_tokens": row["proof_length"], "heartbeats": r.heartbeats, "ref_heartbeats": hbs.get(name), "warnings": r.warnings,
               "errors": [_rel(digest_error(e), decl) for e in r.errors[:5]], "linter_hints": hints}
        if _autofix:
            res["auto_fixed"] = _autofix
        if not r.ok:   # cycle 50: closest real declaration names for unknown identifiers / missing fields
            from harness.leantools import suggest_names as _sn
            _sug = _sn(row, primary, r.errors)
            if _sug:
                res["did_you_mean"] = _sug
        _best_before = float(best.get("score") or 33.33)
        if hardtail_target:   # hard-tail runs: steer away from polishing the old architecture
            hardtail_local = hardtail_local + 1 if toks > hardtail_target / 0.7 * 0.9 else 0
            if hardtail_local >= 4:
                res["strategy_note"] = (f"{hardtail_local} checks in a row are still local edits of the old proof ({toks} tokens; target <= {hardtail_target}). "
                                        "Stop polishing: go back to the protocol (lean_goals map, lemma search, 3-5 different architectures in one lean_check_variants).")
        # Cycle 28 signature assist: "Application type mismatch … in the application <const> …" was the top failure class in scout C
        # (23 of ~94 failed candidates) — the model guesses a library lemma's argument order/implicitness and retries blind.
        # Look the constant's signature up once (#check @const via lean_run; library names only, locals like `ih`/`h3` skipped)
        # and attach it to the result, saving the model a turn and a repeat guess.
        try:
            _heads = []
            for e_ in r.errors[:5]:
                m_ = re.search(r"in the application\s+\(?@?([A-Za-z_][\w.'!?]*)", re.sub(r"\s+", " ", str(e_)))
                if m_ and ("." in m_.group(1) or m_.group(1)[0].isupper()) and m_.group(1) not in _heads:
                    _heads.append(m_.group(1))
            if _heads:
                sigs = {}
                for h_ in _heads[:2]:
                    if h_ not in sig_cache:
                        sig_cache[h_] = lean_run(f"#check @{h_}")[:400]
                    sigs[h_] = sig_cache[h_]
                res["signatures"] = sigs
                res["signature_note"] = "application/type mismatch: `signatures` holds the exact signature of the applied constant — match its implicit/explicit argument order before retrying"
        except Exception:  # noqa: BLE001
            pass
        try:  # POC 2 token map: where the length axis is (proof-body line numbers)
            _off = decl[:len(decl) - len(body)].count("\n") if _rel_on and decl.endswith(body) else 0   # cycle 76: declaration lines under the flag
            _lt = [(i + 1 + _off, count_tokens(l), l.strip()[:70]) for i, l in enumerate(body.split("\n")) if l.strip()]
            _lt.sort(key=lambda x: -x[1])
            res["costliest_lines"] = [{"line": i, "tokens": n, "text": s} for i, n, s in _lt[:6]]
        except Exception:  # noqa: BLE001
            pass
        # Cycle 19 repeated-error nudge: pass 14 spent 7 of 12 checks on the variational problem re-trying `linarith` at the same
        # position (134:4) with slightly different surrounding text, each failing the same way. When the same error head
        # (position + first words) has failed >= 3 times in this run, say so and demand a different route.
        if not r.ok and r.errors:
            # cycle 33: build the head exactly as the attempt was recorded (digest_error). The raw form keeps the hypotheses of an
            # `unsolved goals` error while the stored digest elides them, so the two never matched: in POC 2, 31 error heads failed
            # >= 3 times within one run (up to 7) and the nudge fired in 1 trajectory.
            _head = digest_error(r.errors[0], 300)[:60]
            _same = sum(1 for a in ws.state.get("attempts", []) if a.get("run_id") == args.run_id and not a.get("ok") and (a.get("error") or "")[:60] == _head)
            if _same >= 3:
                res["note"] = (f"This same error has now failed {_same} times in this run ({_rel(_head, decl)!r}). Retrying variants of the same tactic at the same spot is not "
                               "working: prove that step by a different route (another tactic family, an explicit `have` with the needed inequality/equality, "
                               "a library lemma via `exact?`), or restore the last compiling candidate and cut elsewhere.")
        # Cycle 16 auto-variant: the top failed-check class is `rw` "Did not find an occurrence of the pattern" (9 of 51 failures in
        # pass 11). When that is the only error, compile the same line once as `simp only [...]`; if it compiles, save it as
        # candidate_autofix.lean and tell the model (it scores/records it via lean_check, so provenance stays the model's run).
        if not r.ok and len(r.errors) == 1 and "Did not find an occurrence of the pattern" in r.errors[0]:
            _m = re.match(r"\s*(\d+):\d+:", r.errors[0])
            if _m:
                _ln = int(_m.group(1)) - head_lines; _lines = decl.split("\n")
                if 1 <= _ln <= len(_lines) and re.search(r"\brw\s*\[", _lines[_ln - 1]):
                    _lines[_ln - 1] = re.sub(r"\brw\s*\[", "simp only [", _lines[_ln - 1], count=1)
                    _variant = "\n".join(_lines)
                    try:
                        _rv = comp(_variant, primary)
                    except Exception:  # noqa: BLE001
                        _rv = None
                    if _rv is not None and _rv.ok:
                        ws.path("candidate_autofix.lean").write_text(_variant + "\n")
                        _vb = split_declaration(_variant, row["statement"]) or ""
                        res["autofix"] = (f"the failing `rw` at candidate line {_ln} compiles as `simp only [...]` ({count_tokens(_vb)} tokens, {_rv.heartbeats} heartbeats); "
                                          "saved as candidate_autofix.lean: lean_check that path to score and record it, or copy it into candidate.lean and continue.")
        if r.ok:
            L = len_pct(row["proof_length"], toks); H = hb_pct_local(name, r.heartbeats, hbs.get(name))
            provisional = problem_score(True, L, H, 100.0)
            res.update({"length_reduction_pct": round(L, 2), "heartbeat_reduction_pct": round(H, 2), "predicted_score_if_compatible": provisional, "reference_score": 33.33})
            try:   # Tier 1 axis signal (panel R1): which axis still has points, and the exchange rate between them
                from scorer.score import local_reference_heartbeats as _lrh
                _rt = int(row["proof_length"]); _rh = int(_lrh(name) or hbs.get(name) or 0); _fl = ws.state.get("hb_floor")
                if _rt and _rh and r.heartbeats is not None:
                    _lp = round(toks / _rt * 100 / 3, 2); _hp = round(max(0, r.heartbeats - (_fl or 0)) / _rh * 100 / 3, 2)
                    res["axis"] = {"points_per_token": round(100 / (3 * _rt), 4), "points_per_1k_heartbeats": round(100000 / (3 * _rh), 3),
                                   "one_token_equals_heartbeats": round(_rh / _rt, 1), "points_left_length": _lp,
                                   "points_left_heartbeats": _hp, "heartbeat_floor": _fl,
                                   "work_on": "tokens" if _lp >= _hp else "heartbeats",
                                   "note": ("points left are upper bounds (a proof cannot reach 0 tokens); " +
                                            ("heartbeat floor measured by lean_profile" if _fl else "heartbeat floor not measured yet: call lean_profile"))}
            except Exception:  # noqa: BLE001
                pass
            if args.simp_prune and provisional > best["score"]:   # cycle 58: one simp? compile prunes unused lemmas from `only` lists
                try:
                    from harness.leantools import simp_prune as _sp
                    _pp = _sp(decl, lambda d: comp(d, primary), head_lines)
                    if _pp:
                        _rp = comp(_pp[0], primary)
                        _tp = count_tokens(split_declaration(_pp[0], row["statement"]) or "")
                        if _rp.ok and _tp:
                            _Lp = len_pct(row["proof_length"], _tp); _Hp = hb_pct_local(name, _rp.heartbeats, hbs.get(name))
                            _sc = problem_score(True, _Lp, _Hp, 100.0)
                            if _sc > provisional:
                                decl, r, toks, L, H, provisional = _pp[0], _rp, _tp, _Lp, _Hp, _sc
                                ws.path(path or "candidate.lean").write_text(decl + "\n")
                                res.update({"tokens": toks, "heartbeats": r.heartbeats, "length_reduction_pct": round(L, 2), "heartbeat_reduction_pct": round(H, 2),
                                            "predicted_score_if_compatible": provisional,
                                            "auto_pruned": f"simp? dropped {_pp[1]} unused lemma(s) from `only` lists; candidate.lean updated"})
                except Exception:  # noqa: BLE001
                    pass
            if provisional > best["score"]:
                compat = {primary: True}; _cfail = {}
                for v in versions[1:]:
                    _rv = comp(decl, v, count=False); compat[v] = _rv.ok
                    if not _rv.ok:   # cycle 56: say why (errors at that toolchain, names that exist there)
                        from harness.leantools import compat_failure as _cf
                        _cfail[v] = _cf(row, v, [_rel(e, decl, _hlc_rel(row, v) - _rel_meas) for e in _rv.errors] if _rel_on else _rv.errors)
                Z = compat_pct(compat); sc = problem_score(True, L, H, Z)
                res.update({"compat": compat, "score": sc})
                if _cfail:
                    from harness.leantools import compat_note as _cn
                    res.update({"compat_failures": _cfail, "compat_note": _cn(primary, _cfail, Z, sc, provisional)})
                if sc > best["score"]:
                    try:   # Tier 1 ledger: record the winning edit as a diff so a later run can re-apply it (panel: tricks lost between passes)
                        import difflib as _dl
                        _prev = best.get("proof") or ""
                        _d = [l for l in _dl.unified_diff(_prev.splitlines(), decl.splitlines(), lineterm="", n=0) if l[:1] in "+-" and not l.startswith(("+++", "---"))]
                        _led = ws.state.setdefault("ledger", {}).setdefault("wins", [])
                        _led.append({"run_id": args.run_id, "check": checks, "d_score": round(sc - float(best.get("score") or 33.33), 2),
                                     "d_tokens": toks - int(best.get("tokens") or row["proof_length"]), "d_heartbeats": (r.heartbeats or 0) - int(best.get("heartbeats") or 0),
                                     "diff": "\n".join(_d)[:700]})
                        ws.state["ledger"]["wins"] = _led[-30:]
                    except Exception:  # noqa: BLE001
                        pass
                    best = {"score": sc, "proof": decl, "tokens": toks, "heartbeats": r.heartbeats, "L": round(L, 2), "H": round(H, 2), "Z": Z, "compat": compat}
                    ws.state["best"] = best; ws.state["attempts"][-1]["score"] = sc; ws.save()
                    ver_f.write(json.dumps({"problem": name, "sha256": hashlib.sha256(decl.encode()).hexdigest()[:16], "proof": decl, "tokens": toks, "ref_tokens": row["proof_length"],
                                            "heartbeats": r.heartbeats, "primary": primary, "primary_ok": True, "compat": compat, "L": round(L, 2), "H": round(H, 2), "Z": Z, "score": sc,
                                            "provenance": {"kind": ("closed-dev-only" if args.model_preset else "api-dev-only"), "model": prov_model, "run_id": args.run_id, "mode": "agent", "check": checks}}, ensure_ascii=False) + "\n"); ver_f.flush()
                    print(f"{name[:18]:18s} check {checks}: NEW BEST tok={toks} ({L:+.1f}%) hb={r.heartbeats} ({H:+.1f}%) Z={Z:.0f} score={sc}", flush=True)
        # R3: 8 checks in a row without a new best -> ask for a new rewrite
        stall_checks = 0 if float(best.get("score") or 33.33) > _best_before else stall_checks + 1
        if stall_checks >= 8 and stall_checks % 8 == 0:
            res["rewrite_note"] = (f"{stall_checks} checks in a row without a new best: editing has stalled. Start a NEW rewrite with a different architecture "
                                   "(outline with sorry holes -> lean_skeleton -> fill one hole at a time), using the goal map, LIBRARY LEADS and technique cards.")
        return json.dumps(res, ensure_ascii=not _rel_on)

    t_start = time.time()
    traj_f.write(json.dumps({"type": "header", "run_id": args.run_id, "problem": name, "model": args.model, "api_model": api_model, "endpoint": args.endpoint,
                             "quant": args.quant if args.endpoint == "openrouter" else None, "reasoning_effort": args.reasoning_effort, "turn_budget": args_turns,
                             "max_tokens": args.max_tokens, "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "system": SYSTEM,
                             "tools": [t["name"] for t in TOOLS], "best_at_start": ws.state["best"].get("score")}, ensure_ascii=False) + "\n"); traj_f.flush()
    notes_written = False
    turns_since_check = 0
    finish_rejections = 0
    shell_calls = 0
    lemma_greps = 0; searched = False   # cycle 42: 57 lemma-hunting greps and 0 lean_search calls in the measurement pass
    last_truncated = False   # after a truncated turn, give the next one double room so the pending tool call can complete
    trunc_count = 0   # pass 7: keep a raised cap for the rest of the run after a truncation; cycle 15: ~60% of remaining truncations hit the doubled 8k cap, so escalate 8k -> 12k -> 16k on repeats
    # Cycle 51 tested running this on every cold start (first improvement comes only at turn 6-26 in the held-out A/B): on four references
    # it gained 0, 0, +1.86, +0.55 for 1.5-4 min each, floors the agent passes in its first turns anyway. Generic closers raise heartbeats
    # above cheap references and H is not floored at 0. Kept behind --length-tools.
    if args.length_tools and (ws.root / "candidate.lean").exists() and not args.from_reference:
        # Mechanical pass before the first model turn (research integration list, 2026-10-07): Mathlib TacticAnalysis linters +
        # lemma-hinted block/tail probes on the starting candidate; an improvement is scored/banked through lean_check and becomes
        # the candidate the model starts from. Costs 1-3 min of Lean (memory-gated), no model tokens.
        try:
            _pre_res = json.loads(lean_mine("candidate.lean"))
            if _pre_res.get("mined"):
                msgs[0]["content"] += (f"\n\nMECHANICAL PRE-PASS: the harness already shortened candidate.lean mechanically "
                                       f"({_pre_res['mined'].get('how', '')[:200]}); score {_pre_res['mined'].get('score')}. Continue from it.")
            print(f"{name[:18]:18s} pre-pass: {(_pre_res.get('mined') or {}).get('score', 'no improvement')}", flush=True)
        except Exception as _e:  # noqa: BLE001
            print(f"{name[:18]:18s} pre-pass failed: {_e}", flush=True)
    # Cycle 45: turn 0 hit the output cap in 16% of recent runs (5 of 31) against 2.4% for later turns: the model plans the whole run in
    # its head from the long opening message. Ask for an early first action, last in the message where it is read last.
    if isinstance(msgs[0]["content"], str) and "SHORT POLISH RUN" not in msgs[0]["content"]:
        msgs[0]["content"] += ("\n\nOPENING MOVE: keep this first turn short. Pick the single most promising idea from the material above and act on it "
                               "with ONE tool call now (a lean_check_variants batch, lean_profile, lean_goals or lean_search). You will see results "
                               "and plan the next step from them; do not plan the whole run before acting.")
    turn = -1; extra_turns = 0; _sess_turn_max = 0.0; _last_in_tokens = 0
    while turn + 1 < args_turns:   # cycle 24: a while-loop so scout turns spent only on rejected shell calls can be refunded
        # 2026-10-11 (the closed-track audit checks the MAX per problem):
        # stop BEFORE a turn that could cross the cap. Reserve = the WORST CASE of the next turn: its whole context billed uncached
        # (caching is best effort; one Sol turn carried 301k tokens) plus its full output cap, at the list prices; never less than 1.25x
        # this session's costliest turn. The provider cannot bill more output than max_tokens, so spend + reserve <= cap is a hard bound.
        _turn_reserve = 0.0
        if args.model_preset:
            _pi, _po, _pr_, _pw = MODEL_PRESETS[args.model_preset]["prices"]
            _cap_next = max(args.max_tokens * min(4, 3 + trunc_count), MODEL_PRESETS[args.model_preset].get("min_cap", 0))
            _ctx = max(_last_in_tokens, (len(SYSTEM) + len(json.dumps(msgs, ensure_ascii=False, default=str))) // 2) + 20000
            _turn_reserve = max((_ctx * max(_pi, _pw) + _cap_next * _po) / 1e6, 1.25 * _sess_turn_max)
        if args.model_preset and float(ws.state.get("api_spend") or 0) + _turn_reserve > args.budget_usd:
            print(f"{name[:18]:18s} budget reached: ${float(ws.state.get('api_spend') or 0):.3f} + reserve ${_turn_reserve:.3f} > ${args.budget_usd:.2f}; session ends", flush=True)
            break
        turn += 1
        if turns_since_check >= 4:
            msgs.append({"role": "user", "content": f"You have not run lean_check for {turns_since_check} turns. Exploration is fine, but convert it now: write candidate.lean with your best complete attempt (even if imperfect) and call lean_check, then continue from the errors."})
            turns_since_check = 0
        # Cycle 21 fresh-start fallback: a new approach that has produced no compiling candidate by turn 20 is not going to
        # (extractedOldExprInVars: two fresh starts, 21 checks, zero compiled). Restore the stored best and spend the rest on it.
        if fresh_start and turn == 20 and (ws.root / "best.lean").exists() and not any(a.get("ok") for a in ws.state.get("attempts", []) if a.get("run_id") == args.run_id):
            (ws.root / "candidate.lean").write_text((ws.root / "best.lean").read_text())
            msgs.append({"role": "user", "content": f"FRESH START FALLBACK: 20 turns and no compiling candidate from the new approach. candidate.lean has been restored to the "
                                                    f"stored best (score {ws.state['best'].get('score')}). Spend the remaining {args_turns - turn} turns on THAT proof: structural cuts one at a "
                                                    "time, lean_check after each. First, add one line to notes.md on why the new approach did not compile, so later runs do not repeat it."})
            print(f"{name[:18]:18s} fresh start produced nothing compiling by turn 20: restored best.lean", flush=True)
            fresh_start = False
        if think_prompt_on and turn > 0 and turn % 6 == 0:
            msgs.append({"role": "user", "content": THINK_NUDGE})
        # Cycle 38: in 6-turn polish runs 73% (24/33) made ZERO checks: this wrap-up message fired at turn 3, after a reading turn, and the model
        # wrote notes and finished. Short runs (<= 10 turns) get it on the final turn only.
        if turn == args_turns - (1 if args_turns <= 10 else 3) and not notes_written:
            msgs.append({"role": "user", "content": "Budget nearly over (3 turns left). Write notes.md now (write_file): what worked, what failed and why, lemma names you confirmed exist or do not exist, and the most promising next idea. Tag every negative claim with the check that showed it, `[tested: <what> -> <result>]`; untagged claims are shown to later runs as unverified. Then make sure candidate.lean holds your best compiling candidate and call finish."})
        # Cycle 26: scouts kept calling shell when the scout rule would reject it (48 rejected calls over scouts A+B, ~22 s each);
        # withhold the tool from the API call instead of refunding the wasted turn.
        tools_now = [t_ for t_ in TOOLS if t_["name"] != "shell"] if (args.from_reference and (checks == 0 or shell_calls >= 3)) else TOOLS
        if not args.length_tools:
            tools_now = [t_ for t_ in tools_now if t_["name"] != "lean_mine"]
        if args.strategy == "hardtail" and hardtail_batches == 0 and turn >= 2 and forced_turns < 3:
            # Smoke 2026-10-07 (8 turns): the model wrote one candidate of its own, never batched architectures, then finished. From turn 2,
            # until a >= 3-variant batch exists, offer only the step-4 tools and say what this turn must produce.
            if forced_turns == 0:
                msgs.append({"role": "user", "content": (f"PROTOCOL STEP 4 NOW: call lean_check_variants with 3-5 FULL candidates of DIFFERENT architecture, each at most "
                                                         f"{hardtail_target} tokens, built from the goal map (shared `<;>` closer over the case split, a generalised helper `have`, "
                                                         "term mode from library lemmas, a different induction/cases variable). lean_run is available for a quick lemma check first. "
                                                         "Other tools return after this batch.")})
            forced_turns += 1
            tools_now = [t_ for t_ in tools_now if t_["name"] in ("lean_check_variants", "lean_run", "lean_goals", "read_file")]
        m = None
        # Cycle 23: truncation rate by cap over passes 15-16 was 21% at 4k, 10% at 8k, 2% at 12k, 1% at 16k; each truncation wastes the
        # turn and the first one only unlocks the next step. Start one step up (8k) and keep the 16k ceiling.
        # Cycle 25: large reference proofs (> 1500 Lean tokens: the Putnam rows, fold_advances) truncate 13-18% of turns even at 8k,
        # because writing the candidate alone costs several thousand tokens; start them at 12k.
        # Cycle 37 (Tier 4 hygiene): over passes 12-16 + POC 2 (2442 turns) truncation was 25.4% at 4k, 8.8% at 8k, 3.2% at 12k, 1.2% at 16k, and
        # 83% of truncations ended with no tool call (a wasted turn). Start every turn at 12k (was 8k; 12k only for references > 1500 tokens).
        cap = args.max_tokens * min(4, 3 + trunc_count)
        if args.model_preset:
            cap = max(cap, MODEL_PRESETS[args.model_preset].get("min_cap", 0))
        t_call = time.time()
        for attempt in range(args.max_api_retries):   # interruptible instances pause when outbid: raise this (e.g. 20) to ride it out
            try:
                if args.endpoint == "openai":
                    m = _oai.create(base_url=args.base_url, api_key=_oai_key, model=api_model, max_tokens=cap, system=(SYSTEM if args.length_tools else SYSTEM_BASE), tools=tools_now, messages=msgs, extra_body=extra_body,
                                    **({"think_mode": MODEL_PRESETS[args.model_preset]["think_mode"], "cache": MODEL_PRESETS[args.model_preset]["cache"],
                                       "stream": MODEL_PRESETS[args.model_preset].get("stream", False)} if args.model_preset else {}))
                else:
                    with cl.messages.stream(model=api_model, max_tokens=cap, system=(SYSTEM if args.length_tools else SYSTEM_BASE), tools=tools_now, messages=msgs,
                                            extra_body=extra_body) as s:
                        m = s.get_final_message()
                break
            except anthropic.RateLimitError:
                time.sleep(min(30 * 2 ** attempt, 300))
            except anthropic.APIStatusError as e:
                if e.status_code in (529, 503, 500) or "overloaded" in str(e).lower():
                    time.sleep(min(30 * 2 ** attempt, 300)); continue
                if attempt >= 2:
                    log_f.write(json.dumps({"problem": name, "turn": turn, "status": f"api_error:{str(e)[:200]}"}) + "\n"); log_f.flush(); flush_traj({"type": "api_error", "turn": turn, "error": str(e)[:500]}); print(f"{name[:18]} turn {turn}: api error {str(e)[:120]}", flush=True); m = None; break
                time.sleep(10)
            except Exception as e:  # noqa: BLE001  (connection resets, timeouts, decode errors: retry with backoff, give up only after 6 tries)
                if attempt >= args.max_api_retries - 1:
                    log_f.write(json.dumps({"problem": name, "turn": turn, "status": f"api_error:{str(e)[:200]}"}) + "\n"); log_f.flush(); flush_traj({"type": "api_error", "turn": turn, "error": str(e)[:500]}); print(f"{name[:18]} turn {turn}: api error {str(e)[:120]}", flush=True); m = None; break
                time.sleep(min(10 * 2 ** attempt, 300))
        if m is None:
            break
        # Budget forcing (2026-10-08; self-hosted endpoint only, where we control the chat template): a turn that hit its cap while still
        # thinking (no tool call, no text) is not thrown away. Its thinking is sent back closed with </think> and the SAME assistant turn continues
        # (vLLM continue_final_message), so the model must act now. Unbiased LR-eval: 61% of A100 high-effort answers hit 32k while thinking.
        if (args.endpoint == "openai" and args.budget_forcing and m.stop_reason == "max_tokens"
                and not any(b.type == "tool_use" for b in m.content) and not any(b.type == "text" and (b.text or "").strip() for b in m.content)):
            _think = "".join(b.thinking or "" for b in m.content if b.type == "thinking")
            if _think:
                try:
                    _forced = msgs + [{"role": "assistant", "content": [{"type": "thinking", "thinking": _think + "\n(Thinking budget reached: act now with one tool call.)"}]}]
                    _m2 = _oai.create(base_url=args.base_url, api_key=_oai_key, model=api_model, max_tokens=args.max_tokens,
                                      system=(SYSTEM if args.length_tools else SYSTEM_BASE), tools=tools_now, messages=_forced,
                                      extra_body={**extra_body, "continue_final_message": True, "add_generation_prompt": False})
                    if not any(b.type in ("tool_use", "text") for b in _m2.content):
                        # the continuation arrives labelled as reasoning (no </think> in the output): read it as the answer, parse tool calls here
                        _txt = "".join(b.thinking or "" for b in _m2.content if b.type == "thinking")
                        _rest, _calls = _oai.parse_glm_tool_calls(_txt)
                        if _calls:
                            _m2.content = ([_oai.Block(type="text", text=_rest)] if _rest else []) + _calls
                            _m2.stop_reason = "tool_use"
                        elif _txt.strip():
                            _m2.content = [_oai.Block(type="text", text=_txt)]
                    if any(b.type in ("tool_use", "text") for b in _m2.content):
                        _m2.content = [b for b in m.content if b.type == "thinking"] + [b for b in _m2.content if b.type != "thinking"]
                        _m2.usage = type(m.usage)(m.usage.input_tokens + _m2.usage.input_tokens, m.usage.output_tokens + _m2.usage.output_tokens)
                        m = _m2; forced_turns_bf += 1
                        print(f"{name[:18]:18s} turn {turn}: budget forcing rescued a capped turn ({m.stop_reason}, {[b.name for b in m.content if b.type == 'tool_use']})", flush=True)
                        flush_traj({"type": "budget_forcing", "turn": turn, "stop": str(m.stop_reason), "tools": [b.name for b in m.content if b.type == "tool_use"]})
                except Exception as _e:  # noqa: BLE001
                    print(f"{name[:18]:18s} turn {turn}: budget forcing failed: {str(_e)[:160]}", flush=True)
        # Cycle 47: the same rescue on z.ai, where the template trick is unavailable. A turn capped while still thinking (7% of turns, 16% of
        # opening turns, 12-16k tokens each) is re-asked once with thinking DISABLED (z.ai accepts {"thinking": {"type": "disabled"}}: an
        # immediate tool call in ~5 s) and the tail of the cut reasoning appended to the last user message, so the turn ends in an action.
        if (args.endpoint != "openai" and m.stop_reason == "max_tokens" and not any(b.type == "tool_use" for b in m.content)
                and not any(b.type == "text" and (b.text or "").strip() for b in m.content)):
            _tail = "".join(getattr(b, "thinking", "") or "" for b in m.content if b.type == "thinking")[-2500:].strip()
            _note = ("[harness] Your previous reply hit the output limit while still thinking and was discarded. "
                     + (f"The end of that reasoning was:\n<<<\n{_tail}\n>>>\n" if _tail else "")
                     + "Act on it now with ONE tool call and minimal text (a lean_check_variants batch of the edits you planned, or "
                       "write_file of a NEW candidate); do not rewrite the current best unchanged.")
            _last = msgs[-1]
            _content = ([*_last["content"], {"type": "text", "text": _note}] if isinstance(_last["content"], list) else _last["content"] + "\n\n" + _note)
            _forced = msgs[:-1] + [{**_last, "content": _content}]
            try:
                _eb = {k: v for k, v in extra_body.items() if k not in ("reasoning_effort", "reasoning")}
                _eb["thinking"] = {"type": "disabled"}
                _m2 = cl.messages.create(model=api_model, max_tokens=args.max_tokens, system=(SYSTEM if args.length_tools else SYSTEM_BASE),
                                         tools=tools_now, messages=_forced, extra_body=_eb)
                if not any(b.type == "tool_use" for b in _m2.content):
                    # cycle 48: in the held-out A/B a real rescue left no trace; with thinking off GLM may write its call as template
                    # markup in the text (<tool_call>name<arg_key>…) instead of a tool_use block: parse it like the budget-forced path
                    from llm import openai_compat as _oaic
                    _rest, _calls = _oaic.parse_glm_tool_calls("".join(b.text or "" for b in _m2.content if b.type == "text"))
                    if _calls:
                        _m2.content = ([_oaic.Block(type="text", text=_rest)] if _rest else []) + _calls; _m2.stop_reason = "tool_use"
                _rtools = [b.name for b in _m2.content if b.type == "tool_use"]
                _rtext = "".join(getattr(b, "text", "") or "" for b in _m2.content if b.type == "text")
                flush_traj({"type": "nothink_rescue", "turn": turn, "ok": bool(_rtools), "stop": str(_m2.stop_reason), "tools": _rtools,
                            "text": _rtext[:400], "output_tokens": _m2.usage.output_tokens})
                if not _rtools:
                    print(f"{name[:18]:18s} turn {turn}: no-thinking retry gave no tool call (stop {_m2.stop_reason}, text {_rtext[:100]!r})", flush=True)
                if _rtools:
                    msgs[-1] = _forced[-1]   # keep what the model actually saw
                    _m2.usage.output_tokens += m.usage.output_tokens
                    m = _m2; forced_turns_bf += 1
                    print(f"{name[:18]:18s} turn {turn}: no-thinking retry rescued a capped turn ({_rtools})", flush=True)
            except Exception as _e:  # noqa: BLE001
                print(f"{name[:18]:18s} turn {turn}: no-thinking retry failed: {str(_e)[:160]}", flush=True)
        total_out += m.usage.output_tokens
        if args.model_preset:   # per-problem spend meter (cap $3/problem): provider cost when reported, else the price table
            _u = m.usage; _pi, _po, _pr_, _pw = MODEL_PRESETS[args.model_preset]["prices"]
            # list_price presets ignore the provider-reported cost: ClinePass reports exactly half of DeepSeek's standard list price
            # (off-peak rate), and the closed track is audited at the public list price (2026-10-11)
            _c = _u.cost if getattr(_u, "cost", None) is not None and not MODEL_PRESETS[args.model_preset].get("list_price") else (
                (max(0, _u.input_tokens - _u.cache_read - _u.cache_write) * _pi + _u.output_tokens * _po + _u.cache_read * _pr_ + _u.cache_write * _pw) / 1e6)
            _sp0 = float(ws.state.get("api_spend") or 0)
            ws.state["api_spend"] = round(_sp0 + _c, 6)
            # budget milestones: the turn whose spend crosses one records a
            # snapshot (spend, best so far, run, turn) in state.json and the trajectory, once per problem and milestone
            for _ms in (float(x) for x in args.budget_milestones.split(",") if x.strip()):
                if _sp0 < _ms <= ws.state["api_spend"] and f"{_ms:g}" not in ws.state.get("budget_milestones", {}):
                    _snap = {"spend": ws.state["api_spend"], "best": best["score"], "run_id": args.run_id, "turn": turn,
                             "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
                    ws.state.setdefault("budget_milestones", {})[f"{_ms:g}"] = _snap
                    print(f"{name[:18]:18s} budget milestone ${_ms:g} crossed: spend ${_snap['spend']:.3f}, best {_snap['best']} (cap ${args.budget_usd:.2f})", flush=True)
                    flush_traj({"type": "budget_milestone", "usd": _ms, **_snap})
            ws.save()
            _sess_turn_max = max(_sess_turn_max, _c); _last_in_tokens = _u.input_tokens
        last_truncated = (m.stop_reason == "max_tokens")
        uses = [b for b in m.content if b.type == "tool_use"]
        # 2026-10-11 (warm-up Sol run: 20 of 54 sessions had a turn cut at the 12k output cap, 22% of the run's spend): Sol degenerates
        # inside a tool-call argument (an endless `\t\t\t \n` tail) until the cap. The unparseable call ({"_raw_arguments": 40k-450k chars})
        # stayed in the conversation and was re-sent every later turn (+65k input tokens on Electromagnetism), inflating the budget gate's
        # reserve. Drop any truncated unparseable call from the history (it cannot execute; the full text goes to the trajectory) and say
        # so in its tool result; when its tail is degenerate repetition, also do not escalate the output cap: more room only buys more junk.
        runaway = [u for u in uses if last_truncated and isinstance(u.input, dict) and "_raw_arguments" in u.input]
        runaway_junk = False
        for u in runaway:
            _raw = str(u.input.get("_raw_arguments") or "")
            _junk = degenerate_tail(_raw)
            flush_traj({"type": "runaway_tool_call", "turn": turn, "tool": u.name, "chars": len(_raw), "degenerate": _junk, "raw": _raw})
            u.input = {"_dropped": f"cut at the output cap after {len(_raw)} chars of arguments"
                                   + (", ending in the same few characters repeated over and over" if _junk else "")}
            runaway_junk = runaway_junk or _junk
            print(f"{name[:18]:18s} turn {turn}: runaway {u.name} call cut at the output cap ({len(_raw)} chars) dropped from the history", flush=True)
        trunc_count += 1 if last_truncated and not runaway_junk else 0   # a cut legitimate long write still escalates as before
        texts = [b.text for b in m.content if b.type == "text"]
        log_f.write(json.dumps({"problem": name, "turn": turn, "out_tok": m.usage.output_tokens, "stop": str(m.stop_reason), "tools": [u.name for u in uses], "text": "".join(texts)[:300]}) + "\n"); log_f.flush()
        flush_traj({"type": "turn", "turn": turn, "max_tokens": cap, "stop": str(m.stop_reason), "input_tokens": m.usage.input_tokens, "output_tokens": m.usage.output_tokens,
                    "cache_read": getattr(m.usage, "cache_read", None), "cost": getattr(m.usage, "cost", None),
                    "seconds": round(time.time() - t_call, 1), "tools": [u.name for u in uses], "checks_so_far": checks, "best_so_far": best["score"]})
        if not uses:
            if m.stop_reason == "max_tokens":
                # Cycle 43: the old "write_file your current best candidate" made 5 of 14 post-truncation writes byte-identical to the best (a
                # wasted turn after the wasted 12k-token one). Hand back the tail of the cut reasoning (thinking from earlier turns may not be kept
                # in context) and ask for the planned edits as variants.
                _tail = "".join(getattr(b, "thinking", "") or "" for b in m.content if b.type == "thinking")[-2500:].strip()
                msgs += [{"role": "assistant", "content": [b.model_dump(exclude_none=True) for b in m.content] or [{"type": "text", "text": "(truncated)"}]},
                         {"role": "user", "content": "You ran out of output budget without calling a tool. "
                          + (f"The end of your cut reasoning was:\n<<<\n{_tail}\n>>>\n" if _tail else "")
                          + "Act on it now with ONE tool call and minimal text: send the edits you were planning as one lean_check_variants call "
                            "(3-6 FULL variants of candidate.lean), or write_file a NEW candidate. Do not rewrite the current best unchanged (it is already "
                            "checked and banked)."}]
                continue
            # Cycle 52: ending a turn with text only is an implicit finish and bypassed the finish guard: gpt-oss-120b (second-model
            # screen) stopped a 40-turn run after 4 turns this way. Apply the same rule as `finish`: refuse while a third of the budget
            # remains (at most 2 refusals per run). Flash never ended a held-out run this way.
            _left = args_turns - turn - 1
            if _left >= max(4, args_turns // 3) and finish_rejections < 2:
                finish_rejections += 1
                msgs += [{"role": "assistant", "content": [b.model_dump(exclude_none=True) for b in m.content] or [{"type": "text", "text": "(no reply)"}]},
                         {"role": "user", "content": f"You ended your turn without a tool call, but {_left} turns remain and the run continues. "
                          f"Best so far {best['score']} (reference 33.33). Work on the proof now with a tool call: a lean_check_variants batch of "
                          "3-6 different candidates (a new architecture if local edits are exhausted), lean_profile, lean_goals or lean_search. "
                          "Call finish only in the last third of the budget."}]
                continue
            break  # finished talking without tools
        results = []
        done = False
        turns_since_check += 1
        n_rejected = 0
        for u in uses:
            tool_calls += 1; inp = u.input or {}
            if u.name in ("lean_check", "lean_check_variants", "lean_mine") and "_dropped" not in inp:
                turns_since_check = 0
            try:
                if "_dropped" in inp:   # a runaway call cut at the output cap (above): nothing is executed
                    out = (f"Your {u.name} call was {inp['_dropped']}; it was dropped and nothing was executed. Write compactly and in smaller "
                           "pieces: one candidate per write_file without padding or trailing whitespace, at most 3 variants per "
                           "lean_check_variants, then continue.")
                elif u.name == "read_file":
                    txt = ws.path(inp["path"]).read_text(); lines = txt.split("\n")
                    s0 = max(1, int(inp.get("start") or 1)); e0 = min(len(lines), int(inp.get("end") or min(len(lines), s0 + 199)))
                    out = "\n".join(f"{i:5d}| {lines[i-1]}" for i in range(s0, e0 + 1)) + (f"\n... ({len(lines)} lines total)" if e0 < len(lines) else "")
                elif u.name == "write_file":
                    ws.path(inp["path"]).write_text(inp["content"]); out = f"wrote {Path(inp['path']).name} ({len(inp['content'])} chars)"
                    if Path(inp["path"]).name == "candidate.lean":
                        _dn = _dup_note(); out += _dn
                        # Cycle 44: 26 of 405 turns in the measurement + top-up runs were a bare lean_check right after a write_file turn.
                        # Check the new candidate in the same tool result (not for drafts with sorry holes: those go to lean_skeleton).
                        if not _dn and "sorry" not in inp["content"]:
                            out += "\n[auto lean_check of candidate.lean — do not check it again]\n" + lean_check("candidate.lean"); turns_since_check = 0
                    if Path(inp["path"]).name == "notes.md":
                        notes_written = True
                elif u.name == "lean_check":
                    out = lean_check(inp.get("path") or "candidate.lean")
                elif u.name == "shell":
                    # POC 2 scout rule (enforced, not just prompted): a 12-turn scout spent 7 turns on grep and never checked a candidate.
                    if args.from_reference and (checks == 0 or shell_calls >= 3):
                        n_rejected += 1
                        out = ("scout rule: " + ("no shell exploration before your first lean_check / lean_check_variants — write a candidate of your own architecture now and check it"
                                                 if checks == 0 else "shell budget (3 calls) exhausted for this scout run — write and check candidates instead"))
                    else:
                        shell_calls += 1; _h0 = _cand_sha(); out = shell(inp.get("command") or "")
                        if not searched and _LEMMA_GREP.search(inp.get("command") or ""):
                            lemma_greps += 1
                            if lemma_greps in (2, 5):
                                out += ("\n\n[harness] You are hunting library lemmas by hand. lean_search does this in one call: it ranks lemmas by match with the "
                                        "goals of candidate.lean (exact? at each goal with probes=true, unused same-file lemmas, simp/grind attributes) and returns "
                                        "signatures. Try it before the next grep.")
                        if _cand_sha() != _h0:   # only when the command changed candidate.lean (read-only greps stay silent)
                            out += _dup_note()
                elif u.name == "lean_run":
                    out = lean_run(inp.get("code") or "")
                elif u.name == "lean_check_variants":
                    out = lean_check_variants(inp.get("variants"))
                elif u.name == "lean_search":
                    searched = True
                    out = lean_search(inp.get("path") or "candidate.lean", bool(inp.get("probes")))
                elif u.name == "lean_skeleton":
                    out = lean_skeleton(inp.get("path") or "", inp.get("content") or "")
                elif u.name == "lean_profile":
                    out = lean_profile(inp.get("path") or "candidate.lean")
                elif u.name == "lean_goals":
                    out = lean_goals(inp.get("path") or "candidate.lean", inp.get("depth") or 1, inp.get("from_line") or 0)
                elif u.name == "lean_mine":
                    out = lean_mine(inp.get("path") or "candidate.lean")
                elif u.name == "finish":
                    # Premature finish guard: pass 5 lost a whole 40-turn budget on fiberwise (finish at turn 5 after one
                    # re-check of the existing best). Accept finish only near the end of the budget or after real work.
                    remaining = args_turns - turn - 1
                    if hardtail_target and hardtail_batches == 0 and remaining > 1 and finish_rejections < 3:
                        # smoke test 2026-10-07: the model finished at turn 2 without trying a single new architecture
                        finish_rejections += 1
                        out = (f"finish rejected: this is a hard-tail strategy run and no new architecture has been tried yet. The goal map is in the "
                               f"opening message. Do steps 2-4 now: plan in notes.md, lemma-search 2-3 routine steps with lean_run, then send 3-5 FULL "
                               f"candidates of different architecture (each <= {hardtail_target} tokens) in ONE lean_check_variants call.")
                    elif args_turns <= 10 and checks == 0 and remaining > 0 and finish_rejections < 2:
                        finish_rejections += 1   # cycle 38: short runs ended with zero checks
                        out = ("finish rejected: this short polish run has made no check yet. Send one lean_check_variants call with 3-6 single-edit "
                               "variants of candidate.lean now; finish after that.")
                    elif remaining >= max(4, args_turns // 3) and finish_rejections < 2:
                        # Cycle 41 (measurement pass, SKI): finished at turn 21/40 right after a new best, "local attack exhausted". Under R3 that is the
                        # moment for a NEW architecture, not for stopping: refuse finish while a third of the budget remains.
                        finish_rejections += 1
                        out = (f"finish rejected: {remaining} turns remain (a third or more of the budget). If local edits are exhausted, that is the signal for "
                               "a NEW rewrite with a different architecture (R3): outline it with sorry holes, check with lean_skeleton, use the LIBRARY LEADS, "
                               "the WINNING EDITS and the technique cards. finish is accepted in the last third of the budget.")
                    elif remaining > 3 and (checks < 5 or turn < args_turns // 2) and finish_rejections < 2:
                        finish_rejections += 1
                        out = (f"finish rejected: {remaining} turns remain and this run has done only {checks} lean_check(s) "
                               f"(best so far {best['score']}, reference 33.33). Re-checking the existing best is pointless. "
                               "Take the first untried item under 'Next ideas' in notes.md (or profile the costliest steps with lean_run), "
                               "edit candidate.lean, lean_check, and keep going. finish is accepted after 5 checks or in the last 3 turns.")
                    else:
                        out = "ok"; done = True
                else:
                    out = f"unknown tool {u.name}"
            except Exception as e:  # noqa: BLE001
                out = f"tool error: {e}"
            if args.lean_io and u.name in ("shell", "lean_run", "read_file") and len(out) > 1500:   # --lean-io output cap
                out = out[:1500] + f"\n... [truncated: {len(out) - 1500} more chars; narrow the command, or read_file with start/end]"
            results.append({"type": "tool_result", "tool_use_id": u.id, "content": out[:12000]})
        if args.from_reference and uses and n_rejected == len(uses) and extra_turns < 6:
            args_turns += 1; extra_turns += 1   # cycle 24: scout A lost ~4 of 12 turns to rejected shell calls; refund them (max 6)
        msgs += [{"role": "assistant", "content": [b.model_dump(exclude_none=True) for b in m.content]}, {"role": "user", "content": results}]
        if done:
            break
    if args.normalize and ws.state["best"].get("proof"):
        # 2026-10-10 (docs/break_90_panel.md item 1): a model-free lexer post-pass on the session's best
        # (harness/normalize.py: λx, $, bare trailing fun, <|, ;). Every rewrite is compiled on every toolchain; an improvement is scored
        # and recorded through the standard checker with this run's provenance, marked normalized. It never fails the session.
        try:
            from harness.normalize import normalize as _norm
            from harness.leantools import lean_check as _lc
            _nr = _norm(name, ws.state["best"]["proof"])
            if _nr.get("status") == "improved":
                _lc(name, _nr["proof"], ws.state, {"kind": ("closed-dev-only" if args.model_preset else "api-dev-only"), "model": prov_model, "run_id": args.run_id, "mode": "agent",
                                                   "check": checks + 1, "normalized": _nr.get("applied")}, out_dir / "verified.jsonl")
                ws.save(); best = dict(ws.state["best"])
                if best.get("proof"):
                    (ws.root / "best.lean").write_text(best["proof"].rstrip() + "\n")
                print(f"{name[:18]:18s} normalized: {_nr['before']['tokens']} -> {_nr['after']['tokens']} tokens, score {_nr['before']['score']} -> "
                      f"{_nr['after']['score']} ({_nr.get('applied')}, {_nr.get('compiles')} compiles)", flush=True)
            else:
                print(f"{name[:18]:18s} normalizer: {_nr.get('status')}", flush=True)
        except Exception as _e:  # noqa: BLE001
            print(f"{name[:18]:18s} normalizer failed: {type(_e).__name__}: {_e}", flush=True)
    summary = {"problem": name, "best_score": best["score"], "checks": checks, "tool_calls": tool_calls, "turns": turn + 1, "out_tokens": total_out, "seconds": round(time.time() - t_start)}
    flush_traj({"type": "end", **summary, "finished": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}); traj_f.close()
    # finished trajectories are committed gzipped (5-10x smaller); the plain file stays only while a run is in progress
    import gzip, shutil
    plain = pathlib.Path(traj_f.name); gz = plain.with_name(plain.name + ".gz")
    with plain.open("rb") as fi, gzip.open(gz, "ab") as fo:
        shutil.copyfileobj(fi, fo)
    plain.unlink()
    print(f"{name[:18]:18s} DONE best={best['score']} checks={checks} tool_calls={tool_calls} turns={turn+1} out_tok={total_out} {summary['seconds']}s", flush=True)
    return summary


# POC 2 (2026-10-07): multi-variant check — up to six full candidates scored in one call (like the lean_multi_attempt tool of public Lean tooling).
TOOLS.append({"name": "lean_check_variants",
              "description": "Compile, score and bank up to 6 FULL candidate variants in one call (each = complete declaration text, statement byte-identical to the reference). "
                             "Use it at a decision point instead of checking alternatives one per turn: e.g. the same proof with {simp_all | grind | omega | aesop} as the closer, "
                             "or three different case structures. Returns a table (ok, score, tokens, heartbeats, first error) and copies the best compiling variant to candidate.lean when it beats the current best.",
              "input_schema": {"type": "object", "properties": {"variants": {"type": "array", "minItems": 1, "maxItems": 6, "items": {"type": "object", "properties": {
                               "label": {"type": "string"}, "content": {"type": "string", "description": "full candidate text"}}, "required": ["content"]}}}, "required": ["variants"]}})
TOOLS.append({"name": "lean_mine",
              "description": "Mechanical length cutter for a COMPILING candidate (no thinking needed): replaces every `case`/typed `have`/bullet block by a "
                             "single closer (grind, simp_all, aesop, omega, fun_prop, norm_num, linarith, positivity, tauto, exact?), tries replacing each "
                             "tail of the proof by `all_goals first | grind | simp_all | aesop | omega | fun_prop`, and the whole proof by one closer; "
                             "combines what compiles, scores and banks it, and writes it to mined.lean (copied to candidate.lean if it beats the best). "
                             "Takes 1-3 minutes. Use it after every new compiling skeleton, then golf what it returns.",
              "input_schema": {"type": "object", "properties": {"path": {"type": "string", "description": "candidate file (default candidate.lean)"}}}})
TOOLS.append({"name": "lean_search",
              "description": "Library lemma search for a candidate: lemmas whose name and conclusion match the goals, same-file lemmas the reference does not use, "
                             "@[simp]/@[grind]/@[to_fun] lemmas for the goal's symbols, induction principles; with probes=true it also runs exact? in place at each "
                             "step (slower, 1-2 min). Returns up to 10 ranked leads with signatures and why. Use it after a restructure, or when a block looks like "
                             "it should be one library lemma. Leads are not answers: check the signature against the goal.",
              "input_schema": {"type": "object", "properties": {"path": {"type": "string", "description": "candidate file (default candidate.lean)"},
                                                                "probes": {"type": "boolean", "description": "also run exact? probes (default false: 2-25 s)"}}}})
TOOLS.append({"name": "lean_skeleton",
              "description": "Top-down development: check a DRAFT proof whose unfinished parts are `sorry` (as a tactic or as a term argument) and get the goal at "
                             "every hole plus any real errors. Use it to build a new architecture piece by piece: write the outline with holes, read each hole's goal, "
                             "fill one hole, re-run. Nothing is scored or banked; when no sorry remains, lean_check the candidate (sorry is forbidden there).",
              "input_schema": {"type": "object", "properties": {"content": {"type": "string", "description": "full draft declaration with sorry holes"},
                                                                "path": {"type": "string", "description": "or a workspace file holding the draft"}}}})
TOOLS.append({"name": "lean_profile",
              "description": "Heartbeat profile of a COMPILING tactic proof (Tier 1): where the heartbeats go, block by block (each block's cost, nested "
                             "blocks under the costliest step), the floor (the statement with a `sorry` body: H can never pass it) and the heartbeat points really "
                             "left. Costs include elaborating terms: notation such as `•` in a lambda or a `set` can cost more than a tactic. Use it before working on "
                             "heartbeats, and to decide between the token and heartbeat axes (see `axis` in lean_check). Takes 1-3 minutes; cached per proof.",
              "input_schema": {"type": "object", "properties": {"path": {"type": "string", "description": "candidate file (default candidate.lean)"}}}})
TOOLS.append({"name": "lean_goals",
              "description": "Goal map of a tactic proof: compiles the candidate once with Lean's `trace_state` before every top-level step (depth 1) or also "
                             "before every step one level down inside bullets / `=>` arms / `by` blocks (depth 2), and returns, keyed by the file's line numbers, "
                             "the goal(s) each step faces (first goal with hypotheses, every further goal as `case <name>: ⊢ <target>`). Use it to see which "
                             "steps are routine, which cases look alike, and to copy exact goals into `example … := by exact?` lemma searches. ~5-10 s.",
              "input_schema": {"type": "object", "properties": {"path": {"type": "string", "description": "candidate file (default candidate.lean)"},
                                                                "depth": {"type": "integer", "enum": [1, 2]},
                                                                "from_line": {"type": "integer", "description": "start at this line (paging for long proofs)"}}}})
SYSTEM += ("\n\nBATCH YOUR ALTERNATIVES: when you can think of 2-6 plausible rewrites of the same spot (different closers, different case structures, with/without a `have`), "
           "send them all in ONE lean_check_variants call rather than one lean_check per turn; every compiling variant is scored and banked, and the best one lands in candidate.lean. "
           "Each lean_check result also lists the costliest proof-body lines by token count: that is where the length axis is.")
SYSTEM_BASE = SYSTEM   # without the length experiment line (prompt text before it is shared)
# Cycle 83: the lexer rules as a constant, so --token-rules can give them to runs without --length-tools. The A100 and default Flash
# lines send SYSTEM_BASE and never saw them; the closed-line union review (2026-10-09) found no best proof using `f $ x`, 1 token
# less than `f (x)`.
# 2026-10-10 (hosted models on this harness, not opencode: Haiku 5.5, Sonnet 5.5, GPT-6.1 Sol, DeepSeek V4.1
# Flash): closed / hosted models run through THIS harness's own loop via the OpenAI-compatible path. Prices are USD per 1M tokens
# (input, output, cache read, cache write) and only back up a missing provider-reported cost. Results are closed-dev-only (never banked).
# They also price the worst-case turn for the cap gate, so they must not be below the real list price: on 2026-10-11 a fit over
# 1,493 Sol and 415 Sonnet billed turns gave exactly 0.99 x ($2.50 in, $10 out, $0.10 cache read) per 1M; Haiku 0.124 / 0.495.
MODEL_PRESETS = {
    "haiku-5.5": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/oline-keys/openrouter_anthropic_claude-haiku-5.5.key",
                      api_model="anthropic/claude-haiku-5.5", cache=True, think_mode="details", prices=(0.125, 0.50, 0.01, 0.15625)),
    "sonnet-5.5": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/oline-keys/openrouter_anthropic_claude-sonnet-5.5.key",
                       api_model="anthropic/claude-sonnet-5.5", cache=True, think_mode="details", prices=(2.50, 10.0, 0.10, 3.125),
                       list_price=True),
    # 2026-10-12 (P0-5): the closed track audits spend at LIST price, while OpenRouter bills exactly 0.99 x this table, so the meter
    # and the hard cap gate price every turn from the table (list_price) instead of the reported (billed) cost. The table's input
    # price is 1.25x the catalog's ($2.50 vs $2.00 per 1M for Sol and Sonnet), so table-priced spend is an upper bound on list spend.
    "gpt-6.1-sol": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/oline-keys/openrouter_openai_gpt-6.1-sol.key",
                        api_model="openai/gpt-6.1-sol", cache=False, think_mode="details", prices=(2.50, 10.0, 0.10, 2.50),
                        list_price=True),
    "deepseek-v4.1-flash": dict(base_url="https://api.cline.bot/api/v1", key="~/.config/vexorium/cline_api_key",
                                api_model="cline-pass/deepseek-v4.1-flash", cache=False, think_mode="none", prices=(0.30, 1.20, 0.006, 0.30),
                                stream=True, min_cap=40000, list_price=True),   # reasons ~35k tokens before its first action (2026-10-10 probe)
}


TOKEN_RULES = ("\n\nTOKEN COUNTING (the scorer's lexer: every bracket, comma, paren and operator is a token; a dotted name like Foo.bar_baz is ONE token). "
           "Measured: `⟨a, b⟩` 5 vs `And.intro a b` 3; `exact ⟨_, h⟩` 6 vs `exact .intro _ h` 4; `obtain ⟨a, b⟩ := h` 8 vs using `h.1`/`h.2`; "
           "`refine ⟨?_, ?_⟩` 6 vs `constructor` 1; `fun x => h x` 5 vs `h` 1; `intro x; exact h x` 6 vs `exact h` 2; `by exact h` 3 vs `h` 1; "
           "`rw [h]; exact h2` 7 vs `rwa [h]` 4; `simp at h; exact h` 6 vs `simpa using h` 3; `apply foo; exact bar` 5 vs `exact foo bar` 3; "
           "`simp only [a, b] at h ⊢` 10 vs `simp_all [a, b]` 6; `f (g x)` vs `f $ g x` saves 1 (`<|` saves 0); `fun x => e` vs `λx => e` saves 1 (write `λx` with no space: Lean reads it as `λ x`, the lexer counts `λx` as one token; also `λ_ =>`, `λx y =>`); each lemma in a hint list costs ~2. "
           "The big wins are still whole blocks replaced by one closer (`grind [lemmas]`, `simp_all`, `omega`, `fun_prop`, `aesop`) — 75-95% of a block.")
SYSTEM += TOKEN_RULES
LEVER_REVIEW = ("\n\nLEVER REVIEW FIRST (what broke the closed lines' plateau: a review that names exact edits, then one batch of compiles). Before "
                "any rewrite: (1) read best.lean line by line against this checklist and write up to 6 LEVERS in notes.md, each an exact edit with "
                "its expected effect on tokens and heartbeats: a hypothesis the goal never uses (drop it with `rintro -` or `clear` before an "
                "induction, so the induction hypotheses stay simple); `induction` followed by `unfold`/`split` on a recursive function (`fun_induction f`); "
                "the same tactic run repeated across cases (`all_goals`/`any_goals`, `<;>`, `iterate n` with `rotate_left`); `<;> first | A | B` "
                "(as `any_goals A` then `all_goals B`); hand-written side conditions (into the `simp only` list, or `(disch := omega)`); an expensive "
                "closer tried on goals a cheap one closes (a `with_reducible` pre-pass, `assumption` or `exact h` before `grind`/`simp`); `grind` on a "
                "simple or-split or list-membership goal (a syntactic `refine Or.imp ?_ ?_`); `exists` whose `try trivial` fails (a `constructor` "
                "chain); `show`/`change`/`unfold` lines that only restate the goal. (2) Test ALL levers in ONE lean_check_variants call, one lever per "
                "variant, each applied to the best. (3) Combine the winners in a second batch. Only when the levers are spent, go on with the plan above.")
SYSTEM += ("\n\nLENGTH IS THE MISSING AXIS: on most problems the proof is still ~40% of the reference length and the target is ~20%. After any new "
           "compiling skeleton, call lean_mine once: it finds which blocks a single automation call closes. Then rewrite the remaining long blocks.")

def _is_scout(r: dict) -> bool:
    """POC 2 scout runs (short, from the reference) are exploration, not resumed history: adaptive budgets, plateau and fresh-start
    logic must ignore them. Tagged mode=scout from cycle 27; earlier scouts recognised by run-id suffix -sA/-sB/-sC."""
    import re as _re
    return r.get("mode") == "scout" or bool(_re.search(r"-s[A-Z]$", r.get("run_id") or ""))

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problems", nargs="*", default=None)
    ap.add_argument("--turns", type=int, default=40)
    ap.add_argument("--workers", type=int, default=3)
    ap.add_argument("--max-tokens", type=int, default=4000)
    ap.add_argument("--model", default="glm-5.3-flash")
    ap.add_argument("--reasoning-effort", default="low")
    ap.add_argument("--no-bank-sync", dest="bank_sync", action="store_false", default=True, help="do not adopt a better same-model candidate from the bank at run start (main work root only; replication roots never sync)")
    ap.add_argument("--endpoint", choices=["zai", "openrouter", "openai"], default="zai", help="zai = z.ai Anthropic-compatible endpoint (dev probe); openrouter = OpenRouter Messages endpoint pinned to --quant providers; openai = any OpenAI-compatible /chat/completions server (self-hosted vLLM/SGLang)")
    ap.add_argument("--base-url", default="http://127.0.0.1:8000/v1", help="--endpoint openai: server base URL (…/v1)")
    ap.add_argument("--api-key-file", default=None, help="--endpoint openai: file holding the bearer token (omit for a local vLLM without auth)")
    ap.add_argument("--api-model", default=None, help="--endpoint openai: model id as the server names it (default: --model)")
    ap.add_argument("--serving-tag", default=None, help="--endpoint openai: provenance tag, e.g. vllm-h100-w4a16 -> model glm-5.3-flash-vllm-h100-w4a16@openai")
    ap.add_argument("--length-tools", action="store_true", help="2026-10-07 length experiment: expose the lean_mine tool and the LENGTH brief (off by default so POC 2 stays comparable)")
    ap.add_argument("--from-reference", action="store_true", help="POC 2 scouts: start candidate.lean from the reference proof (stored best is kept unless beaten)")
    ap.add_argument("--term-card", action="store_true", help="2026-10-11: add the TERM-MODE FINISH / PROBE-BEFORE-COMMIT card (DeepSeek→Sol lesson); off until an A/B")
    ap.add_argument("--brief-dir", default=None, help="append <dir>/<problem>.md (a facts-only knowledge brief) to the opening message")
    ap.add_argument("--brief", choices=["none", "automation", "direct", "restructure"], default="none", help="POC 2 scout strategy brief appended to the opening message")
    ap.add_argument("--closed-lessons", action=argparse.BooleanOptionalAction, default=True, help="cycle 80, DEFAULT ON since cycle 89 (held-out "
                    "flagab-1010-1014: +2.76 paired, 7/10 better, new-file +4.19): the general habits mined from the Opus 5.5 / GPT Astra lines "
                    "(simp dischargers, write each piece once, fun_induction, reducible pre-pass, syntactic closers) in the first message; "
                    "--no-closed-lessons turns them off")
    ap.add_argument("--variant-scores", action="store_true", help="cycle 78: lean_check_variants rows show each compiling variant's provisional score "
                    "and vs_best (duplicates filled from their earlier result), so the 'not above the stored best' note can fire")
    ap.add_argument("--relative-error-lines", action="store_true", help="cycle 76: lean_check-family errors (incl. compat failures) give positions as "
                    "`line n `<text>`, col C` of the compiled declaration instead of the scratch file's line; costliest_lines in declaration lines")
    ap.add_argument("--simp-prune", action="store_true", help="cycle 58: on a would-be new best, one simp? compile drops unused lemmas from `only` lists "
                    "(kept when it compiles and scores higher). Off by default while the A100-80 run uses the tagged harness.")
    ap.add_argument("--no-upstream-history", dest="upstream_history", action="store_false", default=True, help="compliance switch (R2): drop the git-history hint from the prompt and block git log/show in the shell tool")
    ap.add_argument("--no-budget-forcing", dest="budget_forcing", action="store_false", default=True, help="self-hosted endpoint: do not rescue turns that hit the cap while thinking (budget forcing, on by default)")
    ap.add_argument("--strategy", choices=["none", "hardtail"], default="none", help="hardtail: goal map tool (lean_goals) + map/lemma-search/restructure protocol with a 70%% token target, for problems flat after many passes")
    ap.add_argument("--think-prompt", choices=["off", "structural", "all"], default="off",
                    help="prompt-based thinking budget (self-hosted servings ignore the effort label): append a THINK LONGER instruction to the "
                         "opening message and re-inject it every 6 turns — in structural/fresh-start runs ('structural') or every run ('all')")
    ap.add_argument("--max-api-retries", type=int, default=6, help="attempts per API call on transport errors, backoff 10 s doubling to 300 s (20 ≈ 1.5 h tolerance for a paused interruptible instance)")
    ap.add_argument("--extra-body-json", default=None, help="--endpoint openai: JSON merged into the request body (e.g. provider pins, chat_template_kwargs)")
    ap.add_argument("--quant", default="nvfp4", help="OpenRouter provider quantization to pin (nvfp4 | fp4 | fp8); only with --endpoint openrouter")
    ap.add_argument("--run-id", default=time.strftime("agent-%Y%m%d-%H%M%S"))
    ap.add_argument("--fresh", action="store_true", help="discard the per-problem persistent state and start from the reference")
    ap.add_argument("--work-root", default="harness/work", help="per-problem state root (use a separate root for model comparisons)")
    ap.add_argument("--adaptive-turns", action="store_true", default=True, help="20 turns if best>=80, 60 if best<45, else 40 (default on)")
    ap.add_argument("--no-adaptive-turns", dest="adaptive_turns", action="store_false")
    ap.add_argument("--normalize", action="store_true", help="2026-10-10: after each session, run the lexer normalizer (harness/normalize.py) on the "
                    "best and record a compile-verified improvement; off until the arena accepts the $/λ style warnings (an upload check)")
    ap.add_argument("--token-rules", action="store_true", help="cycle 83: add the TOKEN COUNTING lexer rules (`f $ x`, projections, "
                    "constructor vs ⟨?_, ?_⟩, ...) to the system prompt of runs without --length-tools, which already have them; off until a z.ai A/B")
    ap.add_argument("--model-preset", choices=list(MODEL_PRESETS), default=None, help="2026-10-10: run a hosted model through this harness "
                    "(OpenRouter: haiku-5.5, sonnet-5.5, gpt-6.1-sol; ClinePass: deepseek-v4.1-flash). Sets endpoint/base-url/key/api-model, "
                    "prompt caching, reasoning passback; records are closed-dev-only (never banked); --budget-usd caps spend per problem")
    ap.add_argument("--lean-io", action=argparse.BooleanOptionalAction, default=None, help="2026-10-11 (docs/lean_io_proposal.md, simpler "
                    "version): no duplicate reference proof in the opening; shell/lean_run/read_file results capped at 1,500 chars. "
                    "Default off: the 2026-10-11 A/B rejected it (cost 113%%, score -3.29)")   # %% (2026-10-13): a bare % broke --help
    ap.add_argument("--budget-usd", type=float, default=2.85, help="with --model-preset: per-problem spend cap, a hard bound (2026-10-11: $2.85; audit limit $3)")
    ap.add_argument("--budget-milestones", default="2.0", help="with --model-preset: comma-separated spend levels whose crossing is recorded per problem (state.json budget_milestones, trajectory event, warning line)")
    ap.add_argument("--lever-review", action="store_true", help="cycle 88: on a problem whose last two runs gained < 3, open with a LEVER REVIEW "
                    "(a checklist of general edits -> up to 6 levers -> one lean_check_variants batch -> combine); off until a z.ai A/B")
    ap.add_argument("--heartbeat-first", action="store_true", help="2026-10-13: the HEARTBEAT_FIRST card with the "
                    "technique cards and heartbeat-aware cards / scout / structural / heartbeat briefs / closed lessons / lever review on problems "
                    "whose stored best has H points left >= L points left (always before a measured best); the system prompt's AUTOMATION FIRST "
                    "closers, LENGTH paragraph and lean_mine description become axis-conditional for the whole run (harness/cards.py HB_REWRITES), "
                    "so the A/B unit is the flag, not the gate; off until an A/B")
    ap.add_argument("--failed-moves", action="store_true", help="2026-10-13 (docs/opus_pass2_deep_dive.md §3: repeats of an already-seen error "
                    "rose to 56%% of failing checks by pass 5): every failed check records its edit against the closer of best / reference as a "
                    "move (state.json attempts[].move), and the opening message lists the REFUTED MOVES (harness/cc_levers.failed_moves_block: "
                    ">= 2 real compile refutations from separate tool calls, reopened when the best changes in the lines they touch); off until an A/B")
    args = ap.parse_args()
    if args.lean_io is None:   # A/B 2026-10-11 (probe/hx-leanio-ab.log): lean-io + effort low cost 113% of base at -3.29 score -> off by default
        args.lean_io = False
    if args.model_preset:   # hosted closed/open models through this harness (2026-10-10)
        _pr = MODEL_PRESETS[args.model_preset]
        args.endpoint, args.base_url, args.api_model = "openai", _pr["base_url"], _pr["api_model"]
        args.api_key_file = _pr["key"]
        if os.environ.get("LRA_SELFTEST_PRESET_URL"):   # harness/selftest.py budget_gate: the scripted fake server, no real key sent
            args.base_url, args.api_key_file = os.environ["LRA_SELFTEST_PRESET_URL"], None
        args.budget_forcing = False          # continue_final_message is a vLLM feature
        if args.model == "glm-5.3-flash":
            args.model = args.model_preset
        if args.work_root == "harness/work":
            raise SystemExit("--model-preset needs its own --work-root (never the Flash main line's harness/work)")
    if args.token_rules:
        globals()["SYSTEM_BASE"] = SYSTEM_BASE + TOKEN_RULES
    if args.heartbeat_first:   # 2026-10-13: one static system prompt per run, so its wording is axis-conditional (the per-problem gate is in run_problem)
        from harness import cards as _cards
        globals()["SYSTEM"] = _cards.heartbeat_aware(SYSTEM); globals()["SYSTEM_BASE"] = _cards.heartbeat_aware(SYSTEM_BASE)
        for _t in TOOLS:   # review 2026-10-13: lean_mine's "after every new compiling skeleton" (HB_REWRITES R11)
            _t["description"] = _cards.heartbeat_aware(_t["description"])
    rows = {json.loads(l)["name"]: json.loads(l) for l in (ROOT / "data/benchmark_warmup.jsonl").open() if l.strip()}
    hbs = {json.loads(l)["name"]: json.loads(l)["heartbeat"] for l in (ROOT / "data/benchmark_heartbeats.jsonl").open() if l.strip()}
    out_dir = ROOT / "probe/runs" / args.run_id; out_dir.mkdir(parents=True, exist_ok=True)
    names = args.problems or list(rows)
    print(f"run {args.run_id}: {len(names)} problems, model={args.model}, turns≤{args.turns}", flush=True)
    with ThreadPoolExecutor(args.workers) as ex:
        res = list(ex.map(lambda n: run_problem(n, args, rows, hbs, out_dir), names))
    (out_dir / "summary.json").write_text(json.dumps(res, indent=1))
    print("done", flush=True)


if __name__ == "__main__":
    main()
