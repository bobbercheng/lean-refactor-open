"""Agentic refactoring harness: the model gets a workspace and tools






"""
from __future__ import annotations

import argparse, json, os, re, sys, time, hashlib, pathlib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
try:                                                                                                                             
    import anthropic              
    from llm.zai_client import _key, BASE_URL              
except ImportError:                                                                                                      
    import types

    def _no_sdk(*_a, **_k):
        raise SystemExit("the anthropic package is needed only for --endpoint zai/openrouter: pip install anthropic, or use --endpoint openai")
    anthropic = types.SimpleNamespace(Anthropic=_no_sdk, RateLimitError=type("RateLimitError", (Exception,), {}),
                                      APIStatusError=type("APIStatusError", (Exception,), {}))                                                
    _key, BASE_URL = _no_sdk, None
from scorer.tokenize import split_declaration, count_tokens              
from scorer.forbidden import check_forbidden              
from scorer.compile import compile_putnam, compile_project, file_prefix              
from scorer.score import len_pct, hb_pct_local, compat_pct, problem_score              
from probe.verify_candidates import newest_first              
from harness.leantools import digest_error              
from harness import golf as G                                                             
from harness import blind_facts as _BF                                                         
from scorer.accept import decide as _decide, exact_score as _exact              

TOOLS = [
    {"name": "read_file", "description": "Read a file in the workspace. Files: original.lean (the reference declaration, compiles), context.lean (imports/header or the surrounding file prefix the declaration lives in — large, read ranges), candidate.lean (your current attempt). Optional start/end line numbers (1-based, inclusive).",
     "input_schema": {"type": "object", "properties": {"path": {"type": "string"}, "start": {"type": "integer"}, "end": {"type": "integer"}}, "required": ["path"]}},
    {"name": "write_file", "description": "Write a file in the workspace (normally candidate.lean with the COMPLETE declaration: the statement byte-for-byte as in original.lean, then `:=` and your proof). Writing candidate.lean also runs lean_check on it and returns the result, so no separate lean_check is needed.",
     "input_schema": {"type": "object", "properties": {"path": {"type": "string"}, "content": {"type": "string"}}, "required": ["path", "content"]}},
    {"name": "lean_check", "description": "Compile the full declaration in a workspace file (default candidate.lean) inside the real project environment on the primary toolchain. Returns ok, errors (line:col relative to the declaration), warnings, heartbeats, token count, and the predicted score vs the reference. If it compiles and improves, also reports compatibility on the other toolchains. Each call costs a few seconds; use it often.",
     "input_schema": {"type": "object", "properties": {"path": {"type": "string"}}}},
    {"name": "lean_run", "description": "Run a scratch Lean snippet in the problem's real environment (same imports/context as the declaration) and return the compiler messages. Use it to discover lemma names and tactics: e.g. `#check @SomeLemma`, `example : <goal> := by exact?`, `example ... := by simp?`, `#print axioms`. The snippet is appended after the context; do not repeat the imports. Each run costs a few seconds.",
     "input_schema": {"type": "object", "properties": {"code": {"type": "string"}}, "required": ["code"]}},
    {"name": "shell", "description": "Run a shell command (bash) in the workspace for exploration: grep/rg the project's Lean sources and Mathlib for lemma names and proof idioms, `git log -p`/`git show` on the problem's file in the project clone to find how the same proof was later simplified upstream, ls/cat/head/sed -n to read other files, or `lake env lean` on a scratch file. Timeout 120 s, output truncated. No network, no writes outside the workspace, no rm/mv/git checkout/lake build.",
     "input_schema": {"type": "object", "properties": {"command": {"type": "string"}}, "required": ["command"]}},
    {"name": "finish", "description": "Stop when you believe the best candidate has been checked (the harness keeps the best compiling candidate it has seen). Accepted only after at least 5 lean_checks in this run or in the last 3 turns; earlier calls are rejected with guidance.",
     "input_schema": {"type": "object", "properties": {"summary": {"type": "string"}}}},
]

SYSTEM = """You are a Lean 4 proof engineer working in a small workspace with tools. Goal: produce a proof of the SAME theorem that scores higher than the reference on
  score = mean(length_reduction%, heartbeat_reduction%, compatibility%),
where length = token count of the proof body (every bracket/operator is a token, dotted names are one token, comments don't count), heartbeats = elaboration cost, compatibility = fraction of listed toolchains on which it compiles unchanged.

Workflow (R3, operator 2026-10-08): REWRITE FIRST. Read original.lean (and context.lean if you need surrounding definitions) for its mathematical plan, then write your own proof of that plan top-down: outline it with `sorry` holes, check the outline with lean_skeleton (it returns each hole's goal), fill one hole at a time, then lean_check the complete candidate. EDIT incrementally (change one thing, lean_check, keep what compiles) only when the problem is too hard to write fresh, or to polish a proof that already compiles; if edits stall (about 8 checks without a new best), start a NEW rewrite with a different architecture instead of more edits. The harness remembers the best compiling candidate; a failed check costs nothing but a turn, so check early and often (every 1–2 turns). A rewrite built hole by hole does not fail all at once; never write a large proof blind and check it only at the end. lean_check returns linter_hints: tactics that do nothing and unused simp arguments are free deletions — do those first. Use lean_run to find lemma names and closing tactics (`example : <goal> := by exact?`, `simp?`, `#check`), and shell (grep/rg over the sources, `git log -p` on the file to see how upstream later simplified this proof) when you need real names or idioms rather than guesses; inside lean_run snippets `sorry` IS allowed, so you can test a proof skeleton with `sorry` placeholders and read the remaining goals. Never put sorry/admit/axiom/native_decide in candidate.lean, never add auxiliary declarations, `open`, or `set_option` outside the proof. CLOSERS: AUTOMATION FIRST (`grind` with lemma hints, forward hints `grind [→ lemma]` for lemmas concluding ∃ or a constructor, `simp`, `omega`, `aesop`, `solve_by_elim`, `linear_combination`): it is robust, while hand-written terms are the most common failure (wrong hypothesis, argument order). Once the proof compiles, replace an automation call by an explicit term only where the `axis` in lean_check says the heartbeats saved are worth more than the tokens added, and keep the swap only if it compiles and scores higher; on small proofs each `grind` call is a large share of the heartbeats, so count calls. When out of ideas or budget, call finish."""

                                                                                                                                       
                                                                                                                                     
                                                                                                                              
                                                                                                                              
SYSTEM_OPEN = """You are a Lean 4 proof engineer working in a small workspace with tools. Goal: produce a proof of the SAME theorem that scores higher than the reference on
  score = mean(length_reduction%, heartbeat_reduction%, compatibility%),
where length = token count of the proof body (every bracket/operator is a token, dotted names are one token, comments don't count), heartbeats = elaboration cost, compatibility = fraction of listed toolchains on which it compiles unchanged.

Workflow: read original.lean (and context.lean if you need surrounding definitions), then improve INCREMENTALLY: change one thing (delete a step, inline a `have`, replace one tactic), write candidate.lean, lean_check, and keep going from whatever compiles. The harness remembers the best compiling candidate; a failed check costs nothing but a turn, so check early and often (every 1–2 turns). Do NOT rewrite the whole proof in one go unless the problem is short — large rewrites almost always fail with "unsolved goals". lean_check returns linter_hints: tactics that do nothing and unused simp arguments are free deletions — do those first. Use lean_run to find lemma names and closing tactics (`example : <goal> := by exact?`, `simp?`, `#check`), and shell (grep/rg over the sources, `git log -p` on the file to see how upstream later simplified this proof) when you need real names or idioms rather than guesses; inside lean_run snippets `sorry` IS allowed, so you can test a proof skeleton with `sorry` placeholders and read the remaining goals. Never put sorry/admit/axiom/native_decide in candidate.lean, never add auxiliary declarations, `open`, or `set_option` outside the proof. Heartbeats matter as much as tokens: replacing `simp`/`simp_all`/`aesop`/`omega`/`nlinarith` with a targeted `simp only [...]`, `rw`, or `exact` usually gives the biggest gains. When out of ideas or budget, call finish."""


_CLAIM_RE = re.compile(r"\b(unavoidable|impossible|cannot|can't|does not exist|doesn't exist|never|not needed|no longer needed|floor|minimal|tight|must|required|only way|no way|dead end|confirmed negative)\b", re.I)


from llm.junk import degenerate_tail, junk_reason                                                                                      

                                                                                                                                           
                                                                                                                                               
                                                                                                                                         
                                                                                                                 
_TOOL_JSON_COMPACT = False


def _tool_json(obj, ensure_ascii: bool = True) -> str:
    """A tool result for the model: compact (no spaces, unicode kept) under --compact-tool-json, else json.dumps as before."""
    if _TOOL_JSON_COMPACT:
        return json.dumps(obj, ensure_ascii=False, separators=(",", ":"))
    return json.dumps(obj, ensure_ascii=ensure_ascii)


def unverified_claims(notes: str, limit: int = 8) -> list[str]:
    """Negative / absolute claims in notes.md without a `[tested: …]` tag (cycle 36). Section headers ("What FAILED (do not retry)") and hard
"""
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


ADAPTIVE_LOW_TURNS = 60                                                                                                 


def adaptive_rung(b0: float, stagnant: bool, low_turns: int = ADAPTIVE_LOW_TURNS) -> int:
    """The adaptive rule's turn budget before the two-strikes cases: 10 / 20 at best >= 80 (stagnant / not), 50 below 70, 40 below 80, and

"""
    return (10 if stagnant else 20) if b0 >= 80 else (int(low_turns) if b0 < 45 else (50 if b0 < 70 else 40))


def missing_file_note(path: str) -> str:
    """The result of a file tool (lean_check, read_file) asked for a workspace file that does not exist (2026-10-30: it raised
"""
    return f"no such file: {path or '(no path given)'}; write it first"


def context_overflow(e: BaseException) -> bool:
    """A model call refused for the context window (HTTP 400 "maximum context length", vLLM / OpenAI wording). 2026-10-30 (gate review of


"""
    return getattr(e, "status_code", None) == 400 and "maximum context length" in f"{getattr(e, 'body', '') or ''} {e}".lower()


class Workspace:
    """Per-problem persistent workspace (keyed by problem, not by run):

"""

    def __init__(self, root: Path, row: dict, version: str, fresh: bool = False, blind: bool = False):
        self.root = root; self.row = row; self.version = version
        root.mkdir(parents=True, exist_ok=True)
        if blind:                                                                                                           
            (root / "original.lean").unlink(missing_ok=True)
        else:
            (root / "original.lean").write_text(row["src"].rstrip() + "\n")
        ctx = row["header"] if row["source"] == "putnambench" else file_prefix(row, version)
        (root / "context.lean").write_text(ctx)
        self.state_path = root / "state.json"
        if fresh or not self.state_path.exists():
            if fresh and self.state_path.exists():
                self.state_path.unlink()                                                                                                                                    
            self.state = {"problem": row["name"], "best": {"score": 33.33, "proof": None, "tokens": row["proof_length"], "heartbeats": None}, "attempts": [], "runs": []}
            (root / "candidate.lean").write_text(_BF.blind_candidate(row["statement"]) if blind else row["src"].rstrip() + "\n")
            if not (root / "notes.md").exists() or fresh:
                (root / "notes.md").write_text("# Notes (yours to keep; persisted across runs)\n")
        else:
            self.state = json.loads(self.state_path.read_text())
            best = self.state["best"].get("proof")
            (root / "candidate.lean").write_text((best or row["src"]).rstrip() + "\n")
        self.save()

    def save(self) -> None:
                                                                                                       
        try:
            disk = json.loads(self.state_path.read_text())
            _db = disk.get("best") or {}
            _own = getattr(self, "own_shas", None)                                                                                              
            if _db.get("score", 0) > (self.state.get("best") or {}).get("score", 0) and not (                                          
                    _own is not None and hashlib.sha256((_db.get("proof") or "").rstrip().encode()).hexdigest()[:12] in _own):
                self.state["best"] = disk["best"]
            seen = {(a.get("sha"), a.get("run_id")) for a in self.state.get("attempts", [])}
            for a in disk.get("attempts", []):
                if (a.get("sha"), a.get("run_id")) not in seen:
                    self.state.setdefault("attempts", []).append(a)
            self.state["attempts"] = sorted(self.state["attempts"], key=lambda a: a.get("t", ""))[-200:]
            known = {r.get("run_id") for r in self.state.get("runs", [])}
            self.state.setdefault("runs", []).extend(r for r in disk.get("runs", []) if r.get("run_id") not in known)
        except Exception:                
            pass
        self.state_path.write_text(json.dumps(self.state, ensure_ascii=False, indent=1))
        if self.state["best"].get("proof"):
            (self.root / "best.lean").write_text(self.state["best"]["proof"].rstrip() + "\n")

    def record_attempt(self, rec: dict) -> None:
        rec["t"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        self.state["attempts"].append(rec)
        self.state["attempts"] = self.state["attempts"][-200:]
        self.save()

    def digest(self, n: int = 8, open_package: bool = False) -> str:
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
        dead = [] if open_package else ((self.state.get("ledger") or {}).get("dead_names") or [])
        if dead:                                                                                                          
            lines.append("NAMES THAT DO NOT EXIST in this environment (unknown in earlier runs' compiles; do not use them): "
                         + ", ".join(f"`{n}`" for n in dead[:15]))
        notes = (self.root / "notes.md").read_text().strip()
        if len(notes.splitlines()) > 1:
            lines.append("Your notes.md from earlier runs:\n" + notes[:3000])
            claims = [] if open_package else unverified_claims(notes)
            if claims:
                lines.append("UNVERIFIED CLAIMS in these notes (cycle 36: the panel review found claims of this kind wrong on six problems: "
                             "'unavoidable', 'is the floor', 'never fires', 'needed', 'tight'; each "
                             "blocked the move that later won). Treat them as hypotheses, not facts: if one blocks your most promising idea, test it with "
                             "one cheap check first, and write the result back as `[tested: <what you ran> -> <result>]`:\n"
                             + "\n".join("  ? " + c for c in claims))
        return "\n".join(lines)

    def path(self, p: str) -> Path:
        return self.root / Path(p).name


def run_problem(name: str, args, rows, hbs, out_dir: Path) -> dict:
    row = rows[name]; versions = newest_first(row["version_info"]); primary = versions[0]
    OPK = bool(getattr(args, "open_package", False))                                                                                      
    BLIND = OPK and bool(getattr(args, "blind_start", False)) and bool(args.fresh)                                                                      
    ws = Workspace(ROOT / args.work_root / re.sub(r"[^A-Za-z0-9_.-]", "_", name), row, primary, fresh=args.fresh, blind=BLIND)
    golf = getattr(args, "mode", "default") == "golf"                                                                               
    ws.own_shas = set() if golf else None                                                                                       
    ws.state["runs"].append({"run_id": args.run_id, "model": args.model, "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}); ws.save()
    if args.endpoint == "openrouter":
                                                                                                                               
                                                                                                                           
                                                          
        cl = anthropic.Anthropic(api_key=Path("~/.config/vexorium/openrouter_api_key").expanduser().read_text().strip(),
                                 base_url="https://openrouter.ai/api", timeout=1800, max_retries=0)                            
        api_model = args.model if "/" in args.model else "z-ai/" + args.model
        extra_body = {"reasoning_effort": args.reasoning_effort, "reasoning": {"effort": args.reasoning_effort},
                      "provider": {"quantizations": [args.quant], "allow_fallbacks": False}}
        prov_model = f"{args.model}-{args.quant}@openrouter"
    elif args.endpoint == "openai":
                                                                                                                            
                                                                                                                        
        from llm import openai_compat as _oai
        cl = None
        _kp = Path(args.api_key_file).expanduser() if args.api_key_file else None
        _oai_key = _kp.read_text().strip() if _kp and _kp.exists() else "EMPTY"
        api_model = args.api_model or args.model
                                                                                                                          
                                                                                                                           
                                                         
                                                                                                                            
                                                                                                                                 
                                                                                                                    
        extra_body = {} if args.reasoning_effort == "default" else {"reasoning_effort": args.reasoning_effort}
        if args.extra_body_json:
            extra_body.update(json.loads(args.extra_body_json))
        prov_model = f"{args.model}-{args.serving_tag}@openai" if args.serving_tag else f"{args.model}@openai"
        if args.model_preset:
            _pr = MODEL_PRESETS[args.model_preset]
            extra_body = {"usage": {"include": True}}
            if args.model_preset != "deepseek-v4.1-flash" and args.reasoning_effort != "default" and not _pr.get("no_effort"):
                extra_body["reasoning"] = {"effort": args.reasoning_effort}
            extra_body.update(_pr.get("extra_body") or {})                                                                             
            prov_model = f"{args.model_preset}@{'clinepass' if 'cline' in _pr['base_url'] else 'azure' if '.azure.com' in _pr['base_url'] else 'openrouter'}"
    else:
                                                                                                                                        
        cl = anthropic.Anthropic(api_key=_key() if not os.environ.get("LRA_SELFTEST_ANTHROPIC_URL") else "selftest",
                                 base_url=os.environ.get("LRA_SELFTEST_ANTHROPIC_URL") or BASE_URL, timeout=1800, max_retries=0)
        api_model = args.model
        extra_body = {"reasoning_effort": args.reasoning_effort}
        prov_model = args.model + "@z.ai"
                                                                                                                          
                                                                                                                              
                                                                                                                           
                                                    
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
        except Exception as _e:                
            print(f"{name[:18]:18s} bank-sync skipped: {_e}", flush=True)
    ver_f = (out_dir / "verified.jsonl").open("a"); log_f = (out_dir / "turns.jsonl").open("a")
                                                                                                                     
                                                                                                                   
                                                                                                                
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
                                                                                                                   
    fresh_start = False; heartbeat_first = False
    if args.adaptive_turns and not args.from_reference:                                                                                               
        b0 = float(ws.state["best"].get("score") or 33.33)
                                                                                                                     
                                                                                                                 
                                                                             
        runs_prev = [r.get("run_id") for r in ws.state.get("runs", [])[:-1] if not _is_scout(r)]                                                     
        recent = set(runs_prev[-2:])
        older_best = max([float(a.get("score") or 0) for a in ws.state.get("attempts", []) if a.get("ok") and a.get("run_id") not in recent] or [33.33])
        stagnant = len(runs_prev) >= 2 and (b0 - older_best) < 0.5
        args_turns = adaptive_rung(b0, stagnant, getattr(args, "adaptive_low_turns", ADAPTIVE_LOW_TURNS))
                                                                                                                                     
                                                                                                                                    
                                                                                                                
        if len(runs_prev) >= 2:
            def _best_excl(excl):
                return max([float(a.get("score") or 0) for a in ws.state.get("attempts", []) if a.get("ok") and a.get("run_id") not in excl] or [33.33])
            _r1, _r2 = runs_prev[-1], runs_prev[-2]
            _b_before_r1 = _best_excl({_r1, args.run_id}); _b_before_r2 = _best_excl({_r1, _r2, args.run_id})
            if (b0 - _b_before_r1) < 0.5 and (_b_before_r1 - _b_before_r2) < 0.5:
                _fresh_prev = sum(1 for r in ws.state.get("runs", [])[:-1] if r.get("mode") == "fresh")                                         
                if b0 < 85 and _fresh_prev >= 2:
                                                                                                                                               
                                                                                                                                     
                                                                                                                                        
                    args_turns = 40; heartbeat_first = True
                    print(f"{name[:18]:18s} two flat runs and {_fresh_prev} fresh starts missed: structural on the best, heartbeat-first, 40 turns", flush=True)
                elif b0 < 85:
                    ws.state["runs"][-1]["mode"] = "fresh"; ws.save()
                                                                                                                                
                                                                                                                                    
                                                                                                                                    
                                                                                              
                    fresh_start = True; args_turns = 40
                    print(f"{name[:18]:18s} two flat runs ({_b_before_r2:.2f} -> {_b_before_r1:.2f} -> {b0:.2f}): FRESH START from the reference, 40 turns", flush=True)
                else:
                    args_turns = min(args_turns, 6)
                    print(f"{name[:18]:18s} two flat runs ({_b_before_r2:.2f} -> {_b_before_r1:.2f} -> {b0:.2f}): 6-turn polish", flush=True)
    else:
        args_turns = args.turns
    if not args.upstream_history:                                                                               
        for _n in ("SYSTEM", "SYSTEM_BASE"):
            globals()[_n] = re.sub(r",?\s*`git log -p` on the file[^,;)]*", "", globals()[_n])
    toolchains = ", ".join(versions)
    msgs = [{"role": "user", "content": f"Problem `{name}` from the {row['source']} corpus. Reference proof body: {row['proof_length']} tokens, {hbs.get(name)} heartbeats. Toolchains: {toolchains}. "
                                         f"Workspace files: original.lean, context.lean ({'imports/header' if row['source']=='putnambench' else 'surrounding file prefix, ' + str((ws.root/'context.lean').read_text().count(chr(10))) + ' lines'}), candidate.lean. "
                                         + (f"Project sources (read-only) for grep/git: {ROOT / 'envs' / (row['source'] + '-' + primary)} ; the problem's file is {row['file_path']} ; "
                                            + (f"full git history of the project (newer commits may contain a simplified version of this very proof — `git -C {ROOT / 'envs' / (row['source'] + '.git-main')} log -p --follow -- {row['file_path']} | head -400`) is in {ROOT / 'envs' / (row['source'] + '.git-main')}. "
                                               if args.upstream_history else "")                                                                 
                                            if row['source'] != 'putnambench' else f"Mathlib sources (read-only) for grep: {ROOT / 'envs' / ('mathlib-' + primary) / 'Mathlib'}. ")
                                         + f"You have {args_turns} tool turns. Keep durable insights (what worked, what failed and why, lemma names that exist) in notes.md so later runs can continue.\n\n" + ws.digest(open_package=OPK)
                                         + ("\n\nBoth original.lean and candidate.lean are shown below: no need to read_file them, start working." if not ws.state["attempts"] else "\n\nContinue from candidate.lean (your best so far, shown below; no need to read_file it); notes.md is summarised above.")}]
                                                                                                                                     
    for _fn, _lbl in (("original.lean", "original.lean (the REFERENCE proof)"), ("candidate.lean", "candidate.lean (your current best)")):
        try:
            _txt = (ws.root / _fn).read_text().rstrip()
            if args.lean_io and _fn == "candidate.lean" and _txt == (ws.root / "original.lean").read_text().rstrip():
                msgs[0]["content"] += "\n\ncandidate.lean: identical to original.lean (the reference above)."                              
                continue
            if _txt:
                msgs[0]["content"] += f"\n\n{_lbl}:\n```lean\n{_txt[:12000]}\n```" + ("\n(truncated: read_file for the rest)" if len(_txt) > 12000 else "")
        except OSError:
            pass
    blind = {"at": None, "revealed": None, "reason": None, "now": None, "banked_turn": None, "violations": []}                              
    if BLIND:
        _bfacts = _BF.facts(row, hbs.get(name), versions)
        blind["at"] = _BF.reveal_turn(args_turns)
        _rows_paths = [p_ for p_ in {str(Path(args.rows).resolve()) if args.rows else "", os.environ.get("LRA_ROWS_FILE", ""),
                                     Path(args.rows).name if args.rows else "", "benchmark_warmup.jsonl"} if p_]
        blind["rows_paths"] = sorted(_rows_paths)
        _src_hint = (f"Mathlib sources (read-only) for grep: {ROOT / 'envs' / ('mathlib-' + primary) / 'Mathlib'}. " if row["source"] == "putnambench" else
                     f"Project sources (read-only) for grep: {ROOT / 'envs' / (row['source'] + '-' + primary)} ; this problem's own file there is "
                     f"{row['file_path']}: do NOT read it (nor the rows file): it holds the reference proof, and the harness logs such reads. ")
        msgs[0]["content"] = (
            f"Problem `{name}` from the {row['source']} corpus. Toolchains: {toolchains}. Workspace files: context.lean "
            f"({'imports/header' if row['source'] == 'putnambench' else 'surrounding file prefix, ' + str((ws.root / 'context.lean').read_text().count(chr(10))) + ' lines'}), "
            f"candidate.lean. {_src_hint}You have {args_turns} tool turns. Keep durable insights (what worked, what failed and why, lemma names "
            "that exist) in notes.md so later runs can continue.\n\n"
            "BLIND START (this is the first session on this problem): the reference proof is withheld. candidate.lean holds the exact statement "
            "with a `sorry` body: replace the `sorry` with your own proof, written from the statement, the definitions and the library. The "
            "statement and the toolchains are the test: a candidate counts when lean_check compiles it (a `sorry` is rejected there), and it "
            "scores above the reference (33.33) only with fewer tokens and/or fewer heartbeats. The reference stays the banked best, so trying "
            f"costs nothing. If no candidate of yours is banked by turn {blind['at']} of {args_turns}, the harness shows the reference proof and "
            "you continue from it.\n\n" + _BF.render(_bfacts)
            + f"\n\ncandidate.lean (the statement; the body is yours to write):\n```lean\n{(ws.root / 'candidate.lean').read_text().rstrip()}\n```")
        ws.state["runs"][-1]["blind_start"] = {"reveal_at": blind["at"], "names": len(_bfacts["names"]), "tactics": len(_bfacts["tactics"])}; ws.save()
        print(f"{name[:18]:18s} blind start: facts sheet ({len(_bfacts['names'])} names, {len(_bfacts['tactics'])} tactics), reference shown at "
              f"turn {blind['at']} of {args_turns} unless a candidate is banked first", flush=True)

    def _blind_banked() -> bool:
        """A candidate of this blind session is the banked best (it beat the reference's 33.33)."""
        return bool(best.get("proof")) and float(best.get("score") or 33.33) > 33.33 + 1e-9

    def _blind_reveal(turn_: int, why: str) -> None:
        """REVEAL: the reference proof in one message; original.lean written, candidate.lean set to it (the session goes on as a normal
"""
        blind["revealed"], blind["reason"] = turn_, why
        src_ = row["src"].rstrip()
        (ws.root / "original.lean").write_text(src_ + "\n")
        _cur = (ws.root / "candidate.lean").read_text() if (ws.root / "candidate.lean").exists() else ""
        if _cur.strip():
            (ws.root / "draft.lean").write_text(_cur)
        (ws.root / "candidate.lean").write_text(src_ + "\n")
        _why = (f"no candidate of yours has been banked after {turn_} of {args_turns} turns" if why == "turn" else
                "you asked to finish before any candidate of yours was banked")
        msgs.append({"role": "user", "content": (
            f"REFERENCE PROOF, now shown: {_why}. original.lean now holds the reference and candidate.lean is set to it, as in a normal session; "
            "your own last draft is kept in draft.lean. From here, improve INCREMENTALLY from whichever is more promising: change one thing, "
            "lean_check, keep what compiles. The reference stays the banked best until a candidate beats it."
            f"\n\noriginal.lean (the REFERENCE proof):\n```lean\n{src_[:12000]}\n```" + ("\n(truncated: read_file for the rest)" if len(src_) > 12000 else ""))})
        ws.state["runs"][-1].setdefault("blind_start", {})["revealed_turn"] = turn_; ws.save()
        flush_traj({"type": "blind_reveal", "turn": turn_, "reason": why, "turns": args_turns, "checks": checks})
        print(f"{name[:18]:18s} blind start: reference shown at turn {turn_} ({why}; {checks} check(s) so far)", flush=True)
    if args.upstream_history:                                                                                                        
        try:
            from harness.leantools import upstream_digest as _ud
            _up = _ud(row, primary)
            if _up:
                msgs[0]["content"] += "\n\n" + _up
        except Exception:                
            pass
    _nn = None                                                                                                                                   
    if getattr(args, "name_neighbors", False):
        try:
            from harness import name_neighbors as _NN
            _nn = _NN.Session(ROOT / args.work_root, row, primary, ws_root=ws.root, max_queries=args.name_neighbors_queries,
                              log=lambda m_: print(f"{name[:18]:18s} {m_}", flush=True))
            _mb = _NN.missing_block(ws.root, _nn.key())
            if _mb:
                msgs[0]["content"] += "\n\n" + _mb
        except Exception as _e:                
            _nn = None; print(f"{name[:18]:18s} name neighbors off: {type(_e).__name__}: {_e}", flush=True)
    best = dict(ws.state["best"])
    if synced_note:
        msgs[0]["content"] += synced_note
                                                                                                                                            
                                                                                                                                              
                                                                                                                 
    _hbf = False
    if getattr(args, "heartbeat_first", False):
        from harness import cards as _cards
        _hbf = _cards.gate(name, row, ws.state, hbs.get(name), log=lambda s: print(f"{name[:18]:18s} {s}", flush=True))
        ws.state["runs"][-1]["heartbeat_first"] = _hbf; ws.save()
    _hbw = (lambda s: _cards.heartbeat_aware(s)) if _hbf else (lambda s: s)
                                                                                                                                
                                                                                                                                  
    if not OPK:                                                                               
        try:                                                                                                         
            from harness import cards as _cards
            _ctx = (ws.root / "context.lean").read_text() if (ws.root / "context.lean").exists() else ""
            _cur = (ws.root / "candidate.lean").read_text() if (ws.root / "candidate.lean").exists() else (ws.state["best"].get("proof") or row["src"])
            msgs[0]["content"] += "\n\n" + _cards.cards_for(row["statement"], _cur, _ctx, heartbeat_first=_hbf)
            print(f"{name[:18]:18s} technique cards: {', '.join(_cards.select(row['statement'], _cur, _ctx)) or 'token rules only'}", flush=True)
        except Exception as _e:                
            print(f"{name[:18]:18s} technique cards failed: {_e}", flush=True)
    if getattr(args, "pattern_cards", False):                                                                                                           
        try:
            from harness.pattern_cards import pattern_cards_for as _pcf
            _pc = _pcf(row["statement"], (ws.root / "candidate.lean").read_text() if (ws.root / "candidate.lean").exists() else (ws.state["best"].get("proof") or row["src"]))
            if _pc:
                msgs[0]["content"] += "\n\n" + _pc
            ws.state["runs"][-1]["pattern_cards"] = _pc.count("PATTERN:"); ws.save()
        except Exception as _e:                
            print(f"{name[:18]:18s} pattern cards failed: {_e}", flush=True)
    _cl0 = len(msgs[0]["content"])                                                                                                                    
    if args.closed_lessons:                                                                                                                           
        msgs[0]["content"] += ("\n\nA HABIT OF THE STRONGEST PROVERS (general, not about this problem):\n"
            "Write each piece once: when cases or steps repeat the same tactic run, close them together (`all_goals`, `<;>`, `case A | B => tac`) "
            "instead of repeating it. `<;> first | A | B` is shorter as `any_goals A` then `all_goals B` (fewer tokens).")
    if _hbf:                                                                                                                                       
        msgs[0]["content"] = msgs[0]["content"][:_cl0] + _hbw(msgs[0]["content"][_cl0:])
    if not OPK:                                                                                                                               
        try:                                                                                                                          
            from harness import lemma_search as _ls
            _cur2 = (ws.root / "candidate.lean").read_text() if (ws.root / "candidate.lean").exists() else (ws.state["best"].get("proof") or row["src"])
            _lr = _ls.search(name, _cur2.rstrip(), top=10, probes=True, budget=120.0) if not golf else {}
            _sg = _lr.get("suggestions") or []
            if _sg:
                msgs[0]["content"] += ("\n\nLIBRARY LEADS for the current proof (lemma search: exact? at each goal, names ranked by match with the goal and statement, "
                                       "same-file lemmas the reference does not use, @[simp]/@[grind]/@[to_fun] lemmas, induction principles). Leads, not answers: "
                                       "check a lead's signature against the goal (lean_goals) before building on it; lean_search re-runs it after a restructure.\n"
                                       + "\n".join(f"  - {s_.get('name')} [{s_.get('source')}{', line ' + str(s_['line']) if s_.get('line') else ''}]: "
                                                    f"{(s_.get('signature') or '')[:180]}  -- {(s_.get('why') or '')[:140]}" for s_ in _sg[:10]))
            print(f"{name[:18]:18s} library leads: {len(_sg)} ({_lr.get('runtime_s')} s, {_lr.get('compiles')} compiles)", flush=True)
        except Exception as _e:                
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
                                                                                                                                    
        if float(best.get("score") or 33.33) > 33.34 and best.get("tokens"):
            msgs[0]["content"] += (f" BLIND TARGET: the stored best has {best.get('tokens')} tokens and {best.get('heartbeats') or '?'} heartbeats "
                                   f"(score {best.get('score')}); a structurally different proof that beats it is the goal.")
    if args.term_card:                                                                                                            
        msgs[0]["content"] += ("\n\nTERM-MODE FINISH AND PROBE-BEFORE-COMMIT (general practices, measured on another model):\n"
            "1. Search the library for a theorem matching the WHOLE statement first (lean_search; `exact?` in lean_run): a single library "
            "lemma often closes the problem outright.\n"
            "2. Once a tactic proof compiles, try ONE variant that collapses it into a single term: chain with `.elim`, `.trans`, `.trans_eq`, "
            "`.trans_lt`, `.imp`, anonymous `fun … =>`; drop `unfold`/`dsimp`/`classical` and `simp … at` on hypotheses (let definitional "
            "unfolding happen inside the term). On algebraic/inequality chains a term proof often cuts BOTH tokens and heartbeats.\n"
            "3. Probe before you commit: test sub-terms and lemma fits in lean_run (`example : <goal> := <term>`; sorry allowed, no check "
            "spent) and only then write the full candidate.")
        print(f"{name[:18]:18s} term-mode card", flush=True)
    if args.brief_dir:                                                                                                        
        _bf = ROOT / args.brief_dir / (re.sub(r"[^A-Za-z0-9_.-]", "_", name) + ".md")
        if _bf.exists():
            msgs[0]["content"] += "\n\n" + _bf.read_text()
            print(f"{name[:18]:18s} knowledge brief: {_bf.name}", flush=True)
    if getattr(args, "open_card", None):                                                                                        
        _oc = Path(args.open_card)
        if _oc.exists():
            msgs[0]["content"] += "\n\n" + _oc.read_text()
            print(f"{name[:18]:18s} open card: {_oc.name}", flush=True)
        else:
            print(f"{name[:18]:18s} WARNING open card {_oc} not found: the opening has no card", flush=True)
    if args.brief != "none":
        msgs[0]["content"] += "\n\n" + _hbw(SCOUT_BRIEFS[args.brief])
        print(f"{name[:18]:18s} scout brief: {args.brief}", flush=True)
    if args_turns <= 10 and not OPK:                                                                                                               
                                                       
        msgs[0]["content"] += (f"\n\nSHORT POLISH RUN: only {args_turns} turns. Spend them on checks. Your FIRST action: one lean_check_variants call with 3-6 "
                               "independent single-edit variants of candidate.lean (re-apply WINNING EDITS the best lost, try LIBRARY LEADS, delete a `have`/`set`, "
                               "swap a closer, token micro-rules). Do not re-read notes or reorganise them; write notes.md only in your final turn.")
    hardtail_target = None
    hardtail_batches = 0                                                                        
    forced_turns = 0                                                                            
    if args.strategy == "hardtail":
                                                                                                                                         
                                                                                                                                       
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
        try:                                                                                        
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
        except Exception as _e:                
            print(f"{name[:18]:18s} hard-tail goal map failed: {_e}", flush=True)
    if fresh_start:
        (ws.root / "candidate.lean").write_text(row["src"].rstrip() + "\n")
        msgs[0]["content"] += ((f"\n\nFRESH START: the last two runs could not improve the stored best (score {best['score']}); it is anchored to one proof "
                                if OPK else                                                                                                     
                                f"\n\nFRESH START: the last two runs could not improve the stored best (score {best['score']}; {best.get('tokens')} tokens, "
                                f"{best.get('heartbeats') or '?'} heartbeats: the target to beat); it is anchored to one proof ")
                               + "skeleton. candidate.lean now holds the ORIGINAL reference proof, not the best. Ignore the old approach: read the statement, "
                               "think about the shortest overall proof strategy (induction + `simp only [defs] at *` + `grind`/`omega`, a direct lemma via "
                               "`exact?`, a different case split), write it, lean_check, iterate. The stored best is kept unless you beat it, so bold "
                               "rewrites cost nothing. notes.md still has the lemma names and pitfalls from earlier runs. "
                               "Build the new proof IN STAGES: the reference compiles, so replace one block at a time and lean_check after each, keeping a "
                               "compiling candidate in hand at all times (a whole new proof written in one shot took 10-25 turns to compile in earlier runs "
                               "and left no time to shorten it). Aim for a first compiling check within your first 6 checks.")
                                                                                                                                         
    if len([r for r in ws.state.get("runs", []) if not _is_scout(r)]) >= 3 and float(ws.state["best"].get("score") or 33.33) < 50:
        msgs[0]["content"] += ("\n\nSTRATEGY CHANGE: earlier runs made local edits to this proof and gained little or nothing. Do not repeat that. Instead: "
                               "(1) read the whole proof and list its 3–4 most expensive or longest steps (big `simp`/`simp_all`/`omega`/`nlinarith`/`norm_num` calls, long `have` chains); "
                               "(2) for each, state the exact goal at that point with lean_run (copy the surrounding context, put `sorry` after it, read the goal from the error), then ask `exact?`, `apply?`, `simp?` or `rw?` on that goal to find a direct closer; "
                               "(3) replace one step at a time with the closer found, lean_check after each. If a `have` is only used once, inline it. "
                               + ("" if OPK else "Also check the project's git history for a later simplification of this very declaration (see the shell hint above). ")
                               + "Aim for a compiling candidate within your first 8 turns.")
                                                                                                                               
                                                                                                                          
                                                                                                                         
    _runs_prev = [r.get("run_id") for r in ws.state.get("runs", [])[:-1] if not _is_scout(r)]
    _b = float(ws.state["best"].get("score") or 33.33)
    _older = max([float(a.get("score") or 0) for a in ws.state.get("attempts", []) if a.get("ok") and a.get("run_id") not in set(_runs_prev[-2:])] or [33.33])
                                                                                                                       
                                                                                                                        
                                  
    _nonscout = [r for r in ws.state["runs"][:-1] if not _is_scout(r)]
    _last = _nonscout[-1] if _nonscout else {}
    _before_last = max([float(a.get("score") or 0) for a in ws.state.get("attempts", []) if a.get("ok") and a.get("run_id") not in (_last.get("run_id"), args.run_id)] or [33.33])
    _keep = _last.get("mode") == "structural" and (_b - _before_last) >= 1.0
                                                                                                                                    
                                                                                                                                
    if not OPK and not golf and args.strategy != "hardtail" and not fresh_start and not args.from_reference and len(_runs_prev) >= 2 and 50 <= _b < 85 and ((_b - _older) < 3.0 or _keep or heartbeat_first):                                                                                                                                                                                                                                 
        ws.state["runs"][-1]["mode"] = "structural"; ws.save()
                                                                                                                         
                                                                                                                         
                                                                                                                    
                                                                                                                         
                                                                                                                                 
                                                                                                                                  
        if args.reasoning_effort == "low":
            extra_body["reasoning_effort"] = "high"
        print(f"{name[:18]:18s} structural mode ({'kept: last run gained %.2f' % (_b - _before_last) if _keep else 'plateau'}; effort {(extra_body.get('chat_template_kwargs') or {}).get('reasoning_effort') or extra_body.get('reasoning_effort') or args.reasoning_effort})", flush=True)
        msgs[0]["content"] += _hbw("\n\nSTRUCTURAL PASS (aligned with R3, cycle 39): editing has stalled on this proof (little gain over the last two runs), so the next "
                               "gain needs a NEW ARCHITECTURE, not more edits of the current one. Rewrite top-down: outline the proof with `sorry` holes, check it with "
                               "lean_skeleton, fill one hole at a time, then lean_check. Aim the new outline at what the old one wastes: "
                               "(1) no scaffolding: no `let`/`set`/`have` used once or not at all (`set` does extra work); destructure directly; "
                               "(2) no long `calc`: rewrite the goal directly or use `_` for intermediate right-hand sides, pass side goals inline as arguments; "
                               "(3) one shared AUTOMATION closer for alike cases (`induction x <;> grind [hints]`, `all_goals simp only [...]`, `case'` + `first | …`) "
                               "instead of a hand-written term per case; "
                               "(4) LIBRARY LEADS first: a lemma that matches a block's conclusion replaces the block; "
                               "(5) no `show`/`change`/`unfold`/`dsimp` lines that only restate the goal. Keep every compiling improvement; several attempts will fail.")
    if heartbeat_first and not OPK:                                                                     
        msgs[0]["content"] += _hbw("\n\nHEARTBEAT FIRST: on this proof the length axis has stalled; the heartbeat axis is where points remain. Prefer, in order: "
                               "a more direct proof shape (term-mode `exact`/anonymous constructors over tactic blocks), lower search burden (`simp only [...]`/"
                               "`rw` over `simp`/`omega`/`grind`/`aesop` where both compile, `exact lemma args` over `apply`+goals), then clarity, then brevity. "
                               "Keep the candidate compiling after every edit; lean_check reports heartbeats — a cut that raises heartbeats is not a win.")
                                                                                                                                            
                                                                                                                                                 
                                                      
    if args.lever_review and args.strategy != "hardtail" and not fresh_start and not args.from_reference and len(_runs_prev) >= 2 and (_b - _older) < 3.0:
        msgs[0]["content"] += _hbw(LEVER_REVIEW)                                                                                  
        print(f"{name[:18]:18s} lever review first (gain over the last two runs {_b - _older:.2f})", flush=True)
    THINK_NUDGE = ("THINK LONGER before each tool call: in your thinking, enumerate at least three distinct proof strategies for the current goal, "
                   "estimate the token/heartbeat payoff and the risk of each, and only then choose one. A short think here wastes a check.")
    _is_structural = (ws.state["runs"][-1].get("mode") == "structural")
    think_prompt_on = args.think_prompt == "all" or (args.think_prompt == "structural" and (_is_structural or fresh_start))
    if think_prompt_on:
        msgs[0]["content"] += "\n\n" + THINK_NUDGE
        print(f"{name[:18]:18s} think-prompt on ({args.think_prompt})", flush=True)
    if getattr(args, "failed_moves", False):                                                                                                    
                                                                                                                                                
                                                                                                
        try:
            from harness import cc_levers as _LVfm
            _fm_base = (ws.root / "candidate.lean").read_text() if (ws.root / "candidate.lean").exists() else (ws.state["best"].get("proof") or row["src"])
            _LVfm.void_stale(ws.state, ws.state["best"].get("proof"))                                                                      
            _fm, ws.state["runs"][-1]["failed_moves"] = _LVfm.failed_moves_render(ws.state, base=_fm_base); ws.save()                       
            if _fm:
                msgs[0]["content"] += "\n\n" + _fm
                print(f"{name[:18]:18s} refuted moves: {ws.state['runs'][-1]['failed_moves']}", flush=True)
        except Exception as _e:                
            print(f"{name[:18]:18s} refuted moves failed: {_e}", flush=True)
    _pre = None
    try:                                                                                                    
        from harness.leantools import lean_check as _lc
        _state_probe = {"best": {"score": 33.33, "proof": None}, "attempts": []}
        _pre = {} if BLIND else _lc(name, (ws.root / "candidate.lean").read_text(), _state_probe, {"run_id": args.run_id, "kind": "probe"}, None)                                             
        if _pre.get("linter_hints"):
            msgs[0]["content"] += "\n\nLinter hints on the current candidate (free deletions, do these first):\n" + "\n".join("  - " + h for h in _pre["linter_hints"])
    except Exception as _e:                
        pass
    checks = 0; tool_calls = 0; total_out = 0
    tool_errors: dict = {}                                                                                                        
    sig_cache = {}                                                   

    def comp(decl, version, count=True):
        return compile_putnam(row["header"], decl, version, count=count, timeout=900) if row["source"] == "putnambench" else compile_project(row, decl, version, count=count, timeout=900)

    def lean_mine(path: str) -> str:
        from harness import mine as _mine
        src = ws.path(path or "candidate.lean")
        if not src.exists():
            return _tool_json({"ok": False, "errors": [f"{src.name} not found"]})
        decl = src.read_text()
        res = _mine.mine(name, decl, jobs=4, log=lambda *_: None)
        if res.get("error"):
            return _tool_json({"ok": False, "errors": [res["error"]]})
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
        return _tool_json(out, ensure_ascii=False)

    def lean_check_variants(variants) -> str:
        nonlocal hardtail_batches
        variants = [v for v in (variants or []) if isinstance(v, dict) and (v.get("content") or "").strip()][:6]
        over = {}
        if hardtail_target:
                                                                                                                                             
                                                                                                                
            for k, v in enumerate(variants):
                _b = split_declaration(v["content"].rstrip(), row["statement"])
                _n = count_tokens(_b) if _b is not None else None
                if _n is not None and _n > hardtail_target * 1.15:
                    over[k] = _n
        if len(variants) - len(over) >= 3:
            hardtail_batches += 1
        if not variants:
            return _tool_json({"ok": False, "errors": ["give 1-6 variants, each {label, content} with the FULL candidate text (statement + proof)"]})
        before = float(ws.state["best"].get("score") or 33.33)
        rows = []; best_k = None; best_s = -1.0; sigs_all = {}; dym_all: dict = {}; cf_all: dict = {}; nn_all: dict = {}
        for k, v in enumerate(variants):                                                                                             
            p = ws.root / f"variant_{k + 1}.lean"; p.write_text(v["content"].rstrip() + "\n")                                                      
            if k in over:
                rows.append({"label": v.get("label") or f"v{k + 1}", "ok": False, "score": None, "tokens": over[k], "heartbeats": None,
                             "error": f"not compiled: {over[k]} tokens is over the hard-tail target ({hardtail_target}); this is an edit of the old proof, not a new architecture",
                             "note": None})
                continue
            _b0 = float(ws.state["best"].get("score") or 33.33)                                                                 
            try:
                r = json.loads(lean_check(p.name))
            except Exception as e:                
                r = {"ok": False, "errors": [str(e)[:200]]}
            s = r.get("score")
            _vs = {}
            if args.variant_scores:                                                                                                      
                                                                                                                                       
                                                                                                                                          
                if r.get("unchanged") and isinstance(r.get("prior"), dict):
                    r = {**r, **{k_: r["prior"].get(k_) for k_ in ("tokens", "heartbeats") if r.get(k_) is None}}
                    s = r["prior"].get("score")
                elif s is None and r.get("ok") and r.get("predicted_score_if_compatible") is not None:
                    s = r["predicted_score_if_compatible"]; _vs["score_kind"] = "provisional (compatibility not checked: not above the best)"
                if isinstance(s, (int, float)):
                    _vs["vs_best"] = round(float(s) - _b0, 2)
            rows.append({"label": v.get("label") or f"v{k + 1}", "ok": bool(r.get("ok")), "score": s, "tokens": r.get("tokens"), "heartbeats": r.get("heartbeats"),
                         "error": ((r.get("errors") or [None])[0] or None), "note": r.get("note") or r.get("auto_fixed"), **_vs})
            for c_, sig_ in (r.get("signatures") or {}).items():                                                                                  
                sigs_all.setdefault(c_, sig_)
            for n_, c_ in (r.get("did_you_mean") or {}).items():
                dym_all.setdefault(n_, c_)
            for n_, c_ in (r.get("name_neighbors") or {}).items():
                nn_all.setdefault(n_, c_)
            if r.get("compat_failures") and len(cf_all) < 2:                                                                  
                cf_all[rows[-1]["label"]] = {"compat": r.get("compat"), "failures": r["compat_failures"], "note": r.get("compat_note")}
            if r.get("ok") and isinstance(s, (int, float)) and s > best_s:
                best_s, best_k = float(s), k
        out = {"variants": rows, "best_variant": rows[best_k]["label"] if best_k is not None else None}
        _rep = next((r_["note"] for r_ in rows if r_.get("note") and "same error has now failed" in r_["note"]), None)
        if _rep:                                                                                                                 
            out["repeated_error"] = _rep
        if dym_all:
            out["did_you_mean"] = dict(list(dym_all.items())[:4])
        if nn_all:                                                 
            out["name_neighbors"] = _nn.cap(nn_all); out["name_neighbors_note"] = _nn.note
        if cf_all:
            out["compat_failures"] = cf_all
        if sigs_all:
            out["signatures"] = dict(list(sigs_all.items())[:3])
            out["signature_note"] = "application/type mismatch in some variants: `signatures` holds the exact signature of each applied constant — match its argument order before retrying"
        if best_k is not None and best_s > before:
            (ws.root / "candidate.lean").write_text((ws.root / f"variant_{best_k + 1}.lean").read_text().rstrip() + "\n")                                          
            out["note"] = f"best variant {rows[best_k]['label']} ({best_s}) beats the previous best ({before}); copied to candidate.lean"
        elif best_k is not None:
            out["note"] = f"best compiling variant {rows[best_k]['label']} scores {best_s}, not above the stored best {before}; candidate.lean unchanged"
        return _tool_json(out, ensure_ascii=False)

    def lean_search(path: str, probes: bool = False) -> str:
        from harness import lemma_search as _ls
        src = ws.path(path or "candidate.lean")
        if not src.exists():
            return _tool_json({"ok": False, "errors": [f"{src.name} not found"]})
        r_ = _ls.search(name, src.read_text().rstrip(), top=10, probes=bool(probes), budget=150.0)
        return _tool_json({"suggestions": [{k: s_.get(k) for k in ("name", "signature", "source", "line", "why")} for s_ in (r_.get("suggestions") or [])[:10]],
                           "runtime_s": r_.get("runtime_s")}, ensure_ascii=False)[:9000]

    def lean_skeleton(path: str = "", content: str = "") -> str:
        from harness import goals as _goals
        draft = content or (ws.path(path).read_text() if path and ws.path(path).exists() else "")
        if not draft.strip():
            return _tool_json({"ok": False, "errors": ["give `content` (the draft with sorry holes) or a `path` to it"]})
        if split_declaration(draft.rstrip(), row["statement"]) is None:
            return _tool_json({"ok": False, "errors": ["statement differs from the reference statement (must be byte-for-byte identical, followed by :=)"]})
        res = _goals.skeleton_check(name, draft.rstrip(), **({"combinators": True} if getattr(args, "skeleton_combinator_holes", False) else {}))
        if OPK and str(res.get("note", "")).startswith("fill one hole"):                                                                     
            res["note"] = "lean_check the full candidate only when no sorry remains (sorry is forbidden in candidates)."
        return _tool_json(res, ensure_ascii=False)

    def lean_profile(path: str) -> str:
        from harness import profile as _prof
        src = ws.path(path or "candidate.lean")
        if not src.exists():
            return _tool_json({"ok": False, "errors": [f"{src.name} not found"]})
        decl = src.read_text().rstrip()
        sha = hashlib.sha256(decl.encode()).hexdigest()[:12]
        cache = ws.state.setdefault("profile_cache", {})
        if sha not in cache:
                                                                                                                                           
                                                                                               
            cache[sha] = _prof.profile(name, decl, max_cuts=12, reference=hbs.get(name) if OPK else None)
            if len(cache) > 6:
                cache.pop(next(iter(cache)))
        res = cache[sha]
        if res.get("floor"):
            ws.state["hb_floor"] = res["floor"]                                                                                
        ws.save()
        return _tool_json(res, ensure_ascii=False)

    def lean_goals(path: str, depth: int = 1, from_line: int = 0) -> str:
        from harness import goals as _goals
        src = ws.path(path or "candidate.lean")
        if not src.exists():
            return _tool_json({"ok": False, "errors": [f"{src.name} not found"]})
        return _tool_json(_goals.goal_map(name, src.read_text(), depth=2 if int(depth or 1) >= 2 else 1, from_line=int(from_line or 0)), ensure_ascii=False)

    def lean_run(code: str, neighbors: bool = True) -> str:
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
                continue                                    
            out.append(f"[{m.get('severity')}] line {ln}: {m.get('data','')}")
        _txt = ("\n".join(out) if out else f"(no messages; exit {pr.returncode})")[:12000]
        if neighbors and _nn is not None and out:                                                                      
            _blk = _nn.text("\n".join(out))
            if _blk:
                _txt += "\n\n" + _blk
        return _txt

    _DENY = re.compile(r"(^|[;&|]\s*)(rm|mv|chmod|chown|sudo|pip|pip3|curl|wget|ssh|scp|nc|ncat|lake\s+build|lake\s+update|lake\s+exe\s+cache|git\s+(checkout|reset|clean|commit|push|pull|stash|rebase|merge|worktree))\b")

    _LEMMA_GREP = re.compile(r"\b(grep|rg)\b.*(\b(theorem|lemma)\b|\.lake/packages|Mathlib/)")

    def shell(command: str) -> str:
        import os, subprocess
        if not args.upstream_history and re.search(r"\bgit\s+(log|show|diff|blame)\b", command):
            return "error: repository history is not available in this run (--no-upstream-history)"
        if _DENY.search(command) or re.search(r"https?://", command):
            return "error: command not permitted (no network, no writes outside the workspace, no rm/mv/git checkout/lake build)"
                                                                                                                                             
                                                                                                                                              
                                                                                                               
        _scan = re.sub(r"<<-?\s*(['\"]?)(\w+)\1[^\n]*\n.*?\n\s*\2\s*(\n|$)", "<<HEREDOC\n", command, flags=re.S)
        for m in re.finditer(r"(?<![=\-≥>])>(?![=>])\s*([^\s;&|]+)", _scan):                                            
            if m.group(1).strip("'\"") in ("/dev/null", "/dev/stdout", "/dev/stderr"):
                continue                                                                                   
            try:
                target = Path(m.group(1)).expanduser()
            except RuntimeError:
                target = Path(m.group(1))
            if (target.is_absolute() and not str(target.resolve()).startswith(str(ws.root.resolve()))) or (not target.is_absolute() and ".." in target.parts):
                return (f"error: redirect target {m.group(1)} is outside the workspace (only workspace files and /dev/null are allowed; "
                        "grep/sed/git output needs no redirect, it is returned to you)")
        from scorer.compile import ELAN_BIN as _ELAN_BIN                                                                         
        env = dict(os.environ, PATH=f"{_ELAN_BIN}:{os.environ.get('PATH','')}")
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

"""
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

                                                                                                                                            
    golf_inc = None; golf_evals = 0; golf_since_gain = 0; golf_gains = 0; golf_seen: dict = {}; golf_profiles: dict = {}
    _pool_f = ws.root / "pool.jsonl"
    _pool_shas = set()

    def _pool_entries(this_run: bool = True) -> list[dict]:
        """pool.jsonl entries (this run's only by default: the golf tools show the run's own candidates), unreadable lines skipped."""
        try:
            text = _pool_f.read_text() if _pool_f.exists() else ""
        except OSError:
            return []
        out = []
        for _l in text.splitlines():
            try:
                e_ = json.loads(_l)
            except Exception:                
                continue
            if not this_run or e_.get("run_id") == args.run_id:
                out.append(e_)
        return out
    _pool_shas.update(e_.get("sha") for e_ in _pool_entries(this_run=True))

    def _sha12(decl: str) -> str:
        return hashlib.sha256(decl.rstrip().encode()).hexdigest()[:12]

    def _pool_add(decl: str, sha: str, toks, hb, score_exact) -> None:
        """B62a: every compiling candidate of the run, for golf's pool tool and the end stage (--pool; golf turns it on)."""
        if not getattr(args, "pool", False) or sha in _pool_shas:
            return
        _pool_shas.add(sha)
        with _pool_f.open("a") as f_:
            f_.write(json.dumps({"sha": sha, "tokens": toks, "heartbeats": hb, "score_exact": round(float(score_exact), 6), "run_id": args.run_id,
                                 "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "proof": decl.rstrip()}, ensure_ascii=False) + "\n")

    def golf_budget_low() -> bool:
        return bool(args.model_preset) and float(ws.state.get("api_spend") or 0) >= 0.85 * args.budget_usd

    def golf_eval(decl: str) -> dict:
        """Compile and measure one candidate on the primary toolchain (no state change: safe in threads)."""
        body = split_declaration(decl, row["statement"])
        if body is None:
            return {"ok": False, "error": "statement differs from the reference statement (must be byte-for-byte identical, followed by :=)"}
        bad = check_forbidden(decl)
        if bad:
            return {"ok": False, "error": f"forbidden construct: {bad}"}
        toks = count_tokens(body)
        try:
            r = comp(decl, primary)
        except Exception as e:                
            return {"ok": False, "tokens": toks, "error": f"compile error: {type(e).__name__}: {e}"[:300]}
        if not r.ok or r.heartbeats is None:
            return {"ok": False, "tokens": toks,
                    "error": (_rel(digest_error(r.errors[0], 300), decl) if r.errors else "compiled without a heartbeat reading")}
        return {"ok": True, "tokens": toks, "heartbeats": r.heartbeats, "L": len_pct(row["proof_length"], toks),
                "H": hb_pct_local(name, r.heartbeats, hbs.get(name))}

    def golf_consider(decl: str, ev: dict) -> tuple[bool, str, float, bool]:
        """scorer/accept.decide against this session's incumbent; a passing candidate is compiled on every pin and once more on the primary

"""
        nonlocal best, golf_inc, golf_since_gain, golf_gains
                                                                                                                                        
        z_scr = golf_inc["Z"] if golf_inc["Z"] >= 100.0 else 100.0
        sx = _exact(ev["L"], ev["H"], golf_inc["Z"])
        ok_, why = _decide(golf_inc, {"score": _exact(ev["L"], ev["H"], z_scr), "tokens": ev["tokens"], "heartbeats": ev["heartbeats"], "Z": z_scr})
        if not ok_:
            return False, why, sx, False
        compat = {primary: True}; _to = False
        for v in versions[1:]:
            _rv = comp(decl, v, count=False); compat[v] = _rv.ok; _to = _to or bool(getattr(_rv, "timed_out", False))
        Z = compat_pct(compat)
        r2 = comp(decl, primary)
        if not r2.ok or r2.heartbeats is None:
            return False, "the confirmation compile failed", sx, bool(getattr(r2, "timed_out", False)) or _to
        hb = max(int(ev["heartbeats"]), int(r2.heartbeats))
        H = hb_pct_local(name, hb, hbs.get(name)); sx = _exact(ev["L"], H, Z)
        cand = {"score": sx, "tokens": ev["tokens"], "heartbeats": hb, "Z": Z}
        ok_, why = _decide(golf_inc, cand)
        if not ok_:
            return False, "after the confirmation compile and the pins: " + why, sx, _to
        sc = problem_score(True, ev["L"], H, Z)
        try:
            import difflib as _dl
            _d = [l for l in _dl.unified_diff((golf_inc.get("proof") or "").splitlines(), decl.splitlines(), lineterm="", n=0)
                  if l[:1] in "+-" and not l.startswith(("+++", "---"))]
            _led = ws.state.setdefault("ledger", {}).setdefault("wins", [])
            _led.append({"run_id": args.run_id, "check": checks, "d_score": round(sx - golf_inc["score"], 4), "d_tokens": ev["tokens"] - golf_inc["tokens"],
                         "d_heartbeats": hb - golf_inc["heartbeats"], "diff": "\n".join(_d)[:700]})
            ws.state["ledger"]["wins"] = _led[-30:]
        except Exception:                
            pass
        best = {"score": sc, "score_exact": round(sx, 6), "proof": decl, "tokens": ev["tokens"], "heartbeats": hb, "L": round(ev["L"], 2),
                "H": round(H, 2), "Z": Z, "compat": compat}
        ws.state["best"] = best; ws.save()
        ver_f.write(json.dumps({"problem": name, "sha256": hashlib.sha256(decl.encode()).hexdigest()[:16], "proof": decl, "tokens": ev["tokens"],
                                "ref_tokens": row["proof_length"], "heartbeats": hb, "primary": primary, "primary_ok": True, "compat": compat,
                                "L": round(ev["L"], 2), "H": round(H, 2), "Z": Z, "score": sc, "score_exact": round(sx, 6),
                                "provenance": {"kind": ("closed-dev-only" if args.model_preset else "api-dev-only"), "model": prov_model,
                                               "run_id": args.run_id, "mode": "golf", "check": checks}}, ensure_ascii=False) + "\n"); ver_f.flush()
        print(f"{name[:18]:18s} golf eval {golf_evals}: NEW BEST {golf_inc['score']:.4f} -> {sx:.4f} tok={ev['tokens']} hb={hb} Z={Z:.0f} ({why})", flush=True)
        golf_inc = {**cand, "proof": decl}; golf_since_gain = 0; golf_gains += 1
        ws.own_shas.add(_sha12(decl))
        (ws.root / "candidate.lean").write_text(decl.rstrip() + "\n")                                                                        
        return True, why, sx, False

    def lean_batch(inp: dict) -> str:
        nonlocal golf_evals, golf_since_gain, checks
        items = [it for it in (inp.get("items") or []) if isinstance(it, dict)][:args.golf_batch_max]
        if not items:
            return G.dumps({"ok": False, "errors": [f"give 1-{args.golf_batch_max} items, each {{label, edits: [{{find, replace}}]}} or {{label, content}}"]})
        bk = str(inp.get("base") or "best").strip()
        base_score = golf_inc["score"]                                                                                        
        if bk in ("", "best"):
            base_text = golf_inc["proof"]
        else:
            ent = next((e_ for e_ in _pool_entries() if str(e_.get("sha", "")).startswith(bk)), None)
            if ent is None:
                return G.dumps({"ok": False, "errors": [f"no pool entry with sha prefix {bk!r} (see the pool tool)"]})
            base_text, base_score = ent["proof"], float(ent.get("score_exact") or golf_inc["score"])
        rows_, todo = [], {}
        for k, it in enumerate(items):
            lab = str(it.get("label") or f"v{k + 1}")[:40]
            if isinstance(it.get("content"), str) and it["content"].strip():
                decl, err = it["content"].rstrip(), None
            else:
                decl, err = G.apply_edits(base_text, it.get("edits"))
            if err:
                rows_.append({"label": lab, "ok": False, "error": err, "compiled": False}); continue
            decl = decl.rstrip(); sh = _sha12(decl)
            if sh in golf_seen:
                _c = dict(golf_seen[sh])
                if _c.get("score") is not None:
                    _c["vs_best"] = round(float(_c["score"]) - golf_inc["score"], 4); _c["is_best"] = sh == _sha12(golf_inc["proof"])
                _c.pop("decision", None); _c.pop("vs_base", None)
                rows_.append({"label": lab, **_c, "compiled": False, "note": "already evaluated in this session (not compiled again)"}); continue
            if sh in todo:
                rows_.append({"label": lab, "same_as": sh, "compiled": False, "note": "the same text as another item of this batch"}); continue
            todo[sh] = decl; rows_.append({"label": lab, "sha": sh})
        evs = {}
        if todo:
            with ThreadPoolExecutor(max(1, min(args.golf_jobs, len(todo)))) as ex_:
                evs = dict(zip(todo, ex_.map(golf_eval, todo.values())))
        res_ = {}
        for sh in sorted(evs, key=lambda h: -(_exact(evs[h]["L"], evs[h]["H"], golf_inc["Z"]) if evs[h].get("ok") else -1e9)):
            ev, decl = evs[sh], todo[sh]
            golf_evals += 1; golf_since_gain += 1; checks += 1
            rec = {"sha": sh, "tokens": ev.get("tokens"), "heartbeats": ev.get("heartbeats"), "ok": bool(ev.get("ok")),
                   "error": (ev.get("error") or None) if not ev.get("ok") else None, "run_id": args.run_id}
            transient = False
            if ev.get("ok"):
                _pool_add(decl, sh, ev["tokens"], ev["heartbeats"], _exact(ev["L"], ev["H"], golf_inc["Z"]))
                banked, why, sx, transient = golf_consider(decl, ev)
                rec["score"] = round(sx, 4)
                res_[sh] = {"ok": True, "tokens": ev["tokens"], "heartbeats": ev["heartbeats"], "score": round(sx, 4),
                            "vs_base": round(sx - base_score, 4), "banked": banked, "decision": why}
            else:
                transient = "timeout" in str(ev.get("error") or "")
                res_[sh] = {"ok": False, "tokens": ev.get("tokens"), "error": (ev.get("error") or "")[:300]}
            ws.record_attempt(rec)
            if not transient:                                                                                     
                golf_seen[sh] = res_[sh]
        for r_ in rows_:
            if "sha" in r_ and r_["sha"] in res_:
                r_.update(res_[r_.pop("sha")])
            elif "same_as" in r_:
                r_.update({k_: v_ for k_, v_ in res_.get(r_.pop("same_as"), {}).items() if k_ != "banked"})
            if r_.get("score") is not None:                                                                                          
                r_["vs_best"] = round(float(r_["score"]) - golf_inc["score"], 4)
        return G.dumps({"items": rows_, "note": "vs_base: against the text the item was made from (the best at the start of this batch, or the "
                                                "pool entry); vs_best: against the best after this batch; items that beat the base but were not "
                                                "banked after another item was are worth combining",
                        "best": {"score": round(golf_inc["score"], 4), "tokens": golf_inc["tokens"], "heartbeats": golf_inc["heartbeats"]},
                        "evaluations": golf_evals, "since_last_gain": golf_since_gain,
                        "stop_rule_met": G.stop_ok(golf_evals, golf_since_gain, args.golf_min_evals, args.golf_flat_evals)})

    def golf_check(path: str) -> str:
        return lean_batch({"items": [{"label": Path(path or "candidate.lean").name, "content": ws.path(path or "candidate.lean").read_text()}]})

    def hb_profile_tool(inp: dict) -> str:
        decl = (inp.get("content") or golf_inc["proof"]).rstrip()
        sh = _sha12(decl)
        if sh not in golf_profiles:
            golf_profiles[sh] = G.profile(row, decl, primary)
        return G.dumps(golf_profiles[sh])

    def pool_tool(inp: dict) -> str:
        ents = _pool_entries()
        return G.dumps({"pool": G.pool_rows(ents, golf_inc["proof"], max(1, min(int(inp.get("k") or 8), 20))), "size": len(ents)})

    hardtail_local = 0                                                                                                   
    stall_checks = 0                                                            
    forced_turns_bf = 0                                      

    def lean_check(path: str) -> str:
        nonlocal checks, best, hardtail_local, stall_checks
        if not ws.path(path or "candidate.lean").is_file():                                                                             
            return _tool_json({"ok": False, "errors": [missing_file_note(path or "candidate.lean")]})                                            
        if golf and golf_inc is not None:
            return golf_check(path)
        decl = ws.path(path or "candidate.lean").read_text().rstrip()
                                                                                                                         
                                                                                         
        sha = hashlib.sha256(decl.encode()).hexdigest()[:12]
        prior = next((a for a in reversed(ws.state["attempts"]) if a.get("sha") == sha), None)
        if prior is not None:
            return _tool_json({"ok": bool(prior.get("ok")), "unchanged": True,
                               "note": "candidate.lean is byte-identical to an attempt already checked (result below); nothing was compiled and this does not count as a check. Edit the candidate before checking again.",
                               "prior": {k: (_rel(prior.get(k), decl) if k == "error" else prior.get(k)) for k in ("tokens", "heartbeats", "ok", "error", "score", "run_id") if prior.get(k) is not None}})
        checks += 1
        body = split_declaration(decl, row["statement"])
        if body is None:
            return _tool_json({"ok": False, "errors": ["statement differs from the reference statement (must be byte-for-byte identical, followed by :=)"]})
        bad = check_forbidden(decl)
        if bad:
            return _tool_json({"ok": False, "errors": [f"forbidden construct: {bad}"]})
        toks = count_tokens(body); r = comp(decl, primary); _autofix = None
        if not r.ok:                                                                                                  
            from harness.leantools import fix_redundant_grind as _frg
            _fixed, _names = _frg(decl, r.errors)
            if _fixed:
                _r2 = comp(_fixed, primary)
                if _r2.ok:
                    decl, r = _fixed, _r2; body = split_declaration(decl, row["statement"]) or body; toks = count_tokens(body)
                    sha = hashlib.sha256(decl.encode()).hexdigest()[:12]
                    ws.path(path or "candidate.lean").write_text(decl + "\n")
                    _autofix = f"removed redundant grind parameter(s) {', '.join(_names)} from candidate.lean (grind uses local hypotheses automatically)"
        if not r.ok and not _autofix:                                                                                   
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
        if not r.ok and not _autofix:                                                                                               
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
        if not r.ok and getattr(args, "failed_moves", False):                                                                                      
            try:                                                                                                                         
                from harness import cc_levers as _LVfm                                                                                     
                from harness.leantools import head_line_count as _hlcfm                                                                            
                _rec["move"] = _LVfm.record_move(ws.state, [("best", best.get("proof")), ("ref", row["src"])], decl, call=f"{args.run_id}:{tool_calls}",
                                                 eline=_LVfm.error_line(r.errors[0] if r.errors else None, _hlcfm(row, primary)))
            except Exception:                
                pass
        ws.record_attempt(_rec)
                                                                                                          
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
        if not r.ok:                                                                                      
            from harness.leantools import suggest_names as _sn
            _sug = _sn(row, primary, r.errors)
            if _sug:
                res["did_you_mean"] = _sug
        if not r.ok and _nn is not None:                                                                                                       
            _nb = _nn.lookup(r.errors)
            if _nb:
                res["name_neighbors"] = _nb; res["name_neighbors_note"] = _nn.note
                _dym = {k_: v_ for k_, v_ in (res.get("did_you_mean") or {}).items() if k_ not in _nb}
                if _dym:
                    res["did_you_mean"] = _dym
                else:
                    res.pop("did_you_mean", None)
        _best_before = float(best.get("score") or 33.33)
        if hardtail_target:                                                                   
            hardtail_local = hardtail_local + 1 if toks > hardtail_target / 0.7 * 0.9 else 0
            if hardtail_local >= 4:
                res["strategy_note"] = (f"{hardtail_local} checks in a row are still local edits of the old proof ({toks} tokens; target <= {hardtail_target}). "
                                        "Stop polishing: go back to the protocol (lean_goals map, lemma search, 3-5 different architectures in one lean_check_variants).")
                                                                                                                                    
                                                                                                                            
                                                                                                                               
                                                                                  
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
                        sig_cache[h_] = lean_run(f"#check @{h_}", neighbors=False)[:400]
                    sigs[h_] = sig_cache[h_]
                res["signatures"] = sigs
                res["signature_note"] = "application/type mismatch: `signatures` holds the exact signature of the applied constant — match its implicit/explicit argument order before retrying"
        except Exception:                
            pass
        try:                                                                       
            _off = decl[:len(decl) - len(body)].count("\n") if _rel_on and decl.endswith(body) else 0                                               
            _lt = [(i + 1 + _off, count_tokens(l), l.strip()[:70]) for i, l in enumerate(body.split("\n")) if l.strip()]
            _lt.sort(key=lambda x: -x[1])
            res["costliest_lines"] = [{"line": i, "tokens": n, "text": s} for i, n, s in _lt[:6]]
        except Exception:                
            pass
                                                                                                                                 
                                                                                                                        
                                                                                                          
        if not r.ok and r.errors:
                                                                                                                                  
                                                                                                                                   
                                                                                      
            _head = digest_error(r.errors[0], 300)[:60]
            _same = sum(1 for a in ws.state.get("attempts", []) if a.get("run_id") == args.run_id and not a.get("ok") and (a.get("error") or "")[:60] == _head)
            if _same >= 3:
                res["note"] = (f"This same error has now failed {_same} times in this run ({_rel(_head, decl)!r}). Retrying variants of the same tactic at the same spot is not "
                               "working: prove that step by a different route (another tactic family, an explicit `have` with the needed inequality/equality, "
                               "a library lemma via `exact?`), or restore the last compiling candidate and cut elsewhere.")
                                                                                                                                    
                                                                                                                            
                                                                                                                               
        if not r.ok and len(r.errors) == 1 and "Did not find an occurrence of the pattern" in r.errors[0]:
            _m = re.match(r"\s*(\d+):\d+:", r.errors[0])
            if _m:
                _ln = int(_m.group(1)) - head_lines; _lines = decl.split("\n")
                if 1 <= _ln <= len(_lines) and re.search(r"\brw\s*\[", _lines[_ln - 1]):
                    _lines[_ln - 1] = re.sub(r"\brw\s*\[", "simp only [", _lines[_ln - 1], count=1)
                    _variant = "\n".join(_lines)
                    try:
                        _rv = comp(_variant, primary)
                    except Exception:                
                        _rv = None
                    if _rv is not None and _rv.ok:
                        ws.path("candidate_autofix.lean").write_text(_variant + "\n")
                        _vb = split_declaration(_variant, row["statement"]) or ""
                        res["autofix"] = (f"the failing `rw` at candidate line {_ln} compiles as `simp only [...]` ({count_tokens(_vb)} tokens, {_rv.heartbeats} heartbeats); "
                                          "saved as candidate_autofix.lean: lean_check that path to score and record it, or copy it into candidate.lean and continue.")
        if r.ok:
            L = len_pct(row["proof_length"], toks); H = hb_pct_local(name, r.heartbeats, hbs.get(name))
            provisional = problem_score(True, L, H, 100.0)
            try:
                _pool_add(decl, sha, toks, r.heartbeats, _exact(L, H, 100.0))
            except Exception:                
                pass
            res.update({"length_reduction_pct": round(L, 2), "heartbeat_reduction_pct": round(H, 2), "predicted_score_if_compatible": provisional, "reference_score": 33.33})
            try:                                                                                                   
                from scorer.score import local_reference_heartbeats as _lrh
                _rt = int(row["proof_length"]); _rh = int(_lrh(name) or hbs.get(name) or 0); _fl = ws.state.get("hb_floor")
                if _rt and _rh and r.heartbeats is not None and not OPK:                                               
                    _lp = round(toks / _rt * 100 / 3, 2); _hp = round(max(0, r.heartbeats - (_fl or 0)) / _rh * 100 / 3, 2)
                    res["axis"] = {"points_per_token": round(100 / (3 * _rt), 4), "points_per_1k_heartbeats": round(100000 / (3 * _rh), 3),
                                   "one_token_equals_heartbeats": round(_rh / _rt, 1), "points_left_length": _lp,
                                   "points_left_heartbeats": _hp, "heartbeat_floor": _fl,
                                   "work_on": "tokens" if _lp >= _hp else "heartbeats",
                                   "note": ("points left are upper bounds (a proof cannot reach zero tokens); " +
                                            ("heartbeat floor measured by lean_profile" if _fl else "heartbeat floor not measured yet: call lean_profile"))}
            except Exception:                
                pass
            if args.simp_prune and provisional > best["score"]:                                                                       
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
                except Exception:                
                    pass
            if provisional > best["score"]:
                compat = {primary: True}; _cfail = {}
                for v in versions[1:]:
                    _rv = comp(decl, v, count=False); compat[v] = _rv.ok
                    if not _rv.ok:                                                                         
                        from harness.leantools import compat_failure as _cf
                        _cfail[v] = _cf(row, v, [_rel(e, decl, _hlc_rel(row, v) - _rel_meas) for e in _rv.errors] if _rel_on else _rv.errors)
                Z = compat_pct(compat); sc = problem_score(True, L, H, Z)
                res.update({"compat": compat, "score": sc})
                if _cfail:
                    from harness.leantools import compat_note as _cn
                    res.update({"compat_failures": _cfail, "compat_note": _cn(primary, _cfail, Z, sc, provisional)})
                if sc > best["score"]:
                    try:                                                                                                                        
                        import difflib as _dl
                        _prev = best.get("proof") or ""
                        _d = [l for l in _dl.unified_diff(_prev.splitlines(), decl.splitlines(), lineterm="", n=0) if l[:1] in "+-" and not l.startswith(("+++", "---"))]
                        _led = ws.state.setdefault("ledger", {}).setdefault("wins", [])
                        _led.append({"run_id": args.run_id, "check": checks, "d_score": round(sc - float(best.get("score") or 33.33), 2),
                                     "d_tokens": toks - int(best.get("tokens") or row["proof_length"]), "d_heartbeats": (r.heartbeats or 0) - int(best.get("heartbeats") or 0),
                                     "diff": "\n".join(_d)[:700]})
                        ws.state["ledger"]["wins"] = _led[-30:]
                    except Exception:                
                        pass
                    best = {"score": sc, "proof": decl, "tokens": toks, "heartbeats": r.heartbeats, "L": round(L, 2), "H": round(H, 2), "Z": Z, "compat": compat}
                    ws.state["best"] = best; ws.state["attempts"][-1]["score"] = sc; ws.save()
                    ver_f.write(json.dumps({"problem": name, "sha256": hashlib.sha256(decl.encode()).hexdigest()[:16], "proof": decl, "tokens": toks, "ref_tokens": row["proof_length"],
                                            "heartbeats": r.heartbeats, "primary": primary, "primary_ok": True, "compat": compat, "L": round(L, 2), "H": round(H, 2), "Z": Z, "score": sc,
                                            "provenance": {"kind": ("closed-dev-only" if args.model_preset else "api-dev-only"), "model": prov_model, "run_id": args.run_id, "mode": "agent", "check": checks}}, ensure_ascii=False) + "\n"); ver_f.flush()
                    print(f"{name[:18]:18s} check {checks}: NEW BEST tok={toks} ({L:+.1f}%) hb={r.heartbeats} ({H:+.1f}%) Z={Z:.0f} score={sc}", flush=True)
                                                                                                                                                  
        stall_checks = 0 if float(best.get("score") or 33.33) > _best_before else stall_checks + 1
        if stall_checks >= 8 and stall_checks % 8 == 0 and not OPK:                                                  
            res["rewrite_note"] = (f"{stall_checks} checks in a row without a new best: editing has stalled. Start a NEW rewrite with a different architecture "
                                   "(outline with sorry holes -> lean_skeleton -> fill one hole at a time), using the goal map, LIBRARY LEADS and technique cards.")
        return _tool_json(res, ensure_ascii=not _rel_on)

    t_start = time.time()
    traj_f.write(json.dumps({"type": "header", "run_id": args.run_id, "problem": name, "model": args.model, "api_model": api_model, "endpoint": args.endpoint,
                             "quant": args.quant if args.endpoint == "openrouter" else None, "reasoning_effort": args.reasoning_effort, "turn_budget": args_turns,
                             "max_tokens": args.max_tokens, "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "system": SYSTEM,
                             "tools": [t["name"] for t in TOOLS], "best_at_start": ws.state["best"].get("score"),
                             **({"blind_start": {"reveal_at": blind["at"]}} if BLIND else {})}, ensure_ascii=False) + "\n"); traj_f.flush()
    notes_written = False
    turns_since_check = 0
    finish_rejections = 0
    shell_calls = 0
    lemma_greps = 0; searched = False                                                                                     
    last_truncated = False                                                                                                
    trunc_count = 0                                                                                                                                                                                  
                                                                                                                                          
                                                                                                                                          
                                                                                   
    if args.length_tools and (ws.root / "candidate.lean").exists() and not args.from_reference:
                                                                                                                               
                                                                                                                                  
                                                                                                     
        try:
            _pre_res = json.loads(lean_mine("candidate.lean"))
            if _pre_res.get("mined"):
                msgs[0]["content"] += (f"\n\nMECHANICAL PRE-PASS: the harness already shortened candidate.lean mechanically "
                                       f"({_pre_res['mined'].get('how', '')[:200]}); score {_pre_res['mined'].get('score')}. Continue from it.")
            print(f"{name[:18]:18s} pre-pass: {(_pre_res.get('mined') or {}).get('score', 'no improvement')}", flush=True)
        except Exception as _e:                
            print(f"{name[:18]:18s} pre-pass failed: {_e}", flush=True)
                                                                                                                                            
                                                                                                                                        
                                                                                                                                            
    if not golf and ws.state["best"].get("proof") and not float(ws.state["best"].get("score") or 0) and (ws.root / "candidate.lean").exists() \
            and not args.from_reference:
        try:
            _r0 = json.loads(lean_check("candidate.lean"))
            if isinstance(msgs[0]["content"], str):
                msgs[0]["content"] += ("\n\nSTART CHECK: the harness compiled candidate.lean before your first turn. " +
                                       (f"It compiles: score {_r0.get('score')} ({_r0.get('tokens')} tokens, {_r0.get('heartbeats')} heartbeats). It is "
                                        "your current best and the starting point: improve it, do not start over from original.lean."
                                        if _r0.get("ok") else "It does NOT compile: " + "; ".join((_r0.get("errors") or [str(_r0.get("error") or "?")])[:2])[:400]))
            print(f"{name[:18]:18s} start check: {_r0.get('score') if _r0.get('ok') else 'does not compile'}", flush=True)
        except Exception as _e:                                                           
            print(f"{name[:18]:18s} start check failed: {type(_e).__name__}: {_e}", flush=True)
                                                                                                                                             
                                                                                                                                        
                                                                                                                                         
    if getattr(args, "auto_brief", None):
        try:
            _abf = ROOT / args.auto_brief / (re.sub(r"[^A-Za-z0-9_.-]", "_", name) + ".json")
            _ab = json.loads(_abf.read_text()) if _abf.exists() else None
            if _ab and _ab.get("brief") and isinstance(msgs[0]["content"], str):
                msgs[0]["content"] += "\n\n" + _ab["brief"]
                _sp = (_ab.get("s1") or {}).get("proof") or (_ab.get("s0") if _ab.get("free_applied") else None)
                _ss = float(((_ab.get("s1") or {}).get("full") or _ab.get("start") or {}).get("score") or 0)
                if _sp and _ss > float(ws.state["best"].get("score") or 0) + 0.05:
                    (ws.root / "autobrief_start.lean").write_text(_sp.rstrip() + "\n")
                    _r = json.loads(lean_check("autobrief_start.lean"))
                    if _r.get("ok"):
                        (ws.root / "candidate.lean").write_text(_sp.rstrip() + "\n")
                    print(f"{name[:18]:18s} auto-brief start: {_r.get('score')} (measured {_ss})", flush=True)
            ws.state["runs"][-1]["auto_brief"] = bool(_ab and _ab.get("brief")); ws.save()
            print(f"{name[:18]:18s} auto-brief: {'appended' if _ab and _ab.get('brief') else 'none for this row'}", flush=True)
        except Exception as _e:                                                                     
            print(f"{name[:18]:18s} auto-brief failed: {type(_e).__name__}: {_e}", flush=True)
                                                                                                                                        
                                                                                                                       
    if golf:                                                                                                                     
        _g0 = (best.get("proof") or row["src"]).rstrip()
        _e0 = golf_eval(_g0)
        if not _e0.get("ok"):                                                                                                                 
            _e0 = golf_eval(_g0)                                                                                                       
        if not _e0.get("ok"):
            print(f"{name[:18]:18s} golf: the start proof does not compile ({str(_e0.get('error'))[:160]}); session ends", flush=True)
            args_turns = 0
        else:
            _z0 = best.get("Z") if best.get("proof") and best["proof"].rstrip() == _g0 and best.get("Z") is not None else None
            if _z0 is None:
                _c0 = {primary: True}
                for v in versions[1:]:
                    _c0[v] = comp(_g0, v, count=False).ok
                _z0 = compat_pct(_c0)
            golf_inc = {"score": _exact(_e0["L"], _e0["H"], _z0), "tokens": _e0["tokens"], "heartbeats": _e0["heartbeats"], "Z": float(_z0), "proof": _g0}
            _sh0 = _sha12(_g0); ws.own_shas.add(_sh0)
            golf_seen[_sh0] = {"ok": True, "tokens": _e0["tokens"], "heartbeats": _e0["heartbeats"], "score": round(golf_inc["score"], 4)}
            _pool_add(_g0, _sh0, _e0["tokens"], _e0["heartbeats"], golf_inc["score"])
            for _fn in ("best.lean", "candidate.lean"):
                (ws.root / _fn).write_text(_g0 + "\n")
            golf_profiles[_sh0] = _prof0 = G.profile(row, _g0, primary)
            from scorer.score import local_reference_heartbeats as _lrh_g
            msgs[0] = {"role": "user", "content": G.opening(name, row, versions, int(_lrh_g(name) or hbs.get(name) or 0), golf_inc, _g0, _prof0,
                                                            (_pre or {}).get("linter_hints") or [], args.budget_usd, args.golf_min_evals, args.golf_flat_evals)}
            ws.state["runs"][-1]["mode"] = "golf"; ws.save()
            print(f"{name[:18]:18s} golf: start {golf_inc['score']:.4f} ({_e0['tokens']} tok, {_e0['heartbeats']} hb, Z {_z0:.0f}); profile "
                  + ("ok" if _prof0.get("ok") else str(_prof0.get("error"))[:100]), flush=True)
    if not golf and isinstance(msgs[0]["content"], str) and "SHORT POLISH RUN" not in msgs[0]["content"]:
        msgs[0]["content"] += ("\n\nOPENING MOVE: keep this first turn short. Pick the single most promising idea from the material above and act on it "
                               + ("with ONE tool call now (a lean_skeleton draft, a lean_run probe, or a lean_check_variants batch of complete candidates). "
                                  "You will see results " if BLIND else
                                  "with ONE tool call now (a lean_check_variants batch or lean_goals). You will see results " if OPK else
                                  "with ONE tool call now (a lean_check_variants batch, lean_profile, lean_goals or lean_search). You will see results ")
                               + "and plan the next step from them; do not plan the whole run before acting.")
    turn = -1; extra_turns = 0; _sess_turn_max = 0.0; _last_in_tokens = 0; cut_continuations = 0; adaptive_cap_now = 0
                                                                                                                                           
                                                                                                                                        
                                                                                                                                        
                                                                                                                                        
                                                                                                                                          
    _pc_on = bool(args.model_preset and getattr(args, "budget_reclaim", False) and not MODEL_PRESETS[args.model_preset].get("adaptive_cap"))

    def _inflight_keep(why: str) -> None:
        inf = ws.state.pop("inflight", None)
        if isinstance(inf, dict):                                                                         
            usd = float(inf.get("usd") or 0)
            ws.state["assumed_spend"] = round(float(ws.state.get("assumed_spend") or 0) + usd, 6); ws.save()
            flush_traj({"type": "assumed_spend", "turn": inf.get("turn"), "usd": round(usd, 6), "inflight": why, "of_run": inf.get("run_id")})
            print(f"{name[:18]:18s} in-flight call ({inf.get('run_id')} turn {inf.get('turn')}) kept as spent: ${usd:.3f} ({why})", flush=True)

    def _inflight_open(usd: float) -> None:
        _inflight_keep("an earlier attempt's record was still open")
        base = float(ws.state.get("api_spend") or 0)
        ws.state["inflight"] = {"base": base, "usd": round(usd, 6), "run_id": args.run_id, "turn": turn}
        ws.state["api_spend"] = round(base + usd, 6); ws.save()

    def _inflight_close() -> None:                                                                                                           
        inf = ws.state.pop("inflight", None)
        if isinstance(inf, dict):
            ws.state["api_spend"] = float(inf["base"])
    if isinstance(ws.state.get("inflight"), dict):
        _inflight_keep("a session ended while its call was in flight")
    while turn + 1 < args_turns:                                                                                             
                                                                                                                                        
                                                                                                                                   
                                                                                                                                        
                                                                                                                                         
        _turn_reserve = 0.0; _reclaim_cap = None
        if args.model_preset:
            _pi, _po, _pr_, _pw = MODEL_PRESETS[args.model_preset]["prices"]
            _cap_next = max(args.max_tokens * min(4, 3 + trunc_count), MODEL_PRESETS[args.model_preset].get("min_cap", 0))
            _ctx = max(_last_in_tokens, (len(SYSTEM) + len(json.dumps(msgs, ensure_ascii=False, default=str))) // 2) + 20000
                                                                                                                                      
                                                                                                                                             
                                                                                                                                                
            _turn_reserve, _reclaim_cap = preset_gate(float(ws.state.get("api_spend") or 0), args.budget_usd, _ctx,
                                                      MODEL_PRESETS[args.model_preset]["prices"], _cap_next, _sess_turn_max,
                                                      reclaim=args.budget_reclaim and not MODEL_PRESETS[args.model_preset].get("adaptive_cap"),
                                                      floor=args.reclaim_floor)
            _acap = MODEL_PRESETS[args.model_preset].get("adaptive_cap")
            if _acap:
                                                                                                                                                  
                                                                                                                                                  
                                                                                                                                                    
                                                                                                                                          
                _room = int((args.budget_usd - float(ws.state.get("api_spend") or 0) - _ctx * max(_pi, _pw) / 1e6) * 1e6 / _po)
                adaptive_cap_now = min(int(_acap), _room)
                _turn_reserve = (_ctx * max(_pi, _pw) + max(adaptive_cap_now, 0) * _po) / 1e6
                if adaptive_cap_now < int(MODEL_PRESETS[args.model_preset].get("adaptive_min", 6000)):
                    _turn_reserve = args.budget_usd + 1                                                 
        if args.model_preset and float(ws.state.get("api_spend") or 0) + _turn_reserve > args.budget_usd:
            print(f"{name[:18]:18s} budget reached: ${float(ws.state.get('api_spend') or 0):.3f} + reserve ${_turn_reserve:.3f} > ${args.budget_usd:.2f}; session ends", flush=True)
            break
        turn += 1
        if BLIND and blind["revealed"] is None and (blind["now"] or turn >= blind["at"]) and not _blind_banked():
            _blind_reveal(turn, blind["now"] or "turn")
        if turns_since_check >= 4:
            msgs.append({"role": "user", "content": f"You have not run lean_check for {turns_since_check} turns. Exploration is fine, but convert it now: write candidate.lean with your best complete attempt (even if imperfect) and call lean_check, then continue from the errors."})
            turns_since_check = 0
                                                                                                                           
                                                                                                                                 
        if fresh_start and turn == 20 and (ws.root / "best.lean").exists() and not any(a.get("ok") for a in ws.state.get("attempts", []) if a.get("run_id") == args.run_id):
            (ws.root / "candidate.lean").write_text((ws.root / "best.lean").read_text())
            msgs.append({"role": "user", "content": f"FRESH START FALLBACK: 20 turns and no compiling candidate from the new approach. candidate.lean has been restored to the "
                                                    f"stored best (score {ws.state['best'].get('score')}). Spend the remaining {args_turns - turn} turns on THAT proof: structural cuts one at a "
                                                    "time, lean_check after each. First, add one line to notes.md on why the new approach did not compile, so later runs do not repeat it."})
            print(f"{name[:18]:18s} fresh start produced nothing compiling by turn 20: restored best.lean", flush=True)
            fresh_start = False
        if think_prompt_on and turn > 0 and turn % 6 == 0:
            msgs.append({"role": "user", "content": THINK_NUDGE})
                                                                                                                                                 
                                                                                           
        if not golf and turn == args_turns - (1 if args_turns <= 10 else 3) and not notes_written:
            msgs.append({"role": "user", "content": "Budget nearly over (3 turns left). Write notes.md now (write_file): what worked, what failed and why, lemma names you confirmed exist or do not exist, and the most promising next idea. " + ("" if OPK else "Tag every negative claim with the check that showed it, `[tested: <what> -> <result>]`; untagged claims are shown to later runs as unverified. ") + "Then make sure candidate.lean holds your best compiling candidate and call finish."})
                                                                                                                                  
                                                                                   
        tools_now = [t_ for t_ in TOOLS if t_["name"] != "shell"] if (args.from_reference and (checks == 0 or shell_calls >= 3)) else TOOLS
        if not args.length_tools:
            tools_now = [t_ for t_ in tools_now if t_["name"] != "lean_mine"]
        if args.strategy == "hardtail" and hardtail_batches == 0 and turn >= 2 and forced_turns < 3:
                                                                                                                                            
                                                                                                                 
            if forced_turns == 0:
                msgs.append({"role": "user", "content": (f"PROTOCOL STEP 4 NOW: call lean_check_variants with 3-5 FULL candidates of DIFFERENT architecture, each at most "
                                                         f"{hardtail_target} tokens, built from the goal map (shared `<;>` closer over the case split, a generalised helper `have`, "
                                                         "term mode from library lemmas, a different induction/cases variable). lean_run is available for a quick lemma check first. "
                                                         "Other tools return after this batch.")})
            forced_turns += 1
            tools_now = [t_ for t_ in tools_now if t_["name"] in ("lean_check_variants", "lean_run", "lean_goals", "read_file")]
        m = None
                                                                                                                                       
                                                                                                             
                                                                                                                                    
                                                                                               
                                                                                                                                                 
                                                                                                                                              
        cap = args.max_tokens * min(4, 3 + trunc_count)
        if args.model_preset:
            cap = max(cap, MODEL_PRESETS[args.model_preset].get("min_cap", 0))
            if MODEL_PRESETS[args.model_preset].get("adaptive_cap"):
                cap = adaptive_cap_now
            elif _reclaim_cap is not None:                                                                                          
                cap = _reclaim_cap
                print(f"{name[:18]:18s} turn {turn}: budget reclaim: output cap {cap} (full {_cap_next}); spend ${float(ws.state.get('api_spend') or 0):.3f} "
                      f"+ worst case ${_turn_reserve:.3f} <= ${args.budget_usd:.2f}", flush=True)
        t_call = time.time()
                                                                                                                                              
                                                                                                                                         
                                                                                                    
        _rl: dict = {}
        def _rl_log(s_: str) -> None:
            print(f"{name[:18]:18s} turn {turn}: {s_}", flush=True); flush_traj({"type": "rate_limit", "turn": turn, "note": s_})
                                                                                                                                                
                                                                                                                                           
                                                                                                                                          
        _cn: dict = {}
        def _cn_log(s_: str) -> None:
            print(f"{name[:18]:18s} turn {turn}: {s_}", flush=True); flush_traj({"type": "connect_retry", "turn": turn, "note": s_})
        def _cn_pause() -> None:                                                                                                             
            if _pc_on:
                _inflight_close(); ws.save()
        def _cn_resume() -> None:
            if _pc_on:
                _inflight_open(_ctx * max(_pi, _pw) / 1e6 + cap * _po / 1e6)
        for attempt in range(args.max_api_retries):                                                                                   
            if _pc_on:                                                                                                                               
                _inflight_open(_ctx * max(_pi, _pw) / 1e6 + cap * _po / 1e6)
            try:
                if args.endpoint == "openai":
                    m = _oai.with_rate_limit_retry(lambda: _oai.with_connect_retry(lambda: _oai.create(
                                    base_url=args.base_url, api_key=_oai_key, model=api_model, max_tokens=cap, system=(SYSTEM if args.length_tools else SYSTEM_BASE), tools=tools_now, messages=msgs, extra_body=extra_body,
                                    **({"think_mode": MODEL_PRESETS[args.model_preset]["think_mode"], "cache": MODEL_PRESETS[args.model_preset]["cache"],
                                       "stream": MODEL_PRESETS[args.model_preset].get("stream", False),
                                       "guard": MODEL_PRESETS[args.model_preset].get("stream_guard", False)} if args.model_preset else {})),
                                    state=_cn, log=_cn_log, pause=_cn_pause, resume=_cn_resume),
                                    budget_s=args.rate_limit_budget, state=_rl, log=_rl_log)
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
            except Exception as e:                                                                                                              
                                                                                                                                               
                                                                                                                                                   
                flush_traj({"type": "api_retry", "turn": turn, "attempt": attempt, "max_tokens": cap, "status": getattr(e, "status_code", None),
                            "error": f"{type(e).__name__}: {str(e)[:300]}", "seconds": round(time.time() - t_call, 1),
                            **({"not_sent": True} if getattr(e, "not_sent", False) else {})})                                                     
                if _pc_on:                                                                                                        
                    _inflight_close()
                if context_overflow(e):                                                                                                
                    log_f.write(json.dumps({"problem": name, "turn": turn, "status": f"context_full:{str(e)[:200]}"}) + "\n"); log_f.flush()
                    flush_traj({"type": "context_full", "turn": turn, "error": str(e)[:500]})
                    print(f"{name[:18]:18s} turn {turn}: context window full, session ends: {str(e)[:160]}", flush=True); m = None; break
                if args.budget_reclaim and args.model_preset and maybe_billed(e) and not MODEL_PRESETS[args.model_preset].get("adaptive_cap"):
                                                                                                                                                  
                                                                                                                                       
                    _wc = _ctx * max(_pi, _pw) / 1e6 + cap * _po / 1e6
                    ws.state["api_spend"] = round(float(ws.state.get("api_spend") or 0) + _wc, 6)
                    ws.state["assumed_spend"] = round(float(ws.state.get("assumed_spend") or 0) + _wc, 6); ws.save()
                    flush_traj({"type": "assumed_spend", "turn": turn, "attempt": attempt, "usd": round(_wc, 6), "max_tokens": cap})
                    _rc, _rr = fit_output_cap(args.budget_usd, float(ws.state["api_spend"]), _ctx * max(_pi, _pw) / 1e6, _po, cap,
                                              args.reclaim_floor, 1.25 * _sess_turn_max)
                    if _rc is None:
                        print(f"{name[:18]:18s} budget reached: ${float(ws.state['api_spend']):.3f} after a failed attempt charged ${_wc:.3f} "
                              f"(may have been billed); no retry fits ${args.budget_usd:.2f}; session ends", flush=True)
                        flush_traj({"type": "budget_stop", "turn": turn, "error": f"{type(e).__name__}: {str(e)[:400]}"})
                        m = None; break
                    cap, _reclaim_cap, _turn_reserve = _rc, _rc, _rr
                if attempt >= args.max_api_retries - 1 or getattr(e, "rate_limit_exhausted", False) or getattr(e, "connect_exhausted", False):
                    log_f.write(json.dumps({"problem": name, "turn": turn, "status": f"api_error:{str(e)[:200]}"}) + "\n"); log_f.flush(); flush_traj({"type": "api_error", "turn": turn, "error": str(e)[:500]}); print(f"{name[:18]} turn {turn}: api error {str(e)[:120]}", flush=True); m = None; break
                time.sleep(min(10 * 2 ** attempt, 300))
        if m is None:
            break
        if _pc_on:                                                                                      
            _inflight_close()
                                                                                                                                                  
                                                                                                                                                   
                                                                                                                                             
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
                except Exception as _e:                
                    print(f"{name[:18]:18s} turn {turn}: budget forcing failed: {str(_e)[:160]}", flush=True)
                                                                                                                                             
                                                                                                                                         
                                                                                                                                          
        if (args.endpoint != "openai" and m.stop_reason == "max_tokens" and not any(b.type == "tool_use" for b in m.content)
                and not any(b.type == "text" and (b.text or "").strip() for b in m.content)):
            _tail = "".join(getattr(b, "thinking", "") or "" for b in m.content if b.type == "thinking")[-2500:].strip()
            _note = ("[harness] Your previous reply hit the output limit while still thinking and was discarded. "
                     + (f"The end of that reasoning was:\n<<<\n{_tail}\n>>>\n" if _tail else "")
                     + ("Act on it now with ONE tool call and minimal text (a lean_batch of the edits you planned); do not resend the "
                        "current best unchanged." if golf else
                        "Act on it now with ONE tool call and minimal text (a lean_check_variants batch of the edits you planned, or "
                        "write_file of a NEW candidate); do not rewrite the current best unchanged."))
            _last = msgs[-1]
            _content = ([*_last["content"], {"type": "text", "text": _note}] if isinstance(_last["content"], list) else _last["content"] + "\n\n" + _note)
            _forced = msgs[:-1] + [{**_last, "content": _content}]
            try:
                _eb = {k: v for k, v in extra_body.items() if k not in ("reasoning_effort", "reasoning")}
                _eb["thinking"] = {"type": "disabled"}
                _m2 = cl.messages.create(model=api_model, max_tokens=args.max_tokens, system=(SYSTEM if args.length_tools else SYSTEM_BASE),
                                         tools=tools_now, messages=_forced, extra_body=_eb)
                if not any(b.type == "tool_use" for b in _m2.content):
                                                                                                                                     
                                                                                                                                      
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
                    msgs[-1] = _forced[-1]                                     
                    _m2.usage.output_tokens += m.usage.output_tokens
                    m = _m2; forced_turns_bf += 1
                    print(f"{name[:18]:18s} turn {turn}: no-thinking retry rescued a capped turn ({_rtools})", flush=True)
            except Exception as _e:                
                print(f"{name[:18]:18s} turn {turn}: no-thinking retry failed: {str(_e)[:160]}", flush=True)
        total_out += m.usage.output_tokens
        if args.model_preset:                                                                                                         
            _u = m.usage; _pi, _po, _pr_, _pw = MODEL_PRESETS[args.model_preset]["prices"]
                                                                                                                                    
                                                                                                    
            _tab = (max(0, _u.input_tokens - _u.cache_read - _u.cache_write) * _pi + _u.output_tokens * _po + _u.cache_read * _pr_ + _u.cache_write * _pw) / 1e6
                                                                                                                                           
                                                                                                                                                
            _c = _u.cost if getattr(_u, "cost", None) is not None and not MODEL_PRESETS[args.model_preset].get("list_price") else (
                max(_tab, float(_u.cost)) if getattr(_u, "cost", None) is not None else _tab)
            _sp0 = float(ws.state.get("api_spend") or 0)
            ws.state["api_spend"] = round(_sp0 + _c, 6)
                                                                                                                                            
                                                                                                                       
            for _ms in (float(x) for x in args.budget_milestones.split(",") if x.strip()):
                if _sp0 < _ms <= ws.state["api_spend"] and f"{_ms:g}" not in ws.state.get("budget_milestones", {}):
                    _snap = {"spend": ws.state["api_spend"], "best": best["score"], "run_id": args.run_id, "turn": turn,
                             "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
                    ws.state.setdefault("budget_milestones", {})[f"{_ms:g}"] = _snap
                    print(f"{name[:18]:18s} budget milestone ${_ms:g} crossed: spend ${_snap['spend']:.3f}, best {_snap['best']} (cap ${args.budget_usd:.2f})", flush=True)
                    flush_traj({"type": "budget_milestone", "usd": _ms, **_snap})
            ws.save()
            _sess_turn_max = max(_sess_turn_max, _c); _last_in_tokens = _u.input_tokens
                                                                                                                                                 
                                                                                                                                                   
                                                                                                                                        
        last_truncated = (m.stop_reason == "max_tokens") or (m.usage.output_tokens or 0) >= cap
        uses = [b for b in m.content if b.type == "tool_use"]
                                                                                                                                       
                                                                                                                                            
                                                                                                                                          
                                                                                                                                         
                                                                                                                                            
        runaway = [u for u in uses if last_truncated and isinstance(u.input, dict) and "_raw_arguments" in u.input]
        runaway_junk = False
        for u in runaway:
            _raw = str(u.input.get("_raw_arguments") or "")
            _junk = degenerate_tail(_raw) or "_junk" in u.input                                                               
            flush_traj({"type": "runaway_tool_call", "turn": turn, "tool": u.name, "chars": len(_raw), "degenerate": _junk, "raw": _raw})
            u.input = {"_dropped": f"cut at the output cap after {len(_raw)} chars of arguments"
                                   + (", ending in the same few characters repeated over and over" if _junk else "")}
            runaway_junk = runaway_junk or _junk
            print(f"{name[:18]:18s} turn {turn}: runaway {u.name} call cut at the output cap ({len(_raw)} chars) dropped from the history", flush=True)
                                                                                                                                         
                                                                                                                                             
                                      
        try:
            for u in uses:
                if isinstance(u.input, dict) and "_dropped" not in u.input and "_raw_arguments" not in u.input:
                    _why = junk_reason(json.dumps(u.input, ensure_ascii=False))
                    if _why:
                        flush_traj({"type": "junk_tool_call", "turn": turn, "tool": u.name, "reason": _why, "raw": u.input})
                        u.input = {"_dropped": f"rejected as junk ({_why[:120]})"}
                        runaway_junk = True
                        print(f"{name[:18]:18s} turn {turn}: junk {u.name} call rejected ({_why[:80]})", flush=True)
            for b in m.content:
                if b.type == "text" and b.text and junk_reason(b.text):
                    flush_traj({"type": "junk_text", "turn": turn, "reason": junk_reason(b.text), "chars": len(b.text)})
                    b.text = b.text[:1500] + "\n[the rest of this reply was degenerate repetition; cut by the harness]"
                    runaway_junk = True
            if getattr(m, "raw_finish_reason", None) == "junk_abort":
                flush_traj({"type": "junk_abort", "turn": turn, "output_tokens": m.usage.output_tokens, "cost": getattr(m.usage, "cost", None)})
                print(f"{name[:18]:18s} turn {turn}: junk stream cut after {m.usage.output_tokens} output tokens", flush=True)
        except Exception as _e:                                                        
            print(f"{name[:18]:18s} turn {turn}: junk check failed: {type(_e).__name__}: {_e}", flush=True)
        trunc_count += 1 if last_truncated and not runaway_junk else 0                                                          
        texts = [b.text for b in m.content if b.type == "text"]
        log_f.write(json.dumps({"problem": name, "turn": turn, "out_tok": m.usage.output_tokens, "stop": str(m.stop_reason), "tools": [u.name for u in uses], "text": "".join(texts)[:300]}) + "\n"); log_f.flush()
        flush_traj({"type": "turn", "turn": turn, "max_tokens": cap, "stop": str(m.stop_reason), "input_tokens": m.usage.input_tokens, "output_tokens": m.usage.output_tokens,
                    "cache_read": getattr(m.usage, "cache_read", None), "cost": getattr(m.usage, "cost", None),
                                                                                                                                              
                                                                                                                 
                    "cache_write": getattr(m.usage, "cache_write", None), "metered_usd": round(_c, 6) if args.model_preset else None,
                                                                                                                                              
                                                                                                                                    
                    "reasoning_tokens": getattr(m.usage, "reasoning", None), "usage_estimated": getattr(m, "usage_estimated", None),
                    "api_attempts": attempt + 1,
                    **({"budget_reclaim": {"full_cap": _cap_next, "worst_usd": round(_turn_reserve, 6)}} if _reclaim_cap is not None else {}),
                    "seconds": round(time.time() - t_call, 1), "tools": [u.name for u in uses], "checks_so_far": checks, "best_so_far": best["score"],
                    **({"rate_limit_hits": _rl["hits"], "rate_limit_wait_s": round(_rl["waited"], 1)} if _rl.get("hits") else {})})
        if not uses:
            if (m.stop_reason == "max_tokens" and args.model_preset and MODEL_PRESETS[args.model_preset].get("continue_on_length")
                    and cut_continuations < 1 and not runaway_junk):
                                                                                                                                            
                                                                               
                cut_continuations += 1
                msgs += [{"role": "assistant", "content": [b.model_dump(exclude_none=True) for b in m.content] or [{"type": "text", "text": "(truncated)"}]},
                         {"role": "user", "content": "Your output was cut by the length limit while you were reasoning. Continue from where your "
                          "reasoning stopped, then act with a tool call."}]
                flush_traj({"type": "length_continuation", "turn": turn, "output_tokens": m.usage.output_tokens})
                continue
            if m.stop_reason == "max_tokens":
                                                                                                                                              
                                                                                                                                                   
                                                                        
                _tail = "".join(getattr(b, "thinking", "") or "" for b in m.content if b.type == "thinking")[-2500:].strip()
                msgs += [{"role": "assistant", "content": [b.model_dump(exclude_none=True) for b in m.content] or [{"type": "text", "text": "(truncated)"}]},
                         {"role": "user", "content": "You ran out of output budget without calling a tool. "
                          + (f"The end of your cut reasoning was:\n<<<\n{_tail}\n>>>\n" if _tail else "")
                          + ("Act on it now with ONE tool call and minimal text: send the edits you were planning as one lean_batch (find/replace "
                             "items). Do not resend the current best unchanged." if golf else
                             "Act on it now with ONE tool call and minimal text: send the edits you were planning as one lean_check_variants call "
                             "(3-6 FULL variants of candidate.lean), or write_file a NEW candidate. Do not rewrite the current best unchanged (it is already "
                             "checked and banked).")}]
                continue
                                                                                                                                    
                                                                                                                                       
                                                                                              
            _left = args_turns - turn - 1
            if golf and not (G.stop_ok(golf_evals, golf_since_gain, args.golf_min_evals, args.golf_flat_evals) or golf_budget_low()) and finish_rejections < 6:
                finish_rejections += 1
                msgs += [{"role": "assistant", "content": [b.model_dump(exclude_none=True) for b in m.content] or [{"type": "text", "text": "(no reply)"}]},
                         {"role": "user", "content": "You ended your turn without a tool call. " + G.refusal(golf_evals, golf_since_gain, args.golf_min_evals,
                                                                                                              args.golf_flat_evals)}]
                continue
            if not golf and _left >= max(4, args_turns // 3) and finish_rejections < 2:
                finish_rejections += 1
                msgs += [{"role": "assistant", "content": [b.model_dump(exclude_none=True) for b in m.content] or [{"type": "text", "text": "(no reply)"}]},
                         {"role": "user", "content": f"You ended your turn without a tool call, but {_left} turns remain and the run continues. "
                          f"Best so far {best['score']} (reference 33.33). Work on the proof now with a tool call: a lean_check_variants batch of "
                          + ("3-6 different candidates or lean_goals. " if OPK else                                                                  
                             "3-6 different candidates (a new architecture if local edits are exhausted), lean_profile, lean_goals or lean_search. ")
                          + "Call finish only in the last third of the budget."}]
                continue
            if BLIND and blind["revealed"] is None and not _blind_banked() and _left > 0:
                blind["now"] = "finish"                                                                            
                msgs += [{"role": "assistant", "content": [b.model_dump(exclude_none=True) for b in m.content] or [{"type": "text", "text": "(no reply)"}]}]
                continue
            break                                  
        cut_continuations = 0
        results = []
        done = False
        turns_since_check += 1
        n_rejected = 0
        for u in uses:
            tool_calls += 1; inp = u.input or {}
            if u.name in ("lean_check", "lean_check_variants", "lean_mine", "lean_batch") and "_dropped" not in inp:
                turns_since_check = 0
            try:
                if (golf or OPK) and u.name not in {t_["name"] for t_ in TOOLS}:                                                           
                    out = f"unknown tool {u.name} in this session (tools: {', '.join(t_['name'] for t_ in TOOLS)})"
                elif "_dropped" in inp:                                                                      
                    out = (f"Your {u.name} call was {inp['_dropped']}; it was dropped and nothing was executed. Write compactly and in smaller "
                           "pieces: one candidate per write_file without padding or trailing whitespace, at most 3 variants per "
                           "lean_check_variants, then continue.")
                elif u.name == "read_file" and BLIND and blind["revealed"] is None and Path(inp.get("path") or "").name == "original.lean":
                    blind["withheld_reads"] = blind.get("withheld_reads", 0) + 1                                                             
                    out = (f"original.lean is withheld in this blind start: write your own proof from the statement and the facts sheet. The harness "
                           f"shows the reference at turn {blind['at']} if no candidate of yours is banked by then.")
                elif u.name == "read_file" and not ws.path(inp.get("path") or "").is_file():                                                     
                    out = missing_file_note(inp.get("path") or "")
                elif u.name == "read_file":
                    txt = ws.path(inp["path"]).read_text(); lines = txt.split("\n")
                    s0 = max(1, int(inp.get("start") or 1)); e0 = min(len(lines), int(inp.get("end") or min(len(lines), s0 + 199)))
                    out = "\n".join(f"{i:5d}| {lines[i-1]}" for i in range(s0, e0 + 1)) + (f"\n... ({len(lines)} lines total)" if e0 < len(lines) else "")
                elif u.name == "write_file":
                    ws.path(inp["path"]).write_text(inp["content"]); out = f"wrote {Path(inp['path']).name} ({len(inp['content'])} chars)"
                    if Path(inp["path"]).name == "candidate.lean":
                        _dn = _dup_note(); out += _dn
                                                                                                                                          
                                                                                                                                       
                        if not _dn and "sorry" not in inp["content"]:
                            out += "\n[auto lean_check of candidate.lean — do not check it again]\n" + lean_check("candidate.lean"); turns_since_check = 0
                    if Path(inp["path"]).name == "notes.md":
                        notes_written = True
                elif u.name == "lean_check":
                    out = lean_check(inp.get("path") or "candidate.lean")
                elif u.name == "shell":
                                                                                                                                          
                    if args.from_reference and (checks == 0 or shell_calls >= 3):
                        n_rejected += 1
                        out = ("scout rule: " + ("no shell exploration before your first lean_check / lean_check_variants — write a candidate of your own architecture now and check it"
                                                 if checks == 0 else "shell budget (3 calls) exhausted for this scout run — write and check candidates instead"))
                    else:
                        shell_calls += 1; _h0 = _cand_sha(); out = shell(inp.get("command") or "")
                        _bv = _BF.violation(inp.get("command") or "", row, blind.get("rows_paths") or ()) if BLIND else None
                        if _bv:                                                                             
                            blind["violations"].append({"turn": turn, "after_reveal": blind["revealed"] is not None, "reason": _bv})
                            flush_traj({"type": "violation", "turn": turn, "after_reveal": blind["revealed"] is not None, "reason": _bv,
                                        "command": (inp.get("command") or "")[:500]})
                            print(f"{name[:18]:18s} blind start: VIOLATION turn {turn}: {_bv}" + (" (after the reveal)" if blind["revealed"] is not None else ""), flush=True)
                        if not searched and _LEMMA_GREP.search(inp.get("command") or ""):
                            lemma_greps += 1
                            if lemma_greps in (2, 5) and not OPK:                                                                     
                                out += ("\n\n[harness] You are hunting library lemmas by hand. lean_search does this in one call: it ranks lemmas by match with the "
                                        "goals of candidate.lean (exact? at each goal with probes=true, unused same-file lemmas, simp/grind attributes) and returns "
                                        "signatures. Try it before the next grep.")
                        if _cand_sha() != _h0:                                                                               
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
                elif u.name == "lean_batch" and golf_inc is not None:
                    out = lean_batch(inp)
                elif u.name == "hb_profile" and golf_inc is not None:
                    out = hb_profile_tool(inp)
                elif u.name == "pool" and golf_inc is not None:
                    out = pool_tool(inp)
                elif u.name == "finish":
                                                                                                                         
                                                                                                                       
                    remaining = args_turns - turn - 1
                    if golf:                                                                                       
                        if G.stop_ok(golf_evals, golf_since_gain, args.golf_min_evals, args.golf_flat_evals) or golf_budget_low() or finish_rejections >= 6:
                            out = "ok"; done = True
                        else:
                            finish_rejections += 1
                            out = G.refusal(golf_evals, golf_since_gain, args.golf_min_evals, args.golf_flat_evals)
                    elif BLIND and blind["revealed"] is None and not _blind_banked() and remaining > 0:
                        blind["now"] = "finish"                                                                                          
                        out = ("finish not accepted yet: no candidate of yours has been banked, so the harness shows the reference proof now "
                               "(next message); continue from it.")
                    elif hardtail_target and hardtail_batches == 0 and remaining > 1 and finish_rejections < 3:
                                                                                                                      
                        finish_rejections += 1
                        out = (f"finish rejected: this is a hard-tail strategy run and no new architecture has been tried yet. The goal map is in the "
                               f"opening message. Do steps 2-4 now: plan in notes.md, lemma-search 2-3 routine steps with lean_run, then send 3-5 FULL "
                               f"candidates of different architecture (each <= {hardtail_target} tokens) in ONE lean_check_variants call.")
                    elif args_turns <= 10 and checks == 0 and remaining > 0 and finish_rejections < 2:
                        finish_rejections += 1                                                
                        out = ("finish rejected: this short polish run has made no check yet. Send one lean_check_variants call with 3-6 single-edit "
                               "variants of candidate.lean now; finish after that.")
                    elif remaining >= max(4, args_turns // 3) and finish_rejections < 2 and not OPK:                                           
                                                                                                                                                         
                                                                                                                             
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
            except Exception as e:                
                out = f"tool error: {e}"
                tool_errors[u.name] = tool_errors.get(u.name, 0) + 1
                print(f"{name[:18]:18s} TOOL ERROR {u.name}: {type(e).__name__}: {str(e)[:200]}", flush=True)
                flush_traj({"type": "tool_error", "turn": turn, "tool": u.name, "error": f"{type(e).__name__}: {str(e)[:500]}"})
            if args.lean_io and u.name in ("shell", "lean_run", "read_file") and len(out) > 1500:                         
                out = out[:1500] + f"\n... [truncated: {len(out) - 1500} more chars; narrow the command, or read_file with start/end]"
            results.append({"type": "tool_result", "tool_use_id": u.id, "content": out[:12000]})
        if args.from_reference and uses and n_rejected == len(uses) and extra_turns < 6:
            args_turns += 1; extra_turns += 1                                                                                       
        msgs += [{"role": "assistant", "content": [b.model_dump(exclude_none=True) for b in m.content]}, {"role": "user", "content": results}]
        if BLIND and blind["banked_turn"] is None and _blind_banked():
            blind["banked_turn"] = turn
        if done:
            break
    if args.normalize and ws.state["best"].get("proof"):
                                                                                                                                          
                                                                                                                                         
                                                                                                                              
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
        except Exception as _e:                
            print(f"{name[:18]:18s} normalizer failed: {type(_e).__name__}: {_e}", flush=True)
    summary = {"problem": name, "best_score": best["score"], "checks": checks, "tool_calls": tool_calls, "turns": turn + 1, "out_tokens": total_out, "seconds": round(time.time() - t_start)}
    if tool_errors:
        summary["tool_errors"] = tool_errors
    if BLIND:                                                                                                     
        summary["blind"] = {"reveal_at": blind["at"], "revealed_turn": blind["revealed"], "reveal_reason": blind["reason"],
                            "banked_turn": blind["banked_turn"], "banked_before_reveal": blind["banked_turn"] is not None and (
                                blind["revealed"] is None or blind["banked_turn"] < blind["revealed"]),
                            "violations": sum(1 for v in blind["violations"] if not v["after_reveal"]),
                            "violations_after_reveal": sum(1 for v in blind["violations"] if v["after_reveal"]),
                            "withheld_reads": blind.get("withheld_reads", 0)}
    if golf:
        summary.update({"mode": "golf", "golf_evaluations": golf_evals, "golf_gains": golf_gains, "golf_since_gain": golf_since_gain,
                        "golf_best_exact": round(golf_inc["score"], 6) if golf_inc else None, "spend": round(float(ws.state.get("api_spend") or 0), 4)})
    if _nn is not None:                                                                                        
        summary["name_neighbors"] = {k_: (round(v_, 1) if isinstance(v_, float) else v_) for k_, v_ in _nn.stats.items()}
    flush_traj({"type": "end", **summary, "finished": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}); traj_f.close()
                                                                                                                       
    import gzip, shutil
    plain = pathlib.Path(traj_f.name); gz = plain.with_name(plain.name + ".gz")
    with plain.open("rb") as fi, gzip.open(gz, "ab") as fo:
        shutil.copyfileobj(fi, fo)
    plain.unlink()
    print(f"{name[:18]:18s} DONE best={best['score']} checks={checks} tool_calls={tool_calls} turns={turn+1} out_tok={total_out} {summary['seconds']}s" + (f" TOOL_ERRORS={tool_errors}" if tool_errors else ""), flush=True)
    return summary


                                                                                                                                       
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
BATCH_ALTERNATIVES = ("\n\nBATCH YOUR ALTERNATIVES: when you can think of 2-6 plausible rewrites of the same spot (different closers, different case structures, with/without a `have`), "
           "send them all in ONE lean_check_variants call rather than one lean_check per turn; every compiling variant is scored and banked, and the best one lands in candidate.lean. "
           "Each lean_check result also lists the costliest proof-body lines by token count: that is where the length axis is.")
SYSTEM += BATCH_ALTERNATIVES
SYSTEM_OPEN += BATCH_ALTERNATIVES                                                                                                           
                                                                                                                                      
                                                                                                                                               
                                                                                                                                       
                                                                                                                                           
                                                                                                                                        
                                                                                                                                 
_OPEN_WORKFLOW = ("Workflow: read original.lean (and context.lean if you need surrounding definitions), then improve INCREMENTALLY: change one thing "
                  "(delete a step, inline a `have`, replace one tactic), write candidate.lean, lean_check, and keep going from whatever compiles. ")
_OPEN_NO_REWRITE = "Do NOT rewrite the whole proof in one go unless the problem is short — large rewrites almost always fail with \"unsolved goals\". "
BLIND_WORKFLOW = ("Workflow (blind start: the first session on this problem): the reference proof is withheld. The statement and the listed "
                  "toolchains are the test your proof must pass; write your OWN proof of the statement for the fewest tokens and heartbeats, from "
                  "the definitions (context.lean), the library and the facts sheet in the first message (the names and tactics the reference uses, "
                  "its size and its cost), not from the reference's text. candidate.lean starts as the statement with a `sorry` body: draft with "
                  "`sorry` placeholders and read the goals they leave with lean_skeleton, then lean_check complete candidates (a candidate with "
                  "sorry is rejected there). The reference stays the banked best, so a failed attempt loses nothing; if none of your candidates "
                  "is banked by a third of your turns, the harness shows the reference proof and you continue from it. Do not read the "
                  "problem's own source file or the rows file: they contain the reference proof. ")
BLIND_TOOL_TEXT = {                                                                                                                     
    "read_file": ("original.lean (the reference declaration, compiles)", "original.lean (the reference declaration: withheld in a blind start "
                  "until the harness shows it)"),
    "write_file": ("the statement byte-for-byte as in original.lean", "the statement byte-for-byte as in original.lean, or as in candidate.lean's "
                   "first lines in a blind start"),
}


def blind_system(system_open: str) -> str:
    """SYSTEM_OPEN for a blind start: its two sentences that send the model to edit original.lean replaced by BLIND_WORKFLOW."""
    if _OPEN_WORKFLOW not in system_open or _OPEN_NO_REWRITE not in system_open:
        raise ValueError("SYSTEM_OPEN changed: the blind-start workflow substitution no longer applies")
    return system_open.replace(_OPEN_WORKFLOW, BLIND_WORKFLOW).replace(_OPEN_NO_REWRITE, "")


def blind_tools(tools: list) -> None:
    """The read_file / write_file descriptions of a blind start (in place)."""
    for t in tools:
        if t["name"] in BLIND_TOOL_TEXT and BLIND_TOOL_TEXT[t["name"]][0] in t["description"]:
            t["description"] = t["description"].replace(*BLIND_TOOL_TEXT[t["name"]])
                                                                                                                                          
                                                                                                                                     
                                                                                                                                          
                                                                                                                                        
                                                                                                                                           
                                                        
OPEN_TOOLS = ("read_file", "write_file", "lean_check", "lean_run", "shell", "finish", "lean_check_variants", "lean_goals", "lean_skeleton",
              "lean_profile")
                                                                                                                                          
                                                                                                                                         
                                                                                                                                      
                                                                                                                                  
OPEN_TOOL_DESCRIPTIONS = {
    "lean_skeleton": "Check a DRAFT proof whose unfinished parts are `sorry` (as a tactic or as a term argument): returns the goal at every hole "
                     "plus any real errors. Nothing is scored or banked; when no sorry remains, lean_check the candidate (sorry is forbidden there).",
    "lean_profile": "Heartbeat profile of a COMPILING tactic proof: where the heartbeats go, block by block (each block's cost, nested blocks under "
                    "the costliest step), the floor (the heartbeats of the statement with a `sorry` body: no proof costs less) and the score points "
                    "left on the heartbeat term above the floor. A block's cost includes elaborating its terms, not only running its tactics. Takes 1-3 minutes; cached per proof.",
}
SYSTEM_BASE = SYSTEM                                                                         
                                                                                                                                    
                                                                                                                                 
                    
                                                                                                                               
                                                                                                                                  
                                                                                                                                         
                                                                                                                               
                                                                                                                              
MODEL_PRESETS = {
    "haiku-5.5": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/oline-keys/openrouter_anthropic_claude-haiku-5.5.key",
                      api_model="anthropic/claude-haiku-5.5", cache=True, think_mode="details", prices=(0.125, 0.50, 0.01, 0.15625)),
    "sonnet-5.5": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/oline-keys/openrouter_anthropic_claude-sonnet-5.5.key",
                       api_model="anthropic/claude-sonnet-5.5", cache=True, think_mode="details", prices=(2.50, 10.0, 0.10, 3.125),
                       list_price=True),
                                                                                                                                    
                                                                                                                                 
                                                                                                                                     
    "gpt-6.1-sol": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/oline-keys/openrouter_openai_gpt-6.1-sol.key",
                        api_model="openai/gpt-6.1-sol", cache=False, think_mode="details", prices=(2.50, 10.0, 0.10, 2.50),
                        list_price=True, stream_guard=True),                                                                
                                                                                                                                    
                                                                                                                                        
                                                                                                                     
    "deepseek-v4.1-flash-or": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/openrouter_api_key",
                                   api_model="deepseek/deepseek-v4.1-flash", cache=False, think_mode="none", prices=(0.02, 0.891, 0.005, 0.02),
                                   list_price=True, stream_guard=True, min_cap=40000),
                                                                                                                                       
                                                                                                                                                 
    "opus-5.5": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/openrouter_api_key",
                     api_model="anthropic/claude-opus-5.5", cache=True, think_mode="details", prices=(4.00, 20.0, 0.20, 5.00),
                     list_price=True),
    "gpt-6.1-sol-main": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/openrouter_api_key",
                             api_model="openai/gpt-6.1-sol", cache=False, think_mode="details", prices=(2.50, 10.0, 0.10, 2.50),
                             list_price=True, stream_guard=True),
                                                                                                                                  
                                                                                                                                              
                                                                                                                       
    "gemini-4-argon": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/openrouter_api_key",                                      
                           api_model="google/gemini-4-argon", cache=False, think_mode="details", prices=(2.00, 10.0, 0.10, 2.00),
                           list_price=True, stream_guard=True),
                                                                                                                                       
                                                                                                                                         
                                                                                                                                             
                                                                                                         
    "kimi-k3-or": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/openrouter_api_key",
                       api_model="moonshotai/kimi-k3", cache=False, think_mode="details", prices=(0.84, 15.0, 0.30, 0.84),
                       stream_guard=True,
                       extra_body={"provider": {"order": ["inference-net/fp4", "relace/fp4", "wafer", "sail-research/fp4"],
                                                "allow_fallbacks": False, "require_parameters": True}}),
                                                                                                                                        
                                                                                                                                      
                                                                                                                                         
                                                           
    "kimi-k3-max": dict(base_url="https://openrouter.ai/api/v1", key="~/.config/vexorium/openrouter_api_key",
                        api_model="moonshotai/kimi-k3", cache=False, think_mode="details", prices=(0.84, 15.0, 0.30, 0.84),
                        stream_guard=True, adaptive_cap=64000, adaptive_min=6000, continue_on_length=True,
                        extra_body={"provider": {"order": ["sail-research/fp4", "relace/fp4", "wafer", "inference-net/fp4"],
                                                 "allow_fallbacks": False, "require_parameters": True}}),
    "deepseek-v4.1-flash": dict(base_url="https://api.cline.bot/api/v1", key="~/.config/vexorium/cline_api_key",
                                api_model="cline-pass/deepseek-v4.1-flash", cache=False, think_mode="none", prices=(0.30, 1.20, 0.006, 0.30),
                                stream=True, min_cap=40000, list_price=True),                                                                   
}


                                                                                                                                     
                                                                                                                                
                                                                                                                                        
                                                                                                                                       
                                                                                                                                          
                                                                                                                                         
                                                                                                                                              
                                                                                                                                              
                                          
AZURE_CONFIG = Path("~/.config/vexorium/azure_ai.json").expanduser()
AZURE_TEMPLATES = {
    "sol": dict(cache=False, think_mode="responses", prices=(2.50, 10.0, 0.10, 2.50), list_price=True, stream_guard=True),
                                                                                                                                    
                                                                                                       
    "deepseek-flash": dict(cache=False, think_mode="none", prices=(0.02, 0.891, 0.005, 0.02), list_price=True, stream_guard=True,
                           min_cap=24000, no_effort=True),
    "opus": dict(cache=True, think_mode="details", prices=(4.00, 20.0, 0.20, 5.00), list_price=True),
                                                                                                                                          
                                                                                   
    "kimi": dict(cache=False, think_mode="none", prices=(0.84, 15.0, 0.30, 0.84), list_price=True, stream_guard=True),
                                                                                                                                          
                                                                                                                                       
    "glm": dict(cache=False, think_mode="none", prices=(0.60, 4.80, 0.11, 0.60), list_price=True, stream_guard=True),
                                                                                                                                
                                                                                                                                    
                                                                                                                                   
    "deepseek-pro": dict(cache=False, think_mode="none", prices=(0.9553, 1.9105, 0.0796, 0.9553), list_price=True, stream_guard=True,
                         min_cap=24000),
}

                                                                                                                                        
                                                                                                                                           
                                                                                                                                         
                                                                                                                                       
                                                                                                                                          
                                                                                                                                        
                                                                    
VERTEX_PROXY = "http://172.17.0.1:18190/v1/projects/lean-refactor/locations/global/endpoints/openapi"
MODEL_PRESETS["gemini-4-argon-vertex"] = dict(base_url=VERTEX_PROXY, key="~/.config/vexorium/vertex/proxy_key", api_model="google/gemini-4-argon",
                                              cache=False, think_mode="none", prices=(2.00, 10.0, 0.10, 2.00), list_price=True, stream_guard=True)
                                                                                                                                            
                                                                                                                                         
MODEL_PRESETS["opus-5.5-vertex"] = dict(base_url="http://172.17.0.1:18190/v1", key="~/.config/vexorium/vertex/proxy_key", api_model="claude-opus-5-5",
                                        cache=False, think_mode="none", prices=(4.00, 20.0, 0.20, 5.00), list_price=True, anthropic_vertex="global")


def _azure_presets() -> dict:
    try:
        c = json.loads(AZURE_CONFIG.read_text())
    except Exception:                                               
        return {}
    def _base(ep: str) -> str:
        ep = ep.rstrip("/")
        return ep if ep.endswith("/openai/v1") else ep + "/openai/v1"
    out = {}
    for alias, dep in (c.get("deployments") or {}).items():
        if alias not in AZURE_TEMPLATES or not dep:
            continue
                                                                                                                            
        d = dep if isinstance(dep, dict) else {"name": dep}
        out[f"{alias}-azure"] = dict(AZURE_TEMPLATES[alias], base_url=_base(d.get("endpoint") or c["endpoint"]),
                                     key=d.get("key") or "~/.config/vexorium/azure_ai_api_key", api_model=d["name"])
    return out


MODEL_PRESETS.update(_azure_presets())


RECLAIM_FLOOR = 2000                                                                                                                    


def fit_output_cap(budget: float, spend: float, fixed_usd: float, out_price: float, cap: int, floor: int,
                   min_reserve: float = 0.0) -> tuple[int | None, float | None]:
    """2026-10-22 (lever 5, budget reclaim; also the review's pre-call gate): the largest output cap n <= cap whose worst case fits,



"""
    cap, floor = int(cap), int(floor)
    if not spend + min_reserve <= budget or not spend + fixed_usd <= budget:                           
        return None, None
    n = cap if out_price <= 0 else min(cap, int((budget - spend - fixed_usd) * 1e6 / out_price))
    for _ in range(8):                                                                                                 
        if n < 0:
            break
        r = max(fixed_usd + n * out_price / 1e6, min_reserve)
        if spend + r <= budget:
            return (n, r) if n >= max(1, min(floor, cap)) else (None, None)
        n -= 1
    return None, None


def preset_gate(spend: float, budget: float, ctx_tokens: int, prices: tuple, cap_full: int, turn_max: float, reclaim: bool = False,
                floor: int = RECLAIM_FLOOR) -> tuple[float, int | None]:
    """The per-turn hard cap gate of a fixed-cap preset session, as one pure function (run_problem's gate; harness/test_budget_cap.py).




"""
    pi, po, _pr, pw = prices
    reserve = max((ctx_tokens * max(pi, pw) + cap_full * po) / 1e6, 1.25 * turn_max)
    if reclaim and spend + reserve > budget:
        n, r = fit_output_cap(budget, spend, ctx_tokens * max(pi, pw) / 1e6, po, cap_full, floor, 1.25 * turn_max)
        if n is not None:
            return r, n
    return reserve, None


def maybe_billed(e: BaseException) -> bool:
    """A failed API attempt the provider may still have billed: a transport error (read timeout, a stream that broke after the request was
"""
    st = getattr(e, "status_code", None)
    if getattr(e, "not_sent", False) or _connect_failure(e):                                                                                      
        return False
    return not getattr(e, "rate_limit_exhausted", False) and not (isinstance(st, int) and 400 <= st < 500)


def _connect_failure(e: BaseException) -> bool:
    """b66 (A4): llm/openai_compat.connect_failure (imported lazily: agent.py's other endpoints do not load the module)."""
    try:
        from llm.openai_compat import connect_failure
    except ImportError:
        return False
    try:
        return connect_failure(e)
    except Exception:                                                                                       
        return False


TOKEN_RULES = ("\n\nTOKEN COUNTING (the scorer's lexer: every bracket, comma, paren and operator is a token; a dotted name like Foo.bar_baz is ONE token). "
           "Measured: `⟨a, b⟩` 5 vs `And.intro a b` 3; `exact ⟨_, h⟩` 6 vs `exact .intro _ h` 4; `obtain ⟨a, b⟩ := h` 8 vs using `h.1`/`h.2`; "
           "`refine ⟨?_, ?_⟩` 6 vs `constructor` 1; `fun x => h x` 5 vs `h` 1; `intro x; exact h x` 6 vs `exact h` 2; `by exact h` 3 vs `h` 1; "
           "`rw [h]; exact h2` 7 vs `rwa [h]` 4; `simp at h; exact h` 6 vs `simpa using h` 3; `apply foo; exact bar` 5 vs `exact foo bar` 3; "
           "`simp only [a, b] at h ⊢` 10 vs `simp_all [a, b]` 6; `f (g x)` vs `f $ g x` saves 1 (`<|` saves 0); `fun x => e` vs `λx => e` saves 1 (write `λx` with no space: Lean reads it as `λ x`, the lexer counts `λx` as one token; also `λ_ =>`, `λx y =>`); each lemma in a hint list costs ~2. "
           "The big wins are still whole blocks replaced by one closer (`grind [lemmas]`, `simp_all`, `omega`, `fun_prop`, `aesop`) — most of a block's tokens.")
SYSTEM += TOKEN_RULES
LEVER_REVIEW = ("\n\nLEVER REVIEW FIRST (what broke the closed lines' plateau: a review that names exact edits, then one batch of compiles). Before "
                "any rewrite: (1) read best.lean line by line against this checklist and write up to 6 LEVERS in notes.md, each an exact edit with "
                "its expected effect on tokens and heartbeats: a hypothesis the goal never uses (drop it before an induction, so the induction "
                "hypotheses stay simple); the same tactic run repeated across cases (`all_goals`/`any_goals`, `<;>`); `<;> first | A | B` "
                "(as `any_goals A` then `all_goals B`); hand-written side conditions (into the `simp only` list or a discharger); an expensive "
                "closer tried on goals a cheap one closes (`assumption` or `exact h` first); `show`/`change`/`unfold` lines that only restate the "
                "goal. (2) Test ALL levers in ONE lean_check_variants call, one lever per "
                "variant, each applied to the best. (3) Combine the winners in a second batch. Only when the levers are spent, go on with the plan above.")
SYSTEM += ("\n\nLENGTH IS OFTEN THE MISSING AXIS. After any new "
           "compiling skeleton, call lean_mine once: it finds which blocks a single automation call closes. Then rewrite the remaining long blocks.")

def _is_scout(r: dict) -> bool:
    """POC 2 scout runs (short, from the reference) are exploration, not resumed history: adaptive budgets, plateau and fresh-start
"""
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
    ap.add_argument("--open-card", default=None, help="2026-10-31 (p85b; harness/open_package.py --dialect-card on passes the shipped harness/open_card_dialect.md): append this generic card (the same text for every row) to the opening message; honoured under --open-package (not one of the inputs it turns off); a missing file is reported and skipped")
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
    ap.add_argument("--upstream-history", dest="upstream_history", action=argparse.BooleanOptionalAction, default=False,
                    help="compliance switch (R2). OFF by default since 2026-10-21 (operator: off for the smoke, the A/B and the final): without it "
                         "no upstream digest, no git-history hint in the prompt or the shell tool description, and git log/show blocked in the shell "
                         "tool; --upstream-history restores the old behaviour (--no-upstream-history still accepted)")
    ap.add_argument("--no-budget-forcing", dest="budget_forcing", action="store_false", default=True, help="self-hosted endpoint: do not rescue turns that hit the cap while thinking (budget forcing, on by default)")
    ap.add_argument("--strategy", choices=["none", "hardtail"], default="none", help="hardtail: goal map tool (lean_goals) + map/lemma-search/restructure protocol with a 70%% token target, for problems flat after many passes")
    ap.add_argument("--think-prompt", choices=["off", "structural", "all"], default="off",
                    help="prompt-based thinking budget (self-hosted servings ignore the effort label): append a THINK LONGER instruction to the "
                         "opening message and re-inject it every 6 turns — in structural/fresh-start runs ('structural') or every run ('all')")
    ap.add_argument("--max-api-retries", type=int, default=6, help="attempts per API call on transport errors, backoff 10 s doubling to 300 s (20 ≈ 1.5 h tolerance for a paused interruptible instance)")
    ap.add_argument("--rate-limit-budget", type=float, default=float(os.environ.get("LRA_RATE_LIMIT_BUDGET_S", "1800")), help="--endpoint openai: seconds of wall time one call may spend on HTTP 429 "
                    "rate-limit / capacity rejections (server retry-after honoured, else 15 s doubling to 120 s), separate from the transport "
                    "retries; then the session ends (default $LRA_RATE_LIMIT_BUDGET_S or 1800)")
    ap.add_argument("--extra-body-json", default=None, help="--endpoint openai: JSON merged into the request body (e.g. provider pins, chat_template_kwargs)")
    ap.add_argument("--quant", default="nvfp4", help="OpenRouter provider quantization to pin (nvfp4 | fp4 | fp8); only with --endpoint openrouter")
    ap.add_argument("--run-id", default=time.strftime("agent-%Y%m%d-%H%M%S"))
    ap.add_argument("--fresh", action="store_true", help="discard the per-problem persistent state and start from the reference")
    ap.add_argument("--work-root", default="harness/work", help="per-problem state root (use a separate root for model comparisons)")
    ap.add_argument("--adaptive-turns", action="store_true", default=True, help="20 turns if best>=80, 60 if best<45 (--adaptive-low-turns), else 40 (default on)")
    ap.add_argument("--adaptive-low-turns", type=int, default=ADAPTIVE_LOW_TURNS, help="2026-10-30: the adaptive rule's turn budget for a session starting below "
                    "45 (default 60 = the rule as before; the open package passes 90 for long rows); no effect with --no-adaptive-turns")
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
                    "Default off: the 2026-10-11 A/B rejected it (cost 113%%, score -3.29)")                                           
    ap.add_argument("--budget-usd", type=float, default=2.85, help="with --model-preset: per-problem spend cap, a hard bound (operator 2026-10-11: $2.85; audit limit $3)")
    ap.add_argument("--budget-reclaim", action="store_true", help="2026-10-22 (lever 5): with --model-preset (fixed output cap), when the "
                    "next turn's worst case at the full cap no longer fits the budget, shrink its output cap to what the budget can pay for "
                    "in the same worst case (context uncached at list price + the shrunk cap) instead of ending the session; it ends only "
                    "below --reclaim-floor tokens. A failed attempt that may have been billed is charged its worst case before the retry. "
                    "spend + worst case <= budget still holds by construction. Off by default")
    ap.add_argument("--reclaim-floor", type=int, default=RECLAIM_FLOOR, help="--budget-reclaim: the smallest output cap a turn is shrunk "
                    "to (tokens)")
    ap.add_argument("--budget-milestones", default="2.0", help="with --model-preset: comma-separated spend levels whose crossing is recorded per problem (state.json budget_milestones, trajectory event, warning line)")
    ap.add_argument("--lever-review", action="store_true", help="cycle 88: on a problem whose last two runs gained < 3, open with a LEVER REVIEW "
                    "(a checklist of general edits -> up to 6 levers -> one lean_check_variants batch -> combine); off until a z.ai A/B")
    ap.add_argument("--auto-brief", default=None, metavar="DIR", help="2026-10-14 (harness/autobrief.py; docs/auto_brief_plan.md): DIR/<ws>.json "
                    "measured on this row's seed in this run (CPU only): its brief goes into the opening and its start candidate is checked "
                    "and adopted when better than the workspace best; off by default")
    ap.add_argument("--auto-brief-wait", type=float, default=None, metavar="SECONDS", help="2026-10-22 (hx_heldout --auto-brief-pipeline; "
                    "harness/brief_gate.py): with --auto-brief, the brief is still being made in the background: a row's session starts only "
                    "when DIR/<ws>.json exists, or the brief process has ended (DIR/.brief_ended), or SECONDS after this batch started; rows "
                    "whose brief is ready first, in --problems order, at most --workers at once; off by default")
    ap.add_argument("--tool-allow", default=None, metavar="NAMES", help="2026-10-24 (open-track re-derivation traces, docs/open_tools_rederive.md section 4): comma-separated tool names offered to the model (read_file, write_file and finish are always kept); off = every tool as before")
    ap.add_argument("--pattern-cards", action="store_true", help="2026-10-13 (harness/pattern_cards.py): general, pattern-keyed knowledge distilled from the theorem-keyed briefs (no problem names, no problem-local identifiers), selected by the shape of the statement and proof; off by default")
    ap.add_argument("--heartbeat-first", action="store_true", help="2026-10-13 (docs/competitor_rma.md): the HEARTBEAT_FIRST card with the "
                    "technique cards and heartbeat-aware cards / scout / structural / heartbeat briefs / closed lessons / lever review on problems "
                    "whose stored best has H points left >= L points left (always before a measured best); the system prompt's AUTOMATION FIRST "
                    "closers, LENGTH paragraph and lean_mine description become axis-conditional for the whole run (harness/cards.py HB_REWRITES), "
                    "so the A/B unit is the flag, not the gate; off until an A/B")
    ap.add_argument("--failed-moves", action="store_true", help="2026-10-13 (docs/opus_pass2_deep_dive.md §3: repeats of an already-seen error "
                    "rose to 56%% of failing checks by pass 5): every failed check records its edit against the closer of best / reference as a "
                    "move (state.json attempts[].move), and the opening message lists the REFUTED MOVES (harness/cc_levers.failed_moves_block: "
                    ">= 2 real compile refutations from separate tool calls, reopened when the best changes in the lines they touch); off until an A/B")
    ap.add_argument("--mode", choices=["default", "golf"], default="default", help="B62c (harness/golf.py, docs/scaffold_panel.md): golf = start from "
                    "the stored best measured in this session, the golf prompt and tools (lean_batch, hb_profile, pool), paired exact acceptance "
                    "(scorer/accept.py) and the harness stop rule; the knowledge sections of the default opening are not used. Off by default")
    ap.add_argument("--golf-min-evals", type=int, default=90, help="golf stop rule: finish is refused before this many evaluations")
    ap.add_argument("--golf-flat-evals", type=int, default=40, help="golf stop rule: ... and before this many evaluations without a banked gain")
    ap.add_argument("--golf-jobs", type=int, default=3, help="golf: concurrent compiles in one lean_batch (memgate still gates each)")
    ap.add_argument("--golf-batch-max", type=int, default=12, help="golf: items per lean_batch call")
    ap.add_argument("--pool", action="store_true", help="B62a: append every compiling candidate (full text, exact provisional score) to "
                    "<work root>/<problem>/pool.jsonl for the end stage; golf turns it on")
    ap.add_argument("--name-neighbors", action="store_true", help="L1 (2026-10-22; harness/name_neighbors.py): an `unknown identifier` / "
                    "`unknown constant` error in a lean_check / lean_run / lean_check_variants result gets up to 8 real constants near the name "
                    "from the row's own environment (listed by Lean at run time, one-line signatures, cached under <work root>/.name_neighbors), "
                    "and the opening lists the names earlier sessions found missing (<workspace>/missing_names.json); off until a held-out A/B")
    ap.add_argument("--name-neighbors-queries", type=int, default=10, help="--name-neighbors: Lean processes per session (each about one "
                    "compile; the disk cache answers repeats without one)")
    ap.add_argument("--compact-tool-json", action="store_true", help="b65: tool results as compact JSON with unicode kept (fewer input tokens); off = byte-identical to before")
    ap.add_argument("--skeleton-combinator-holes", action="store_true", help="b64 L1 (harness/goals.py _TACTIC_CTX_COMB): lean_skeleton reads a "
                    "`sorry` after all_goals / any_goals / try / repeat / iterate / focus / a first alternative as a tactic hole (the default "
                    "reading writes a term hole there, which does not parse); off by default")
    ap.add_argument("--open-package", action="store_true", help="2026-10-27 (docs/open_package_audit.md): the open-track package mode: the "
                    "open model on --endpoint openai (a local OpenAI-compatible server) with no TAINTED or UNCLEAR prompt material: the "
                    "2026-10-06 system prompt (SYSTEM_OPEN), the OPEN_TOOLS tool set, no technique / pattern cards, habits, briefs, auto-brief, "
                    "library leads, structural / heartbeat / lever / scout / hard-tail blocks, axis signal, winning-edits ledger, dead names, "
                    "unverified-claims block, upstream history or bank sync")
    ap.add_argument("--blind-start", action="store_true", help="2026-10-31 (operator; docs/open_blind_start.md; --open-package and --fresh "
                    "only, i.e. a row's first session): candidate.lean starts as the statement with a `sorry` body, the opening carries a facts "
                    "sheet of the reference (harness/blind_facts.py: names and numbers, no proof text) instead of the reference, which stays the "
                    "banked best and is shown only when nothing of the session's own is banked after a third of its turns (or at a finish before "
                    "that); shell reads of the problem's source file / name are logged as violations (counted, not blocked). Off by default")
    ap.add_argument("--rows", default=None, help="rows JSONL (default data/benchmark_warmup.jsonl); the open package passes its bundled "
                    "problem file and sets LRA_ROWS_FILE for harness/leantools")
    ap.add_argument("--heartbeats", default=None, help="reference heartbeats JSONL for --rows (default data/benchmark_heartbeats.jsonl)")
    args = ap.parse_args()
    global _TOOL_JSON_COMPACT
    _TOOL_JSON_COMPACT = bool(getattr(args, "compact_tool_json", False))
    if args.open_package:                                                                                                
        if args.model_preset or args.endpoint != "openai" or args.mode != "default":
            raise SystemExit("--open-package runs the open model on --endpoint openai (a local OpenAI-compatible server) in the default "
                             "mode, without --model-preset")
        for _f in ("closed_lessons", "pattern_cards", "heartbeat_first", "term_card", "length_tools", "token_rules", "lever_review",
                   "failed_moves", "from_reference", "upstream_history", "bank_sync", "name_neighbors", "normalize", "variant_scores",
                   "relative_error_lines", "lean_io", "pool", "budget_reclaim", "simp_prune"):
            setattr(args, _f, False)
        args.brief, args.brief_dir, args.auto_brief, args.auto_brief_wait, args.strategy = "none", None, None, None, "none"
        globals()["SYSTEM"] = globals()["SYSTEM_BASE"] = SYSTEM_OPEN
        TOOLS[:] = [t for t in TOOLS if t["name"] in OPEN_TOOLS]
        for _t in TOOLS:                                                                                                 
            if _t["name"] in OPEN_TOOL_DESCRIPTIONS:
                _t["description"] = OPEN_TOOL_DESCRIPTIONS[_t["name"]]
        print("open package: SYSTEM_OPEN, tools " + ", ".join(t["name"] for t in TOOLS) + "; cards, habits, briefs, leads, axis off", flush=True)
    if args.blind_start:                                                                        
        if not args.open_package:
            raise SystemExit("--blind-start is an --open-package option (docs/open_blind_start.md)")
        if not args.fresh:
            print("blind start: only a --fresh session (the row's first) starts blind; this one starts as usual", flush=True)
            args.blind_start = False
        else:
            globals()["SYSTEM"] = globals()["SYSTEM_BASE"] = blind_system(SYSTEM_OPEN)
            blind_tools(TOOLS)
            print("blind start: the statement + facts sheet, the reference withheld until a third of the turns", flush=True)
    if args.lean_io is None:                                                                                                                     
        args.lean_io = False
    if args.model_preset:                                                                
        _pr = MODEL_PRESETS[args.model_preset]
        if _pr.get("anthropic_vertex"):
            raise SystemExit(f"{args.model_preset} is a reviewer preset (harness/architect.call); agent sessions on it are not wired")
        args.endpoint, args.base_url, args.api_model = "openai", _pr["base_url"], _pr["api_model"]
        args.api_key_file = _pr["key"]
        if os.environ.get("LRA_SELFTEST_PRESET_URL"):                                                                                
            args.base_url, args.api_key_file = os.environ["LRA_SELFTEST_PRESET_URL"], None
        args.budget_forcing = False                                                    
        if args.model == "glm-5.3-flash":
            args.model = args.model_preset
        if args.work_root == "harness/work":
            raise SystemExit("--model-preset needs its own --work-root (never the Flash main line's harness/work)")
    if args.token_rules:
        globals()["SYSTEM_BASE"] = SYSTEM_BASE + TOKEN_RULES
    if args.heartbeat_first:                                                                                                                              
        from harness import cards as _cards
        globals()["SYSTEM"] = _cards.heartbeat_aware(SYSTEM); globals()["SYSTEM_BASE"] = _cards.heartbeat_aware(SYSTEM_BASE)
        for _t in TOOLS:                                                                                          
            _t["description"] = _cards.heartbeat_aware(_t["description"])
    if not args.upstream_history:                                                                                                     
        for _t in TOOLS:
            if _t["name"] == "shell":
                _t["description"] = _t["description"].replace(", `git log -p`/`git show` on the problem's file in the project clone to find how the "
                                                               "same proof was later simplified upstream", "")
    if args.mode == "golf":                                                                                     
        for _f in ("closed_lessons", "pattern_cards", "heartbeat_first", "term_card", "length_tools", "lever_review", "failed_moves", "from_reference",
                   "adaptive_turns", "normalize", "simp_prune", "variant_scores", "name_neighbors"):
            setattr(args, _f, False)
        args.auto_brief, args.brief, args.brief_dir, args.strategy, args.relative_error_lines, args.pool = None, "none", None, "none", True, True
        globals()["SYSTEM"] = globals()["SYSTEM_BASE"] = G.system_prompt(args.golf_batch_max, args.golf_min_evals, args.golf_flat_evals)
        _keep = ("read_file", "write_file", "lean_check", "lean_run", "lean_goals", "shell")
        TOOLS[:] = [t for t in TOOLS if t["name"] in _keep] + G.tools(args.golf_batch_max) + [
            {"name": "finish", "description": "End the session. Refused until the stop rule in the system prompt is met or the budget is nearly spent.",
             "input_schema": {"type": "object", "properties": {"summary": {"type": "string"}}}}]
    if args.tool_allow:                                                                                                                        
        _allow = {x.strip() for x in args.tool_allow.split(",") if x.strip()} | {"read_file", "write_file", "finish"}
        _unknown = _allow - {t["name"] for t in TOOLS}
        if _unknown:
            raise SystemExit(f"--tool-allow: unknown tool(s) {sorted(_unknown)}")
        TOOLS[:] = [t for t in TOOLS if t["name"] in _allow]
    rows = {json.loads(l)["name"]: json.loads(l) for l in (Path(args.rows) if args.rows else ROOT / "data/benchmark_warmup.jsonl").open() if l.strip()}
    hbs = {json.loads(l)["name"]: json.loads(l)["heartbeat"] for l in (Path(args.heartbeats) if args.heartbeats else ROOT / "data/benchmark_heartbeats.jsonl").open() if l.strip()}
    out_dir = ROOT / "probe/runs" / args.run_id; out_dir.mkdir(parents=True, exist_ok=True)
    names = args.problems or list(rows)
    print(f"run {args.run_id}: {len(names)} problems, model={args.model}, turns≤{args.turns}", flush=True)
    if args.auto_brief and args.auto_brief_wait is not None:                                                                                
        from harness.brief_gate import run_gated
        res = run_gated(names, args.workers, lambda n: run_problem(n, args, rows, hbs, out_dir), ROOT / args.auto_brief, args.auto_brief_wait)
    else:
        with ThreadPoolExecutor(args.workers) as ex:
            res = list(ex.map(lambda n: run_problem(n, args, rows, hbs, out_dir), names))
    (out_dir / "summary.json").write_text(json.dumps(res, indent=1))
    print("done", flush=True)


if __name__ == "__main__":
    main()
