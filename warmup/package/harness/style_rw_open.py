#!/usr/bin/env python3
"""Open-track style rewrite step (2026-10-30; docs/open_style_step.md). Operator 2026-10-30 ~19:30 UTC: "Yes, build the style step now"








































"""
from __future__ import annotations

import argparse, base64, hashlib, json, math, os, queue, re, sys, threading, time, traceback, zlib
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:                                                                                
    sys.path.insert(0, str(ROOT))

TAG = "style_rw"
EXEMPLARS_PATH = ROOT / "harness" / "style_rw_open_exemplars.json"
EXEMPLARS_SHA16 = "3ed15491e0b5b09a"                                                                                                         
WALL_S = 900.0                                                             
STAGE_SECONDS = 7200.0                                                                                                 
STAGE_MIN_START_S = 300.0                                                                 
MAX_TOKENS = 7000                                                                                    
EFFORT = "default"                                                                                                                    
                                                                                                                                       
                                                                                                                                        
EFFORTS = ("default", "low", "high", "max")
K_CANDS, MAX_REPAIRS = 4, 2
OTHER_UNITS = 1                                                                         
UNIT_JACCARD = 0.6                                                                    
UNIT_MARGIN = 2.5                                              
POLISH_MARGIN = 2.5                                                                                       
MIN_GAIN = 0.05                                                 
CALL_MIN_LEFT_S = 240.0                                                                                                       
CALL_READ_MIN_S = 60.0                                                                                     
POLISH_MIN_S = 60.0                                                                                            
POST_READS = 4.0                                                                                                      
POST_MIN_S = 60.0
MEASURE_MIN_S = 20.0                                                                                
GOAL_MIN_LEFT_S = 420.0                                                                        
RECORD_RESERVE_S = 10.0                                                                                             
CAND_JOBS = 3                                                                                                                          
MAX_DECL_CHARS = 30000                                                        
DISTINCT_MIN_CHARS = 20                                                                                  
STATUSES = ("improved", "kept", "skipped", "stopped", "error")
RETRY = ("skipped", "error")                                                                                      
_LOCK = threading.Lock()
_LEAN_SEM = threading.Semaphore(2)                                                                                         


                                                                                                                                          
def sha16_text(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()[:16]


def row_sha(name: str) -> str:
    """How the exemplar file names a pair's row (the file carries no row name)."""
    return sha16_text(name)


def exemplars_sha(path: Path = EXEMPLARS_PATH) -> str:
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()[:16]


def encode_pairs(pairs: list[dict]) -> str:
    """The pairs as the shipped file stores them ("pairs_z"): zlib + base64 of their JSON. Review 2026-10-30: the pairs are compiled


"""
    return base64.b64encode(zlib.compress(json.dumps(pairs, ensure_ascii=False).encode(), 9)).decode()


def decode_pairs(d: dict) -> list[dict]:
    """The pairs of an exemplar file's JSON: "pairs_z" (encode_pairs, the shipped form) or "pairs" (plain, dev only)."""
    if isinstance(d.get("pairs_z"), str):
        return json.loads(zlib.decompress(base64.b64decode(d["pairs_z"])).decode())
    return d["pairs"]


def load_exemplars(sha: str | None, path: Path = EXEMPLARS_PATH) -> list[dict]:
    """The exemplar pairs; raises when the file's sha is not `sha` (the frozen flag) or a pair is not usable (both sides verified, Z 100,
"""
    from scorer.forbidden import check_forbidden
    path = Path(path)
    have = exemplars_sha(path)
    if sha and have != sha:
        raise RuntimeError(f"{path.name}: sha {have} differs from the frozen --style-rw-exemplars {sha}")
    d = json.loads(path.read_text())
    out = []
    for x in decode_pairs(d):
        m = x.get("measured") or {}
        b, a = m.get("before") or {}, m.get("after") or {}
        if not (x.get("id") and x.get("row_sha") and x.get("before", "").strip() and x.get("after", "").strip() and b.get("Z") == 100.0
                and a.get("Z") == 100.0 and float(a.get("score_exact", -1)) >= float(b.get("score_exact", 0))
                and check_forbidden(x["before"]) is None and check_forbidden(x["after"]) is None):
            raise RuntimeError(f"{path.name}: pair {x.get('id')} is not a usable exemplar")
        out.append(x)
    return out


GENERIC_WORDS = frozenset((
    "intro intros rintro introv obtain rcases cases induction constructor econstructor assumption exact exacts apply refine refine' "
    "rewrite rw rwa simp simp_all simpa simp_rw only using with at from show have this let suffices calc conv change convert congr "
    "unfold delta subst subst_vars generalize specialize exists exfalso contradiction omega decide trivial rfl linarith nlinarith "
    "norm_num positivity grind aesop ring ring_nf field_simp norm_cast push_cast exact_mod_cast push_neg by_cases by_contra split "
    "split_ifs funext ext all_goals any_goals repeat repeat' iterate first focus case case' next rotate_left rotate_right pick_goal "
    "unhygienic rename_i clear revert injection injections nofun nomatch choose use existsi left right symm trans fun_induction "
    "fun_cases solve_by_elim apply_rules assumption' trace_state skip done sorry admit match then else true false True False "
    "Nat Int List Finset Set Prop Type Option Function Classical Exists And Or Not Iff Eq Ne HEq id absurd Bool Fin Real").split())
_IDENT = re.compile(r"[^\W\d][\w'!?₀-₉ₛₗ]*(?:\.[^\W\d][\w'!?₀-₉ₛₗ]*)*")


def distinctive_lines(text: str) -> set[str]:
    """The lines of `text` (comments stripped, whitespace collapsed) that are at least DISTINCT_MIN_CHARS long and name an identifier
"""
    from scorer.forbidden import strip_lean_comments
    out = set()
    for l in strip_lean_comments(text or "").split("\n"):
        s = re.sub(r"\s+", " ", l).strip()
        if len(s) < DISTINCT_MIN_CHARS:
            continue
        if any(len(i) >= 5 and i not in GENERIC_WORDS and i.split(".")[-1] not in GENERIC_WORDS for i in _IDENT.findall(s)):
            out.add(s)
    return out


def _flat(s: str) -> str:
    return re.sub(r"\s+", " ", s or "").strip()


def exemplars_for(row: dict, pairs: list[dict], known: list[str] | None = None) -> tuple[list[dict], dict]:
    """(the pairs shown on `row`, {pair id: why dropped}). Dropped, per target: a pair of the row itself (its row sha, or the row's exact

"""
    from scorer.tokenize import split_declaration
    me = row_sha(row["name"])
    st = _flat(row.get("statement") or "")
    mine: set = set()
    for p in known or []:
        body = split_declaration(p or "", row["statement"]) if p else None
        mine |= distinctive_lines(body if body is not None else (p or ""))
    shown, dropped = [], {}
    for x in pairs:
        if x.get("row_sha") == me:
            dropped[x["id"]] = "the pair's row is the target"; continue
        if me in (x.get("exclude_rows") or []):
            dropped[x["id"]] = "excluded for the target by the leak check"; continue
        if st and (st in _flat(x["before"]) or st in _flat(x["after"])):
            dropped[x["id"]] = "the pair carries the target's statement"; continue
        common = mine & (distinctive_lines(x["before"]) | distinctive_lines(x["after"]))
        if common:
            dropped[x["id"]] = f"shares {len(common)} distinctive line(s) with the target's proofs"; continue
        shown.append(x)
    return shown, dropped


                                                                                                                                          
SYSTEM_RW = ("You are an expert Lean 4 proof golfer. You rewrite verified proofs into the shortest and cheapest form the scorer rewards, "
             "keeping their mathematical approach. You answer by calling submit_proofs once.")

DIALECT = """THE SCORING DIALECT (the moves below are what the shortest verified proofs of hard rows share; each appears in a compiled exemplar below):
1. `unhygienic`: `:= by unhygienic` (or `unhygienic` at the head of ONE tactic block) makes Lean's auto-generated names accessible, so names
   need not be written: bare `intro` / `intros` / `repeat' intro`, `cases h` and `induction h` with no `with` arms, `rcases h` with no pattern.
   The new hypotheses are then named as Lean prints them without the dagger: `a✝` is `a`, `a✝¹` is `a_1`, `h✝` is `h`, induction hypotheses
   `a_ih` / `ih` (the goal map below shows the daggered names). `‹_›` or `‹T›` uses an anonymous hypothesis.
   Caution: a top-level `unhygienic` breaks every `rename_i` of the proof ("too many variable names provided"): drop those `rename_i`
   (use the auto names) or scope `unhygienic` to the one block that needs it.
2. Positional case handling: `rotate_left k` / `rotate_right`, `case'`, `next =>`, or one combinator over all goals, instead of named
   `case foo x y =>` arms and bullets.
3. Uniform closers: one `all_goals` / `any_goals` / `<;>` block for cases that look alike; `repeat' constructor` to split conjunctions,
   existentials and inductive goals, then `assumption'` / `all_goals assumption` / one `exact`; `first | A | B` inside a combinator.
4. Pre-shaping instead of destructuring: a `.imp` call with a lambda on the hypothesis (`Exists.imp`, `And.imp`), `.1` / `.2`
   projections instead of `obtain ⟨..⟩ := h`, `choose` or `choose_spec.1`.
5. `exists` with the witnesses instead of `use` / `refine ⟨.., ?_⟩` (it tries `trivial` on what remains); `rewrite` instead of `rw` when
   no `rfl` is needed; `apply_rfl`.
6. Fewer tokens is the main lever on these rows; a dialect move that costs heartbeats (for example a combinator that tries a closer on
   many goals) pays only when its token saving is worth more (see the exchange rate).
7. Elaboration cost: `simp only [..]` over `simp`, `exact` over `apply` when the term is known, `(h : T)` ascriptions only where
   unification is slow; a heartbeat lever is worth taking when it does not add tokens."""

SUBMIT = [{"name": "submit_proofs", "description": "Submit complete Lean 4 declarations (the exact statement followed by := and a proof).",
           "input_schema": {"type": "object", "properties": {"proofs": {"type": "array", "items": {"type": "object", "properties": {
               "label": {"type": "string", "description": "short unique name"},
               "strategy": {"type": "string", "description": "one line: the dialect moves used"},
               "declaration": {"type": "string", "description": "the complete declaration: the exact statement, := and the proof"}},
               "required": ["label", "declaration"]}}}, "required": ["proofs"]}}]


def versions_of(row: dict) -> list[str]:
    from probe.verify_candidates import newest_first
    return list(newest_first(row["version_info"]))


def scoring_text(row: dict, ref_h: int | None) -> str:
    """The scoring rule with the row's own reference tokens and heartbeats (the package scores on the official reference heartbeats)."""
    ref_t = int(row["proof_length"])
    pins = versions_of(row)
    p_tok = 100.0 / (3 * ref_t)
    p_100hb = 100.0 * 100 / (3 * ref_h) if ref_h else None
    return (f"SCORING (one row): score = (L + H + Z) / 3 with L = 100 x (1 - tokens / {ref_t}) (Lean lexer tokens of the proof body after "
            f"`:=`), H = 100 x (1 - heartbeats / {ref_h}) (elaboration heartbeats of the declaration), Z = 100 x (share of the toolchains "
            f"{', '.join(pins)} on which it compiles; it must compile on all of them). Exchange rate: one token = {p_tok:.3f} points"
            + (f", 100 heartbeats = {p_100hb:.3f} points, so one token is worth {ref_h / ref_t:.1f} heartbeats" if p_100hb else "") + ".\n"
            + ("Toolchain note: `assumption'` is an unknown tactic on v4.26.0 (use `all_goals assumption` on this row).\n"
               if "v4.26.0" in pins else ""))


def exemplar_text(exs: list[dict]) -> str:
    out = ["EXEMPLARS (other theorems, not this one; each pair compiled and measured on every toolchain; the AFTER side is the dialect):"]
    for x in exs:
        m = x["measured"]; b, a = m["before"], m["after"]
        out.append(f"\n[{x['id']}] moves: {'; '.join(x['moves'])}\nBEFORE ({b['tokens']} tokens, {b['heartbeats']} heartbeats, score "
                   f"{b['score_exact']:.2f}):\n```lean\n{x['before'].strip()}\n```\nAFTER ({a['tokens']} tokens, {a['heartbeats']} heartbeats, "
                   f"score {a['score_exact']:.2f}):\n```lean\n{x['after'].strip()}\n```")
    return "\n".join(out) + "\n"


def goal_text(gm: dict | None) -> str:
    if not gm or not gm.get("steps"):
        return "GOAL MAP: (not available for this proof)\n"
    lines = ["GOAL MAP of the CURRENT PROOF (Lean's goal state before each step, keyed by the proof's line numbers, line 1 = the first "
             "line of the declaration; depth 2: also inside bullets / `=>` arms / `by` blocks):"]
    for s in gm["steps"]:
        lines.append(f"- line {s['line']} `{s['tactic'][:80]}` ({s.get('n_goals')} goal(s)):\n{s['goals']}")
    if gm.get("note"):
        lines.append(f"(note: {gm['note']})")
    return "\n".join(lines) + "\n"


def fmt(r: dict | None) -> str:
    if not r or not r.get("ok"):
        return "fails"
    return f"{r['tokens']} tokens, {r['heartbeats']} heartbeats, score {r['score_exact']:.2f}" + ("" if r.get("Z") == 100.0 else f" (Z {r.get('Z')})")


def token_rules() -> str:
    from harness.agent import TOKEN_RULES
    return TOKEN_RULES.strip()


def round_prompt(row: dict, ref_h, proof: str, reading: dict, gm: dict | None, exs: list[dict], rnd: int, results: list[dict] | None = None,
                 best: dict | None = None) -> str:
    parts = ["TASK: rewrite a verified Lean 4 proof into the scoring dialect, keeping its approach.\n\n" + scoring_text(row, ref_h) + "\n"
             + token_rules() + "\n\n" + DIALECT + "\n\n",
             f"STATEMENT (copy it exactly):\n```lean\n{row['statement'].rstrip()}\n```\n\n"
             f"CURRENT PROOF ({fmt(reading)}; it compiles on every toolchain):\n```lean\n", proof.strip(), "\n```\n\n" + goal_text(gm) + "\n",
             exemplar_text(exs) + "\n"]
    if rnd == 1:
        parts.append(f"YOUR TASK: rewrite the CURRENT PROOF into the dialect. Keep its approach: the same key lemmas and the same "
                     f"induction / case structure (you may merge or reorder cases and replace closers). Write {K_CANDS} complete "
                     "declarations (the exact statement, `:=`, the proof), from conservative (a few safe dialect moves) to "
                     "aggressive (every move that may apply), each aimed at fewer tokens than the CURRENT PROOF without losing "
                     "on heartbeats more than the tokens are worth. No sorry, admit, native_decide, axioms, auxiliary "
                     "declarations, `set_option` or `open` outside the proof. Call submit_proofs ONCE with the "
                     f"{K_CANDS} declarations.\n")
        return "".join(parts)
    res = ["ROUND 1 RESULTS (every candidate measured on every toolchain):"]
    for r in results or []:
        m = r.get("reading") or {}
        res.append(f"- {r['label']} ({r['origin']}): " + (fmt(m) if m.get("ok") and m.get("Z") == 100.0
                                                         else f"fails: {(r.get('error_short') or m.get('error') or '?')[:240]}"))
    parts.append("\n".join(res) + "\n\n")
    if best and best.get("decl") and best["decl"].strip() != proof.strip():
        parts += [f"BEST SO FAR ({fmt(best['reading'])}):\n```lean\n", best["decl"].strip(), "\n```\n\n"]
    else:
        parts.append("BEST SO FAR: the CURRENT PROOF (no round-1 candidate beat it).\n\n")
    parts.append(f"YOUR TASK (round 2): write {K_CANDS} NEW complete declarations that score higher than BEST SO FAR. Push the "
                 "moves that worked further, combine them, and avoid what failed. Same approach, same rules (no sorry, admit, "
                 "native_decide, axioms, auxiliary declarations). Call submit_proofs ONCE.\n")
    return "".join(parts)


def repair_prompt(row: dict, proof: str, cand: dict) -> str:
    return ("A rewrite of a verified Lean 4 proof into a shorter dialect failed to compile. Fix it with the smallest change: keep "
            "its dialect moves where they can work and undo only the move that breaks. Return ONE complete declaration (the exact "
            "statement, `:=`, the proof) by calling submit_proofs once. No sorry, admit, native_decide or axioms.\n\n" + DIALECT + "\n\n"
            f"STATEMENT (copy it exactly):\n```lean\n{row['statement'].rstrip()}\n```\n\nORIGINAL VERIFIED PROOF (the same approach; "
            "it compiles):\n```lean\n" + proof.strip() + "\n```\n\nFAILING REWRITE:\n```lean\n" + cand["decl"].strip()
            + f"\n```\n\nCOMPILER ERROR ({cand.get('error_pin') or 'primary toolchain'}):\n{cand.get('error_full') or cand.get('error_short') or '?'}\n")


                                                                                                                                          
def sha16(p: str) -> str:
    return hashlib.sha256(p.strip().encode()).hexdigest()[:16]


def normalize(decl, statement: str) -> tuple[str | None, str | None]:
    """(declaration on the exact statement, None) or (None, why). A re-typed statement is replaced by the exact one."""
    from scorer.tokenize import split_declaration
    if not isinstance(decl, str):
        return None, "the declaration is not text"
    d = decl.strip()
    d = re.sub(r"^```(?:lean4?)?\s*\n|\n```\s*$", "", d).strip()
    if not d:
        return None, "empty declaration"
    if len(d) > MAX_DECL_CHARS:
        return None, f"{len(d)} chars (over {MAX_DECL_CHARS})"
    if split_declaration(d, statement) is not None:
        return d, None
    k = statement.count(":=")                                                                                
    pos = -2
    for _ in range(k + 1):
        pos = d.find(":=", pos + 2)
        if pos < 0:
            return None, "no `:=` after the statement in the declaration"
    body = d[pos + 2:].lstrip(" ")
    nd = statement.rstrip() + " :=" + ("" if body.startswith("\n") else " ") + body
    return (nd, None) if split_declaration(nd, statement) is not None else (None, "statement differs")


                                                                                                                  
                                                                                                                                    
                                                                                                                                     
                                                                                                        
TOP_LEVEL = re.compile(r"(?m)^(theorem|lemma|example|def|abbrev|instance|axiom|namespace|section|end|open|set_option|attribute|noncomputable|"
                       r"private|protected|universe|variable|macro|syntax|elab|notation|infix|prefix|postfix|#\w+|@\[)(?![\w'.])")


def precheck(decl: str, statement: str | None = None) -> str | None:
    """The whole declaration against the forbidden-pattern list (the Arena's, as the export applies it), and (given the statement) no
"""
    from scorer.forbidden import check_forbidden
    bad = check_forbidden(decl)
    if bad:
        return f"forbidden: {bad}"
    if statement is not None:
        from scorer.tokenize import split_declaration
        body = split_declaration(decl, statement)
        m = TOP_LEVEL.search(body if body is not None else decl)
        if m:
            return f"forbidden: a top-level command after the proof ({m.group(0)})"
    return None


def features(decl: str) -> list[str]:
    f = []
    for k, rx in (("unhygienic", r"\bunhygienic\b"), ("rotate", r"\brotate_(left|right)\b"), ("repeat'", r"\brepeat'"),
                  ("assumption'", r"\bassumption'"), ("any_goals", r"\bany_goals\b"), ("all_goals", r"\ball_goals\b"),
                  ("imp", r"\.imp\b"), ("exists", r"(^|\s)exists\s")):
        if re.search(rx, decl, re.M):
            f.append(k)
    return f


def jaccard(a: str, b: str) -> float:
    from scorer.tokenize import tokens as lex
    try:
        sa, sb = set(lex(a)), set(lex(b))
    except Exception:                
        sa, sb = set(a.split()), set(b.split())
    return len(sa & sb) / max(1, len(sa | sb))


def is_verified(rd: dict | None) -> bool:
    return bool(rd and rd.get("ok") and rd.get("heartbeats") is not None and rd.get("Z") == 100.0 and isinstance(rd.get("score_exact"), (int, float))
                and math.isfinite(float(rd["score_exact"])))


def measure_full(meter, decl: str, timeout: float | None = None) -> tuple[dict, dict]:
    """(reading as endstage.Meter.measure gives it, {"pin", "errors"} of the first failing pin or {}): the compiles of
"""
    decl = decl.strip()
    if not all(hasattr(meter, a) for a in ("freeze", "_check", "_one", "_reading", "versions")):
        rd = meter.measure(decl, full=True, timeout=timeout)
        fail = {} if is_verified(rd) else {"pin": rd.get("fail_pin"), "errors": [rd.get("error") or "?"]}
        return rd, fail
    path = meter.freeze()
    bad = meter._check(decl)
    if bad:
        return {"ok": False, "error": bad, "compiles": 0, "meter": path}, {"pin": None, "errors": [bad]}
    n0 = meter.compiles
    meter._cand_timeout = timeout
    fail: dict = {}
    try:
        prim, _ = meter._one(decl, meter.versions[0], True, path)
        compat = None
        if not (prim.ok and prim.heartbeats is not None):
            fail = {"pin": meter.versions[0], "errors": list(prim.errors or [])}
        else:
            compat = {meter.versions[0]: True}
            for v in meter.versions[1:]:
                r, _ = meter._one(decl, v, False, path)
                compat[v] = bool(r.ok)
                if not r.ok and not fail:
                    fail = {"pin": v, "errors": list(r.errors or [])}
    finally:
        meter._cand_timeout = None
    return meter._reading(decl, prim, compat, None, path, meter.compiles - n0), fail


def repair_error(name: str, decl: str, fail: dict, primary: str, timeout: float = 600) -> tuple[str, str | None]:
    """(text, fault): the compiler error for the repair prompt. On the primary pin the declaration is recompiled through

"""
    lines = decl.split("\n")
    if fail.get("pin") is None:                                      
        return "\n".join(fail.get("errors") or []) or "(no error message)", None
    fault = None
    if fail.get("pin") == primary:
        try:
            from harness.lean_untrunc import lean_run
            with _LEAN_SEM:
                msgs = lean_run(name, decl, timeout=int(max(30, min(600, timeout))))
            out = []
            for x in [x for x in msgs if x.get("severity") == "error"][:3]:
                ln = int(x.get("line") or 0)
                src = lines[ln - 1].strip() if 1 <= ln <= len(lines) else ""
                out.append(f"line {ln}" + (f" (`{src[:120]}`)" if src else "") + f": {str(x.get('data'))[:1800]}")
            if out:
                return "\n\n".join(out), None
        except Exception as e:                                                                       
            fault = f"{type(e).__name__}: {str(e)[:200]}"
    return "\n\n".join(str(e)[:1800] for e in (fail.get("errors") or [])[:3]) or "(no error message)", fault


def goal_map(name: str, decl: str, total: int = 8000) -> dict:
    """The depth-2 goal map of a proof (harness/goals), depth 1 when Lean asks for it; a fault note on any failure (informational)."""
    try:
        from harness import goals as GO
        with _LEAN_SEM:
            gm = GO.goal_map(name, decl, depth=2, total=total)
            if not gm.get("steps") and gm.get("ok") is False and "Retry with depth 1" in (gm.get("note") or ""):
                gm = GO.goal_map(name, decl, depth=1, total=total)
        return gm if isinstance(gm, dict) else {}
    except Exception as e:                
        return {"ok": False, "note": f"goal map unavailable ({type(e).__name__}: {str(e)[:160]})"}


                                                                                                                                         
def _block(b):
    import dataclasses
    if dataclasses.is_dataclass(b):
        return {k: v for k, v in dataclasses.asdict(b).items() if v is not None}
    return b.model_dump(exclude_none=True) if hasattr(b, "model_dump") else str(b)


_DECL_RX = re.compile(r'"declaration"\s*:\s*"((?:[^"\\]|\\.)*)"', re.S)
_LEAN_BLOCK = re.compile(r"```(?:lean4?)?\s*\n(.*?)\n```", re.S)


def answer_proofs(m) -> tuple[list[dict], str | None]:
    """The declarations of one reply: the submit_proofs call's proofs (an argument string that is not JSON is read leniently, one
"""
    from llm.junk import junk_reason
    tools = [b for b in (getattr(m, "content", None) or []) if getattr(b, "type", None) == "tool_use"]
    text = "".join(getattr(b, "text", None) or "" for b in (getattr(m, "content", None) or []) if getattr(b, "type", None) == "text")
    out: list[dict] = []
    for b in tools:
        if getattr(b, "name", None) != "submit_proofs":
            continue
        inp = getattr(b, "input", None) or {}
        raw = inp.get("_raw_arguments") if isinstance(inp, dict) else None
        if isinstance(raw, str):
            j = junk_reason(raw)
            if j:
                return [], f"junk arguments: {j}"
            for i, s in enumerate(_DECL_RX.findall(raw)):
                try:
                    out.append({"label": f"c{i}", "declaration": json.loads('"' + s + '"')})
                except ValueError:
                    continue
            continue
        proofs = inp.get("proofs") if isinstance(inp, dict) else None
        if isinstance(proofs, str):                                                
            try:
                proofs = json.loads(proofs)
            except ValueError:
                proofs = None
        for i, p in enumerate(proofs if isinstance(proofs, list) else []):
            if isinstance(p, dict):
                out.append({"label": str(p.get("label") or f"c{i}")[:40], "declaration": p.get("declaration")})
            elif isinstance(p, str):
                out.append({"label": f"c{i}", "declaration": p})
    if not out and text:
        j = junk_reason(text)
        if j:
            return [], f"junk text: {j}"
        out = [{"label": f"t{i}", "declaration": d} for i, d in enumerate(_LEAN_BLOCK.findall(text))]
    if not out:
        stop = getattr(m, "stop_reason", None)
        return [], "no declarations" + (" (the output cap was reached: over-deliberation)" if stop == "max_tokens" else "")
    for d in out:
        if isinstance(d.get("declaration"), str):
            j = junk_reason(d["declaration"])
            if j:
                d["declaration"] = None; d["junk"] = j
    if not any(isinstance(d.get("declaration"), str) and d["declaration"].strip() for d in out):
        return out, "no usable declaration (empty, not text or junk)"
    return out, None


def request_extra(effort: str) -> dict:
    """The extra request body of the step's calls for an --effort value: "default" = thinking OFF (chat_template_kwargs enable_thinking

"""
    if effort == "default":
        return {"chat_template_kwargs": {"enable_thinking": False}}
    return {"reasoning_effort": effort}


class ModelError(Exception):
    """A call that failed after its retry (the step stops; the input stays)."""


class Caller:
    """The step's calls to the package's model (llm/openai_compat.create, the sessions' client). call() returns the submitted
"""

    def __init__(self, base_url: str, api_key: str, model: str, effort: str = EFFORT, max_tokens: int = MAX_TOKENS, log=print,
                 trajectory: Path | str | None = None, row: str = "", create=None, clock=time.time):
        self.base_url, self.api_key, self.model, self.effort, self.max_tokens = base_url, api_key, model, effort, int(max_tokens)
        self.log, self.row, self.clock = log, row, clock
        self.trajectory = Path(trajectory) if trajectory else None
        self._create = create
        self.calls: list[dict] = []
        self.lock = threading.Lock()

    def _trace(self, rec: dict) -> None:
        if self.trajectory is None:
            return
        try:                                 
            self.trajectory.parent.mkdir(parents=True, exist_ok=True)
            with _LOCK, self.trajectory.open("a") as f:
                f.write(json.dumps(rec, ensure_ascii=False, default=str) + "\n")
        except OSError:
            pass

    def _send(self, prompt: str, read_s: float, connect_s: float):
        from llm import openai_compat as OC
        extra = request_extra(self.effort)
        if self._create is not None:
            return self._create(prompt=prompt, max_tokens=self.max_tokens, read_s=read_s, system=SYSTEM_RW, tools=SUBMIT, extra_body=extra)
        return OC.with_connect_retry(lambda: OC.create(base_url=self.base_url, api_key=self.api_key, model=self.model, max_tokens=self.max_tokens,
                                                       system=SYSTEM_RW, tools=SUBMIT, messages=[{"role": "user", "content": prompt}],
                                                       extra_body=extra, timeout=(30, read_s)),
                                     budget_s=max(0.0, connect_s), log=self.log)

    def call(self, kind: str, prompt: str, deadline: float | None) -> list[dict]:
        t0 = self.clock()
        tr = {"t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "row": self.row, "kind": kind, "model": self.model,
              "effort": self.effort, "extra_body": request_extra(self.effort), "max_tokens": self.max_tokens, "system": SYSTEM_RW,
              "prompt": prompt}
        rec = {"kind": kind, "chars": len(prompt)}
        last = None
        for attempt in (1, 2):
            left = math.inf if deadline is None else deadline - self.clock()
            if attempt == 2 and left < CALL_MIN_LEFT_S:
                break
            read_s = max(CALL_READ_MIN_S, min(1800.0, left))
            try:
                m = self._send(prompt, read_s, min(left - CALL_READ_MIN_S, 1800.0) if math.isfinite(left) else 1800.0)
            except Exception as e:                                                                                 
                last = f"{type(e).__name__}: {str(e)[:300]}"
                st = getattr(e, "status_code", None)
                if isinstance(st, int) and 400 <= st < 500 and st not in (408, 429):                                           
                    break
                continue
            sub, why = answer_proofs(m)
            u = getattr(m, "usage", None)
            rec.update(seconds=round(self.clock() - t0, 1), attempt=attempt, stop=getattr(m, "stop_reason", None), n_proofs=len(sub),
                       output=getattr(u, "output_tokens", None), input=getattr(u, "input_tokens", None),
                       reasoning=getattr(u, "reasoning", None), noop=why)
            with self.lock:
                self.calls.append(rec)
            self._trace(dict(tr, reply=[_block(b) for b in (getattr(m, "content", None) or [])], stop=rec["stop"],
                             usage={k: rec.get(k) for k in ("input", "output", "reasoning")}, seconds=rec["seconds"], n_proofs=len(sub), noop=why))
            self.log(f"{TAG} {kind}: {len(sub)} declaration(s) in {rec['seconds']:.0f} s" + (f" (no-op: {why})" if why else ""))
            return sub
        rec.update(seconds=round(self.clock() - t0, 1), error=last or "no time for a retry")
        with self.lock:
            self.calls.append(rec)
        self._trace(dict(tr, error=rec["error"], seconds=rec["seconds"]))
        raise ModelError(rec["error"])


                                                                                                                                         
def other_units(incumbent: str, inc_score, cands: list[dict], k: int = OTHER_UNITS) -> list[dict]:
    """Up to k other verified proofs ({"proof", "score"} with a stored score) unlike the input (token Jaccard < UNIT_JACCARD) and within
"""
    pool = []
    for c in cands or []:
        p = (c.get("proof") or "").strip()
        s = c.get("score")
        if not p or p == incumbent.strip() or not isinstance(s, (int, float)) or not math.isfinite(float(s)):
            continue
        pool.append((float(s), p))
    pool.sort(key=lambda t: -t[0])
    top = float(inc_score) if isinstance(inc_score, (int, float)) else (pool[0][0] if pool else None)
    out: list[dict] = []
    for s, p in pool:
        if len(out) >= k or (top is not None and s < top - UNIT_MARGIN):
            break
        if jaccard(p, incumbent) >= UNIT_JACCARD or any(jaccard(p, o["proof"]) >= UNIT_JACCARD for o in out):
            continue
        out.append({"proof": p, "score": s})
    return out


class Step:
    """One row's step. Lean and the model are attributes, so tests replace them: `caller` (Caller-like: call(kind, prompt, deadline)),


"""

    def __init__(self, row: dict, ref_h, incumbent: str, exs: list[dict], caller, meter, audit, polish=None, log=print,
                 units: list[dict] | None = None, clock=time.time, deadline: float | None = None, meter_factory=None,
                 goal_map_fn=None, repair_error_fn=None):
        self.row, self.name, self.ref_h, self.exs = row, row["name"], ref_h, exs
        self.inc = incumbent.strip()
        self.caller, self.meter, self.audit, self.polish, self.log, self.clock = caller, meter, audit, polish, log, clock
        self.units = [{"proof": self.inc, "role": "input"}] + [dict(u, role="other") for u in (units or [])]
        self.primary = versions_of(row)[0]
        self.deadline = deadline
        self.goal_map_fn = goal_map_fn or goal_map
        self.repair_error_fn = repair_error_fn or repair_error
        self.meters: queue.Queue = queue.Queue()
        self.meters.put(meter)
        for _ in range(CAND_JOBS - 1 if meter_factory else 0):
            try:
                self.meters.put(meter_factory())
            except Exception:                                                         
                break
        self.cands: list[dict] = []
        self.cache: dict = {}
        self.clock_lock = threading.Lock()
        self.t0 = clock()
        self.read_s = 0.0
        self.rep: dict = {"units": [], "calls": 0, "cands": 0, "compiled": 0, "stopped": None}

    def rlog(self, m: str) -> None:
        self.log(f"{TAG}: {m}")

    def left(self) -> float:
        return math.inf if self.deadline is None else self.deadline - self.clock()

    def post_reserve(self) -> float:
        return max(POST_MIN_S, POST_READS * float(self.read_s or 0.0))

    def call_ok(self) -> bool:
        if self.left() < CALL_MIN_LEFT_S:
            self.rep["wall_stop"] = f"no new call: {max(0.0, self.left()):.0f} s left (a call needs {CALL_MIN_LEFT_S:g} s)"
            return False
        return True

    def call(self, kind: str, prompt: str) -> list:
        with self.clock_lock:
            self.rep["calls"] += 1
        return self.caller.call(kind, prompt, None if self.deadline is None else self.deadline - self.post_reserve())

                     
    def _measure_one(self, s, i: int, origin: str, timeout: float, unit: str) -> dict:
        d0 = s.get("declaration") if isinstance(s, dict) else s
        decl, why = normalize(d0, self.row["statement"])
        c = {"label": (s.get("label") if isinstance(s, dict) else None) or f"c{i}", "origin": origin, "unit": unit,
             "raw_chars": len(d0) if isinstance(d0, str) else 0}
        if decl is None:
            why = (s.get("junk") and f"junk: {s['junk']}") or why if isinstance(s, dict) else why
            c.update(decl=None, reading={"ok": False, "error": why}, error_short=why, error_full=why)
            return c
        bad = precheck(decl, self.row["statement"])
        if bad:                   
            c.update(decl=decl, sha=sha16(decl), reading={"ok": False, "error": bad}, error_short=bad, error_full=bad, features=features(decl),
                     rejected="forbidden")
            return c
        k = sha16(decl)
        with self.clock_lock:
            hit = self.cache.get(k)
        room = self.left() - self.post_reserve()
        if hit is None and room < MEASURE_MIN_S:
            why = f"not measured: {max(0.0, room):.0f} s left before the wall cap's reserve"
            c.update(decl=decl, sha=k, reading={"ok": False, "error": why}, error_short=why, error_full=why, features=features(decl))
            self.rep["wall_stop"] = why
            return c
        if hit is None:
            m = self.meters.get()
            try:
                rd, fail = measure_full(m, decl, timeout=min(timeout, room))
            finally:
                self.meters.put(m)
            rd = {kk: rd.get(kk) for kk in ("ok", "tokens", "heartbeats", "Z", "L", "H", "score_exact", "compat", "error", "timed_out", "meter",
                                             "compiles", "seconds")}
            hit = {"reading": rd, "fail": fail}
            with self.clock_lock:
                self.cache[k] = hit
        c.update(decl=decl, sha=k, reading=hit["reading"], features=features(decl))
        if not is_verified(hit["reading"]):
            f = hit["fail"] or {"pin": None, "errors": [hit["reading"].get("error") or "?"]}
            c.update(error_pin=f.get("pin"), fail=f, error_short=str(f.get("errors") and f["errors"][0] or "?")[:300])
        return c

    def measure_cands(self, sub: list, origin: str, timeout: float, unit: str) -> list[dict]:
        items = list(sub[:K_CANDS])
        if not items:
            return []
        n = min(len(items), self.meters.qsize() or 1)
        with ThreadPoolExecutor(n) as ex:
            out = list(ex.map(lambda t: self._measure_one(t[1], t[0], origin, timeout, unit), enumerate(items)))
        for c in out:
            if is_verified(c.get("reading")):
                self.rep["compiled"] += 1
            self.rlog(f"{origin} {c['label']}: {fmt(c['reading'])} {c.get('features')}"
                      + ("" if is_verified(c.get("reading")) else f" ({str(c.get('error_short'))[:120]})"))
        self.rep["cands"] += len(out)
        return out

    def with_error(self, c: dict) -> dict:
        """The repair prompt's compiler error for a failing candidate (recompiled on the primary pin when that pin failed)."""
        if "error_full" not in c:
            r = self.repair_error_fn(self.name, c["decl"], c.get("fail") or {"pin": None, "errors": [c.get("error_short") or "?"]}, self.primary,
                                     timeout=max(30.0, min(600.0, self.left() - self.post_reserve())))
            c["error_full"], fault = r if isinstance(r, tuple) else (r, None)
            if fault:
                self.rep.setdefault("helper_faults", []).append(f"repair error: {fault}")
        return c

    def best_of(self, cands: list[dict]) -> dict | None:
        ok = [c for c in cands if c.get("decl") and is_verified(c["reading"])]
        return max(ok, key=lambda c: c["reading"]["score_exact"]) if ok else None

    def run_unit(self, u: dict, reading: dict) -> dict:
        urec = {"role": u["role"], "sha": sha16(u["proof"]), "reading": {k: reading.get(k) for k in ("tokens", "heartbeats", "score_exact", "Z")},
                "calls": 0, "status": "running"}
        gm = {}
        if self.left() >= GOAL_MIN_LEFT_S:
            gm = self.goal_map_fn(self.name, u["proof"])
        urec["goal_steps"] = len(gm.get("steps") or [])
        if not gm.get("steps") and gm.get("note"):
            urec["goal_note"] = str(gm["note"])[:200]
            if "unavailable" in str(gm["note"]):
                self.rep.setdefault("helper_faults", []).append(f"goal map: {gm['note']}")
        timeout = max(180.0, 8.0 * float(reading.get("seconds") or 30.0))
        results: list = []; best = None
        for rnd in (1, 2):
            if not self.call_ok():
                urec["status"] = "wall"; break
            prompt = round_prompt(self.row, self.ref_h, u["proof"], reading, gm, self.exs, rnd, results=results, best=best)
            sub = self.call(f"r{rnd}", prompt); urec["calls"] += 1
            cs = self.measure_cands(sub, f"r{rnd}", timeout, urec["sha"])
            self.cands += cs
            fails = [c for c in cs if c.get("decl") and not is_verified(c["reading"]) and not c.get("rejected")
                     and not str(c["reading"].get("error") or "").startswith("not measured")][:MAX_REPAIRS]
            if fails and self.call_ok():
                def repair(c):
                    rs = self.call("repair", repair_prompt(self.row, u["proof"], self.with_error(c)))
                    return self.measure_cands(rs[:1], f"r{rnd}-repair-{c['label']}", timeout, urec["sha"])
                with ThreadPoolExecutor(len(fails)) as ex:
                    for got in ex.map(repair, fails):
                        self.cands += got
                urec["calls"] += len(fails)
            results = [c for c in self.cands if c["origin"].startswith(f"r{rnd}") and c.get("unit") == urec["sha"]]
            b = self.best_of([c for c in self.cands if c.get("unit") == urec["sha"]])
            if b and b["reading"]["score_exact"] > float(reading.get("score_exact") or -1e9):
                best = b
        else:
            urec["status"] = "done"
        return urec

    def run(self) -> dict:
        """The step's report with "candidate" (the best verified, audited (and polished) candidate, or None); never raises."""
        rep = self.rep
        try:
            for i, u in enumerate(self.units):
                if i > 0 and not self.call_ok():
                    break
                t_read = self.clock()
                m = self.meters.get()
                try:
                    rd, _fail = measure_full(m, u["proof"])
                finally:
                    self.meters.put(m)
                if u["role"] == "input":
                    self.read_s = max(0.0, self.clock() - t_read)
                    rep["input_read_s"] = round(self.read_s, 1)
                if not is_verified(rd):
                    rep["units"].append({"role": u["role"], "sha": sha16(u["proof"]), "status": "does not read on the meter",
                                         "error": str(rd.get("error"))[:300]})
                    if u["role"] == "input":
                        rep["status"] = "skipped"; rep["why"] = "the input does not read on the meter (every pin): no call"
                        return rep
                    continue
                if u["role"] == "input":
                    rep["input_reading"] = {k: rd.get(k) for k in ("tokens", "heartbeats", "score_exact", "Z", "meter")}
                rep["units"].append(self.run_unit(u, rd))
        except Exception as e:                                                                                                       
            rep["error"] = f"{type(e).__name__}: {str(e)[:300]}"
            rep["stopped"] = "model" if isinstance(e, ModelError) else "error"
            self.rlog(f"stopped on {rep['error']}")
        rep["call_records"] = list(getattr(self.caller, "calls", []))
        rep["candidates"] = [{k: c.get(k) for k in ("label", "origin", "sha", "features", "error_short", "rejected")} | {"reading": c.get("reading")}
                             for c in self.cands]
        try:
            rep["candidate"] = self.select()
        except Exception as e:                
            rep["candidate"] = None
            rep["select_error"] = f"{type(e).__name__}: {str(e)[:300]}"
        return rep

    def select(self) -> dict | None:
        rep = self.rep
        inc = (rep.get("input_reading") or {}).get("score_exact")
        ok = [c for c in self.cands if c.get("decl") and is_verified(c["reading"]) and c["decl"].strip() != self.inc]
        ok.sort(key=lambda c: -c["reading"]["score_exact"])
        for c in ok[:3]:
            if self.left() < self.post_reserve():
                rep["wall_stop"] = f"no candidate taken: {max(0.0, self.left()):.0f} s left, the audit and the confirm read need {self.post_reserve():.0f} s"
                return None
            try:
                st, why = self.audit(c["decl"], self.deadline)
            except Exception as e:                
                st, why = "unknown", f"audit raised {type(e).__name__}: {str(e)[:120]}"
            c["audit"] = {"status": st, "why": why}
            if st not in ("clean", "skipped"):
                self.rlog(f"candidate {c['label']} rejected by the axiom audit: {st}: {str(why)[:160]}"); continue
            best = {"proof": c["decl"], "reading": c["reading"], "label": c["label"], "origin": c["origin"], "audit": c["audit"], "polished": False}
            if self.polish is None:
                rep["polish"] = {"status": "off"}
                return best
            if inc is not None and c["reading"]["score_exact"] < float(inc) - POLISH_MARGIN:
                rep["polish"] = {"status": f"skipped: best raw {c['reading']['score_exact']:.3f} is more than {POLISH_MARGIN} below the input"}
                return best
            stop_at = None if self.deadline is None else self.deadline - self.post_reserve()
            if stop_at is not None and stop_at - self.clock() < POLISH_MIN_S:
                rep["polish"] = {"status": f"skipped: {max(0.0, stop_at - self.clock()):.0f} s before the reserve (< {POLISH_MIN_S:g} s)"}
                return best
            try:
                pr = self.polish({"proof": c["decl"], **{k: c["reading"].get(k) for k in ("tokens", "heartbeats", "Z", "L", "H", "compat")},
                                  "score": c["reading"]["score_exact"], "score_exact": c["reading"]["score_exact"], "stage": TAG, "verified": True},
                                 stop_at)
            except Exception as e:                
                pr = {"error": f"{type(e).__name__}: {str(e)[:200]}"}
            rep["polish"] = {k: pr.get(k) for k in ("stage", "compiles", "error", "meter")}
            m = pr.get("metrics") if isinstance(pr.get("metrics"), dict) else pr
            pp = (pr.get("proof") or "").strip()
            verified = bool(pr["verified"]) if "verified" in pr else pr.get("stage") not in (None, "unmeasured")
            m = dict(m, ok=bool(m.get("ok", verified)))
            rep["polish"]["score_exact"] = m.get("score_exact")
            if pp and verified and is_verified(m) and pp != self.inc and pp != c["decl"].strip() and float(m["score_exact"]) >= float(c["reading"]["score_exact"]):
                nd, why = normalize(pp, self.row["statement"])
                if nd is not None and precheck(nd, self.row["statement"]) is None and self.left() >= self.post_reserve() / 2:
                    try:
                        st2, why2 = self.audit(nd, self.deadline)
                    except Exception as e:                
                        st2, why2 = "unknown", f"audit raised {type(e).__name__}"
                    if st2 in ("clean", "skipped"):
                        best = {"proof": nd, "reading": {k: m.get(k) for k in ("ok", "tokens", "heartbeats", "Z", "L", "H", "score_exact", "compat", "meter")},
                                "label": c["label"], "origin": c["origin"] + "+polish", "audit": {"status": st2, "why": why2}, "polished": True,
                                "polish_stage": pr.get("stage")}
                        rep["polish"]["gain"] = round(float(m["score_exact"]) - float(c["reading"]["score_exact"]), 4)
                    else:
                        rep["polish"]["rejected"] = f"audit {st2}: {str(why2)[:120]}"
                else:
                    rep["polish"]["rejected"] = "the polished text is not usable (statement, forbidden pattern or no time for its audit)"
            elif pp == c["decl"].strip():
                rep["polish"]["rejected"] = "the polish found nothing"
            elif pp == self.inc:
                rep["polish"]["rejected"] = "the polish returned the input's text"
            else:
                rep["polish"]["rejected"] = "the polish result is not verified on every pin or reads below the raw candidate"
            return best
        return None


def confirm(meter, incumbent: str, candidate: str) -> dict:
    """The single confirm read: the input and the candidate back to back on one meter, every pin. ok = the candidate reads (Z 100, no lower
"""
    a = meter.measure(incumbent.strip(), full=True)
    b = meter.measure(candidate.strip(), full=True)
    rd = lambda m: {k: m.get(k) for k in ("ok", "tokens", "heartbeats", "Z", "L", "H", "score_exact", "compat", "meter", "error")}              
    out = {"input": rd(a), "candidate": rd(b), "compiles": int(a.get("compiles") or 0) + int(b.get("compiles") or 0), "bar": MIN_GAIN}
    if not is_verified(b):
        out.update(ok=False, why="the candidate does not read on the confirm read (every pin)", delta=None)
    elif not is_verified(a):
        out.update(ok=False, why="the input does not read on the confirm read: nothing is accepted", delta=None)
    else:
        d = float(b["score_exact"]) - float(a["score_exact"])
        out.update(ok=float(b["Z"]) >= float(a["Z"]) - 1e-9 and d >= MIN_GAIN - 1e-9, delta=round(d, 6),
                   why=f"confirm read: candidate {float(b['score_exact']):.4f} vs input {float(a['score_exact']):.4f} (bar +{MIN_GAIN:g})")
    return out


def run_row(row: dict, ref_h, incumbent: str, exs: list[dict], step_kw: dict, confirm_meter, clock=time.time,
            deadline: float | None = None) -> dict:
    """The step on one row, then the confirm read; the record (status improved / kept / skipped, before / after / gain / proof)."""
    t0 = clock()
    st = Step(row, ref_h, incumbent, exs, clock=clock, deadline=deadline, **step_kw)
    rep = st.run()
    rec = {"status": rep.get("status") or "kept", "why": rep.get("why"), "input_sha": sha16(incumbent), "before": rep.get("input_reading"),
           "calls": rep.get("calls"), "cands": rep.get("cands"), "compiled": rep.get("compiled"), "units": rep.get("units"),
           "call_records": rep.get("call_records"), "candidates": rep.get("candidates"), "polish": rep.get("polish"),
           "error": rep.get("error"), "stopped": rep.get("stopped"), "wall_stop": rep.get("wall_stop"),
           "helper_faults": rep.get("helper_faults"), "select_error": rep.get("select_error")}
    cand = rep.get("candidate")
    if rec["status"] != "skipped":
        if not cand:
            rec["why"] = rec["why"] or ("no verified candidate differs from the input" if not rep.get("error") else f"stopped: {rep['error']}")
        elif deadline is not None and deadline - clock() < max(POST_MIN_S / 2, 2.2 * st.read_s):
            rec["why"] = f"no time for the confirm read ({max(0.0, deadline - clock()):.0f} s left)"
            rec["candidate"] = {k: cand.get(k) for k in ("label", "origin", "polished")} | {"reading": cand.get("reading")}
        else:
            cf = confirm(confirm_meter, incumbent, cand["proof"])
            rec["confirm"] = cf
            rec["candidate"] = {k: cand.get(k) for k in ("label", "origin", "polished", "audit")} | {"reading": cand.get("reading")}
            if cf["ok"] and (deadline is None or clock() <= deadline):
                rec.update(status="improved", proof=cand["proof"].strip(), gain=cf["delta"], after=cf["candidate"],
                           why=cf["why"], before=cf["input"])
            else:
                rec["why"] = cf["why"] + ("" if cf["ok"] else " (not accepted)")
    rec["seconds"] = round(clock() - t0, 1)
    return rec


                                                                                                                                        
def _atomic_write(p: Path, text: str) -> None:
    tmp = p.with_name(p.name + ".tmp")
    tmp.write_text(text)
    os.replace(tmp, p)


def make_polish(row: dict, meter, cfg_path: Path, log):
    """The open end stage's $0 tools on one candidate: harness/endstage.end_stage with the package's frozen end config (load_config +
"""
    from harness import endstage as ES
    from harness import open_config as OC_
    a = ES.build_parser().parse_args(["--run-dir", str(ROOT)])
    vals, _rec = ES.load_config(cfg_path)
    for k, v in vals.items():
        setattr(a, k, v)
    fams = ES.families_for(a.sweep, a.tools)
    a.family_caps = ES.parse_caps(a.family_caps)
    a.family_ops = a.family_ops if isinstance(a.family_ops, dict) else ES.parse_ops(a.family_ops)
    a.opt_in = a.opt_in if isinstance(a.opt_in, dict) else ES.parse_opt_in(a.opt_in)
    for f in fams:
        ES._load_family(f)
    if getattr(a, "open", None):
        OC_.apply(a.open)
    probs = ES.check_ops(fams, a.family_ops, a.opt_in, getattr(a, "family_ctx_extra", None))
    if probs:
        raise RuntimeError("; ".join(probs))
    ES.normalize_method(a, fams)
    share = float(((getattr(a, "open", None) or {}).get("r5") or {}).get("sweep_share") or 0.1)

    def polish(item: dict, stop_at: float | None) -> dict:
        allow = 3600.0 if stop_at is None else max(1.0, 0.85 * (stop_at - time.time()))
        a.max_seconds, a.tools_max_seconds = max(1.0, allow * share), max(1.0, allow * (1.0 - share))
        r = ES.end_stage(row, row["src"], [dict(item, origins=[TAG])], meter, k=a.k, sweep=a.sweep, crossover=a.crossover,
                         max_compiles=a.max_compiles, checkpoint_bests={"style_rw_cand": item}, log=log, **ES.end_kwargs(a))
        return {"proof": r.get("proof"), "metrics": r.get("metrics") or {}, "stage": r.get("stage"), "compiles": r.get("compiles"),
                "meter": r.get("meter"), "verified": r.get("stage") not in (None, "unmeasured")}
    return polish


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--problem", required=True)
    ap.add_argument("--file", required=True, help="the input proof (the row's export pick)")
    ap.add_argument("--rows", required=True); ap.add_argument("--heartbeats", required=True)
    ap.add_argument("--record", required=True, help="the record JSON this process writes (atomically, once)")
    ap.add_argument("--deadline", type=float, required=True, help="the row's hard wall (epoch seconds)")
    ap.add_argument("--base-url", required=True); ap.add_argument("--api-model", required=True)
    ap.add_argument("--api-key-file", default=None)
    ap.add_argument("--effort", default=EFFORT, choices=EFFORTS,
                    help="default: thinking off (chat_template_kwargs enable_thinking false); low / high / max: thinking on, reasoning_effort")
    ap.add_argument("--max-tokens", type=int, default=MAX_TOKENS)
    ap.add_argument("--exemplars", default=EXEMPLARS_SHA16, help="sha16 of harness/style_rw_open_exemplars.json (frozen)")
    ap.add_argument("--others", default=None, help="JSON list of {proof, score}: the row's other verified proofs")
    ap.add_argument("--input-score", type=float, default=None, help="the input's stored score (the window of --others)")
    ap.add_argument("--end-config", default=None, help="the package's end config (the polish); none: no polish")
    ap.add_argument("--meter-state", default=None, help="the end stage's meter.json (its run state is reused; else the self-test)")
    ap.add_argument("--trajectory", default=None)
    ap.add_argument("--scratch", default=None, help="compile-slot directory (default: $LRA_HBTOOL_SCRATCH/style or probe/hbtool/.scratch/style)")
    return ap


def main(argv=None) -> int:
    a = build_parser().parse_args(argv)
    os.environ.setdefault("LRA_FORCE_WARN_SORRY", "1")                                                                            
    rec_p = Path(a.record)
    t_start = time.time()
    deadline = float(a.deadline) - RECORD_RESERVE_S
    rec: dict = {"problem": a.problem}

    def log(m: str) -> None:
        print(f"[{time.strftime('%H:%M:%S')}] {m}", flush=True)
    try:
        from harness.hb_tool_eval import load_dataset
        from harness import endstage as ES
        rows, hbs = load_dataset(a.rows, a.heartbeats)
        row = rows[a.problem]
        ref_h = hbs.get(a.problem)
        incumbent = Path(a.file).read_text().strip()
        pairs = load_exemplars(a.exemplars)
        others = json.loads(Path(a.others).read_text()) if a.others and Path(a.others).exists() else []
        units = other_units(incumbent, a.input_score, others)
        exs, dropped = exemplars_for(row, pairs, [incumbent, row.get("src") or ""] + [u["proof"] for u in units])
        rec["exemplars"] = {"sha": exemplars_sha(), "shown": [x["id"] for x in exs], "dropped": dropped}
        log(f"{a.problem[:40]}: {len(exs)} exemplar pair(s) shown, {len(dropped)} dropped; {len(units)} other unit(s); "
            f"{a.deadline - time.time():.0f} s to the wall")
        if not ref_h:
            raise RuntimeError("no reference heartbeats for the row")
        if a.meter_state and Path(a.meter_state).exists():
            ES.restore_run_state(json.loads(Path(a.meter_state).read_text()))
        base = Path(os.environ.get("LRA_HBTOOL_SCRATCH") or ROOT / "probe/hbtool/.scratch")
        scratch = Path(a.scratch) if a.scratch else base / "style"
        scratch.mkdir(parents=True, exist_ok=True)

        def new_meter():
            m = ES.Meter(row, hbs, log=lambda s: log(f"meter: {s}"))
            m.scratch = scratch
            return m
        meter = new_meter()
        meter.self_test(row["src"])                                                                    
        key = Path(a.api_key_file).expanduser() if a.api_key_file else None
        caller = Caller(a.base_url, key.read_text().strip() if key and key.exists() else "EMPTY", a.api_model, a.effort, a.max_tokens, log=log,
                        trajectory=a.trajectory, row=a.problem)
        from harness import open_package as OP
        versions = versions_of(row)
        seed_sorry: dict = {}

        def audit(proof: str, dl: float | None):
            return OP.audit_proof(row, proof, versions, seed_sorry, timeout=OP.AUDIT_TIMEOUT_S, deadline=dl)
        polish, fault = None, None
        if a.end_config:
            try:                                                                        
                polish = make_polish(row, meter, Path(a.end_config), log)
            except Exception as e:                
                fault = f"polish not available ({type(e).__name__}: {str(e)[:200]})"
                log(fault)
        out = run_row(row, ref_h, incumbent, exs, {"caller": caller, "meter": meter, "audit": audit, "polish": polish, "log": log,
                                                   "units": units, "meter_factory": new_meter}, meter, deadline=deadline)
        rec.update(out)
        if fault:
            rec["helper_faults"] = (rec.get("helper_faults") or []) + [fault]
    except Exception as e:                                                                   
        rec.update(status="error", why=f"{type(e).__name__}: {str(e)[:300]}", trace=traceback.format_exc()[-2000:])
    rec["wall_s"] = round(time.time() - t_start, 1)
    rec["finished_at"] = time.time()
    try:
        _atomic_write(rec_p, json.dumps(rec, ensure_ascii=False, default=str, indent=1))
    except OSError as e:
        log(f"record not written: {e}")
        return 1
    log(f"{a.problem[:40]}: {rec['status']}" + (f" {rec.get('gain'):+.3f}" if rec.get("status") == "improved" else "")
        + f" ({rec.get('why') or ''})"[:200] + f" in {rec['wall_s']:.0f} s")
    return 0


                                                                                                                                         
def gzip_trajectories(d: Path) -> int:
    """Every <d>/*.jsonl replaced by <d>/*.jsonl.gz (complete, compressed), at the end of the stage (review 2026-10-30): the prompts show
"""
    import gzip, shutil
    n = 0
    try:
        files = sorted(Path(d).glob("*.jsonl")) if Path(d).is_dir() else []
    except OSError:
        return 0
    for p in files:
        try:
            with p.open("rb") as fi, gzip.open(p.with_name(p.name + ".gz"), "ab") as fo:
                shutil.copyfileobj(fi, fo)
            p.unlink(); n += 1
        except OSError:
            pass
    return n


def read_records(path: Path) -> dict:
    """{(row, input sha): the last line} of a style_rw.jsonl (torn lines skipped)."""
    out = {}
    try:
        lines = Path(path).read_text(errors="replace").splitlines()
    except OSError:
        return out
    for l in lines:
        try:
            r = json.loads(l) if l.strip() else None
        except ValueError:
            continue
        if isinstance(r, dict):
            out[(r.get("problem"), r.get("input_sha"))] = r
    return out


def choice(row: dict, rec: dict | None, input_proof: str) -> str | None:
    """The accepted proof of a style_rw.jsonl line when the export may take it: status improved, for exactly this input (sha), a different
"""
    from scorer.tokenize import split_declaration
    if not rec or rec.get("status") != "improved" or rec.get("input_sha") != sha16(input_proof):
        return None
    p = (rec.get("proof") or "").rstrip()
    if not p or p.strip() == input_proof.strip() or split_declaration(p, row["statement"]) is None or precheck(p, row["statement"]) is not None:
        return None
    if not isinstance(rec.get("gain"), (int, float)) or float(rec["gain"]) < MIN_GAIN - 1e-9:
        return None
    return p


def row_cmd(cfg: dict, name: str, proof_file: Path, record: Path, deadline: float, others: Path | None, input_score, traj: Path) -> list[str]:
    cmd = [sys.executable, "harness/style_rw_open.py", "--problem", name, "--file", str(proof_file), "--rows", cfg["rows"], "--heartbeats",
           cfg["heartbeats"], "--record", str(record), "--deadline", f"{deadline:.3f}", "--base-url", cfg["base_url"], "--api-model",
           cfg["api_model"], "--effort", cfg["effort"], "--max-tokens", str(int(cfg["max_tokens"])), "--exemplars", cfg["exemplars"],
           "--trajectory", str(traj)]
    if cfg.get("api_key_file"):
        cmd += ["--api-key-file", cfg["api_key_file"]]
    if others is not None:
        cmd += ["--others", str(others)]
    if isinstance(input_score, (int, float)):
        cmd += ["--input-score", str(float(input_score))]
    if cfg.get("end_config"):
        cmd += ["--end-config", cfg["end_config"]]
    if cfg.get("meter_state"):
        cmd += ["--meter-state", cfg["meter_state"]]
    if cfg.get("scratch"):
        cmd += ["--scratch", cfg["scratch"]]
    return cmd


def run_stage(names: list[str], rows: dict, inputs: dict, cfg: dict, dest: Path, deadline: float, jobs: int, env: dict, runner=None,
              now=time.time, log=print, wall_s: float = WALL_S, others: dict | None = None) -> dict:
    """The step over `names` (one process per row, at most `jobs` at once, rows in order): inputs {row: {"source", "proof", "score"}},




"""
    dest = Path(dest); sd = dest / "style_rw"; (sd / "trajectories").mkdir(parents=True, exist_ok=True); (dest / "logs").mkdir(exist_ok=True)
    rec_path = dest / "style_rw.jsonl"
    prior = read_records(rec_path)
    idx = {n: i for i, n in enumerate(names)}
    todo, reused = [], 0
    for n in names:
        inp = inputs.get(n)
        if not inp or not (inp.get("proof") or "").strip():
            continue
        h = sha16(inp["proof"])
        old = prior.get((n, h))
        if old and old.get("status") not in RETRY:
            reused += 1; continue
        todo.append(n)
    lock = threading.Lock(); counts: dict = {}; gains: list = []

    def write(line: dict) -> None:
        with lock:
            counts[line["status"]] = counts.get(line["status"], 0) + 1
            if line["status"] == "improved":
                gains.append(float(line.get("gain") or 0))
            with rec_path.open("a") as fh:
                fh.write(json.dumps(line, ensure_ascii=False, default=str) + "\n")

    if runner is None:
        from harness.open_package import run_session

        def runner(n, k, cmd, log_path, row_deadline):
            return run_session(cmd, env, log_path, row_deadline, now=now)

    def one(n: str) -> None:
        k = idx[n]; inp = inputs[n]
        base = {"problem": n, "row": k, "source": inp.get("source"), "input_sha": sha16(inp["proof"]),
                "t": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        try:
            left = deadline - now()
            if left < STAGE_MIN_START_S:
                write(dict(base, status="skipped", why=f"{left:.0f} s left before the step's deadline")); return
            bound = min(float(wall_s), left)
            pf, rf, of, tf = sd / f"r{k:02d}.lean", sd / f"r{k:02d}.json", sd / f"r{k:02d}.others.json", sd / "trajectories" / f"r{k:02d}.jsonl"
            pf.write_text(inp["proof"].strip() + "\n"); rf.unlink(missing_ok=True)
            oth = (others or {}).get(n) or []
            if oth:
                of.write_text(json.dumps(oth, ensure_ascii=False))
            t0 = now()
            cmd = row_cmd(cfg, n, pf, rf, t0 + bound, of if oth else None, inp.get("score"), tf)
            try:
                rc = runner(n, k, cmd, dest / "logs" / f"style_rw.r{k:02d}.log", t0 + bound)
            except Exception as e:                
                rc = -1; log(f"style_rw row#{k:02d}: runner raised {type(e).__name__}: {e}")
            secs = now() - t0
            try:
                r = json.loads(rf.read_text())
            except (OSError, ValueError):
                r = None
            if rc is None:                                                                       
                r = {"status": "stopped", "why": f"the {bound:.0f} s wall cap was reached"}
            elif not isinstance(r, dict) or r.get("status") not in STATUSES:
                r = {"status": "error", "why": f"no usable record (rc {rc})"}
            line = dict(base, status=r["status"], why=r.get("why"), rc=rc, seconds=round(secs, 1), bound_s=round(bound, 1),
                        **{x: r[x] for x in ("before", "after", "gain", "calls", "cands", "compiled", "exemplars", "wall_stop", "error")
                           if r.get(x) is not None})
            if r["status"] == "improved":
                if r.get("input_sha") != base["input_sha"] or not r.get("proof"):
                    line.update(status="error", why="an improved record for another input"); line.pop("gain", None)
                else:
                    line["proof"] = r["proof"]
            write(line)
            log(f"style_rw row#{k:02d} ({inp.get('source')}): {line['status']}"
                + (f" {line.get('gain', 0):+.3f}" if line["status"] == "improved" else f" ({str(line.get('why') or '')[:100]})")
                + f" in {secs:.0f} s")
        except Exception as e:                                                                                    
            log(f"style_rw row#{k:02d}: failed ({type(e).__name__}: {e}); the row keeps its input")
            try:
                write(dict(base, status="error", why=f"{type(e).__name__}: {e}"[:300]))
            except Exception:                
                pass

    room = deadline - now()
    log(f"style_rw step: {len(todo)} row(s) to run ({reused} already done), {jobs} at once, {room:.0f} s before its deadline, wall "
        f"{float(wall_s):.0f} s per row")
    if todo:
        with ThreadPoolExecutor(max(1, int(jobs)), thread_name_prefix="opk-style") as ex:
            list(ex.map(one, todo))
    summ = {"rows": len(names), "run": len(todo), "reused": reused, "statuses": counts, "jobs": jobs, "gain_sum": round(sum(gains), 4),
            "seconds_left_at_start": round(room, 1), "trajectories_gzipped": gzip_trajectories(sd / "trajectories")}
    log(f"style_rw step done: {summ}")
    return summ


if __name__ == "__main__":
    raise SystemExit(main())
