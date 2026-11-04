"""Golf mode for harness/agent.py (B62c, docs/scaffold_panel.md; `agent.py --mode golf`, OFF by default).









"""
from __future__ import annotations

import json, re

from scorer.tokenize import count_tokens, split_declaration

MARK = "lra_hb!"
                                                                                                                                           
                                                  
PRELUDE = ("open Lean Elab Tactic in\n"
           "elab \"lra_hb!\" : tactic => do\n"
           "  let n ← IO.getNumHeartbeats\n"
           "  logInfo m!\"LRA_HB {n}\"\n\n")
_HB_RE = re.compile(r"LRA_HB (\d+)")
_CONT = ("|", "<;>", ")", "]", "}", ",", "⟩", "with", "at ", "using", "=>", ":=", "<|", "fun ", "then", "else", "_ ", "·" + "·")
                                                                                             
_OPEN_END = (",", "(", "[", "{", "⟨", "<;>", "<|", "$", ":=", "fun", "|", "+", "-", "*", "/", "=", "≠", "≤", "<", "≥", ">", "∧", "∨", "→",
             "↔", "∘", "•", "×", "∈", "▸", "←", "^", "then", "else", "from", "show", "↦")
_CONV = re.compile(r"^\s*conv(_lhs|_rhs)?\b")
_TAC_ALT = re.compile(r"^\s*(induction|cases|rcases|fun_induction|induction'|cases')\b.*\bwith\s*$")
_CLAUSE = re.compile(r"^\s*(termination_by|decreasing_by|where)\b")
_BRK = {"(": ")", "[": "]", "{": "}", "⟨": "⟩"}


def system_prompt(batch_max: int, min_evals: int, flat_evals: int) -> str:
    return (
        "You are a Lean 4 proof engineer golfing a proof that already compiles. Goal: raise its score\n"
        "  score = mean(length_reduction%, heartbeat_reduction%, compatibility%)\n"
        "against the reference proof: length = tokens of the proof body (every bracket and operator is a token, a dotted name is one token, "
        "comments and whitespace are free), heartbeats = elaboration cost, compatibility = share of the listed toolchains on which it compiles "
        "unchanged.\n\n"
        "How this session works: the harness keeps the current best proof (best.lean). Every candidate you send is compiled and measured; it "
        "replaces the best only when a paired, unrounded comparison against the best, measured in this same session, shows a real gain and it "
        "compiles on every toolchain the best compiles on. The best can never get worse. Small gains count: a few thousandths of a point are "
        "banked.\n\n"
        "Method: many cheap measured edits, not a few big rewrites.\n"
        "1. hb_profile shows where the heartbeats of a proof go, step by step. The opening message gives this problem's exchange rate (what one "
        "token is worth in heartbeats): spend tokens where heartbeats are expensive, cut tokens where heartbeats are cheap.\n"
        f"2. lean_batch evaluates up to {batch_max} independent candidates in one call, each a small edit of the best (find/replace pairs; every "
        "`find` must occur exactly once) or a full text. Send many alternatives per call: delete a step, merge steps, replace a closer by a "
        "cheaper or shorter one, pin automation to the lemmas it needs (the `simp?` / `grind?` certificates through lean_run), replace a "
        "hand-written step by automation where tokens dominate, swap a lemma for a variant, restructure a case split, drop a type ascription "
        "or a name that is not needed.\n"
        "3. Combine: after a batch, send combinations of the edits that helped, applied together.\n"
        "4. pool lists the compiling candidates of this run with their numbers and their difference to the best: one that lost on one axis "
        "may combine with another; lean_batch can start from a pool entry (`base`).\n"
        "5. lean_run tests a lemma or a closer in the problem's environment (sorry is allowed there); lean_goals prints the goals.\n"
        f"The session ends when the budget is spent, or by the stop rule: at least {min_evals} evaluations, the last {flat_evals} of them "
        "without a banked gain. finish is refused before that, so keep proposing edits.\n"
        "Never put sorry/admit/axiom/native_decide in a candidate; never add declarations, `open` or `set_option` outside the proof; the "
        "statement must stay byte-for-byte identical.")


def tools(batch_max: int) -> list[dict]:
    return [
        {"name": "lean_batch",
         "description": (f"Evaluate up to {batch_max} candidates in one call. Each item is either `edits` (find/replace pairs applied in order to "
                         "the base; every `find` must occur exactly once in the text at that point) or `content` (a full candidate: statement, := "
                         "and proof). The base is the current best unless `base` names a pool entry (its sha prefix). Every item is compiled and "
                         "measured; returns per item ok, tokens, heartbeats, exact score, the difference to the best, the first error, and "
                         "whether it was banked. Already-evaluated texts are not compiled again."),
         "input_schema": {"type": "object", "properties": {
             "base": {"type": "string", "description": "'best' (default) or the sha prefix of a pool entry"},
             "items": {"type": "array", "items": {"type": "object", "properties": {
                 "label": {"type": "string"},
                 "edits": {"type": "array", "items": {"type": "object", "properties": {"find": {"type": "string"}, "replace": {"type": "string"}},
                                                      "required": ["find", "replace"]}},
                 "content": {"type": "string"}}}}},
             "required": ["items"]}},
        {"name": "hb_profile",
         "description": ("Heartbeats per tactic step of a proof (default: the best; or `content`, a full candidate), from one instrumented "
                         "compile: a heartbeat reading before every step of the top-level tactic block and of nested blocks (bullets, "
                         "alternatives, `by` blocks). Returns the costliest line ranges first. Steps run several times (inside `all_goals`, "
                         "`<;>`) are summed."),
         "input_schema": {"type": "object", "properties": {"content": {"type": "string"}}}},
        {"name": "pool",
         "description": ("The compiling candidates of this run, best first: sha prefix, exact score, tokens, heartbeats, and the lines that "
                         "differ from the current best. Use a sha prefix as lean_batch `base` to edit a pool entry."),
         "input_schema": {"type": "object", "properties": {"k": {"type": "integer"}}}},
    ]


def apply_edits(base: str, edits: list) -> tuple[str | None, str | None]:
    """(text, None) after applying every find/replace in order, or (None, error)."""
    text = base
    for k, e in enumerate(edits or []):
        f = (e or {}).get("find")
        if not isinstance(f, str) or not f:
            return None, f"edit {k + 1}: empty find"
        n = text.count(f)
        if n != 1:
            return None, f"edit {k + 1}: `find` occurs {n} times (it must occur exactly once){'' if n else '; copy it from the base text'}"
        text = text.replace(f, str(e.get("replace") or ""), 1)
    return text, None


def exchange(ref_tokens: int, ref_hb: int) -> dict:
    """Points per token and per 1k heartbeats on this row, and one token in heartbeats (the row's own numbers)."""
    return {"points_per_token": round(100 / (3 * ref_tokens), 4) if ref_tokens else None,
            "points_per_1k_heartbeats": round(100000 / (3 * ref_hb), 4) if ref_hb else None,
            "one_token_equals_heartbeats": round(ref_hb / ref_tokens, 1) if ref_tokens and ref_hb else None}


                                                                                                                                       

def _indent(l: str) -> int:
    return len(l) - len(l.lstrip(" "))


def _code(l: str) -> str:
    """The line without a trailing comment or string literals (for bracket counting)."""
    l = re.sub(r'"(?:[^"\\]|\\.)*"', '""', l)
    return l.split("--", 1)[0]


def instrument(decl: str, statement: str, top_only: bool = False) -> tuple[str, list[int]] | None:
    """The declaration with a MARK line before every step of each tactic block, and the original (0-based) line index each marker precedes


"""
    body = split_declaration(decl, statement)
    if body is None or not decl.endswith(body) or "\n" not in body.strip():
        return None
    lines = decl.split("\n")
    mb = re.match(r"\s*by\b", body)
    if not mb:
        return None
    by_line = decl[: len(decl) - len(body) + mb.end()].count("\n")                                      
    tail = [i for i in range(by_line + 1, len(lines)) if lines[i].strip() and not lines[i].strip().startswith("--")]
    if not tail:
        return None
    base = _indent(lines[tail[0]])
    end = next((i for i in tail if _indent(lines[i]) <= base and _CLAUSE.match(lines[i])), len(lines))
    tail = [i for i in tail if i < end]
    stack: list = []                                                                                                      
    marks, prev = [], by_line

    def scan(i: int) -> None:
        for ch in _code(lines[i]):
            if ch in _BRK:
                stack.append((ch, i))
            elif ch in _BRK.values() and stack and _BRK[stack[-1][0]] == ch:
                stack.pop()

    def opener(j: int) -> bool:                                                                            
        t = _code(lines[j]).rstrip()
        if re.search(r"(^|[\s(⟨{])by$", t) or t.endswith("by {"):
            return not _CONV.match(lines[j])
        st = t.strip()
        if re.match(r"^(case\s|next\b)", st) and st.endswith("=>"):
            return True
        if st.startswith("|") and st.endswith("=>"):                                                                                           
            g = next((k for k in range(j - 1, by_line, -1) if lines[k].strip() and _indent(lines[k]) <= _indent(lines[j])
                      and not lines[k].strip().startswith("|")), None)
            return g is not None and bool(_TAC_ALT.match(lines[g]))
        return False

    for i in tail:
        s_, ind = lines[i].strip(), _indent(lines[i])
        p = _code(lines[prev]).rstrip()
        cont = s_.startswith(_CONT) or (p.endswith(_OPEN_END) and not opener(prev))
        anc, k = [], i                                                                                                               
        for j in range(i - 1, by_line - 1, -1):
            if lines[j].strip() and _indent(lines[j]) < _indent(lines[k] if k != i else lines[i]):
                anc.append(j); k = j
        in_conv = any(_CONV.match(lines[j]) for j in anc[: next((n for n, j in enumerate(anc) if opener(j)), len(anc))])
        in_brk = bool(stack) and not any(opener(j) and j >= stack[-1][1] for j in anc)
        ok = not cont and not in_conv and not in_brk
        if ok and ind == base and all(_indent(lines[j]) < base for j in anc):
            marks.append(i)
        elif ok and not top_only and anc:
            g = anc[0]; gs = lines[g].strip()
            first_in_block = next((j for j in tail if j > g and _indent(lines[j]) > _indent(lines[g])), None)
            if (re.match(r"^[·.]\s", gs) and ind == _indent(lines[g]) + 2) or \
               (opener(g) and first_in_block is not None and ind == _indent(lines[first_in_block])):
                marks.append(i)
        scan(i); prev = i
    if not marks:
        return None
    out, idx = [], []
    ms = set(marks)
    for i, l in enumerate(lines):
        if i == end:
            out.append(" " * base + MARK); idx.append(end)
        if i in ms:
            out.append(" " * _indent(l) + MARK); idx.append(i)
        out.append(l)
    if end == len(lines):
        out.append(" " * base + MARK); idx.append(len(lines))
    return "\n".join(out), idx


def profile_compile(row: dict, text: str, version: str, timeout: int = 900):
    """Compile the instrumented declaration with the marker tactic defined first; returns (CompileResult, line offset of the declaration).
"""
    from scorer import compile as C
    pre = PRELUDE + "set_option Elab.async false in\n"
    if row["source"] == "putnambench":
        head = row["header"].rstrip() + "\n\n" + pre
        return C.compile_putnam(head, text, version, count=False, timeout=timeout), (head.rstrip() + "\n\n").count("\n")
    core, mods = C.split_modifiers(C.file_prefix(row, version))
    lean_args = C.lakefile_options(row["source"], version)
    m = C._MODULE_LINE.match(core)
    variants = [core] + ([core[: m.end()] + "public meta import Lean.Elab.Tactic\n" + core[m.end():]] if m else [])
    res, off = None, 0
    for c in variants:
        lead = c.rstrip("\n") + "\n\n" + pre + mods
        res = C._lean_in_project(row["source"], version, lead + text.rstrip() + "\n", lean_args, timeout, first_line=C._first_line(c))
        off = lead.count("\n")
        p0 = c.rstrip("\n").count("\n") + 3                                                       
        on_prelude = any(p0 <= (e.get("pos") or {}).get("line", 0) < p0 + pre.count("\n") for e in res.messages if e.get("severity") == "error")
        if res.ok or not on_prelude:
            break
    return res, off


def profile(row: dict, decl: str, version: str, timeout: int = 900) -> dict:
    """Heartbeats per step range of `decl`, costliest first."""
    res = None
    for top in (False, True):
        ins = instrument(decl, row["statement"], top_only=top)
        if ins is None:
            continue
        text, idx = ins
        res, off = profile_compile(row, text, version, timeout)
        if res is not None and res.ok:
            break
    if ins is None and res is None:
        return {"ok": False, "error": "not a multi-line tactic proof: nothing to instrument (measure alternatives with lean_batch instead)"}
    if res is None or not res.ok:
        return {"ok": False, "error": "profiler limitation on this proof's syntax (the proof itself is fine): the instrumented copy did not "
                                      "compile; measure alternatives with lean_batch instead"}
                                                                        
    tl = text.split("\n"); orig_of = {}; k = 0
    for j, l in enumerate(tl):
        if l.strip() == MARK:
            orig_of[j + 1] = idx[k]; k += 1                                  
    reads = []
    for m in res.messages:
        g = _HB_RE.search(str(m.get("data", "")))
        if g:
            ln = (m.get("pos") or {}).get("line", 0) - off
            if ln in orig_of:
                reads.append((int(g.group(1)), orig_of[ln]))
    if len(reads) < 2:
        return {"ok": False, "error": "the markers did not report (the proof may not run its tactic block as written)"}
    reads.sort()
    lines = decl.split("\n")
    cost: dict = {}
    for (n0, l0), (n1, l1) in zip(reads, reads[1:]):
        key = (l0, l1 if l1 > l0 else l0 + 1)
        cost[key] = cost.get(key, 0) + (n1 - n0)
    rows = sorted(({"lines": f"{a + 1}-{b}" if b - a > 1 else f"{a + 1}", "heartbeats": round(v / 1000),
                    "text": lines[a].strip()[:90] if a < len(lines) else "(end)"} for (a, b), v in cost.items()), key=lambda r: -r["heartbeats"])
    total = round((reads[-1][0] - reads[0][0]) / 1000)
    return {"ok": True, "tactic_block_heartbeats": total, "steps": rows[:14],
            "note": "line numbers are lines of the declaration (1 = the statement's first line); the statement and the kernel check are "
                    "outside the tactic block and not in these numbers"}


                                                                                                                                         

def opening(name: str, row: dict, versions: list[str], ref_hb: int, inc: dict, best_text: str, prof: dict, hints: list[str],
            budget: float, min_evals: int, flat_evals: int) -> str:
    ex = exchange(int(row["proof_length"]), int(ref_hb or 0))
    out = [f"Problem `{name}` ({row['source']}). Toolchains: {', '.join(versions)}. Reference proof: {row['proof_length']} tokens, {ref_hb} "
           f"heartbeats (score 33.33).",
           f"Exchange rate on this problem: one token = {ex['one_token_equals_heartbeats']} heartbeats; {ex['points_per_token']} points per token, "                                                            
           f"{ex['points_per_1k_heartbeats']} points per 1,000 heartbeats.",
           f"Current best, measured now: {inc['tokens']} tokens, {inc['heartbeats']} heartbeats, exact score {inc['score']:.4f} (Z {inc['Z']:.0f}).",
           f"Budget: ${budget:.2f} for this session. Stop rule: at least {min_evals} evaluations and {flat_evals} without a banked gain.",
           "best.lean (the current best; lean_batch edits apply to it):\n```lean\n" + best_text.rstrip()[:12000] + "\n```"]
    if prof.get("ok"):
        out.append("hb_profile of the best (costliest step ranges first):\n" + "\n".join(
            f"  lines {s['lines']}: {s['heartbeats']} hb  `{s['text']}`" for s in prof["steps"][:10])
                   + f"\n  (tactic block total {prof['tactic_block_heartbeats']} hb)")
    else:
        out.append(f"hb_profile: {prof.get('error')}")
    if hints:
        out.append("Linter hints on the best (free deletions, try them first):\n" + "\n".join("  - " + h for h in hints[:12]))
    out.append("Start with one lean_batch of several independent single edits of the best, guided by the profile and the exchange rate.")
    return "\n\n".join(out)


def stop_ok(evals: int, since_gain: int, min_evals: int, flat_evals: int) -> bool:
    return evals >= min_evals and since_gain >= flat_evals


def refusal(evals: int, since_gain: int, min_evals: int, flat_evals: int) -> str:
    need = []
    if evals < min_evals:
        need.append(f"{min_evals - evals} more evaluation(s) (done {evals} of at least {min_evals})")
    if since_gain < flat_evals:
        need.append(f"{flat_evals - since_gain} more evaluation(s) without a banked gain ({since_gain} so far)")
    return ("finish refused by the stop rule: " + " and ".join(need) + ". Keep golfing: profile the costliest steps, send a lean_batch of "
            "independent edits, combine the ones that helped, and try pool entries as bases.")


def pool_rows(pool: list[dict], best_text: str, k: int = 8) -> list[dict]:
    """Distinct compiling pool entries, best exact score first, with the lines that differ from the best."""
    import difflib
    seen, out = set(), []
    for e in sorted(pool, key=lambda e: -float(e.get("score_exact") or 0)):
        if e.get("sha") in seen or not e.get("proof"):
            continue
        seen.add(e["sha"])
        d = [l for l in difflib.unified_diff(best_text.splitlines(), e["proof"].splitlines(), lineterm="", n=0)
             if l[:1] in "+-" and not l.startswith(("+++", "---"))]
        out.append({"sha": e["sha"][:10], "score": round(float(e.get("score_exact") or 0), 4), "tokens": e.get("tokens"),
                    "heartbeats": e.get("heartbeats"), "is_best": not d, "diff": "\n".join(d)[:600]})
        if len(out) >= k:
            break
    return out


def body_tokens(decl: str, statement: str) -> int | None:
    b = split_declaration(decl, statement)
    return count_tokens(b) if b is not None else None


def dumps(o) -> str:
    return json.dumps(o, ensure_ascii=False)
