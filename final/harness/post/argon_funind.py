#!/usr/bin/env python3
"""Post-step op `argon_funind`: functional induction + closer/tail adaptation, pre-screened and heartbeat-measured in one Core-compatible
batch compile (`IO.getNumHeartbeats` sandwich, requiring no `import Lean`). Every token comes from the proof, the statement, or Lean tactic
syntax; no row names, lemma tables, or proof text."""
from __future__ import annotations

# provenance: research lane gaplane2-argon (worktree lra-gl2-argon), commit b4b47ef, ported unchanged into open-post-v3 (2026-11-04)

import hashlib, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness import funind as FI  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from scorer.forbidden import check_forbidden  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "argon_funind"
MAX_CANDS = 8
MAX_QUERY_VARIANTS = 24
HB_START_RE = re.compile(r'^"?LRAHB_B\\t(\d+)\\t(\d+)"?$')
HB_END_RE = re.compile(r'^"?LRAHB_E\\t(\d+)\\t(\d+)"?$')
SORRY_RE = re.compile(r"\bdeclaration uses\b.*\bsorry", re.DOTALL)
RCASES_DROP_RE = re.compile(r"^\s*(?:any_goals|all_goals)\s+rcases\s+[^\n]+$")
GRIND_LINE_RE = re.compile(r"^\s*(grind(?:\s+only)?\s*\[[^\]]*\])\s*$")
OBTAIN_HYP_RE = re.compile(r"\bobtain\s+⟨[^⟩]+⟩\s*:=\s*([^\W\d][\w'!?₀-₉]*)")
AUX_LEMMA_RE = re.compile(r"\b(?:cases|have\s*:=)\s+([^\W\d][\w'!?₀-₉]*(?:\.[^\W\d][\w'!?₀-₉]*)+)\s+([^\W\d][\w'!?₀-₉]*)\b")
SIMP_AT_CHUNK_RE = re.compile(r"(?m)^[ \t]*(?:all_goals|any_goals)\s+[^\n]*\bsimp(?:\s+only)?\s*\[[^\]]*\]\s*at\s+([^\W\d][\w'!?₀-₉]*)")


def proof_key(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def has_sites(proof: str, statement: str) -> bool:
    if not FI.IND_RE.search(proof):
        return False
    hb = FI.head_body(proof, statement)
    if hb is None:
        return False
    _, body = hb
    for s in FI.induction_sites(body):
        if FI.fun_targets(statement, s["var"], s["gen"]) or (s["using"] and s["using"].endswith(".induct")):
            return True
    return False


def _drop_fn_from_simp_only(text: str, f_full: str) -> str:
    """Remove `f_full` and its short suffix from `simp only [...]` / `simp_all only [...]` lists when `fun_induction` already unfolds it."""
    names = {f_full, f_full.split(".")[-1]}

    def repl(m: re.Match) -> str:
        head, inner, tail = m.group(1), m.group(2), m.group(3)
        items = [x.strip() for x in inner.split(",")]
        kept = [x for x in items if x.lstrip("↓↑←- ").strip() not in names]
        if not kept or len(kept) == len(items):
            return m.group(0)
        return f"{head}[{', '.join(kept)}]{tail}"

    return re.sub(r"(\bsimp(?:_all)?\s+only\s*)\[([^\]]*)\](\s*(?:at\b|\n|$))", repl, text)


def raw_candidates(proof: str, statement: str) -> list[dict]:
    """Generate unscreened functional-induction candidates from `proof` and `statement` alone."""
    hb = FI.head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    lines = body.split("\n")
    btypes = FI.binder_types(statement)
    cands = list(FI.generate(proof, statement))

    for s in FI.induction_sites(body):
        funs = FI.fun_targets(statement, s["var"], s["gen"])
        if not funs:
            continue
        line = lines[s["line"]]
        a0, a1 = s["tac_span"]
        prefix = " " * (len(line) - len(line.lstrip(" ")))
        block_lines = lines[s["line"]:s["end"] + 1]
        hints_all = FI.hint_names(s["block"], [])
        for f in funs:
            f["hint_hits"] = sum(1 for h in hints_all if h == f["f"] or h.endswith("." + f["f"]) or f["f"].endswith("." + h)) + \
                s["block"].count(f["f"].split(".")[-1])
        funs.sort(key=lambda f: (-f["hint_hits"], -f["n"]))
        stmt_funs = []
        for f in funs:
            if f["f"] not in stmt_funs:
                stmt_funs.append(f["f"])
        grind_lines = []
        for bl in block_lines[1:]:
            gm = GRIND_LINE_RE.match(bl)
            if gm and gm.group(1) not in grind_lines:
                grind_lines.append(gm.group(1))

        for fr, f in enumerate(funs[:FI.MAX_FUNS]):
            F = f["f"]
            lit = f["args"][0]
            compound = not all(FI._is_ident(x) or x[0].isdigit() for x in FI._split_args(lit))
            variants = (f["args"][1:2] + [lit]) if compound and len(f["args"]) > 1 else list(f["args"][:2])
            for ar, args in enumerate(variants):
                argvars = {t for t, _, _ in FI.lex(args) if FI._is_ident(t)}
                argvars |= {t.split(".")[0] for t in argvars}
                for v in list(argvars):
                    argvars |= {t for t, _, _ in FI.lex(btypes.get(v, "")) if FI._is_ident(t)}
                gen = [g for g in s["gen"] if g not in argvars]
                gtxt = (" generalizing " + " ".join(gen)) if gen else ""
                fi = f"fun_induction {F} {args}{gtxt}"
                r = fr + ar

                # (1) Multi-function statement hints: `fun_induction F args <;> grind [F1, F2]` / `simp_all [F1, F2]`
                if len(stmt_funs) >= 2:
                    f_list = ", ".join(stmt_funs)
                    cands.append(FI._mk(head, lines, s, [prefix + f"{fi} <;> grind [{f_list}]"],
                                        s["line"], s["end"], "block:grind_funs", 0.8 + 2.0 * r, F, args))
                    cands.append(FI._mk(head, lines, s, [prefix + f"{fi} <;> simp_all [{f_list}]"],
                                        s["line"], s["end"], "block:simp_funs", 0.9 + 2.0 * r, F, args))

                # (2) Preserve block's `grind only [...]` closer after `fun_induction` + `simp_all`
                f_list = ", ".join(stmt_funs if len(stmt_funs) >= 2 else [F])
                for gl in grind_lines[:2]:
                    cands.append(FI._mk(head, lines, s,
                                        [prefix + f"{fi} <;> simp_all [{f_list}]", prefix + gl],
                                        s["line"], s["end"], "tail:semi_grind", 0.6 + 2.0 * r, F, args))
                    cands.append(FI._mk(head, lines, s,
                                        [prefix + fi, prefix + f"all_goals simp_all [{f_list}]", prefix + gl],
                                        s["line"], s["end"], "tail:all_grind", 0.7 + 2.0 * r, F, args))
                    cands.append(FI._mk(head, lines, s,
                                        [prefix + f"{fi} <;> {gl}"],
                                        s["line"], s["end"], "tail:direct_grind", 0.75 + 2.0 * r, F, args))

                # (3) Adapted swap: drop redundant `any_goals rcases ...`, strip `F` from `simp only`, relax `all_goals simp` -> `any_goals simp`
                if len(block_lines) >= 2:
                    new_fi_line = prefix + fi + line[a1:]
                    tail_lines = list(block_lines[1:])
                    if tail_lines and RCASES_DROP_RE.match(tail_lines[0]):
                        tail_lines = tail_lines[1:]
                    tail_txt = "\n".join(tail_lines)
                    tail_stripped = _drop_fn_from_simp_only(tail_txt, F)
                    for t_idx, cur_tail in enumerate(dict.fromkeys([tail_stripped, tail_txt])):
                        cands.append(FI._mk(head, lines, s, [new_fi_line] + cur_tail.split("\n"),
                                            s["line"], s["end"], "swap:clean", 0.4 + 0.05 * t_idx + 2.0 * r, F, args))
                        cur_any = re.sub(r"\ball_goals(\s+(?:first\b|simp\b))", r"any_goals\1", cur_tail)
                        if cur_any != cur_tail:
                            cands.append(FI._mk(head, lines, s, [new_fi_line] + cur_any.split("\n"),
                                                s["line"], s["end"], "swap:any_simp", 0.35 + 0.05 * t_idx + 2.0 * r, F, args))

                    # (4) Existential-unpacking collapse: when >=2 `obtain ⟨...⟩ := hyp` follow a `simp ... at hyp`
                    obt_hyps = OBTAIN_HYP_RE.findall(tail_stripped)
                    sm = SIMP_AT_CHUNK_RE.search(tail_stripped)
                    if sm and len(obt_hyps) >= 2:
                        hyp = sm.group(1)
                        if obt_hyps.count(hyp) >= 2:
                            simp_chunk = re.sub(r"^\s*all_goals\b", prefix + "any_goals", sm.group(0))
                            aux_lems = list(dict.fromkeys(m.group(1) for m in AUX_LEMMA_RE.finditer(tail_stripped)))
                            last_ln = tail_lines[-1].strip()
                            closer_ln = last_ln if last_ln.startswith(("all_goals ", "any_goals ")) else f"all_goals {last_ln}"
                            collapsed = [
                                new_fi_line,
                                simp_chunk,
                                prefix + f"any_goals repeat obtain ⟨_, {hyp}⟩ := {hyp}",
                            ]
                            for lem in aux_lems[:2]:
                                collapsed.append(prefix + f"any_goals have := {lem} (by assumption)")
                            collapsed.append(prefix + "any_goals subst_vars")
                            collapsed.append(prefix + closer_ln)
                            cands.append(FI._mk(head, lines, s, collapsed,
                                                s["line"], s["end"], "collapse:obtain", 0.3 + 2.0 * r, F, args))

    seen, out = set(), []
    for c in sorted(cands, key=lambda x: (x.get("prio", 9.0), x.get("tokens", 999999))):
        d = c["decl"].rstrip()
        if d in seen or d == proof.rstrip():
            continue
        seen.add(d)
        b = split_declaration(d, statement)
        if b is None or check_forbidden(b):
            continue
        kind = c.get("kind", "block").split(":")[0]
        op = f"{FAMILY}:{kind}"
        note = c.get("note") or f"{c.get('kind')} {c.get('f')} [{c.get('args')}]"
        out.append({"op": op, "decl": d + "\n", "body": b, "note": note[:200], "tokens": count_tokens(b), "prio": c.get("prio", 9.0)})
    return out


def build_core_batch(statement: str, bodies: list[str], max_hb: int = 50000) -> tuple[str | None, list[tuple[int, int]]]:
    """Build a pure-Core batch file measuring compilation and heartbeats of `bodies` via `IO.getNumHeartbeats`."""
    lines = ["theorem lraArgonDummy : True := trivial"]
    spans: list[tuple[int, int]] = []
    for i, b in enumerate(bodies):
        r = MS.renamed(statement, i)
        if r is None:
            return None, []
        start_line = len(lines) + 1
        chunk = (
            f'#eval show IO String from do pure s!"LRAHB_B\\t{i}\\t{{← IO.getNumHeartbeats}}"\n'
            f"set_option maxHeartbeats {max(5000, int(max_hb))} in\n"
            f"set_option Elab.async false in\n"
            f"{r.rstrip()} :={b.rstrip()}\n"
            f'#eval show IO String from do pure s!"LRAHB_E\\t{i}\\t{{← IO.getNumHeartbeats}}"'
        )
        chunk_lines = chunk.split("\n")
        lines.extend(chunk_lines)
        end_line = len(lines)
        spans.append((start_line, end_line))
    return "\n".join(lines) + "\n", spans


def parse_core_batch(messages: list, spans: list[tuple[int, int]], line_offset: int | None = None) -> dict[int, dict]:
    """Parse `{i: {"ok": bool, "hb": int}}` from a `build_core_batch` run's JSON messages."""
    hb_b: dict[int, int] = {}
    hb_e: dict[int, int] = {}
    b_line: dict[int, int] = {}
    e_line: dict[int, int] = {}
    for m in messages or []:
        txt = K.msg_text(m).strip()
        ln = (m.get("pos") or {}).get("line") or 0
        mb = HB_START_RE.match(txt)
        if mb:
            idx = int(mb.group(1))
            hb_b[idx] = int(mb.group(2))
            b_line[idx] = ln
            continue
        me = HB_END_RE.match(txt)
        if me:
            idx = int(me.group(1))
            hb_e[idx] = int(me.group(2))
            e_line[idx] = ln
    out: dict[int, dict] = {}
    for i in range(len(spans)):
        if i not in hb_b or i not in hb_e or i not in b_line or i not in e_line:
            continue
        lo, hi = b_line[i], e_line[i]
        bad = False
        for m in messages or []:
            ln = (m.get("pos") or {}).get("line") or 0
            if lo <= ln <= hi:
                sev = m.get("severity")
                data = str(m.get("data") or "")
                if sev == "error" or m.get("kind") == "hasSorry" or SORRY_RE.search(data):
                    bad = True
                    break
        if not bad and hb_e[i] >= hb_b[i]:
            out[i] = {"ok": True, "hb": max(1, (hb_e[i] - hb_b[i]) // 1000)}
    return out


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    """Screen and measure heartbeats of `raw_candidates` in one batch compile; return ranked winning candidates."""
    if not versions:
        return {}
    hb = FI.head_body(proof, statement)
    if hb is None:
        return {}
    _, body0 = hb
    raw = raw_candidates(proof, statement)
    if not raw:
        return {}
    batch_cands = raw[:MAX_QUERY_VARIANTS - 1]
    inc_hb = (ctx or {}).get("inc_hb") or 20000
    max_hb = max(15000, int(inc_hb) * 4 + 5000)
    bodies = [body0] + [c["body"] for c in batch_cands]
    btxt, spans = build_core_batch(statement, bodies, max_hb=max_hb)
    if btxt is None:
        return {}
    res = run(btxt, versions[0])
    readings = parse_core_batch(getattr(res, "messages", None) or [], spans)
    r0 = readings.get(0)
    tok0 = count_tokens(body0)
    ctl = r0 if (r0 and r0.get("ok")) else {"ok": True, "hb": int(inc_hb or 0)}
    exchange = (ctx or {}).get("exchange")
    kept = []
    for idx, c in enumerate(batch_cands, 1):
        ri = readings.get(idx)
        if not ri or not ri.get("ok"):
            continue
        pred = MS.predicted(ctl, body0, c["body"], ri, exchange)
        if pred is not None and (pred > 0 or c["tokens"] < tok0):
            kept.append((pred, c["tokens"], ri["hb"], {k: c[k] for k in ("op", "decl", "note")}))
    kept.sort(key=lambda x: (-x[0], x[1], x[2]))
    if log is not None:
        log(f"argon_funind query: {len(batch_cands)} screened, {len(kept)} passed")
    return {"argon_funind_cands": [x[3] for x in kept[:MAX_CANDS]], "argon_funind_for": proof_key(proof)}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=MAX_CANDS, ctx=None) -> list[dict]:
    """Return query-verified candidates when `ctx` matches `proof`, else pure top-ranked candidates (for `--show`)."""
    c = ctx or {}
    cap = max(1, int(max_per_op or MAX_CANDS))
    if c.get("argon_funind_for") == proof_key(proof):
        return list(c.get("argon_funind_cands") or [])[:cap]
    if "argon_funind_for" in c:
        return []
    return [{k: x[k] for k in ("op", "decl", "note")} for x in raw_candidates(proof, statement)[:cap]]
