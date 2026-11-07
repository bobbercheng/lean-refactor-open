#!/usr/bin/env python3
"""Post-step op `argon_hbsimp`: heartbeat & simp/elaborator micro-normalizer, config toggles, and unused simp/grind/tactic pruning,
screened and heartbeat-measured in one warm-cached Core-compatible batch compile (`IO.getNumHeartbeats` sandwich + `unusedSimpArgs`
linter probe on the warmup copy). Every token comes from the proof, the statement, or Lean tactic syntax; no row names, lemma tables,
or proof text."""

# provenance: research lane gaplane2-argon (worktree lra-gl2-argon), commit 2b119a8, ported into open-post-v5-lanes (2026-11-04) unchanged
from __future__ import annotations

import difflib, hashlib, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness import hb_rewrite as HR  # noqa: E402
from harness import hb_tool_candidates as HC  # noqa: E402
from harness import hb_tool_extra as HE  # noqa: E402
from harness import lint_delete as LD  # noqa: E402
from harness.normalize import _mask, _pairs, apply as _norm_apply  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from scorer.forbidden import check_forbidden  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "argon_hbsimp"
MAX_CANDS = 3
MAX_BATCH_CANDS = 24
HB_START_RE = re.compile(r'^"?LRAHB_B\\t(\d+)\\t(\d+)"?$')
HB_END_RE = re.compile(r'^"?LRAHB_E\\t(\d+)\\t(\d+)"?$')
SORRY_RE = re.compile(r"\bdeclaration uses\b.*\bsorry", re.DOTALL)
EXT_LIST_HEAD_RE = re.compile(r"(?<![\w.'?!])(simp_all|simpa|simp|dsimp|grind|norm_num|field_simp|push_cast)(?![\w'?!])")


def proof_key(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def _extra_arg_dels(body: str) -> list[LD.Del]:
    """Extend `lint_delete`'s simp-list argument deletions to `grind`, `norm_num`, `field_simp`, `push_cast` and compound list items."""
    mask = _mask(body)
    pairs = _pairs(body, mask)
    fb = HR._first_by(body, mask)
    if fb < 0:
        return []
    out = []
    for m in EXT_LIST_HEAD_RE.finditer(body):
        i = m.start()
        if not HR._tac_pos(body, mask, i, fb):
            continue
        lb = LD._list_after_head(body, pairs, m.end())
        items = LD._list_items(body, mask, pairs, lb) if lb is not None else None
        if not items:
            continue
        if len(items) == 1 and m.group(1) == "grind" and "only" in body[m.end():lb]:
            continue
        for s, e in items:
            out.append(LD.Del("arg", (s, e), lb, body[s:e][:48], "delsearch", pos=s))
    return out


def has_sites(proof: str, statement: str) -> bool:
    hb = K.head_body(proof, statement)
    if hb is None:
        return False
    _, body = hb
    return bool(raw_candidates(proof, statement))


def _edit_interval(s: HR.Site) -> tuple[int, int]:
    if not s.edits:
        return s.span
    return (min(p for p, _, _ in s.edits), max(p + d for p, d, _ in s.edits))


def raw_candidates(proof: str, statement: str) -> list[dict]:
    """Generate prioritized heartbeat, simp/grind config, and deletion candidates from `proof` and `statement` alone."""
    hb = K.head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    tok0 = count_tokens(body)
    raw: list[dict] = []

    # 1. Deletions (`tac` and `arg` from lint_delete + extended list args for grind/simp/norm_num)
    base_dels = list(LD.search_dels(body))
    seen_del_spans = {(d.kind, d.span) for d in base_dels}
    for d in _extra_arg_dels(body):
        if (d.kind, d.span) not in seen_del_spans:
            seen_del_spans.add((d.kind, d.span))
            base_dels.append(d)

    for idx, d in enumerate(base_dels):
        if d.kind == "tac" and d.note.startswith("unfold ") and "decide +kernel" in body:
            continue
        nb = LD.render(body, [d])
        if nb == body:
            continue
        nt = count_tokens(nb)
        if d.kind == "arg":
            # `linter.unusedSimpArgs` on Copy 0 already checks `simp only` / `simp_all only`; prioritize `grind`, `simpa`, `dsimp`, non-`only`
            pre = body[max(0, d.lb - 24):d.lb]
            is_simp_only = bool(re.search(r"\bsimp(?:_all)?\s+only\s*$", pre))
            is_rev_or_erase = d.note.lstrip().startswith(("←", "<-", "-"))
            prio = ((0.88 if is_rev_or_erase else 1.05) if is_simp_only else 0.72) + 0.004 * idx
        else:
            # Prefer small cleanup tactic deletions over huge block deletions
            tok_dropped = max(1, tok0 - nt)
            prio = (0.78 if tok_dropped <= 8 else (0.96 if tok_dropped <= 20 else 1.35)) + 0.006 * idx
        raw.append({
            "op": f"{FAMILY}:del_{d.kind}",
            "decl": head + nb.rstrip() + "\n",
            "body": nb,
            "note": f"del_{d.kind}: {d.note}"[:200],
            "tokens": nt,
            "prio": prio,
            "bucket": f"del_{d.kind}",
            "del_obj": d,
        })

    # 2. `hb_rewrite` grouped and individual rewrites
    hr_sites = HR.sites(body, ops=HR.ALL_OPS)
    # 2a. Grouped `fold_all` combining non-conflicting simpmerge / rwsimpfold / simpafold
    fold_sites = [s for s in hr_sites if s.op in ("simpmerge", "rwsimpfold", "simpafold") and not s.late]
    fold_chosen: list[HR.Site] = []
    for s in fold_sites:
        if not HR.conflicts(s, fold_chosen):
            fold_chosen.append(s)
    if len(fold_chosen) >= 2:
        nb_fold = HR.apply(body, fold_chosen)
        if nb_fold != body:
            raw.append({
                "op": f"{FAMILY}:fold_all",
                "decl": head + nb_fold.rstrip() + "\n",
                "body": nb_fold,
                "note": f"fold_all ({len(fold_chosen)} sites)",
                "tokens": count_tokens(nb_fold),
                "prio": 0.22,
                "bucket": "group",
            })

    # 2b. Recursive `bulletdrop_all` (up to 4 rounds so nested bullets are dropped in a single candidate)
    bd_body = body
    bd_count = 0
    for _ in range(4):
        bd_sites = [s for s in HR.sites(bd_body, ops={"bulletdrop"}) if not s.late]
        bd_chosen: list[HR.Site] = []
        for s in bd_sites:
            if not HR.conflicts(s, bd_chosen):
                bd_chosen.append(s)
        if not bd_chosen:
            break
        nb_bd = HR.apply(bd_body, bd_chosen)
        if nb_bd == bd_body:
            break
        bd_body = nb_bd
        bd_count += len(bd_chosen)
    if bd_count >= 2 and bd_body != body:
        raw.append({
            "op": f"{FAMILY}:bulletdrop_all",
            "decl": head + bd_body.rstrip() + "\n",
            "body": bd_body,
            "note": f"bulletdrop_all ({bd_count} sites)",
            "tokens": count_tokens(bd_body),
            "prio": 0.36,
            "bucket": "group",
        })

    for grp_op, grp_prio in (
        ("anonhave", 0.32),
        ("use2refine", 0.34),
        ("exact2assumption", 0.36),
        ("rw2rewrite", 0.45),
        ("simponly2dsimp", 0.50),
    ):
        grp = [s for s in hr_sites if s.op == grp_op and not s.late]
        chosen: list[HR.Site] = []
        chosen_ivs: list[tuple[int, int]] = []
        for s in grp:
            if grp_op == "anonhave":
                iv = _edit_interval(s)
                if not any(iv[0] <= b and a <= iv[1] for a, b in chosen_ivs):
                    chosen.append(s)
                    chosen_ivs.append(iv)
            elif not HR.conflicts(s, chosen):
                chosen.append(s)
        if len(chosen) >= 2:
            nb = HR.apply(body, chosen)
            if nb != body:
                raw.append({
                    "op": f"{FAMILY}:{grp_op}_all",
                    "decl": head + nb.rstrip() + "\n",
                    "body": nb,
                    "note": f"{grp_op}_all ({len(chosen)} sites)",
                    "tokens": count_tokens(nb),
                    "prio": grp_prio,
                    "bucket": "group",
                })

    hr_prio_map = {
        "simpmerge": 0.25,
        "rwsimpfold": 0.28,
        "simpafold": 0.30,
        "use2refine": 0.55,
        "exact2assumption": 0.58,
        "anonhave": 0.60,
        "bulletdrop": 0.62,
        "simponly2dsimp": 0.85,
        "rw2rewrite": 0.90,
        "clearhyp": 1.05,
        "preorder": 1.15,
        "withreducible": 1.25,
        "firstorder": 1.30,
        "specialize": 1.40,
    }
    for idx, s in enumerate(hr_sites):
        nb = HR.apply(body, [s])
        if nb == body:
            continue
        nt = count_tokens(nb)
        base_p = hr_prio_map.get(s.op, 1.5) + (0.35 if s.late else 0.0) + (0.45 if nt > tok0 else 0.0) + 0.008 * idx
        raw.append({
            "op": f"{FAMILY}:{s.op}",
            "decl": head + nb.rstrip() + "\n",
            "body": nb,
            "note": f"{s.op}: {s.note}"[:200],
            "tokens": nt,
            "prio": base_p,
            "bucket": "hb_add" if nt > tok0 else "hr",
        })

    # 3. `hb_tool_candidates` + `hb_tool_extra` rewrites & config toggles
    hc_prio_map = {
        "let_have": 0.52,
        "elimination": 0.68,
        "elimination_rcases": 0.72,
        "ext_funext": 0.78,
        "dsimp_unfold": 0.82,
        "simp_once": 0.92,
        "simp_target": 0.98,
        "choose_destruct": 1.02,
        "congr_arg": 1.08,
        "simp_config": 1.48,
        "grind_config": 1.46,
        "vacuous_function": 1.65,
    }
    hc_all = list(HC.candidates(body)) + list(HE.extra_candidates(body))
    for idx, c in enumerate(hc_all):
        nb = _norm_apply(body, [c])
        if nb == body:
            continue
        nt = count_tokens(nb)
        base_p = hc_prio_map.get(c.kind, 1.5) + (0.35 if nt > tok0 and c.kind not in ("simp_once", "simp_target") else 0.0) + 0.005 * idx
        raw.append({
            "op": f"{FAMILY}:{c.kind}",
            "decl": head + nb.rstrip() + "\n",
            "body": nb,
            "note": f"{c.kind}: {c.note}"[:200],
            "tokens": nt,
            "prio": base_p,
            "bucket": "hb_add" if (nt > tok0 and c.kind not in ("simp_once", "simp_target")) else "hc",
        })

    # Balance across buckets via round-robin so even small batch caps (8..16) test every bucket (especially del_tac & del_arg)
    bucket_caps = {"group": 4, "del_tac": 7, "del_arg": 7, "hr": 5, "hc": 5, "hb_add": 2}
    bucket_order = ("group", "del_tac", "del_arg", "hr", "hc", "hb_add")
    by_bkt: dict[str, list[dict]] = {b: [] for b in bucket_order}
    seen, overflow = set(), []
    for c in sorted(raw, key=lambda x: (x["prio"], x["tokens"])):
        d = c["decl"].rstrip()
        if d in seen or d == proof.rstrip():
            continue
        seen.add(d)
        b = split_declaration(d, statement)
        if b is None or check_forbidden(b):
            continue
        c["decl"] = d + "\n"
        c["body"] = b
        bkt = c.get("bucket", "hr")
        if bkt in by_bkt and len(by_bkt[bkt]) < bucket_caps[bkt]:
            by_bkt[bkt].append(c)
        else:
            overflow.append(c)
    primary = []
    max_len = max((len(v) for v in by_bkt.values()), default=0)
    for idx in range(max_len):
        for bkt in bucket_order:
            if idx < len(by_bkt[bkt]):
                primary.append(by_bkt[bkt][idx])
    return primary + overflow


def _batch_cap(ctx: dict | None) -> int:
    cs = (ctx or {}).get("compile_s")
    if isinstance(cs, (int, float)) and cs > 0:
        if cs <= 6.0:
            return 22
        if cs <= 12.0:
            return 16
        if cs <= 20.0:
            return 10
        return 8
    return MAX_BATCH_CANDS


def build_warm_batch(statement: str, body0: str, cand_bodies: list[str], max_hb: int = 250000) -> tuple[str | None, list[tuple[int, int]], int]:
    """Build a pure-Core batch file where:
      - Copy 0 is `body0` with top-level `warningAsError false` and `linter.unusedSimpArgs true` (cache warmup + unused-simp-arg linter probe),
      - Copy 1 is `body0` with `linter.unusedSimpArgs false` (warm-cache heartbeat control),
      - Copies 2..K+1 are `cand_bodies`.
    Returns `(batch_text, spans, copy0_decl_start_line)`."""
    lines = [
        "theorem lraArgonDummy : True := trivial",
        "set_option warningAsError false",
        "set_option linter.unusedSimpArgs true",
    ]
    spans: list[tuple[int, int]] = []
    all_bodies = [body0, body0] + list(cand_bodies)
    copy0_decl_start = 1
    hb_bound = max(5000, int(max_hb))
    for i, b in enumerate(all_bodies):
        r = MS.renamed(statement, i)
        if r is None:
            return None, [], 0
        if i == 1:
            lines.append("set_option linter.unusedSimpArgs false")
        start_line = len(lines) + 1
        prefix_chunk = (
            f'#eval show IO String from do pure s!"LRAHB_B\\t{i}\\t{{← IO.getNumHeartbeats}}"\n'
            f"set_option maxHeartbeats {hb_bound} in\n"
            f"set_option Elab.async false in"
        )
        lines.extend(prefix_chunk.split("\n"))
        if i == 0:
            copy0_decl_start = len(lines) + 1
        decl_chunk = (
            f"{r.rstrip()} :={b.rstrip()}\n"
            f'#eval show IO String from do pure s!"LRAHB_E\\t{i}\\t{{← IO.getNumHeartbeats}}"'
        )
        lines.extend(decl_chunk.split("\n"))
        end_line = len(lines)
        spans.append((start_line, end_line))
    return "\n".join(lines) + "\n", spans, copy0_decl_start


def parse_warm_batch(messages: list, num_copies: int) -> tuple[dict[int, dict], dict[int, tuple[int, int]]]:
    """Parse `({i: {"ok": bool, "hb": int}}, {i: (b_line, e_line)})` from `build_warm_batch` messages."""
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
    line_spans: dict[int, tuple[int, int]] = {}
    for i in range(num_copies):
        if i not in hb_b or i not in hb_e or i not in b_line or i not in e_line:
            continue
        lo, hi = b_line[i], e_line[i]
        line_spans[i] = (lo, hi)
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
    return out, line_spans


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    """Screen and measure heartbeats of `raw_candidates` in one warm-cached batch compile; synthesize joint deletion candidate when >=2 pass."""
    if not versions:
        return {}
    hb = K.head_body(proof, statement)
    if hb is None:
        return {}
    head, body0 = hb
    raw = raw_candidates(proof, statement)
    if not raw:
        return {}
    batch_cands = raw[:_batch_cap(ctx)]
    inc_hb = (ctx or {}).get("inc_hb")
    compile_s = (ctx or {}).get("compile_s")
    if isinstance(inc_hb, (int, float)) and inc_hb > 0:
        max_hb = max(40000, int(inc_hb) * 4 + 10000)
    elif isinstance(compile_s, (int, float)) and 0 < compile_s <= 4.0:
        max_hb = 80000
    else:
        max_hb = 250000
    btxt, spans, _ = build_warm_batch(statement, body0, [c["body"] for c in batch_cands], max_hb=max_hb)
    if btxt is None:
        return {}
    res = run(btxt, versions[0])
    msgs = getattr(res, "messages", None) or []
    readings, line_spans = parse_warm_batch(msgs, len(batch_cands) + 2)
    r_warm = readings.get(1) or readings.get(0)
    ctl = r_warm if (r_warm and r_warm.get("ok")) else {"ok": True, "hb": int(inc_hb or 0)}
    hb0 = ctl["hb"]
    tok0 = count_tokens(body0)
    exchange = (ctx or {}).get("exchange")
    hb_min_drop = max(25, int(0.02 * hb0))

    passed = []
    passed_dels: list[LD.Del] = []
    for idx, c in enumerate(batch_cands):
        ri = readings.get(idx + 2)
        if not ri or not ri.get("ok"):
            continue
        pred = MS.predicted(ctl, body0, c["body"], ri, exchange)
        if pred is None or pred <= 0:
            continue
        dt = c["tokens"] - tok0
        dhb = hb0 - ri["hb"]
        # Require either strict token reduction or >=2% (+25hb) warm-cache heartbeat reduction
        if dt >= 0 and dhb < hb_min_drop:
            continue
        passed.append((pred, c["tokens"], ri["hb"], c))
        if "del_obj" in c:
            passed_dels.append(c["del_obj"])

    # Also check if Copy 0's `unusedSimpArgs` linter reported unused simp arguments
    lint_dels: list[LD.Del] = []
    if 0 in line_spans:
        lo0, hi0 = line_spans[0]
        # Copy 0 declaration starts at lo0 + 3 (after LRAHB_B, maxHeartbeats, Elab.async)
        r0_head = (MS.renamed(statement, 0) or statement).rstrip() + " :="
        decl0 = r0_head + body0.rstrip()
        c0_warns = [m for m in msgs if lo0 <= ((m.get("pos") or {}).get("line") or 0) <= hi0 and m.get("severity") == "warning"]
        try:
            lint_dels, _ = LD.lint_dels(body0, len(r0_head), 0, decl0, c0_warns, lo0 + 2)
        except Exception:
            lint_dels = []
        seen_spans = {(d.kind, d.span) for d in passed_dels}
        for ld in lint_dels:
            if (ld.kind, ld.span) not in seen_spans:
                seen_spans.add((ld.kind, ld.span))
                passed_dels.append(ld)

    passed.sort(key=lambda x: (-x[0], x[1], x[2]))
    final_cands: list[dict] = []
    seen_decls: set[str] = set()

    # Build joint deletion body from `lint_dels + passed_dels` if any
    jbody_all = LD.render(body0, passed_dels) if passed_dels else body0
    # Try to merge non-overlapping passed non-deletion candidates onto `jbody_all` via SequenceMatcher opcodes on `body0`
    base_edits = [
        (i1, i2, jbody_all[j1:j2])
        for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, body0, jbody_all, autojunk=False).get_opcodes()
        if tag != "equal"
    ]
    combo_edits = list(base_edits)
    combo_parts = (1 if passed_dels else 0)
    for _, _, _, c in passed:
        if "del_obj" in c:
            continue
        c_edits = [
            (i1, i2, c["body"][j1:j2])
            for tag, i1, i2, j1, j2 in difflib.SequenceMatcher(None, body0, c["body"], autojunk=False).get_opcodes()
            if tag != "equal"
        ]
        if not c_edits:
            continue
        if not any(a1 - 2 <= b2 and a2 - 2 <= b1 for a1, b1, _ in c_edits for a2, b2, _ in combo_edits):
            combo_edits.extend(c_edits)
            combo_parts += 1

    if combo_parts >= 2 and combo_edits:
        cbody = body0
        for a, b, repl in sorted(combo_edits, key=lambda e: -e[0]):
            cbody = cbody[:a] + repl + cbody[b:]
        if cbody != body0 and not check_forbidden(cbody):
            cdecl = (head + cbody.rstrip() + "\n").rstrip()
            if cdecl != proof.rstrip() and cdecl not in seen_decls:
                seen_decls.add(cdecl)
                final_cands.append({
                    "op": f"{FAMILY}:combo",
                    "decl": cdecl + "\n",
                    "note": f"combo ({len(passed_dels)} dels + {combo_parts - (1 if passed_dels else 0)} rewrites)"[:200],
                })

    # If >=2 deletions passed (or lint_dels + passed_dels), emit the joint deletion candidate
    if len(passed_dels) >= 2:
        if jbody_all != body0 and not check_forbidden(jbody_all):
            jdecl = (head + jbody_all.rstrip() + "\n").rstrip()
            if jdecl != proof.rstrip() and jdecl not in seen_decls:
                seen_decls.add(jdecl)
                final_cands.append({
                    "op": f"{FAMILY}:joint_del",
                    "decl": jdecl + "\n",
                    "note": f"joint_del ({len(passed_dels)} deletions)"[:200],
                })

    # If `lint_dels` found unused simp args in Copy 0, emit the all-lint-deletions candidate
    if lint_dels:
        lbody = LD.render(body0, lint_dels)
        if lbody != body0 and not check_forbidden(lbody):
            ldecl = (head + lbody.rstrip() + "\n").rstrip()
            if ldecl != proof.rstrip() and ldecl not in seen_decls:
                seen_decls.add(ldecl)
                final_cands.append({
                    "op": f"{FAMILY}:lint_del",
                    "decl": ldecl + "\n",
                    "note": f"lint_del ({len(lint_dels)} unused simp args)"[:200],
                })

    for _, _, _, c in passed:
        d = c["decl"].rstrip()
        if d not in seen_decls:
            seen_decls.add(d)
            final_cands.append({k: c[k] for k in ("op", "decl", "note")})

    emit_cap = 2 if (isinstance(compile_s, (int, float)) and compile_s > 8.0) else MAX_CANDS
    if log is not None:
        log(f"argon_hbsimp query: {len(batch_cands)} screened, {len(passed)} passed, {len(lint_dels)} lint, {len(final_cands[:emit_cap])} emitted")
    return {"argon_hbsimp_cands": final_cands[:emit_cap], "argon_hbsimp_for": proof_key(proof)}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=MAX_CANDS, ctx=None) -> list[dict]:
    """Return query-verified candidates when `ctx` matches `proof`, else pure top-ranked candidates (for `--show`)."""
    c = ctx or {}
    cap = max(1, int(max_per_op or MAX_CANDS))
    if c.get("argon_hbsimp_for") == proof_key(proof):
        return list(c.get("argon_hbsimp_cands") or [])[:cap]
    if "argon_hbsimp_for" in c:
        return []
    return [{k: x[k] for k in ("op", "decl", "note")} for x in raw_candidates(proof, statement)[:cap]]
