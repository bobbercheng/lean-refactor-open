#!/usr/bin/env python3
"""Post-step op `argon_calcstep`: structural `calc`-chain wildcarding (`calc <LHS> <rel> <RHS> := <prf>` -> `calc _ <rel> _ := <prf>`
and `:= by apply/exact <term>` unwrap), nested `have h : T := by <BODY>; [rw at h;] assumption` unwrap, `have : X = Y := by ... cases h; rfl; subst this`
direct-cases unwrap, `obtain ⟨...⟩ := Prod.mk.inj h` compaction, and multi-line adjacent `simp only` / `rw` / `erw` block fusion,
screened and heartbeat-measured in a single pure-Core `IO.getNumHeartbeats` batch compile.

Every token comes from the proof, the statement, or Lean syntax; no row names, lemma tables, or proof text."""

# provenance: research lane gaplane2-argon (worktree lra-gl2-argon), commit 2b119a8, ported into open-post-v5-lanes (2026-11-04) unchanged
from __future__ import annotations

import difflib, hashlib, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.normalize import _mask, _pairs  # noqa: E402
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from scorer.forbidden import check_forbidden  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

FAMILY = "argon_calcstep"
MAX_CANDS = 3
MAX_BATCH_CANDS = 22
HB_START_RE = re.compile(r'^"?LRAHB_B(?:\\t|\t)(\d+)(?:\\t|\t)(\d+)"?$')
HB_END_RE = re.compile(r'^"?LRAHB_E(?:\\t|\t)(\d+)(?:\\t|\t)(\d+)"?$')
CALC_KW_RE = re.compile(r"(?<![\w.'])calc(?![\w'?!])")
REL_RE = re.compile(r"^(≤|<|=|≥|>|≠|↔|⊆|⊂)(?![=<>])")


def _indent_of(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def _dedent_block(text: str, spaces: int = 2) -> str:
    out = []
    for ln in text.splitlines():
        if ln.startswith(" " * spaces):
            out.append(ln[spaces:])
        else:
            out.append(ln)
    return "\n".join(out)


def _find_ident_spans(text: str, name: str, offset: int = 0) -> list[tuple[int, int]]:
    if not name:
        return []
    mask = _mask(text)
    pat = re.compile(rf"(?<![\w.']){re.escape(name)}(?![\w'])")
    out = []
    for m in pat.finditer(text):
        if not mask[m.start()]:
            out.append((offset + m.start(), offset + m.end()))
    return out


def _parse_calc_steps(body: str) -> list[dict]:
    """Parse `calc` blocks and their step headers `<lhs> <rel> <rhs> := <prf>`."""
    mask = _mask(body)
    pairs = _pairs(body, mask)
    steps: list[dict] = []

    for cm in CALC_KW_RE.finditer(body):
        c_start = cm.start()
        if mask[c_start]:
            continue
        ls = body.rfind("\n", 0, c_start) + 1
        calc_indent = _indent_of(body[ls:c_start + 4])
        # Find the end of the `calc` block by line indentation
        pos = cm.end()
        block_end = len(body)
        cur = body.find("\n", pos)
        while cur != -1 and cur + 1 < len(body):
            nxt_nl = body.find("\n", cur + 1)
            ln = body[cur + 1:nxt_nl if nxt_nl != -1 else len(body)]
            st = ln.strip()
            if st and not st.startswith("--") and not mask[cur + 1]:
                if _indent_of(ln) <= calc_indent:
                    block_end = cur
                    break
            cur = nxt_nl

        # Scan inside `body[cm.end():block_end]` for top-level `:=` of calc steps
        i = cm.end()
        step_idx = 0
        lhs_start = i
        while i < block_end:
            if mask[i]:
                i += 1
                continue
            if i in pairs and pairs[i] > i:
                i = pairs[i] + 1
                continue
            if body[i:i + 2] == ":=":
                # Found a `:=` inside the calc block; check if the header `body[lhs_start:i]` has a top-level relational op
                hdr_lo = lhs_start
                hdr_hi = i
                # Find top-level relational operator in `body[hdr_lo:hdr_hi]`
                j = hdr_lo
                rel_pos = None
                rel_len = 0
                while j < hdr_hi:
                    if mask[j]:
                        j += 1
                        continue
                    if j in pairs and pairs[j] > j:
                        j = pairs[j] + 1
                        continue
                    rm = REL_RE.match(body[j:hdr_hi])
                    if rm:
                        rel_pos = j
                        rel_len = len(rm.group(1))
                        break
                    j += 1
                # Find where this step's proof ends: either the next `_ <rel>` line in the calc block or `block_end`
                prf_start = i + 2
                prf_end = block_end
                scan_nl = body.find("\n", prf_start, block_end)
                while scan_nl != -1 and scan_nl + 1 < block_end:
                    nn = body.find("\n", scan_nl + 1, block_end)
                    ln = body[scan_nl + 1:nn if nn != -1 else block_end]
                    if re.match(r"^[ \t]+_[ \t]*(?:≤|<|=|≥|>|≠|↔|⊆|⊂)", ln) and not mask[scan_nl + 1]:
                        prf_end = scan_nl
                        break
                    scan_nl = nn

                if rel_pos is not None:
                    # Trim leading/trailing whitespace spans for LHS and RHS
                    l_lo = hdr_lo
                    while l_lo < rel_pos and body[l_lo].isspace():
                        l_lo += 1
                    l_hi = rel_pos
                    while l_hi > l_lo and body[l_hi - 1].isspace():
                        l_hi -= 1
                    r_lo = rel_pos + rel_len
                    while r_lo < hdr_hi and body[r_lo].isspace():
                        r_lo += 1
                    r_hi = hdr_hi
                    while r_hi > r_lo and body[r_hi - 1].isspace():
                        r_hi -= 1
                    steps.append({
                        "calc_start": c_start,
                        "step_idx": step_idx,
                        "lhs_span": (l_lo, l_hi),
                        "lhs_raw": body[l_lo:l_hi],
                        "rel_span": (rel_pos, rel_pos + rel_len),
                        "rel_raw": body[rel_pos:rel_pos + rel_len],
                        "rhs_span": (r_lo, r_hi),
                        "rhs_raw": body[r_lo:r_hi],
                        "walrus_pos": i,
                        "prf_span": (prf_start, prf_end),
                        "prf_raw": body[prf_start:prf_end].strip(),
                    })
                    step_idx += 1
                lhs_start = prf_end
                i = prf_end
                continue
            i += 1
    return steps


def raw_candidates(proof: str, statement: str) -> list[dict]:
    body = split_declaration(proof, statement)
    if body is None:
        return []
    head = f"{statement} :="
    tok0 = count_tokens(body)
    raw: list[dict] = []

    def add_cand(op_sub: str, nb: str, note: str, prio: float, bucket: str):
        if nb == body:
            return
        nt = count_tokens(nb)
        if nt >= tok0:
            return
        raw.append({
            "op": f"{FAMILY}:{op_sub}",
            "decl": head + nb.rstrip() + "\n",
            "body": nb,
            "note": f"{op_sub}: {note}"[:200],
            "tokens": nt,
            "prio": prio - 0.025 * min(60, tok0 - nt),
            "bucket": bucket,
        })

    # --- Family 1: `calc` wildcarding & `:= by apply/exact` unwrap ---
    csteps = _parse_calc_steps(body)
    for idx, st in enumerate(csteps):
        l_lo, l_hi = st["lhs_span"]
        r_lo, r_hi = st["rhs_span"]
        lhs_s = st["lhs_raw"]
        rhs_s = st["rhs_raw"]
        prf_s = st["prf_raw"]
        p_lo, p_hi = st["prf_span"]

        # 1a. Initial step LHS -> `_`
        lhs_can_wild = st["step_idx"] == 0 and lhs_s != "_" and count_tokens(lhs_s) >= 2
        if lhs_can_wild:
            nb_l = body[:l_lo] + "_" + body[l_hi:]
            add_cand("calc_lhs", nb_l, f"wildcard calc LHS ({count_tokens(lhs_s)} tok)", 0.28 + 0.0002 * idx, "calc")

        # 1b. Step RHS -> `_` (when proof is not `by rw`/`by ring`/`by field_simp` that needs target)
        rhs_can_wild = rhs_s != "_" and count_tokens(rhs_s) >= 3 and not re.match(r"^by\s+(?:rw|rewrite|ring|field_simp|simp\b|linear_combination)", prf_s)
        if rhs_can_wild:
            nb_r = body[:r_lo] + "_" + body[r_hi:]
            add_cand("calc_rhs", nb_r, f"wildcard calc RHS ({count_tokens(rhs_s)} tok)", 0.29 + 0.0002 * idx, "calc")

        # 1c. Both LHS and RHS -> `_` on step 0
        if lhs_can_wild and rhs_can_wild:
            nb_lr = body[:l_lo] + "_" + body[l_hi:r_lo] + "_" + body[r_hi:]
            add_cand("calc_both", nb_lr, f"wildcard calc LHS+RHS", 0.24 + 0.0002 * idx, "calc")

        # 1d. `:= by apply <term>` or `:= by exact <term>` unwrap in calc step
        am = re.match(r"^by\s+(?:apply|exact)\s+([^\n;]+)$", prf_s)
        if am:
            term_a = am.group(1).strip()
            nb_ap = body[:p_lo] + " " + term_a + body[p_hi:]
            add_cand("calc_apply", nb_ap, f"unwrap by apply/exact in calc", 0.32 + 0.0002 * idx, "calc")
            if rhs_can_wild:
                nb_apr = body[:r_lo] + "_" + body[r_hi:p_lo] + " " + term_a + body[p_hi:]
                add_cand("calc_rhs_apply", nb_apr, f"wildcard calc RHS + unwrap apply", 0.26 + 0.0002 * idx, "calc")
            if lhs_can_wild and rhs_can_wild:
                nb_aplr = body[:l_lo] + "_" + body[l_hi:r_lo] + "_" + body[r_hi:p_lo] + " " + term_a + body[p_hi:]
                add_cand("calc_both_apply", nb_aplr, f"wildcard calc LHS+RHS + unwrap apply", 0.22 + 0.0002 * idx, "calc")

    # --- Family 2: Nested `have <nm> [: <T>] := by\n <BODY>\n <indent>[rw at <nm>;] assumption` unwrap ---
    have_by_re = re.compile(r"^([ \t]*)have(?:\s+([^\W\d][\w'₀-₉]*))?(?:\s*:\s*[^\n]+?)?\s*:=\s*by[ \t]*\n", re.M)
    mask = _mask(body)
    for idx, hm in enumerate(have_by_re.finditer(body)):
        if mask[hm.start()]:
            continue
        ind_s = hm.group(1)
        ind_n = len(ind_s)
        h_nm = hm.group(2) or "this"
        inner_start = hm.end()
        # Scan lines of the `have ... := by` block (strictly greater indent than `ind_n`)
        cur = inner_start
        inner_end = len(body)
        while cur < len(body):
            nxt_nl = body.find("\n", cur)
            ln = body[cur:nxt_nl if nxt_nl != -1 else len(body)]
            st = ln.strip()
            if st and not st.startswith("--") and not mask[cur]:
                if _indent_of(ln) <= ind_n:
                    inner_end = cur
                    break
            if nxt_nl == -1:
                inner_end = len(body)
                break
            cur = nxt_nl + 1

        inner_block = body[inner_start:inner_end].rstrip("\n")
        if not inner_block.strip():
            continue
        # Inspect the lines immediately following `inner_end` at indentation `ind_n`
        tail = body[inner_end:]
        # Subcase 2a: Immediately followed by `<ind_s>(?:assumption|exact <h_nm>)`
        m_assump = re.match(rf"^{re.escape(ind_s)}(?:assumption|exact[ \t]+{re.escape(h_nm)})[ \t]*(?=\n|$)", tail)
        if m_assump:
            after_pos = inner_end + m_assump.end()
            if not _find_ident_spans(body[after_pos:], h_nm):
                dedented = _dedent_block(inner_block, 2)
                nb_u = body[:hm.start()] + dedented + body[after_pos:]
                add_cand("have_assump", nb_u, f"unwrap redundant have {h_nm}..assumption", 0.23 + 0.0002 * idx, "unwrap")

        # Subcase 2b: Immediately followed by `<ind_s>(rw|rewrite) [(←|<-)? <rule>] at <h_nm>\n<ind_s>assumption`
        m_rw_assump = re.match(
            rf"^{re.escape(ind_s)}(rw|rewrite)[ \t]*\[[ \t]*(←|<-)?[ \t]*([^\],]+)[ \t]*\][ \t]+at[ \t]+{re.escape(h_nm)}[ \t]*\n{re.escape(ind_s)}(?:assumption|exact[ \t]+{re.escape(h_nm)})[ \t]*(?=\n|$)",
            tail,
        )
        if m_rw_assump:
            after_pos = inner_end + m_rw_assump.end()
            if not _find_ident_spans(body[after_pos:], h_nm):
                rw_kw, rev_arr, r_item = m_rw_assump.group(1), m_rw_assump.group(2), m_rw_assump.group(3).strip()
                flipped = r_item if rev_arr else f"← {r_item}"
                dedented = _dedent_block(inner_block, 2)
                nb_rwu = body[:hm.start()] + f"{ind_s}{rw_kw} [{flipped}]\n{dedented}" + body[after_pos:]
                add_cand("have_rw_assump", nb_rwu, f"unwrap have {h_nm} + invert {rw_kw} [{flipped}]", 0.24 + 0.0002 * idx, "unwrap")

        # --- Family 3: `have : X = Y := by <LINES>; cases <h>; rfl\n<ind_s>subst this` unwrap ---
        m_subst = re.match(rf"^{re.escape(ind_s)}subst[ \t]+{re.escape(h_nm)}[ \t]*(?=\n|$)", tail)
        if m_subst:
            after_pos = inner_end + m_subst.end()
            inner_lines = inner_block.splitlines()
            if len(inner_lines) >= 3 and inner_lines[-1].strip() == "rfl" and re.match(r"^[ \t]*cases[ \t]+[^\s]+$", inner_lines[-2]):
                dedented_no_rfl = _dedent_block("\n".join(inner_lines[:-1]), 2)
                nb_cs = body[:hm.start()] + dedented_no_rfl + body[after_pos:]
                add_cand("cases_subst", nb_cs, f"unwrap have {h_nm}..cases..rfl; subst {h_nm}", 0.25 + 0.0002 * idx, "unwrap")
                # Check if `dedented_no_rfl` also has `have [h1] := E1\n rewrite [R] at h1\n have h2 := E2\n rewrite [h1] at h2\n cases h2`
                fm = re.match(
                    r"^([ \t]*)have(?:[ \t]+([^\W\d][\w'₀-₉]*))?[ \t]*:=[ \t]*([^\n]+)\n\1(rw|rewrite)[ \t]*\[([^\]]+)\][ \t]+at[ \t]+([^\W\d][\w'₀-₉]*)\n\1have[ \t]+([^\W\d][\w'₀-₉]*)[ \t]*:=[ \t]*([^\n]+)\n\1(?:rw|rewrite)[ \t]*\[\6\][ \t]+at[ \t]+\7\n\1cases[ \t]+\7$",
                    dedented_no_rfl,
                )
                if fm and (fm.group(2) or "this") == fm.group(6):
                    f_ind, h1_opt, e1_s, rw_k, r_list, h1_nm, h2_nm, e2_s = fm.groups()
                    h1_decl = f"have {h1_opt} :=" if h1_opt else "have :="
                    folded = f"{f_ind}{h1_decl} {e1_s}\n{f_ind}{rw_k} [{r_list.strip()}, {e2_s.strip()}] at {h1_nm}\n{f_ind}cases {h1_nm}"
                    nb_csf = body[:hm.start()] + folded + body[after_pos:]
                    add_cand("cases_subst_fold", nb_csf, f"fold {h1_nm}/{h2_nm} + cases_subst", 0.21 + 0.0002 * idx, "unwrap")

        # Subcase 2c: `have <nm> : <Type> := by\n (rw|rewrite) [(←|<-)? <K>]\n exact <E>` -> `have <nm> := <K> ▸ (<E>)`
        m_rw_ex = re.match(
            r"^[ \t]*(?:rw|rewrite)[ \t]*\[[ \t]*(←|<-)?[ \t]*([^\],]+)[ \t]*\][ \t]*\n[ \t]*exact[ \t]+([^\n]+)$",
            inner_block,
        )
        if m_rw_ex and h_nm != "this":
            rev_a, k_id, ex_e = m_rw_ex.group(1), m_rw_ex.group(2).strip(), m_rw_ex.group(3).strip()
            for k_expr, tag_s in ((k_id, "mp"), (f"({k_id}).symm", "symm_mp")):
                nb_mp = body[:hm.start()] + f"{ind_s}have {h_nm} := {k_expr} ▸ ({ex_e})\n" + body[inner_end:]
                add_cand(f"have_rw_{tag_s}", nb_mp, f"have {h_nm} := {k_expr} ▸ exact", 0.26 + 0.0002 * idx, "unwrap")

    # --- Family 4: `obtain ⟨...⟩ := Prod.mk.inj h` -> `obtain ⟨...⟩ := h` (and optional preceding `dsimp only at h`) ---
    prod_inj_re = re.compile(r"(?:^([ \t]*)dsimp only at ([^\W\d][\w'₀-₉]*)[ \t]*\n)?([ \t]*obtain[ \t]+⟨[^⟩]+⟩[ \t]*:=[ \t]*)Prod\.mk\.inj[ \t]+([^\W\d][\w'₀-₉]*)", re.M)
    prod_edits_all: list[tuple[int, int, str]] = []
    for idx, pm in enumerate(prod_inj_re.finditer(body)):
        if mask[pm.start()]:
            continue
        d_ind, d_hyp, obt_pre, h_id = pm.groups()
        # Variant 4a: keep `dsimp only at h` if present, just drop `Prod.mk.inj`
        s_obt = pm.start(3)
        repl_4a = f"{obt_pre}{h_id}"
        nb_4a = body[:s_obt] + repl_4a + body[pm.end():]
        add_cand("prod_inj", nb_4a, f"drop Prod.mk.inj on {h_id}", 0.30 + 0.0002 * idx, "tactic")
        prod_edits_all.append((s_obt, pm.end(), repl_4a))
        # Variant 4b: if `d_hyp == h_id`, also drop `dsimp only at h`
        if d_hyp and d_hyp == h_id:
            nb_4b = body[:pm.start()] + repl_4a + body[pm.end():]
            add_cand("dsimp_prod_inj", nb_4b, f"drop dsimp only + Prod.mk.inj on {h_id}", 0.27 + 0.0002 * idx, "tactic")

    if len(prod_edits_all) >= 2:
        nb_pall = body
        for a, b_pos, repl in sorted(prod_edits_all, key=lambda x: -x[0]):
            nb_pall = nb_pall[:a] + repl + nb_pall[b_pos:]
        add_cand("prod_inj_all", nb_pall, f"drop all {len(prod_edits_all)} Prod.mk.inj", 0.22, "tactic")

    # --- Family 5: Multi-line adjacent `simp only [...]` and `rw/rewrite/erw [...]` fusion ---
    # 5a. Adjacent `simp only [<A>]` + `simp only [<B>]` (same indentation, no `at` clause, allowing newlines inside `[...]`)
    msimp_re = re.compile(r"^([ \t]*)simp only[ \t]*\[((?:[^\[\]]|\n)+)\][ \t]*\n\1simp only[ \t]*\[((?:[^\[\]]|\n)+)\](?=[ \t]*(?:\n|$))", re.M)
    for idx, sm in enumerate(msimp_re.finditer(body)):
        if mask[sm.start()]:
            continue
        ind_s, a_items, b_items = sm.group(1), sm.group(2).strip(), sm.group(3).strip()
        merged = f"{ind_s}simp only [{a_items}, {b_items}]"
        nb_sm = body[:sm.start()] + merged + body[sm.end():]
        add_cand("simp_merge_ml", nb_sm, "merge adjacent multi-line simp only", 0.31 + 0.0002 * idx, "tactic")

    # 5b. Adjacent `(rw|rewrite|erw) [<A>] (at h)?` + `\1 [<B>] \3`
    mrw_re = re.compile(r"^([ \t]*)(rw|rewrite|erw)[ \t]*\[((?:[^\[\]]|\n)+)\]([ \t]+at[ \t]+[^\n]+)?[ \t]*\n\1\2[ \t]*\[((?:[^\[\]]|\n)+)\]\4(?=[ \t]*(?:\n|$))", re.M)
    for idx, rm in enumerate(mrw_re.finditer(body)):
        if mask[rm.start()]:
            continue
        ind_s, rw_k, a_items, at_cl, b_items = rm.groups()
        at_s = at_cl or ""
        merged = f"{ind_s}{rw_k} [{a_items.strip()}, {b_items.strip()}]{at_s}"
        nb_rm = body[:rm.start()] + merged + body[rm.end():]
        add_cand("rw_merge_ml", nb_rm, f"merge adjacent {rw_k}", 0.31 + 0.0002 * idx, "tactic")

    # 5c. `apply <E>.trans\n (rw|rewrite) [<R>]` -> `(rw|rewrite) [<E>, <R>]`
    ap_tr_re = re.compile(r"^([ \t]*)apply[ \t]+([^\n]+?)\.trans[ \t]*\n\1(rw|rewrite)[ \t]*\[([^\]]+)\](?=[ \t]*(?:\n|$))", re.M)
    for idx, am in enumerate(ap_tr_re.finditer(body)):
        if mask[am.start()]:
            continue
        ind_s, e_tr, rw_k, r_items = am.groups()
        merged = f"{ind_s}{rw_k} [{e_tr.strip()}, {r_items.strip()}]"
        nb_at = body[:am.start()] + merged + body[am.end():]
        add_cand("apply_trans_rw", nb_at, f"fold apply {e_tr[:24]}.trans into {rw_k}", 0.28 + 0.0002 * idx, "tactic")

    # Round-robin across buckets (`calc`, `unwrap`, `tactic`) so every mechanism gets screened in the batch
    bucket_caps = {"calc": 10, "unwrap": 8, "tactic": 8}
    bucket_order = ("calc", "unwrap", "tactic")
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
        bkt = c.get("bucket", "calc")
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


def has_sites(proof: str, statement: str) -> bool:
    return bool(raw_candidates(proof, statement))


def _batch_cap(ctx: dict | None) -> int:
    hb = (ctx or {}).get("inc_hb")
    if isinstance(hb, (int, float)) and hb > 0:
        if hb <= 16000:
            return 22
        if hb <= 30000:
            return 16
        return 10
    return MAX_BATCH_CANDS


def build_core_batch(statement: str, body0: str, cand_bodies: list[str], max_hb: int = 250000) -> tuple[str | None, int]:
    """Build a pure-Core batch file measuring compilation and heartbeats of `[body0] + cand_bodies` via `IO.getNumHeartbeats`."""
    lines = [
        "theorem lraArgonCalcstepDummy : True := trivial",
        "set_option warningAsError false",
    ]
    if max_hb > 0:
        lines.append(f"set_option maxHeartbeats {max_hb}")
    all_bodies = [body0] + list(cand_bodies)
    for i, b in enumerate(all_bodies):
        decl_i = MS.renamed(statement, i)
        if decl_i is None:
            return None, 0
        lines.append("section")
        lines.append(f'#eval show IO String from do return s!"LRAHB_B\\t{i}\\t{{← IO.getNumHeartbeats}}"')
        lines.append(f"{decl_i} :={b}")
        lines.append(f'#eval show IO String from do return s!"LRAHB_E\\t{i}\\t{{← IO.getNumHeartbeats}}"')
        lines.append("end")
    return "\n\n".join(lines) + "\n", len(all_bodies)


def parse_core_batch(res, n: int) -> list[dict]:
    msgs = getattr(res, "messages", None)
    if msgs is None:
        return [{"ok": False, "hb": None, "errors": ["no messages"]} for _ in range(n)]
    starts: dict[int, tuple[int, int]] = {}
    ends: dict[int, tuple[int, int]] = {}
    other_lines: list[tuple[int, str, str]] = []
    for m in msgs:
        sev = m.get("severity")
        txt = (m.get("data") or "").strip()
        ln = (m.get("pos") or {}).get("line") or 0
        if sev == "info":
            ms = HB_START_RE.match(txt)
            if ms:
                starts[int(ms.group(1))] = (ln, int(ms.group(2)))
                continue
            me = HB_END_RE.match(txt)
            if me:
                ends[int(me.group(1))] = (ln, int(me.group(2)))
                continue
        other_lines.append((ln, sev or "", txt))
    out: list[dict] = []
    for i in range(n):
        if i not in starts or i not in ends:
            out.append({"ok": False, "hb": None, "errors": ["missing marker"]})
            continue
        l0, h0 = starts[i]
        l1, h1 = ends[i]
        errs = [t for ln, sev, t in other_lines if l0 <= ln <= l1 and (sev == "error" or "sorry" in t)]
        hb = max(1, (h1 - h0) // 1000)
        out.append({"ok": not errs, "hb": hb if not errs else None, "errors": errs})
    return out


def _combine_disjoint_bodies(body0: str, cand_bodies: list[str]) -> str | None:
    edits: list[tuple[int, int, str]] = []
    for b in cand_bodies:
        if b == body0:
            continue
        sm = difflib.SequenceMatcher(a=body0, b=b, autojunk=False)
        ops = [(tag, i1, i2, j1, j2) for tag, i1, i2, j1, j2 in sm.get_opcodes() if tag != "equal"]
        if not ops:
            continue
        i1 = ops[0][1]
        i2 = ops[-1][2]
        repl = b[ops[0][3]:ops[-1][4]]
        conflict = False
        for a, b_end, _ in edits:
            if not (i2 <= a or i1 >= b_end):
                conflict = True
                break
        if not conflict:
            edits.append((i1, i2, repl))
    if len(edits) < 2:
        return None
    out = body0
    for a, b_end, repl in sorted(edits, key=lambda x: -x[0]):
        out = out[:a] + repl + out[b_end:]
    return out if out != body0 else None


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict | None:
    body0 = split_declaration(proof, statement)
    if body0 is None or not versions:
        return None
    raw = raw_candidates(proof, statement)
    if not raw:
        return None
    head = f"{statement} :="
    tok0 = count_tokens(body0)
    pin = versions[0]
    batch_cands = raw[:_batch_cap(ctx)]

    def call(text: str):
        if stats is not None:
            stats["compiles"] = stats.get("compiles", 0) + 1
        return run(text, pin)

    btext, n = build_core_batch(statement, body0, [c["body"] for c in batch_cands])
    if btext is None:
        return {"verified": raw[:MAX_CANDS]}
    res = call(btext)
    slots = parse_core_batch(res, n)
    hb0 = slots[0]["hb"]
    if not slots[0]["ok"] or not hb0:
        return {"verified": raw[:MAX_CANDS]}

    ex = (ctx or {}).get("exchange")
    passed: list[dict] = []
    for c, sl in zip(batch_cands, slots[1:]):
        if not sl["ok"] or not sl["hb"]:
            continue
        hb = sl["hb"]
        dt = tok0 - c["tokens"]
        dh = hb0 - hb
        if dt > 0 and dh >= 0:
            ok_gate = True
        elif dt > 0 and MS.predicted(c["tokens"], hb, tok0, hb0, ex) > 1e-4:
            ok_gate = True
        else:
            ok_gate = False
        if ok_gate:
            item = dict(c)
            item["hb"] = hb
            item["pred"] = MS.predicted(c["tokens"], hb, tok0, hb0, ex)
            passed.append(item)

    passed.sort(key=lambda x: (-x["pred"], x["tokens"], x["hb"]))

    # Synthesize a disjoint multi-edit combo candidate if >=2 passed edits touch non-overlapping spans
    if len(passed) >= 2:
        combo_body = _combine_disjoint_bodies(body0, [p["body"] for p in passed])
        if combo_body is not None and not check_forbidden(combo_body):
            ctok = count_tokens(combo_body)
            if ctok < min(p["tokens"] for p in passed):
                combo_item = {
                    "op": f"{FAMILY}:combo",
                    "decl": head + combo_body.rstrip() + "\n",
                    "body": combo_body,
                    "note": f"combo ({len(passed)} non-overlapping passed edits)",
                    "tokens": ctok,
                    "hb": passed[0]["hb"],
                    "pred": passed[0]["pred"] + 0.05,
                }
                passed.insert(0, combo_item)

    verified = passed[:MAX_CANDS]
    if log is not None:
        log(f"{FAMILY} query: {len(batch_cands)} screened, {len(passed)} passed, {len(verified)} emitted")
    return {"verified": verified, "screened": True}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=MAX_CANDS, ctx=None) -> list[dict]:
    q = (ctx or {}).get("query") or {}
    if "verified" in q:
        out = q["verified"]
    elif q.get("screened"):
        out = []
    else:
        out = raw_candidates(proof, statement)
    cap = max_per_op or MAX_CANDS
    return [{"op": c["op"], "decl": c["decl"], "note": c["note"]} for c in out[:cap]]
