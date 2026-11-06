#!/usr/bin/env python3
"""Post-step op `argon_haveopt`: binding & type-ascription elimination (`have` type-signature elision across multi-line and parameterized
declarations, definitional `have ... := rfl` unfold propagation, single-use `have`/`let` inlining and `convert` fusion, shadowed/dead `have`
deletion, `by_cases` proposition elision via `Classical.em _`, and inline `(expr : Type)` / `show Type by tac` elision), screened and
heartbeat-measured in one warm-cached Core-compatible batch compile (`IO.getNumHeartbeats` sandwich).

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

FAMILY = "argon_haveopt"
MAX_CANDS = 3
MAX_BATCH_CANDS = 24
HB_START_RE = re.compile(r'^"?LRAHB_B(?:\\t|\t)(\d+)(?:\\t|\t)(\d+)"?$')
HB_END_RE = re.compile(r'^"?LRAHB_E(?:\\t|\t)(\d+)(?:\\t|\t)(\d+)"?$')
SORRY_RE = re.compile(r"\bdeclaration uses\b.*\bsorry", re.DOTALL)
HAVE_KW_RE = re.compile(r"(?<![\w.'])(have|let|set)(?![\w.'])")
IDENT_ONLY_RE = re.compile(r"^[^\W\d][\w'₀-₉]*$")
HEAD_IDENT_RE = re.compile(r"[^\W\d][\w'₀-₉.]*")
BINDER_PRE_RE = re.compile(r"(?:fun|λ|∀|forall|obtain|rcases|cases|induction|have|let|set|suffices|ext|intro|rintro)[ \t\n]*$")


def proof_key(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def _code_str(body: str, mask: list[int] | None = None) -> str:
    if mask is None:
        mask = _mask(body)
    return "".join(" " if mask[i] else ch for i, ch in enumerate(body))


def _line_indent(body: str, pos: int) -> int:
    ls = body.rfind("\n", 0, pos) + 1
    ln = body[ls:pos]
    return len(ln) - len(ln.lstrip(" \t"))


def _block_end_by_indent(body: str, mask: list[int], pairs: dict[int, int], start_pos: int, base_indent: int) -> tuple[int, int]:
    """Return `(decl_end, scope_end)`:
      - `decl_end`: end offset of the declaration starting at `base_indent` whose RHS starts at `start_pos`,
      - `scope_end`: end offset of the enclosing tactic block (first line with indent < `base_indent`)."""
    n = len(body)
    i = start_pos
    decl_end = None
    scope_end = n
    while i < n:
        if mask[i]:
            i += 1
            continue
        if i in pairs and pairs[i] > i:
            i = pairs[i] + 1
            continue
        if body[i] == "\n":
            ls = i + 1
            le = body.find("\n", ls)
            if le < 0:
                le = n
            code_ln = "".join(" " if mask[ls + k] else ch for k, ch in enumerate(body[ls:le]))
            if code_ln.strip():
                ind = len(code_ln) - len(code_ln.lstrip(" \t"))
                if ind <= base_indent and decl_end is None:
                    decl_end = i
                if ind < base_indent:
                    scope_end = i
                    break
            i = le
            continue
        i += 1
    if decl_end is None:
        decl_end = n
    return decl_end, scope_end


def parse_bindings(body: str) -> list[dict]:
    """Parse all `have` / `let` / `set` bindings in `body` with their top-level `: <Type> := <RHS>` spans and indentation scopes."""
    mask = _mask(body)
    pairs = _pairs(body, mask)
    out: list[dict] = []
    for m in HAVE_KW_RE.finditer(body):
        kw = m.group(1)
        s = m.start()
        if mask[s]:
            continue
        # Must be at start of tactic line (possibly after `·`)
        ls = body.rfind("\n", 0, s) + 1
        pre = "".join(" " if mask[ls + k] else ch for k, ch in enumerate(body[ls:s])).strip()
        if pre not in ("", "·"):
            continue
        base_ind = _line_indent(body, s) if pre == "" else _line_indent(body, ls + body[ls:s].find("·"))
        i = m.end()
        colon_pos = None
        walrus_pos = None
        while i < len(body):
            if mask[i]:
                i += 1
                continue
            if i in pairs and pairs[i] > i:
                i = pairs[i] + 1
                continue
            if body[i:i + 2] == ":=":
                walrus_pos = i
                break
            if body[i] == ":" and colon_pos is None:
                colon_pos = i
            if body[i] == "\n" and colon_pos is None:
                break
            i += 1
        if walrus_pos is None:
            continue
        decl_end, scope_end = _block_end_by_indent(body, mask, pairs, walrus_pos + 2, base_ind)
        sig_end = colon_pos if colon_pos is not None else walrus_pos
        lhs_raw = body[m.end():sig_end].strip()
        # Extract bound identifier and optional binders
        tokens_lhs = lhs_raw.split()
        if not tokens_lhs:
            bname = "this"
            binders = ""
        elif IDENT_ONLY_RE.match(tokens_lhs[0]):
            bname = tokens_lhs[0]
            binders = lhs_raw[len(bname):].strip()
        else:
            bname = ""
            binders = lhs_raw
        ty_raw = body[colon_pos + 1:walrus_pos].strip() if colon_pos is not None else None
        rhs_raw = body[walrus_pos + 2:decl_end].strip()
        out.append({
            "kw": kw,
            "start": s,
            "line_start": ls,
            "kw_end": m.end(),
            "colon_pos": colon_pos,
            "walrus_pos": walrus_pos,
            "decl_end": decl_end,
            "scope_end": scope_end,
            "indent": base_ind,
            "lhs_raw": lhs_raw,
            "bname": bname,
            "binders": binders,
            "ty_raw": ty_raw,
            "rhs_raw": rhs_raw,
        })
    return out


def _effective_scope_end(body: str, b: dict, all_bindings: list[dict]) -> int:
    """Return the offset where `b['bname']` ends its scope or is shadowed by a later binding of the same name at `<= b['indent']`."""
    limit = b["scope_end"]
    nm = b["bname"]
    if not nm:
        return limit
    for other in all_bindings:
        if other["start"] <= b["decl_end"]:
            continue
        if other["start"] >= limit:
            break
        if other["bname"] == nm and other["indent"] <= b["indent"]:
            return other["start"]
    return limit


def _find_ident_spans(text: str, ident: str, offset: int = 0) -> list[tuple[int, int]]:
    if not ident:
        return []
    mask = _mask(text)
    pat = re.compile(rf"(?<![\w.']){re.escape(ident)}(?![\w'])")
    out = []
    for m in pat.finditer(text):
        if not mask[m.start()]:
            out.append((offset + m.start(), offset + m.end()))
    return out


def _is_term_rhs(rhs: str) -> bool:
    s = rhs.lstrip()
    return bool(s) and not re.match(r"^by(?![\w'?!])", s)


def raw_candidates(proof: str, statement: str) -> list[dict]:
    """Generate prioritized binding, type-signature, and ascription candidates from `proof` and `statement` alone."""
    hb = K.head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    mask = _mask(body)
    pairs = _pairs(body, mask)
    tok0 = count_tokens(body)
    bindings = parse_bindings(body)
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

    # Map local `set`/`let` definitions to their RHS head identifier for `rfl_fold`
    local_def_heads: dict[str, str] = {}
    for b in bindings:
        if b["kw"] in ("set", "let") and b["bname"]:
            hm = HEAD_IDENT_RE.match(b["rhs_raw"].lstrip("(@"))
            if hm:
                local_def_heads[b["bname"]] = hm.group(0)

    rfl_fold_edits: list[tuple[int, int, str]] = []
    rfl_ascr_edits: list[tuple[int, int, str]] = []

    for idx, b in enumerate(bindings):
        s = b["start"]
        ls = b["line_start"]
        cpos = b["colon_pos"]
        wpos = b["walrus_pos"]
        dend = b["decl_end"]
        nm = b["bname"]
        rhs = b["rhs_raw"]
        ty = b["ty_raw"]
        eff_end = _effective_scope_end(body, b, bindings)
        uses = _find_ident_spans(body[dend:eff_end], nm, offset=dend) if nm else []

        # --- Family 1: `typesig` (`have` / `let` type-signature elision) ---
        if cpos is not None and ty:
            lhs_part = (" " + b["lhs_raw"]) if b["lhs_raw"] else ""
            # 1a. Term RHS: drop `: <Type>` directly
            if _is_term_rhs(rhs) and rhs != "rfl":
                nb = body[:s] + f"{b['kw']}{lhs_part} :=" + body[wpos + 2:]
                add_cand("typesig", nb, f"drop : Type on {nm or 'anon'}", 0.30 + 0.0002 * idx, "typesig")
                # Also if RHS starts with `λ vars => body` or `fun vars => body` and `nm` is named
                lm = re.match(r"^(?:fun|λ)\s*([^:=\n]+?)\s*=>\s*(.+)$", rhs, re.DOTALL)
                if lm and b["lhs_raw"] and IDENT_ONLY_RE.match(b["lhs_raw"]):
                    bvars, lbody = lm.group(1).strip(), lm.group(2).strip()
                    nb_lam = body[:s] + f"{b['kw']} {b['lhs_raw']} {bvars} := {lbody}" + body[dend:]
                    add_cand("typesig_lam", nb_lam, f"fuse lambda binders on {nm}", 0.28 + 0.0002 * idx, "typesig")
                    # 1d. Keep `: <Type_body>` while fusing `∀ <bvars>,` + `λ <bvars> =>` into `have nm <bvars> : <Type_body> := <lbody>`
                    fm = re.match(rf"^(?:∀|forall)\s*\(?{re.escape(bvars)}\)?\s*,\s*(.+)$", ty, re.DOTALL)
                    if fm:
                        ty_inner = fm.group(1).strip()
                        nb_flam = body[:s] + f"{b['kw']} {b['lhs_raw']} {bvars} : {ty_inner} := {lbody}" + body[dend:]
                        add_cand("typesig_forall_lam", nb_flam, f"fuse ∀/λ binder {bvars} on {nm}", 0.26 + 0.0002 * idx, "typesig")
                # Also if RHS starts with `show <T2> from <term>`
                sm = re.match(r"^show\b.+?\bfrom\s+(.+)$", rhs, re.DOTALL)
                if sm:
                    inner_t = sm.group(1).strip()
                    nb_sh1 = body[:wpos + 2] + " " + inner_t + body[dend:]
                    nb_sh2 = body[:s] + f"{b['kw']}{lhs_part} := {inner_t}" + body[dend:]
                    add_cand("typesig_show", nb_sh1, f"drop show..from on {nm}", 0.32 + 0.0002 * idx, "typesig")
                    add_cand("typesig_show", nb_sh2, f"drop : Type and show..from on {nm}", 0.29 + 0.0002 * idx, "typesig")
            # 1b. Single-step `by exact <term>` or `by intro <vars>; exact <term>`
            else:
                em = re.match(r"^by\s+exact\s+(.+)$", rhs, re.DOTALL)
                if em and "\n" not in em.group(1).strip():
                    term_e = em.group(1).strip()
                    nb_ex1 = body[:s] + f"{b['kw']}{lhs_part} := {term_e}" + body[dend:]
                    nb_ex2 = body[:wpos + 2] + " " + term_e + body[dend:]
                    add_cand("typesig_exact", nb_ex1, f"by exact -> term on {nm}", 0.31 + 0.0002 * idx, "typesig")
                    add_cand("typesig_exact", nb_ex2, f"drop by exact on {nm}", 0.35 + 0.0002 * idx, "typesig")
                im = re.match(r"^by\s+intro\s+([^\n;]+?)\s*(?:;|\n\s*)exact\s+([^\n]+)$", rhs)
                if im and b["lhs_raw"] and IDENT_ONLY_RE.match(b["lhs_raw"]):
                    ivars, iterm = im.group(1).strip(), im.group(2).strip()
                    nb_in = body[:s] + f"{b['kw']} {b['lhs_raw']} {ivars} := {iterm}" + body[dend:]
                    add_cand("typesig_intro", nb_in, f"by intro..exact -> term on {nm}", 0.30 + 0.0002 * idx, "typesig")

        # --- Family 2: `rfl_fold` (`have [nm] : LHS = RHS := rfl` elimination & head unfold) ---
        if b["kw"] == "have" and ty and "=" in ty and rhs in ("rfl", "by rfl") and uses:
            lhs_eq = ty.split("=", 1)[0].strip().lstrip("(@")
            hm = HEAD_IDENT_RE.match(lhs_eq)
            hd_id = hm.group(0) if hm else None
            # Check if all uses of `nm` are inside `[...]` bracket lists
            all_in_brackets = True
            for u_lo, u_hi in uses:
                # Look backwards for `[` or `,`
                pre_u = body[max(0, u_lo - 16):u_lo].rstrip()
                post_u = body[u_hi:min(len(body), u_hi + 16)].lstrip()
                if not (pre_u.endswith(("[", ",", "←", "<-", "↓", "↑")) and post_u.startswith(("]", ","))):
                    all_in_brackets = False
                    break
            if all_in_brackets:
                del_lo = ls if body[ls:s].strip() == "" else s
                del_hi = dend + 1 if (dend < len(body) and body[dend] == "\n" and del_lo == ls) else dend
                # Variant 2a: replace `nm` in bracket lists with `hd_id` (and `local_def_heads[hd_id]` if `hd_id` is a local `set`/`let`)
                if hd_id:
                    repl_items = hd_id
                    if hd_id in local_def_heads:
                        repl_items = f"{hd_id}, {local_def_heads[hd_id]}"
                    nb_rfl = body
                    for u_lo, u_hi in reversed(uses):
                        nb_rfl = nb_rfl[:u_lo] + repl_items + nb_rfl[u_hi:]
                    nb_rfl = nb_rfl[:del_lo] + nb_rfl[del_hi:]
                    add_cand("rfl_fold", nb_rfl, f"unfold {repl_items} for {nm} := rfl", 0.33 + 0.0002 * idx, "inline")
                    rfl_fold_edits.append((del_lo, del_hi, ""))
                    for u_lo, u_hi in uses:
                        rfl_fold_edits.append((u_lo, u_hi, repl_items))
                # Variant 2b: single-use `have [nm] : <Type> := rfl` -> inline `(rfl : <Type>)` at use site
                if len(uses) == 1:
                    u_lo, u_hi = uses[0]
                    ascr_rfl = f"(rfl : {ty})"
                    nb_arfl = body[:u_lo] + ascr_rfl + body[u_hi:]
                    nb_arfl = nb_arfl[:del_lo] + nb_arfl[del_hi:]
                    add_cand("inline_rfl_ascr", nb_arfl, f"inline (rfl : Type) for {nm}", 0.31 + 0.0002 * idx, "inline")
                    rfl_ascr_edits.append((del_lo, del_hi, ""))
                    rfl_ascr_edits.append((u_lo, u_hi, ascr_rfl))

        # --- Family 3: `inline` (Single-use `have` / `let` inlining & `convert` fusion) ---
        if len(uses) == 1 and b["kw"] in ("have", "let"):
            u_lo, u_hi = uses[0]
            del_lo = ls if body[ls:s].strip() == "" else s
            del_hi = dend + 1 if (dend < len(body) and body[dend] == "\n" and del_lo == ls) else dend
            if _is_term_rhs(rhs) and not b["binders"] and "\n" not in rhs and len(rhs) <= 120:
                # Check if `nm == 'this'` and an unnamed tactic appears between `dend` and `u_lo`
                if nm != "this" or not re.search(r"\b(omega|linarith|nlinarith|simp_all|grind|assumption)\b", body[dend:u_lo]):
                    lm = re.match(r"^(?:fun|λ)\s+([^\W\d][\w'₀-₉]*)\s*=>\s*(.+)$", rhs)
                    # Check if used as `nm arg`
                    app_m = re.match(r"^[ \t]+([^\W\d][\w'₀-₉]*)(?![\w'.])", body[u_hi:u_hi + 32]) if lm else None
                    if lm and app_m:
                        lvar, lbody = lm.group(1), lm.group(2).strip()
                        arg_id = app_m.group(1)
                        sub_body = re.sub(rf"(?<![\w.']){re.escape(lvar)}(?![\w'])", arg_id, lbody)
                        nb_in = body[:u_lo] + f"({sub_body})" + body[u_hi + app_m.end():]
                        nb_in = nb_in[:del_lo] + nb_in[del_hi:]
                        add_cand("inline_lam", nb_in, f"beta-inline {nm} {arg_id}", 0.40 + 0.005 * idx, "inline")
                    else:
                        nb_in = body[:u_lo] + f"({rhs})" + body[u_hi:]
                        nb_in = nb_in[:del_lo] + nb_in[del_hi:]
                        add_cand("inline_term", nb_in, f"inline single-use {nm}", 0.42 + 0.005 * idx, "inline")
            # Subcase 3c: `have K : LHS = RHS := by TAC` used once at `rewrite [← K]\n exact E` or `rw [← K]\n exact E`
            elif ty and "=" in ty and rhs.startswith("by"):
                tac_body = re.sub(r"^by\s+", "", rhs, count=1).strip()
                # Check if `u_lo` is inside `rewrite [← nm]` or `rw [← nm]` followed by `exact E`
                rw_m = re.search(
                    rf"([ \t]*)(?:rewrite|rw)\s*\[\s*(←|<-)?\s*{re.escape(nm)}\s*\]\s*\n\1exact\s+([^\n]+)",
                    body[dend:eff_end],
                )
                if rw_m and "\n" not in tac_body:
                    ind_s, rev_arrow, ex_term = rw_m.group(1), rw_m.group(2), rw_m.group(3).strip()
                    rw_abs_lo = dend + rw_m.start()
                    rw_abs_hi = dend + rw_m.end()
                    # Replace `rewrite [..]; exact E` with `convert E using 1; <tac_body>` (or `symm; <tac_body>`)
                    for sym_prefix, vtag in (("", "conv1"), ("symm; ", "conv1_symm")):
                        repl_tac = f"{ind_s}convert {ex_term} using 1\n{ind_s}{sym_prefix}{tac_body}"
                        nb_cv = body[:rw_abs_lo] + repl_tac + body[rw_abs_hi:]
                        nb_cv = nb_cv[:del_lo] + nb_cv[del_hi:]
                        add_cand(f"inline_{vtag}", nb_cv, f"fuse {nm} into convert", 0.36 + 0.005 * idx, "inline")

        # --- Family 4: `dead` (Shadowed or unreferenced `have` / `let` deletion) ---
        if len(uses) == 0 and b["kw"] in ("have", "let") and IDENT_ONLY_RE.match(nm):
            del_lo = ls if body[ls:s].strip() == "" else s
            del_hi = dend + 1 if (dend < len(body) and body[dend] == "\n" and del_lo == ls) else dend
            if del_lo == ls:
                nb_dead = body[:del_lo] + body[del_hi:]
                # Prioritize shadowed `this` or multi-token dead `have`
                is_shadowed = eff_end < b["scope_end"]
                prio_dead = (0.24 if is_shadowed else 0.55) + 0.006 * idx
                add_cand("dead", nb_dead, f"drop unreferenced {nm} (shadowed={is_shadowed})", prio_dead, "dead")

    # Joint `rfl_fold` if >=2 `:= rfl` haves were unfolded
    if len(rfl_fold_edits) >= 4:
        nb_jrfl = body
        for a, b_pos, repl in sorted(rfl_fold_edits, key=lambda x: -x[0]):
            nb_jrfl = nb_jrfl[:a] + repl + nb_jrfl[b_pos:]
        add_cand("rfl_fold_all", nb_jrfl, "unfold all := rfl haves", 0.22, "inline")

    # Joint `inline_rfl_ascr_all` if >=2 `:= rfl` haves were inlined as `(rfl : Type)`
    if len(rfl_ascr_edits) >= 4:
        nb_jarfl = body
        for a, b_pos, repl in sorted(rfl_ascr_edits, key=lambda x: -x[0]):
            nb_jarfl = nb_jarfl[:a] + repl + nb_jarfl[b_pos:]
        add_cand("inline_rfl_ascr_all", nb_jarfl, "inline all (rfl : Type) haves", 0.23, "inline")

    # --- Family 5: `em_cases` (`by_cases h : <Prop>` -> `rcases Classical.em _ with h | h`) ---
    for idx, m in enumerate(re.finditer(r"^([ \t]*)by_cases[ \t]+([^\W\d][\w'₀-₉]*)[ \t]*:[ \t]*([^\n]+)$", body, re.M)):
        if mask[m.start()]:
            continue
        ind_s, h_nm, prop_s = m.group(1), m.group(2), m.group(3).strip()
        if count_tokens(prop_s) < 5:
            continue
        repl_em = f"{ind_s}rcases Classical.em _ with {h_nm} | {h_nm}"
        nb_em = body[:m.start()] + repl_em + body[m.end():]
        add_cand("em_cases", nb_em, f"Classical.em _ on {h_nm}", 0.44 + 0.0002 * idx, "ascr")
        # Check if immediately preceding tactic line is `let x := ...` or `have x := ...` used ONLY inside `prop_s`
        prev_ls = body.rfind("\n", 0, max(0, m.start() - 1)) + 1 if m.start() > 0 else 0
        prev_ln = body[prev_ls:m.start()].strip()
        pm = re.match(r"^(?:let|have)\s+([^\W\d][\w'₀-₉]*)\s*:=\s*(.+)$", prev_ln)
        if pm:
            p_nm = pm.group(1)
            if _find_ident_spans(prop_s, p_nm) and not _find_ident_spans(body[m.end():], p_nm):
                nb_em2 = body[:prev_ls] + repl_em + body[m.end():]
                add_cand("em_cases_let", nb_em2, f"drop {p_nm} + Classical.em _ on {h_nm}", 0.26 + 0.0002 * idx, "ascr")

    # --- Family 6: `ascr_drop` (`(expr : Type)` -> `(expr)` and `show Type by tac` -> `by tac`) ---
    # 6a. Parenthesized type ascriptions `(inner : Type)`
    for open_p, close_p in sorted(pairs.items()):
        if close_p <= open_p or body[open_p] != "(" or body[close_p] != ")":
            continue
        # Skip binder lists (`fun (x : T)`, `∀ (x : T)`, `have h (x : T)`, etc.)
        pre_ctx = body[max(0, open_p - 40):open_p]
        if BINDER_PRE_RE.search(pre_ctx):
            continue
        # Look for top-level `:` inside `( ... )`
        i = open_p + 1
        colon_p = None
        valid = True
        while i < close_p:
            if mask[i]:
                i += 1
                continue
            if i in pairs and pairs[i] > i:
                i = pairs[i] + 1
                continue
            if body[i:i + 2] == ":=":
                valid = False
                break
            if body[i] == ":":
                if colon_p is not None:
                    valid = False
                    break
                colon_p = i
            i += 1
        if not valid or colon_p is None:
            continue
        inner = body[open_p + 1:colon_p].strip()
        ty_part = body[colon_p + 1:close_p].strip()
        if not inner or not ty_part or count_tokens(ty_part) < 2:
            continue
        # Skip single-identifier binder `(x : T)` unless `inner` is `rfl`
        if IDENT_ONLY_RE.match(inner) and inner != "rfl":
            continue
        # Check if followed by `.field` projection (which often needs the type if `inner` is `by ...`)
        post_ctx = body[close_p + 1:close_p + 4]
        if post_ctx.startswith(".") and inner.startswith("by"):
            continue
        nb_ascr = body[:open_p] + f"({inner})" + body[close_p + 1:]
        add_cand("ascr_paren", nb_ascr, f"drop : {ty_part[:32]} in parens", 0.38, "ascr")

    # 6b. `show <Type> by <tac>` -> `by <tac>` and `show <Type> from <term>` -> `<term>`
    for idx, sm in enumerate(re.finditer(r"(?<![\w.'])show\b", body)):
        s_pos = sm.start()
        if mask[s_pos]:
            continue
        # Find top-level `by` or `from` after `show`
        i = sm.end()
        kw_pos = None
        kw_str = None
        while i < len(body):
            if mask[i]:
                i += 1
                continue
            if i in pairs and pairs[i] > i:
                i = pairs[i] + 1
                continue
            if body[i] in "\n;)]}":
                break
            m_by = re.match(r"^(by|from)(?![\w'?!])", body[i:])
            if m_by and body[i - 1:i].isspace():
                kw_pos = i
                kw_str = m_by.group(1)
                break
            i += 1
        if kw_pos is None:
            continue
        ty_s = body[sm.end():kw_pos].strip()
        if count_tokens(ty_s) < 2:
            continue
        if kw_str == "by":
            nb_sh = body[:s_pos] + body[kw_pos:]
            add_cand("ascr_show", nb_sh, f"drop show {ty_s[:32]} before by", 0.39 + 0.0002 * idx, "ascr")
        else:
            nb_sh = body[:s_pos] + body[kw_pos + 4:].lstrip()
            add_cand("ascr_show", nb_sh, f"drop show {ty_s[:32]} from", 0.39 + 0.0002 * idx, "ascr")

    # Round-robin across buckets (`typesig`, `inline`, `ascr`, `dead`) so every mechanism gets screened in the batch
    bucket_caps = {"typesig": 10, "inline": 7, "ascr": 7, "dead": 6}
    bucket_order = ("typesig", "inline", "ascr", "dead")
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
        bkt = c.get("bucket", "typesig")
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
    cs = (ctx or {}).get("compile_s")
    if isinstance(cs, (int, float)) and cs > 0:
        if cs <= 10.0:
            return 22
        if cs <= 20.0:
            return 16
        return 10
    return MAX_BATCH_CANDS


def build_core_batch(statement: str, body0: str, cand_bodies: list[str], max_hb: int = 250000) -> tuple[str | None, int]:
    """Build a pure-Core batch file measuring compilation and heartbeats of `[body0] + cand_bodies` via `IO.getNumHeartbeats`."""
    lines = [
        "theorem lraArgonHaveoptDummy : True := trivial",
        "set_option warningAsError false",
    ]
    all_bodies = [body0] + list(cand_bodies)
    hb_bound = max(5000, int(max_hb))
    for i, b in enumerate(all_bodies):
        r = MS.renamed(statement, i)
        if r is None:
            return None, 0
        chunk = (
            f'#eval show IO String from do pure s!"LRAHB_B\\t{i}\\t{{← IO.getNumHeartbeats}}"\n'
            f"set_option maxHeartbeats {hb_bound} in\n"
            f"set_option Elab.async false in\n"
            f"{r.rstrip()} :={b.rstrip()}\n"
            f'#eval show IO String from do pure s!"LRAHB_E\\t{i}\\t{{← IO.getNumHeartbeats}}"'
        )
        lines.extend(chunk.split("\n"))
    return "\n".join(lines) + "\n", len(all_bodies)


def parse_core_batch(messages: list, num_copies: int) -> dict[int, dict]:
    """Parse `{i: {"ok": bool, "hb": int}}` from `build_core_batch` messages."""
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
    for i in range(num_copies):
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
    """Screen and measure heartbeats of `raw_candidates` in one batch compile; synthesize a combined candidate when >=2 pass."""
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
    btxt, n_copies = build_core_batch(statement, body0, [c["body"] for c in batch_cands], max_hb=max_hb)
    if btxt is None:
        return {}
    res = run(btxt, versions[0])
    msgs = getattr(res, "messages", None) or []
    readings = parse_core_batch(msgs, n_copies)
    r0 = readings.get(0)
    ctl = r0 if (r0 and r0.get("ok")) else {"ok": True, "hb": int(inc_hb or 0)}
    exchange = (ctx or {}).get("exchange")

    passed = []
    for idx, c in enumerate(batch_cands):
        ri = readings.get(idx + 1)
        if not ri or not ri.get("ok"):
            continue
        pred = MS.predicted(ctl, body0, c["body"], ri, exchange)
        if pred is None or pred <= 0:
            continue
        passed.append((pred, c["tokens"], ri["hb"], c))

    passed.sort(key=lambda x: (-x[0], x[1], x[2]))
    final_cands: list[dict] = []
    seen_decls: set[str] = set()

    # Synthesize a joint `combo` candidate from non-overlapping passed edits
    combo_edits: list[tuple[int, int, str]] = []
    combo_parts = 0
    for _, _, _, c in passed:
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
        for a, b_pos, repl in sorted(combo_edits, key=lambda e: -e[0]):
            cbody = cbody[:a] + repl + cbody[b_pos:]
        if cbody != body0 and not check_forbidden(cbody):
            cdecl = (head + cbody.rstrip() + "\n").rstrip()
            if cdecl != proof.rstrip() and cdecl not in seen_decls:
                seen_decls.add(cdecl)
                final_cands.append({
                    "op": f"{FAMILY}:combo",
                    "decl": cdecl + "\n",
                    "note": f"combo ({combo_parts} non-overlapping passed edits)"[:200],
                })

    for _, _, _, c in passed:
        d = c["decl"].rstrip()
        if d not in seen_decls:
            seen_decls.add(d)
            final_cands.append({k: c[k] for k in ("op", "decl", "note")})

    emit_cap = 2 if (isinstance(compile_s, (int, float)) and compile_s > 8.0) else MAX_CANDS
    if log is not None:
        log(f"argon_haveopt query: {len(batch_cands)} screened, {len(passed)} passed, {len(final_cands[:emit_cap])} emitted")
    return {"argon_haveopt_cands": final_cands[:emit_cap], "argon_haveopt_for": proof_key(proof)}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=MAX_CANDS, ctx=None) -> list[dict]:
    """Return query-verified candidates when `ctx` matches `proof`, else pure top-ranked candidates (for `--show`)."""
    c = ctx or {}
    cap = max(1, int(max_per_op or MAX_CANDS))
    if c.get("argon_haveopt_for") == proof_key(proof):
        return list(c.get("argon_haveopt_cands") or [])[:cap]
    if "argon_haveopt_for" in c:
        return []
    return [{k: x[k] for k in ("op", "decl", "note")} for x in raw_candidates(proof, statement)[:cap]]
