"""harness/post/argon_bindelide.py — Binder, Type-Annotation, Ascription, Named-Arg & Modifier Elision (`argon_bindelide`).

Targets the #1 remaining token-length (and elaboration-overhead) gap beyond v3 on `open_r3v3` and `open_r2v2x2`:
1. `forall_intro`: folds leading `∀` binders into `have` declarations (both named `have h : ∀ ...` and anonymous
   `have : ∀ ...` via `have this ...`), including multiline return types, `intros`, `unhygienic intros`, bare `intro`,
   `iterate k intro`, partial `intro` prefix trimming, and untyped binder group simplification `(x y : T)` -> `x y`.
2. `forall_lam`: folds single-line and multiline `have [h] : ∀ x, T := λ x => ...` into binder form (with and without `: T`).
3. `decl_type`: drops redundant `: T` type annotations on `set x : T := v`, `let x : T := v`, `have [h] [binders] : T := v`
   (single-line and multiline `T`, when `v` is a term), `obtain pat : T := v`, and simplifies `have this` -> `have`.
4. `show_elide`: elides `show T from e` -> `e`, `show T from by tac` -> `(by tac)`, and `$ show T by tac` -> `$ by tac`.
5. `paren_asc`: elides term-position parenthesized type ascriptions `(e : T)` -> `e` / `(e)` (including `(by tac : T)` -> `(by tac)`
   and `(.intro _ rfl : T)` -> `⟨_, rfl⟩`).
6. `named_arg`: elides `(name := val)` named arguments by dropping them (implicit params), converting to positional `val` / `(val)`
   (explicit params), or replacing with `_`.
7. `mod_elide`: drops redundant `unhygienic`, `with_reducible`, `with_reducible_and_instances`, converts `iterate k intro` -> `intros`,
   and collapses trailing `_ _` runs to `..`.

Verification uses a single-theorem multi-variant `have _lra_v{k} : (<target>) := by ...; clear _lra_v{k}` batch query in `query()`,
which preserves all trailing `open ... in`, `omit ... in`, docstrings, `private`, and `module` contexts across all variants in one compile.
"""

# provenance: research lane gaplane-argon (worktree lra-gl-argon), commit 12dc4b9, ported into open-post-v5-lanes (2026-11-04) unchanged
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import re
import textwrap
from typing import Callable

from scorer.tokenize import count_tokens, split_declaration

OP_NAME = "argon_bindelide"
MAX_ROUNDS = 3

_FORALL_INTRO_ML_RE = re.compile(
    r"(?m)^([ \t]*have(?:\s+([A-Za-z0-9_']+))?([ \t]+[^:\n]+?)?\s*:\s*∀\s+([^\n,]+),\s*([\s\S]+?)\s*:=\s*by)[ \t]*\n"
    r"([ \t]+)(unhygienic\s+)?(?:iterate\s+(\d+)\s+intro\b|intros\b([ \t]*)|intro\b([ \t]+[^\n]+|[ \t]*))(?=\n|$)"
)

_FORALL_LAM_ML_RE = re.compile(
    r"(?m)^([ \t]*have(?:\s+([A-Za-z0-9_']+))?\s*:\s*∀\s+([A-Za-z0-9_']+)\s*,\s*([\s\S]+?)\s*:=)\s*(?:fun|λ)\s*\3\s*(?:=>|↦)\s*"
)

_SET_LET_TYPE_RE = re.compile(
    r"(?m)^([ \t]*)(set|let)\s+([A-Za-z0-9_']+)(\s*:\s*[^:=\n]+?)\s*:="
)

_HAVE_THIS_RE = re.compile(r"\bhave\s+this(?=\s*(?::|:=))")

_SHOW_FROM_BY_RE = re.compile(
    r"(\b(?:from|:=|\$)\s+|\b)show\s+[^\n]+?\s+from\s+by\b"
)

_SHOW_FROM_TERM_RE = re.compile(
    r"\bshow\s+[^\n]+?\s+from(?![ \t\n]+by\b)\s+"
)

_SHOW_BY_RE = re.compile(
    r"(\$\s*|\bexact_mod_cast\s+)show\s+[^\n]+?\s+by\s+"
)

_UNHYG_BY_RE = re.compile(r"\bby[ \t]+unhygienic(?=[ \t]*\n)")
_UNHYG_TAC_RE = re.compile(r"\bunhygienic[ \t]+(?=(?:induction|cases|rcases|intros|intro)\b)")
_WITH_RED_RE = re.compile(r"\bwith_reducible(?:_and_instances)?[ \t]+")
_ITER_INTRO_RE = re.compile(r"\biterate[ \t]+\d+[ \t]+intro\b")
_TRAIL_USCORE_RE = re.compile(r"(?<=[A-Za-z0-9_'])(?:[ \t]+_){2,}(?=[ \t]*(?:\n|\)|\]|⟩|,|\$|$))")

_BINDER_KW_BEFORE_PAREN_RE = re.compile(
    r"(?:\b(?:have|let|set|obtain|rcases|fun|intro|rintro|theorem|lemma|def)\b[^:=\n]*|[λ∀∃][^,\n=>↦]*)\Z"
)

_NAMED_ARG_INNER_RE = re.compile(r"^\s*([A-Za-z_][A-Za-z0-9_']*)\s*:=\s*([^\n]+?)\s*$")
_ATOMIC_EXPR_RE = re.compile(r"^(?:[A-Za-z0-9_'.]+|⟨[^⟩]+⟩|\([^)]+\))$")


@dataclass(frozen=True)
class SiteOption:
    start: int
    end: int
    replacement: str
    rule: str
    dtok: int
    note: str


@dataclass(frozen=True)
class Site:
    start: int
    end: int
    options: tuple[SiteOption, ...]


def _parse_forall_binders(binder_str: str) -> tuple[list[str], str, str]:
    """Return (flat_var_names, typed_binder_text, untyped_binder_text) from a `∀ <binder_str>,` clause."""
    s = binder_str.strip()
    names: list[str] = []
    typed_parts: list[str] = []
    untyped_parts: list[str] = []
    i = 0
    n = len(s)
    while i < n:
        while i < n and s[i].isspace():
            i += 1
        if i >= n:
            break
        if s[i] in "({[":
            open_ch = s[i]
            close_ch = {")": "(", "}": "{", "]": "["}
            target_close = {"(": ")", "{": "}", "[": "]"}[open_ch]
            d = 0
            j = i
            while j < n:
                if s[j] == open_ch:
                    d += 1
                elif s[j] == target_close:
                    d -= 1
                    if d == 0:
                        j += 1
                        break
                j += 1
            grp = s[i:j]
            typed_parts.append(grp)
            inner = grp[1:-1].strip()
            if open_ch == "(" and ":" in inner:
                lhs = inner.split(":", 1)[0].strip()
                g_names = [w for w in lhs.split() if re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", w)]
                if g_names:
                    names.extend(g_names)
                    untyped_parts.extend(g_names)
                else:
                    return [], "", ""
            else:
                return [], "", ""
            i = j
        else:
            j = i
            while j < n and not s[j].isspace() and s[j] not in "({[:":
                j += 1
            if j < n and s[j] == ":":
                # Bare `x : T` without outer parens in `∀ x : T,`
                lhs = s[:j].strip()
                rhs = s[j + 1:].strip()
                g_names = [w for w in lhs.split() if re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", w)]
                if not g_names or not rhs:
                    return [], "", ""
                return g_names, f"({' '.join(g_names)} : {rhs})", " ".join(g_names)
            tok = s[i:j]
            if not re.match(r"^[A-Za-z_][A-Za-z0-9_']*$", tok):
                return [], "", ""
            names.append(tok)
            typed_parts.append(tok)
            untyped_parts.append(tok)
            i = j
    return names, " ".join(typed_parts), " ".join(untyped_parts)


def _extract_forall_intro_sites(body: str) -> list[Site]:
    sites: list[Site] = []
    for m in _FORALL_INTRO_ML_RE.finditer(body):
        full_hdr = m.group(1)
        h_name = m.group(2)
        existing_binders = (m.group(3) or "").strip()
        forall_binders_raw = m.group(4)
        rest_type = m.group(5)
        # Do not cross nested `:=` inside `rest_type`
        if ":=" in rest_type:
            continue
        intro_indent = m.group(6)
        unhyg_prefix = m.group(7) or ""
        iter_k_str = m.group(8)
        intros_rest = m.group(9)
        intro_args_raw = m.group(10)

        f_names, typed_b, untyped_b = _parse_forall_binders(forall_binders_raw)
        if not f_names:
            continue

        lead_ws = re.match(r"^[ \t]*", full_hdr).group(0)
        eff_name = h_name or "this"
        mid_b = f" {existing_binders}" if existing_binders else ""
        orig_span = m.group(0)
        orig_toks = count_tokens(orig_span)

        opts: list[SiteOption] = []

        def add_opt(repl: str, tag: str, note: str) -> None:
            dt = orig_toks - count_tokens(repl)
            if dt > 0 and repl != orig_span:
                opts.append(SiteOption(m.start(), m.end(), repl, tag, dt, note))

        if iter_k_str is not None:
            k = int(iter_k_str)
            if k == len(f_names):
                if untyped_b != typed_b:
                    add_opt(
                        f"{lead_ws}have {eff_name}{mid_b} {untyped_b} : {rest_type} := by",
                        "forall_intro_untyped",
                        f"fold ∀ {untyped_b} + iterate {k} intro",
                    )
                add_opt(
                    f"{lead_ws}have {eff_name}{mid_b} {typed_b} : {rest_type} := by",
                    "forall_intro",
                    f"fold ∀ {typed_b} + iterate {k} intro",
                )
        elif intros_rest is not None:
            if not unhyg_prefix:
                if untyped_b != typed_b:
                    add_opt(
                        f"{lead_ws}have {eff_name}{mid_b} {untyped_b} : {rest_type} := by",
                        "forall_intros_untyped",
                        f"fold ∀ {untyped_b} + intros",
                    )
                add_opt(
                    f"{lead_ws}have {eff_name}{mid_b} {typed_b} : {rest_type} := by",
                    "forall_intros",
                    f"fold ∀ {typed_b} + intros",
                )
            # Fallback keeping `intros` when `rest_type` has further arrows/foralls
            add_opt(
                f"{lead_ws}have {eff_name}{mid_b} {typed_b} : {rest_type} := by\n{intro_indent}{unhyg_prefix}intros",
                "forall_keep_intros",
                f"fold ∀ {typed_b} (keep intros)",
            )
        elif intro_args_raw is not None:
            i_args = intro_args_raw.strip().split()
            if not i_args and len(f_names) == 1 and not unhyg_prefix:
                if untyped_b != typed_b:
                    add_opt(
                        f"{lead_ws}have {eff_name}{mid_b} {untyped_b} : {rest_type} := by",
                        "forall_bare_intro_untyped",
                        f"fold ∀ {untyped_b} + bare intro",
                    )
                add_opt(
                    f"{lead_ws}have {eff_name}{mid_b} {typed_b} : {rest_type} := by",
                    "forall_bare_intro",
                    f"fold ∀ {typed_b} + bare intro",
                )
            elif len(i_args) >= len(f_names) and i_args[: len(f_names)] == f_names:
                rem_args = i_args[len(f_names) :]
                tail_line = f"\n{intro_indent}{unhyg_prefix}intro {' '.join(rem_args)}" if rem_args else ""
                if untyped_b != typed_b:
                    add_opt(
                        f"{lead_ws}have {eff_name}{mid_b} {untyped_b} : {rest_type} := by{tail_line}",
                        "forall_intro_untyped",
                        f"fold ∀ {untyped_b} + intro",
                    )
                add_opt(
                    f"{lead_ws}have {eff_name}{mid_b} {typed_b} : {rest_type} := by{tail_line}",
                    "forall_intro",
                    f"fold ∀ {typed_b} + intro",
                )

        if opts:
            opts.sort(key=lambda o: -o.dtok)
            sites.append(Site(m.start(), m.end(), tuple(opts)))
    return sites


def _extract_forall_lam_sites(body: str) -> list[Site]:
    sites: list[Site] = []
    for m in _FORALL_LAM_ML_RE.finditer(body):
        full_hdr = m.group(1)
        h_name = m.group(2) or "this"
        var_name = m.group(3)
        rest_type = m.group(4).strip()
        if ":=" in rest_type or "\n\n" in rest_type:
            continue
        lead_ws = re.match(r"^[ \t]*", full_hdr).group(0)
        orig_span = m.group(0)
        orig_toks = count_tokens(orig_span)
        opts: list[SiteOption] = []

        repl_no_type = f"{lead_ws}have {h_name} {var_name} := "
        dt_no_type = orig_toks - count_tokens(repl_no_type)
        if dt_no_type > 0:
            opts.append(SiteOption(m.start(), m.end(), repl_no_type, "forall_lam_notype", dt_no_type, f"fold ∀ {var_name} + drop type"))

        repl_typed = f"{lead_ws}have {h_name} {var_name} : {rest_type} := "
        dt_typed = orig_toks - count_tokens(repl_typed)
        if dt_typed > 0:
            opts.append(SiteOption(m.start(), m.end(), repl_typed, "forall_lam", dt_typed, f"fold ∀ {var_name} + λ"))

        if opts:
            opts.sort(key=lambda o: -o.dtok)
            sites.append(Site(m.start(), m.end(), tuple(opts)))
    return sites


def _extract_decl_type_sites(body: str) -> list[Site]:
    sites: list[Site] = []
    # 1. `set x : T :=` and `let x : T :=`
    for m in _SET_LET_TYPE_RE.finditer(body):
        indent, kw, name, ty_part = m.group(1), m.group(2), m.group(3), m.group(4)
        # Check that the RHS after `:=` is not `by`
        after = body[m.end() : m.end() + 20].lstrip()
        if after.startswith("by") and (len(after) == 2 or not after[2].isalnum()):
            continue
        orig = m.group(0)
        orig_toks = count_tokens(orig)
        opts: list[SiteOption] = []
        repl1 = f"{indent}{kw} {name} :="
        dt1 = orig_toks - count_tokens(repl1)
        if dt1 > 0:
            opts.append(SiteOption(m.start(), m.end(), repl1, f"{kw}_type_drop", dt1, f"drop type on {kw} {name}"))
        if kw == "set":
            repl2 = f"{indent}let {name} :="
            dt2 = orig_toks - count_tokens(repl2)
            if dt2 > 0:
                opts.append(SiteOption(m.start(), m.end(), repl2, "set_to_let", dt2, f"set {name} : T -> let {name}"))
        if opts:
            sites.append(Site(m.start(), m.end(), tuple(opts)))

    # 2. `have [h] [binders] : T := <term>` (not `:= by`)
    have_re = re.compile(
        r"(?m)^([ \t]*have(?:\s+([A-Za-z0-9_']+))?([ \t]+\([^:\n]+\)|[ \t]+[A-Za-z0-9_']+)*)(\s*:\s*([^:=\n]+(?:\n[ \t]+[^:=\n]+)?))\s*:=(?![ \t\n]*by\b)"
    )
    for m in have_re.finditer(body):
        prefix = m.group(1)
        h_name = m.group(2)
        binders = m.group(3) or ""
        ty_annot = m.group(4)
        if "\n" in ty_annot and ("∀" in ty_annot or "∃" in ty_annot):
            continue
        orig = m.group(0)
        orig_toks = count_tokens(orig)
        opts = []
        if h_name == "this" and not binders.strip():
            lead_ws = re.match(r"^[ \t]*", prefix).group(0)
            repl_anon = f"{lead_ws}have :="
            dt_anon = orig_toks - count_tokens(repl_anon)
            if dt_anon > 0:
                opts.append(SiteOption(m.start(), m.end(), repl_anon, "have_this_type_drop", dt_anon, "have this : T := -> have :="))
        repl = f"{prefix} :="
        dt = orig_toks - count_tokens(repl)
        if dt > 0:
            opts.append(SiteOption(m.start(), m.end(), repl, "have_type_drop", dt, f"drop type on have {h_name or '_'}"))
        if opts:
            opts.sort(key=lambda o: -o.dtok)
            sites.append(Site(m.start(), m.end(), tuple(opts)))

    # 3. `have this` -> `have` (when `: T := by` or `:=`)
    for m in _HAVE_THIS_RE.finditer(body):
        orig = m.group(0)
        repl = "have"
        dt = count_tokens(orig) - count_tokens(repl)
        if dt > 0:
            sites.append(Site(m.start(), m.end(), (SiteOption(m.start(), m.end(), repl, "have_this", dt, "have this -> have"),)))

    return sites


def _extract_show_sites(body: str) -> list[Site]:
    sites: list[Site] = []
    for m in _SHOW_FROM_TERM_RE.finditer(body):
        orig = m.group(0)
        dt = count_tokens(orig)
        if dt > 0:
            sites.append(Site(m.start(), m.end(), (SiteOption(m.start(), m.end(), "", "show_from_drop", dt, "drop show T from"),)))
    for m in _SHOW_BY_RE.finditer(body):
        prefix = m.group(1)
        orig = m.group(0)
        repl = f"{prefix}by "
        dt = count_tokens(orig) - count_tokens(repl)
        if dt > 0:
            sites.append(Site(m.start(), m.end(), (SiteOption(m.start(), m.end(), repl, "show_by_drop", dt, "drop show T before by"),)))
    return sites


def _find_balanced_parens(body: str) -> list[tuple[int, int]]:
    """Return (start, end) of all balanced `(...)` spans in `body` (excluding single-line comments and strings)."""
    spans: list[tuple[int, int]] = []
    stack: list[int] = []
    in_str = False
    in_line_comment = False
    i = 0
    n = len(body)
    while i < n:
        ch = body[i]
        if in_line_comment:
            if ch == "\n":
                in_line_comment = False
            i += 1
            continue
        if in_str:
            if ch == '"' and (i == 0 or body[i - 1] != "\\"):
                in_str = False
            i += 1
            continue
        if ch == "-" and i + 1 < n and body[i + 1] == "-":
            in_line_comment = True
            i += 2
            continue
        if ch == '"':
            in_str = True
            i += 1
            continue
        if ch == "(":
            stack.append(i)
        elif ch == ")" and stack:
            s = stack.pop()
            spans.append((s, i + 1))
        i += 1
    return spans


def _split_depth0_colon(inner: str) -> tuple[str, str] | None:
    """If `inner` has a single top-level `:` (not `:=` or `::`), return `(lhs, rhs)`."""
    d = 0
    colon_pos = -1
    i = 0
    n = len(inner)
    while i < n:
        ch = inner[i]
        if ch in "([{⟨":
            d += 1
        elif ch in ")]}⟩":
            d = max(0, d - 1)
        elif ch == ":" and d == 0:
            if inner[i + 1 : i + 2] in ("=", ":") or inner[i - 1 : i] in (":",):
                i += 2
                continue
            if colon_pos != -1:
                return None
            colon_pos = i
        i += 1
    if colon_pos == -1:
        return None
    return inner[:colon_pos].strip(), inner[colon_pos + 1 :].strip()


def _extract_paren_and_named_arg_sites(body: str) -> list[Site]:
    sites: list[Site] = []
    for s, e in _find_balanced_parens(body):
        inner = body[s + 1 : e - 1]
        if "\n" in inner:
            continue
        # 1. Check `(name := val)` named argument
        nm = _NAMED_ARG_INNER_RE.match(inner)
        if nm:
            arg_name, val = nm.group(1), nm.group(2).strip()
            # Include leading horizontal space when dropping the whole named argument
            drop_s = s
            while drop_s > 0 and body[drop_s - 1] in " \t":
                drop_s -= 1
            orig_with_ws = body[drop_s:e]
            orig_toks = count_tokens(orig_with_ws)
            lead_ws = body[drop_s:s] or " "
            opts: list[SiteOption] = []

            # Option A: drop ` (name := val)` completely (implicit arg)
            if drop_s < s:
                opts.append(SiteOption(drop_s, e, "", "named_arg_drop", orig_toks, f"drop ({arg_name} := ...)"))

            # Option B: positional replacement `val` or `(val)`
            pos_repl = f"{lead_ws}{val}" if _ATOMIC_EXPR_RE.match(val) else f"{lead_ws}({val})"
            dt_pos = orig_toks - count_tokens(pos_repl)
            if dt_pos > 0:
                opts.append(SiteOption(drop_s, e, pos_repl, "named_arg_pos", dt_pos, f"({arg_name} := ...) -> positional"))

            # Option C: placeholder `_`
            us_repl = f"{lead_ws}_"
            dt_us = orig_toks - count_tokens(us_repl)
            if dt_us > 0 and val != "_":
                opts.append(SiteOption(drop_s, e, us_repl, "named_arg_hole", dt_us, f"({arg_name} := ...) -> _"))

            if opts:
                opts.sort(key=lambda o: -o.dtok)
                sites.append(Site(drop_s, e, tuple(opts)))
            continue

        # 2. Check `(expr : Type)` in term position (not binder list, not followed by `.proj`)
        if e < len(body) and body[e : e + 1] == ".":
            continue
        line_start = body.rfind("\n", 0, s) + 1
        before_on_line = body[line_start:s]
        if _BINDER_KW_BEFORE_PAREN_RE.search(before_on_line):
            continue
        sp = _split_depth0_colon(inner)
        if sp is None:
            continue
        expr, ty = sp
        if not expr or not ty:
            continue
        orig = body[s:e]
        orig_toks = count_tokens(orig)
        opts = []

        if expr.startswith(".intro ") and len(expr.split()) == 3:
            parts = expr.split()
            angle_repl = f"⟨{parts[1]}, {parts[2]}⟩"
            dt_a = orig_toks - count_tokens(angle_repl)
            if dt_a > 0:
                opts.append(SiteOption(s, e, angle_repl, "asc_ctor_angle", dt_a, f"({expr} : ...) -> {angle_repl}"))

        if _ATOMIC_EXPR_RE.match(expr) or before_on_line.rstrip().endswith((":=", "$", ",", "[")):
            dt_bare = orig_toks - count_tokens(expr)
            if dt_bare > 0:
                opts.append(SiteOption(s, e, expr, "asc_drop_bare", dt_bare, "drop (: T) and parens"))

        paren_repl = f"({expr})"
        dt_p = orig_toks - count_tokens(paren_repl)
        if dt_p > 0:
            opts.append(SiteOption(s, e, paren_repl, "asc_drop_type", dt_p, "drop : T inside parens"))

        if opts:
            opts.sort(key=lambda o: -o.dtok)
            sites.append(Site(s, e, tuple(opts)))

    return sites


def _extract_mod_sites(body: str) -> list[Site]:
    sites: list[Site] = []
    for m in _UNHYG_BY_RE.finditer(body):
        sites.append(Site(m.start(), m.end(), (SiteOption(m.start(), m.end(), "by", "unhyg_by_drop", 1, "by unhygienic -> by"),)))
    for m in _UNHYG_TAC_RE.finditer(body):
        sites.append(Site(m.start(), m.end(), (SiteOption(m.start(), m.end(), "", "unhyg_tac_drop", 1, "drop unhygienic"),)))
    for m in _WITH_RED_RE.finditer(body):
        sites.append(Site(m.start(), m.end(), (SiteOption(m.start(), m.end(), "", "with_red_drop", 1, "drop with_reducible"),)))
    for m in _ITER_INTRO_RE.finditer(body):
        orig = m.group(0)
        dt = count_tokens(orig) - 1
        if dt > 0:
            sites.append(Site(m.start(), m.end(), (SiteOption(m.start(), m.end(), "intros", "iter_intro_to_intros", dt, f"{orig} -> intros"),)))
    for m in _TRAIL_USCORE_RE.finditer(body):
        orig = m.group(0)
        repl = " .."
        dt = count_tokens(orig) - count_tokens(repl)
        if dt > 0:
            sites.append(Site(m.start(), m.end(), (SiteOption(m.start(), m.end(), repl, "trail_uscore_dots", dt, f"{orig.strip()} -> .."),)))
    return sites


def extract_sites(body: str) -> list[Site]:
    """Return non-overlapping `Site`s ordered by start offset, preferring higher token savings on overlap."""
    all_raw: list[Site] = []
    all_raw.extend(_extract_forall_intro_sites(body))
    all_raw.extend(_extract_forall_lam_sites(body))
    all_raw.extend(_extract_decl_type_sites(body))
    all_raw.extend(_extract_show_sites(body))
    all_raw.extend(_extract_paren_and_named_arg_sites(body))
    all_raw.extend(_extract_mod_sites(body))

    # Deduplicate and resolve overlaps greedily by highest dtok first
    all_raw.sort(key=lambda st: (-st.options[0].dtok, st.start, st.end))
    picked: list[Site] = []
    for st in all_raw:
        if any(not (st.end <= p.start or st.start >= p.end) for p in picked):
            continue
        picked.append(st)
    picked.sort(key=lambda st: st.start)
    return picked


def apply_options(body: str, opts: list[SiteOption]) -> str:
    ordered = sorted(opts, key=lambda o: o.start)
    out: list[str] = []
    cur = 0
    for o in ordered:
        if o.start < cur:
            continue
        out.append(body[cur : o.start])
        out.append(o.replacement)
        cur = o.end
    out.append(body[cur:])
    return "".join(out)


def _split_target(stmt: str) -> tuple[str | None, str | None]:
    d = 0
    in_str = False
    for i, ch in enumerate(stmt):
        if ch == '"' and (i == 0 or stmt[i - 1] != "\\"):
            in_str = not in_str
        if in_str:
            continue
        if ch in "([{⟨":
            d += 1
        elif ch in ")]}⟩":
            d = max(0, d - 1)
        elif ch == ":" and d == 0:
            if stmt[i + 1 : i + 2] != "=" and stmt[i - 1 : i] != ":":
                return stmt[: i + 1], stmt[i + 1 :].strip()
    return None, None


def _strip_by_and_indent(body: str, spaces: int = 4) -> str:
    b = body.lstrip()
    if b.startswith("by") and (len(b) == 2 or not b[2].isalnum()):
        rest = b[2:]
        first_nl = rest.find("\n")
        if first_nl == -1:
            ded = rest.strip()
        else:
            same_line = rest[:first_nl].strip()
            after_lines = textwrap.dedent(rest[first_nl + 1 :])
            ded = (same_line + "\n" + after_lines) if same_line else after_lines
    else:
        ded = f"exact ({b})"
    pad = " " * spaces
    return "\n".join((pad + ln if ln.strip() else "") for ln in ded.splitlines())


def _run_single_theorem_batch(stmt: str, variants: list[str], run: Callable) -> list[bool] | None:
    """Compile `variants` inside one `theorem ... := by` using `have _lra_v{idx} : (<target>) := by ...`."""
    _, target = _split_target(stmt)
    if not target:
        return None
    lines = stmt.splitlines()
    lines[-1] = lines[-1] + " := by"
    lines.append("  have _lra_anchor : True := by")
    lines.append("    trace_state")
    anchor_local_line = len(lines)
    lines.append("    trivial")
    lines.append("  clear _lra_anchor")
def _option_line_ranges_in_variant(body: str, opts: list[SiteOption], base_line_in_variant: int) -> list[tuple[int, int]]:
    """Return 1-based `(start_line, end_line)` inside the stripped+indented variant for each option in `opts`."""
    ordered = sorted(opts, key=lambda o: o.start)
    # Build the modified body while tracking character offsets of each replacement
    parts: list[str] = []
    spans_char: list[tuple[int, int]] = []
    cur = 0
    cur_len = 0
    for o in ordered:
        pre = body[cur : o.start]
        parts.append(pre)
        cur_len += len(pre)
        s_c = cur_len
        parts.append(o.replacement)
        cur_len += len(o.replacement)
        e_c = cur_len
        spans_char.append((s_c, e_c))
        cur = o.end
    parts.append(body[cur:])
    mod_body = "".join(parts)

    # Compute how many leading lines `_strip_by_and_indent` removes or shifts
    b_l = mod_body.lstrip()
    lead_stripped = len(mod_body) - len(b_l)
    extra_line_shift = 0
    if b_l.startswith("by") and (len(b_l) == 2 or not b_l[2].isalnum()):
        rest = b_l[2:]
        first_nl = rest.find("\n")
        if first_nl != -1:
            same_line = rest[:first_nl].strip()
            if not same_line:
                # The `by\n` line was removed, so line numbers in `mod_body` after `first_nl` shift by -1
                extra_line_shift = -1

    ranges: list[tuple[int, int]] = []
    for s_c, e_c in spans_char:
        s_adj = max(0, s_c - lead_stripped)
        e_adj = max(s_adj, e_c - lead_stripped)
        s_ln = base_line_in_variant + b_l[:s_adj].count("\n") + extra_line_shift
        e_ln = base_line_in_variant + b_l[:e_adj].count("\n") + extra_line_shift
        ranges.append((s_ln, e_ln))
    return ranges


def _run_single_theorem_batch(
    stmt: str, variants: list[str], run: Callable, return_error_lines: bool = False
) -> list[bool] | tuple[list[bool], dict[int, list[int]]] | None:
    """Compile `variants` inside one `theorem ... := by` using `have _lra_v{idx} : (<target>) := by ...`."""
    _, target = _split_target(stmt)
    if not target:
        return None
    lines = stmt.splitlines()
    lines[-1] = lines[-1] + " := by"
    lines.append("  have _lra_anchor : True := by")
    lines.append("    trace_state")
    anchor_local_line = len(lines)
    lines.append("    trivial")
    lines.append("  clear _lra_anchor")
    spans: list[tuple[int, int, int, int]] = []
    t_ind = "\n".join(("    " + ln if ln.strip() else "") for ln in textwrap.dedent(target).splitlines())
    for idx, v in enumerate(variants):
        start_ln = len(lines) + 1
        lines.append(f"  have _lra_v{idx} : (")
        lines.extend(t_ind.splitlines())
        lines.append("  ) := by")
        body_start_ln = len(lines) + 1
        lines.extend(_strip_by_and_indent(v, 4).splitlines())
        lines.append("  trace_state")
        trace_ln = len(lines)
        if idx + 1 < len(variants):
            lines.append(f"  clear _lra_v{idx}")
        else:
            lines.append(f"  exact _lra_v{idx}")
        end_ln = len(lines)
        spans.append((start_ln, end_ln, trace_ln, body_start_ln))
    text = "\n".join(lines) + "\n"
    r = run(text, None)
    res = r[0] if isinstance(r, tuple) else r
    msgs = getattr(res, "messages", None) or []
    anchor_abs = None
    for msg in msgs:
        if "⊢ True" in str(msg.get("data", "")):
            anchor_abs = (msg.get("pos") or {}).get("line")
            break
    if anchor_abs is None:
        return None
    offset = anchor_abs - anchor_local_line
    bad_idxs: set[int] = set()
    seen_traces: set[int] = set()
    err_lines_by_idx: dict[int, list[int]] = {i: [] for i in range(len(variants))}
    for msg in msgs:
        sev = msg.get("severity")
        data = str(msg.get("data", ""))
        ln = (msg.get("pos") or {}).get("line")
        if ln is None:
            continue
        loc = ln - offset
        if sev == "information":
            for idx, (_s, _e, t_ln, _b_ln) in enumerate(spans):
                if loc == t_ln:
                    seen_traces.add(idx)
        if sev == "error" or ("sorry" in data and sev == "warning"):
            for idx, (s, e, _t_ln, b_ln) in enumerate(spans):
                if s <= loc <= e:
                    bad_idxs.add(idx)
                    err_lines_by_idx[idx].append(loc - b_ln + 1)
    verdicts = [(idx not in bad_idxs and idx in seen_traces) for idx in range(len(variants))]
    if return_error_lines:
        return verdicts, err_lines_by_idx
    return verdicts


def has_sites(proof: str, statement: str) -> bool:
    body = split_declaration(proof, statement)
    if body is None:
        return False
    return bool(extract_sites(body))


def query(
    proof: str,
    statement: str,
    run: Callable,
    *,
    versions=None,
    ctx: dict | None = None,
    stats: dict | None = None,
    log: Callable | None = None,
) -> dict:
    body = split_declaration(proof, statement)
    if body is None:
        return {}
    sites = extract_sites(body)
    if not sites:
        return {}

    inc_hb = int((ctx or {}).get("inc_hb") or 3000)
    max_copies = max(4, min(14, int(150000 // max(inc_hb, 1000))))

    # Active option index per site (start with index 0 = best dtok)
    active_opts: list[SiteOption] = [st.options[0] for st in sites]

    # Round 1: test [control, joint_all, ...individual or chunked edits...]
    n_test_slots = max_copies - 2
    if len(active_opts) <= n_test_slots:
        groups: list[list[int]] = [[i] for i in range(len(active_opts))]
    else:
        groups = [[] for _ in range(n_test_slots)]
        for i in range(len(active_opts)):
            groups[i % n_test_slots].append(i)

    r1_variants = [body, apply_options(body, active_opts)] + [
        apply_options(body, [active_opts[i] for i in grp]) for grp in groups
    ]
    verdicts = _run_single_theorem_batch(statement, r1_variants, run)
    if verdicts is None or not verdicts[0]:
        return {}

    if verdicts[1]:
        # All active edits compiled cleanly together in Round 1!
        return {"queried": True, "verified_opts": active_opts, "union_verified": True}

    verified_indices: list[int] = []
    failed_single_sites: list[int] = []
    failed_multi_groups: list[list[int]] = []
    for g_idx, grp in enumerate(groups):
        if verdicts[2 + g_idx]:
            verified_indices.extend(grp)
        elif len(grp) == 1:
            failed_single_sites.append(grp[0])
        else:
            failed_multi_groups.append(grp)

    # Round 2: test fallback spellings for failed single sites + split failed multi-groups + test current verified union
    r2_tasks: list[ tuple[str, list[SiteOption]] ] = []
    if len(verified_indices) >= 2:
        r2_tasks.append(("verified_union", [active_opts[i] for i in sorted(verified_indices)]))

    for s_idx in failed_single_sites:
        if len(sites[s_idx].options) > 1:
            r2_tasks.append((f"alt:{s_idx}:1", [sites[s_idx].options[1]]))

    for grp in failed_multi_groups:
        for s_idx in grp:
            r2_tasks.append((f"split:{s_idx}:0", [active_opts[s_idx]]))

    verified_opts: list[SiteOption] = [active_opts[i] for i in sorted(verified_indices)]
    union_verified = len(verified_opts) <= 1

    if r2_tasks:
        r2_slice = r2_tasks[: max_copies - 1]
        r2_variants = [body] + [apply_options(body, opts) for _, opts in r2_slice]
        v2 = _run_single_theorem_batch(statement, r2_variants, run)
        if v2 is not None and v2[0]:
            newly_verified: list[SiteOption] = []
            for t_idx, (tag, opts) in enumerate(r2_slice):
                if v2[1 + t_idx]:
                    if tag == "verified_union":
                        union_verified = True
                    else:
                        newly_verified.extend(opts)
            if newly_verified:
                verified_opts.extend(newly_verified)
                verified_opts.sort(key=lambda o: o.start)
                union_verified = False

    # Round 3 (if needed): verify the full `verified_opts` union in a clean 2-variant batch `[body, union]`
    # and prune any option whose line in `_lra_v1` raises a postponed synthesis error.
    if len(verified_opts) >= 2 and not union_verified:
        res3 = _run_single_theorem_batch(
            statement, [body, apply_options(body, verified_opts)], run, return_error_lines=True
        )
        if res3 is not None:
            v3, err_lines = res3
            if v3[0] and v3[1]:
                union_verified = True
            elif v3[0] and err_lines.get(1):
                bad_rel_lines = set(err_lines[1])
                ranges = _option_line_ranges_in_variant(body, verified_opts, 1)
                hit_opts = [
                    i
                    for i, (_o, (r_s, r_e)) in enumerate(zip(verified_opts, ranges))
                    if any((r_s - 1) <= bl <= (r_e + 1) for bl in bad_rel_lines)
                ]
                # If a line has both `have_this` (always safe) and a type/ctor elision, drop the non-have_this first
                non_triv_hits = [i for i in hit_opts if verified_opts[i].rule != "have_this"]
                drop_set = set(non_triv_hits if non_triv_hits else hit_opts)
                pruned = [o for i, o in enumerate(verified_opts) if i not in drop_set]
                if pruned and len(pruned) < len(verified_opts):
                    verified_opts = pruned
                    union_verified = True

    return {
        "queried": True,
        "verified_opts": verified_opts,
        "union_verified": union_verified,
    }


def candidates(
    proof: str,
    statement: str,
    *,
    exchange=None,
    max_per_op=None,
    ctx: dict | None = None,
    **kw,
) -> list[dict]:
    body = split_declaration(proof, statement)
    if body is None:
        return []
    sites = extract_sites(body)
    if not sites:
        return []

    out: list[dict] = []
    seen: set[str] = set()
    base_toks = count_tokens(body)

    def emit(opts: list[SiteOption], variant_tag: str, note: str) -> None:
        if not opts:
            return
        new_body = apply_options(body, opts)
        if new_body == body or count_tokens(new_body) >= base_toks:
            return
        decl = f"{statement} :={new_body}"
        h = hashlib.sha256(decl.rstrip().encode()).hexdigest()[:16]
        if h in seen:
            return
        seen.add(h)
        out.append({"op": f"{OP_NAME}:{variant_tag}", "decl": decl, "note": note[:160]})

    queried = bool((ctx or {}).get("queried"))
    verified_opts: list[SiteOption] = (ctx or {}).get("verified_opts") or []
    if queried:
        if not verified_opts:
            return []
        # 1. Joint candidate of all verified options
        emit(
            verified_opts,
            "joint",
            f"verified joint ({len(verified_opts)} edits, -{sum(o.dtok for o in verified_opts)} tok)",
        )
        # 2. Exclude `unhyg_*` or `set_to_let` in case of subtle interaction if joint wasn't pre-verified
        safe_sub = [o for o in verified_opts if not o.rule.startswith("unhyg_")]
        if len(safe_sub) < len(verified_opts):
            emit(safe_sub, "joint_no_unhyg", f"verified joint without unhyg ({len(safe_sub)} edits)")
        # 3. Individual verified edits ordered by token savings
        for o in sorted(verified_opts, key=lambda x: -x.dtok):
            emit([o], o.rule, f"{o.note} (-{o.dtok} tok)")
    else:
        # Pure fallback (when `--show` or no query ctx)
        top_opts = [st.options[0] for st in sites]
        emit(top_opts, "joint_raw", f"raw joint ({len(top_opts)} edits)")
        for o in sorted(top_opts, key=lambda x: -x.dtok):
            emit([o], o.rule, f"{o.note} (-{o.dtok} tok)")

    if max_per_op is not None:
        out = out[: int(max_per_op)]
    return out
