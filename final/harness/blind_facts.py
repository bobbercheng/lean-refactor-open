#!/usr/bin/env python3
"""Blind first session (operator 2026-10-31 ~02:15 UTC: "forget the original and use statement/pins as test driven approach for mini







"""
from __future__ import annotations

import argparse, json, math, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scorer.tokenize import split_declaration              

                                                                                                                                       
                                                                                            
_START = "A-Za-z_α-κμ-ωΑ-ΟΡ΢Τ-Ωϊ-ϻἀ-῾℀-⅏\U0001d49c-\U0001d59f"
_REST = _START + "0-9'!?₀-₉ₐ-ₜᵢ-ᵪⱼ"
ID = rf"[{_START}][{_REST}]*"
_TOKEN = re.compile(rf"(?P<id>(?<![{_REST}.])\.?{ID}(?:\.(?:{ID}|\d+))*)|(?P<op><;>|:=|=>|←|\S)")
REVEAL_FRACTION = 3                                                                                                                    

                                                                                                                                       
                                                                                                           
TACTICS = set("""
abel abel_nf absurd ac_rfl aesop aesop? all_goals and_intros any_goals apply apply? apply_assumption apply_fun apply_rules assumption
assumption' bound by_cases by_contra by_contra! by_contra' calc cancel_denoms case case' cases cases' change choose classical clear
congr congr! congrm constructor continuity contradiction contrapose contrapose! convert convert_to dsimp dsimp? decide decreasing_tactic
done norm_num1 eq_refl erw exact exact? exact_mod_cast exacts exfalso exists existsi ext ext1 fail field_simp fin_cases first focus
fun_induction fun_cases fun_prop funext gcongr generalize generalize_proofs grind grind? group have haveI induction induction' infer_instance
injection injections interval_cases intro intros introv iterate left let letI lia lift linarith linarith! linear_combination match
measurability mod_cases module monotonicity next nlinarith nofun nomatch noncomm_ring norm_cast norm_num nth_rewrite nth_rw obtain omega
on_goal peel pick_goal polyrith positivity push_cast push_neg qify rcases rename rename_i repeat repeat' replace revert rewrite rfl rify
right ring ring1 ring_nf rintro rw rw? rwa rw_mod_cast set show simp simp? simp! simp_all simp_all? simp_all! simp_arith simp_intro
simp_rw simpa simpa? simpa! skip sorry specialize split split_ands split_ifs subst subst_vars suffices swap symm tauto trans trivial
try unfold unfold_let use use! wlog zify stop nofun refine refine' rcases? solve_by_elim norm_num? tfae_have tfae_finish
conv conv_lhs conv_rhs enter arg lhs rhs pattern rw! module ring_nf! field_simp! norm_num! decide! simp_arith! bv_omega bv_decide
apply_mod_cast assumption_mod_cast rename' clear_value lift_lets extract_lets tauto! itauto finiteness borelize filter_upwards
casesm cases_type constructorm rcongr subsingleton with_reducible show_term says observe exact! apply! delta beta_reduce
simp_wf decreasing_trivial cutsat ac_nf abel1 linear_combination' simp_all_arith compute_degree monicity norm_fin rel bound
contrapose! choose! gcongr? unfold_projs whnf reduce eta_reduce admit split_ifs! nth_rw! omega! positivity! aesop_cat
""".split())
                                                                                                     
_TERMISH = {"rfl", "trivial", "decide", "absurd", "id"}
_TERM_KW = set("""fun by at with using generalizing only from in then else if do match let have show calc this Type Prop Sort where
deriving mod true false True False case case' next""".split())
                                                                                                                                    
_PROJ = {"mp", "mpr", "symm", "trans", "le", "ge", "lt", "ne", "ne'", "elim", "left", "right", "out", "imp", "some", "choose", "choose_spec", "1", "2"}
_TARGET_TACS = ("induction", "induction'", "cases", "cases'", "rcases", "obtain", "fun_induction", "fun_cases", "match", "interval_cases",
                "fin_cases", "mod_cases")
_READERS = re.compile(r"(?<![\w./-])(cat|zcat|grep|egrep|fgrep|zgrep|rg|ag|ack|sed|awk|gawk|head|tail|less|more|nl|tac|bat|batcat|view|vi|vim|"
                      r"strings|cut|xxd|od|python3?|perl|ruby|find|git|diff|cmp|sort|uniq|tr|jq|cp|tee|xargs)(?![\w-])")


def statement_name(statement: str) -> str:
    m = re.search(rf"\b(?:theorem|lemma|def|abbrev|instance|example)\s+({ID}(?:\.{ID})*)", statement or "")
    return m.group(1) if m else ""


def blind_candidate(statement: str) -> str:
    """candidate.lean of a blind first session: the exact benchmark statement with a `sorry` body (never banked: the forbidden-pattern
"""
    return statement.rstrip() + " := by\n  sorry\n"


def _strip(text: str) -> str:
    text = re.sub(r"/-.*?-/", " ", text, flags=re.S)
    text = re.sub(r"--[^\n]*", "", text)
    return re.sub(r'"(?:[^"\\\n]|\\.)*"', '""', text)


def _lex(text: str) -> list[tuple[str, str, int]]:
    """(kind, text, line) of every token: kind id / op."""
    out = []
    for ln, line in enumerate(text.split("\n")):
        for m in _TOKEN.finditer(line):
            kind = "id" if m.group("id") else "op"
            if kind == "id" and m.group(0).startswith(".") and m.start() > 0 and line[m.start() - 1] in ")]}⟩":
                kind = "proj"                                                                             
            out.append((kind, m.group(0), ln))
    return out


def _base_name(w: str) -> str:
    parts = w.split(".")
    lead = w.startswith(".")
    while len(parts) > (3 if lead else 2) and parts[-1] in _PROJ or (len(parts) == 2 and not lead and parts[0][:1].islower() and parts[-1] in _PROJ):
        parts = parts[:-1]
    return ".".join(parts)


def _is_id(t) -> bool:
    return t[0] == "id" and not t[1].startswith(".") and not re.fullmatch(r"_+", t[1])


class _Bound(set):
    """A set of bound names that also records where each was bound (for the target origins)."""

    def __init__(self, where):
        super().__init__(); self.where = where

    def add(self, name, idx=None, kind="other"):
        super().add(name)
        if self.where is not None and idx is not None:
            self.where.setdefault(name, []).append((idx, kind))


def _binders(toks: list, where: dict | None = None) -> set:
    """Names bound inside the text: intro-like tactics, case / next / match alternatives, obtain / rcases / rintro patterns, have / let /

"""
    out = _Bound(where)
    n = len(toks)

    def ids_until(i, stops, bracket_ok=True):
        got = []; depth = 0
        while i < n:
            k, s, _ = toks[i]
            if depth == 0 and s in stops:
                break
            if s in "(⟨[{⦃":
                depth += 1
            elif s in ")⟩]}⦄":
                if depth == 0:
                    break
                depth -= 1
            elif depth > 0 and s == ":" and not bracket_ok:
                pass
            if k == "id" and _is_id(toks[i]):
                got.append((s.split(".")[0], i))
            i += 1
        return got
    for i, (k, s, ln) in enumerate(toks):
        nxt = toks[i + 1] if i + 1 < n else ("op", "", ln)
        if k == "id" and s in ("intro", "intros", "rintro", "introv", "rename_i", "ext", "ext1", "funext", "next"):
            j = i + 1; depth = 0
            while j < n and toks[j][2] == ln and (depth > 0 or toks[j][1] not in (";", "<;>", "=>", ":")):
                t = toks[j]
                depth += t[1] in "(⟨[{" ; depth -= t[1] in ")⟩]}"
                if _is_id(t) and t[1] not in ("rfl",):
                    out.add(t[1].split(".")[0], j, "intro" if s in ("intro", "intros", "rintro") else "other")
                j += 1
        elif k == "id" and s in ("case", "case'") and not (i > 0 and toks[i - 1][1] in ("case", "case'")) or (
                k == "op" and s == "|" and i + 1 < n and toks[i + 1][0] == "id"):
                                                                                                                                   
            j = i + 2
            while j < n and toks[j][2] == ln and toks[j][1] not in ("=>", "|"):
                if _is_id(toks[j]):
                    out.add(toks[j][1], j)
                j += 1
        elif k == "id" and s in ("obtain", "rcases", "cases'", "induction'", "injection", "choose", "set", "generalize"):
                                                                                                                                          
            j = i + 1; seen_with = s in ("obtain", "choose")
            while j < n and toks[j][2] == ln and toks[j][1] not in (";", "<;>"):
                t = toks[j]
                if t[1] == "with":
                    seen_with = True
                elif t[1] in (":=", "using") and s in ("obtain", "choose", "set", "generalize"):
                    if s in ("set", "generalize"):
                        seen_with = False
                    else:
                        break
                elif t[1] == ":" and s == "obtain":
                    break
                if (seen_with or s in ("set", "generalize") and toks[j - 1][1] in (s, ":")) and _is_id(t) and t[1] not in ("rfl", "with"):
                    out.add(t[1].split(".")[0], j)
                elif s == "generalize" and toks[j - 1][1] == "=" and _is_id(t):                         
                    out.add(t[1], j)
                j += 1
        elif k == "id" and s in ("have", "haveI", "let", "letI", "suffices", "by_cases", "by_contra", "by_contra!", "by_contra'", "replace",
                                  "set", "obtain", "show"):
            if s == "show":
                continue
            if nxt[1] == "⟨":
                for nm, jj in ids_until(i + 2, ("⟩",)):
                    out.add(nm, jj)
            elif _is_id(nxt) and nxt[1] not in ("this",):
                out.add(nxt[1], i + 1)
        elif k == "id" and s in ("fun", "∀", "∃", "∃!") or (k == "op" and s in ("∀", "∃", "λ", "Σ", "Π", "∑", "∏", "⋃", "⋂")):
            stop = ("=>", "↦") if s in ("fun", "λ") else (",",)
            j = i + 1; depth = 0
            while j < n and toks[j][1] not in stop:
                t = toks[j]
                if t[1] in ("(", "⟨", "{", "[", "⦃"):
                    depth += 1
                elif t[1] in (")", "⟩", "}", "]", "⦄"):
                    depth -= 1
                    if depth < 0:
                        break
                elif t[1] in (":", "∈", "∉", "<", "≤", ">", "≥", "⊆", "≠") and depth == 0:
                    while j < n and toks[j][1] not in stop:                                                    
                        j += 1
                    break
                elif t[1] == ":" and depth > 0:                                                    
                    d = depth
                    while j < n and d >= depth:
                        j += 1
                        if j < n and toks[j][1] in (")", "⟩", "}", "]", "⦄"):
                            d -= 1
                        elif j < n and toks[j][1] in ("(", "⟨", "{", "[", "⦃"):
                            d += 1
                    depth -= 1
                    j += 1
                    continue
                if _is_id(t):
                    out.add(t[1], j)
                j += 1
        elif k == "op" and s in ("(", "{", "[", "⦃") and nxt[0] == "id":
                                                                    
            j = i + 1; names = []
            while j < n and _is_id(toks[j]) and "." not in toks[j][1]:
                names.append((toks[j][1], j)); j += 1
            if j < n and names and toks[j][1] in (":", ":="):
                for nm, jj in names:
                    out.add(nm, jj)
    return out


def _step_starts(toks: list) -> list[int]:
    """Indices of the tokens that start a tactic step: a line's first word after bullets and `case … =>` / `next … =>` / `| … =>`
"""
    starts = []
    n = len(toks)
    line_first = {}
    for i, t in enumerate(toks):
        line_first.setdefault(t[2], i)
    for ln, i in sorted(line_first.items()):
        j = i
        while j < n and toks[j][2] == ln:
            s = toks[j][1]
            if s in ("·", ".", "<;>", "(", "{"):
                j += 1; continue
            if s in ("case", "case'", "next") or s == "|":
                k = j + 1
                while k < n and toks[k][2] == ln and toks[k][1] != "=>":
                    k += 1
                if k < n and toks[k][2] == ln:
                    j = k + 1; continue
                break
            break
        if j < n and toks[j][2] == ln:
            starts.append(j)
    for i, t in enumerate(toks):
        if t[1] in ("by", "<;>", ";", "all_goals", "any_goals", "try", "repeat", "repeat'", "focus", "first") and i + 1 < n:
            j = i + 1
            while j < n and toks[j][1] in ("(", "{", "|", "·"):
                j += 1
            if j < n:
                starts.append(j)
        if t[1] == "|" and i > 0 and toks[i - 1][1] == "first" and i + 1 < n:
            starts.append(i + 1)
    return sorted(set(starts))


def _is_tactic(toks, i, locals_: set) -> bool:
    t = toks[i]
    if t[0] != "id" or t[1].startswith("."):
        return False
    w = t[1]
    if w in _TERM_KW and w not in ("let", "have", "show", "calc", "match"):
        return False
    return w in TACTICS                                                                                                    


def facts(row: dict, ref_heartbeats=None, versions: list | None = None) -> dict:
    """The facts of a row's reference proof (module docstring). Never raises on odd input: the lists come back shorter."""
    src = row.get("src") or ""
    statement = row.get("statement") or ""
    body = split_declaration(src, statement)
    if body is None:
        i = src.find(":=", len(statement) - 5 if len(statement) > 5 else 0)
        body = src[i + 2:] if i >= 0 else ""
    toks = _lex(_strip(body))
    st_toks = _lex(_strip(statement))
    me = statement_name(statement)
    st_ids = {t[1] for t in st_toks if t[0] == "id"}
    st_binders = _binders(st_toks)
    locals_ = _binders(toks) | st_binders
    starts = set(_step_starts(toks))
    tac_idx = {i for i in starts if _is_tactic(toks, i, locals_)}
    tactics: dict = {}
    for i in sorted(tac_idx):
        tactics[toks[i][1]] = tactics.get(toks[i][1], 0) + 1
    n_comb = sum(1 for t in toks if t[1] == "<;>")
    labels, names, recursive = [], [], False
    label_idx = set()
    for i, t in enumerate(toks):
        if t[1] in ("case", "case'") and i + 1 < len(toks) and toks[i + 1][0] == "id" and i not in label_idx:
            label_idx.add(i + 1)                                                    
        elif t[1] == "|" and i + 1 < len(toks) and toks[i + 1][0] == "id" and any(
                toks[k][1] == "=>" for k in range(i + 1, min(len(toks), i + 12)) if toks[k][2] == t[2]):
            label_idx.add(i + 1)
    for i in sorted(label_idx):
        lab = toks[i][1].lstrip(".")
        if lab not in labels:
            labels.append(lab)
    for i, t in enumerate(toks):
        if t[0] != "id" or i in tac_idx or i in label_idx:
            continue
        w = t[1]
        head = w.lstrip(".").split(".")[0]
        if re.fullmatch(r"_+", w) or w in _TERM_KW or w in TACTICS and (i in starts or w not in _TERMISH):
            continue
        if not w.startswith(".") and (head in locals_ or w in locals_):
            continue
        if i > 0 and toks[i - 1][1] in ("(", "{", "[") and i + 1 < len(toks) and toks[i + 1][1] == ":=":
            continue                              
        if me and (w == me or w.split(".")[-1] == me.split(".")[-1] and "." in me and w == me.split(".")[-1]):
            recursive = True
            continue
        if w in st_ids:
            continue                                     
        if w in ("rfl", "trivial") and i in starts:
            continue
        w = _base_name(w)
        if w not in names and w not in st_ids:
            names.append(w)
                                                                                                               
    intro_order = []
    for i, t in enumerate(toks):
        if t[1] in ("intro", "intros", "rintro") and i in tac_idx:
            j = i + 1
            while j < len(toks) and toks[j][2] == t[2] and toks[j][1] not in (";", "<;>"):
                if _is_id(toks[j]):
                    intro_order.append(toks[j][1])
                j += 1
    where: dict = {}
    _binders(toks, where)
    targets = []
    for i, t in enumerate(toks):
        if t[1] not in _TARGET_TACS or (t[1] != "match" and i not in tac_idx):
            continue
        tac = t[1]
        j = i + 1
        if tac == "obtain":                    
            while j < len(toks) and toks[j][2] == t[2] and toks[j][1] != ":=":
                j += 1
            j += 1
        nxt = toks[j] if j < len(toks) and toks[j][2] == t[2] else None
        end = toks[j + 1][1] if j + 1 < len(toks) and toks[j + 1][2] == t[2] else ""
        if nxt is None:
            continue
        if nxt[0] == "id" and end in ("", "with", "generalizing", "using", "<;>", ";"):
            w = nxt[1]; head = w.split(".")[0]
            before = [b for b in where.get(head, []) if b[0] < j]
            if before and before[-1][1] == "intro":                                                                          
                bi = before[-1][0]; k0 = bi
                while k0 > 0 and toks[k0 - 1][1] not in ("intro", "intros", "rintro") and toks[k0 - 1][2] == toks[bi][2]:
                    k0 -= 1
                pos = sum(1 for x in range(k0, bi + 1) if _is_id(toks[x]))
                origin = f"the {_ordinal(pos)} name introduced by {toks[k0 - 1][1] if k0 > 0 else 'intro'}"
            elif before:
                origin = "a local hypothesis/term of the proof"
            elif w in st_binders or head in st_binders:
                origin = "a variable/hypothesis of the statement"
            elif head in locals_:
                origin = "a local hypothesis/term of the proof"
            else:
                origin = "a library/project term"
            gen = []
            if end == "generalizing":
                k = j + 2
                while k < len(toks) and toks[k][2] == t[2] and _is_id(toks[k]):
                    gen.append(toks[k][1]); k += 1
            targets.append({"tactic": tac, "target": w, "origin": origin, **({"generalizing": gen} if gen else {})})
        else:
            targets.append({"tactic": tac, "target": None, "origin": "an expression"})
    ref_tokens = int(row.get("proof_length") or 0)
    hb = None
    try:
        hb = int(ref_heartbeats) if ref_heartbeats is not None else None
    except (TypeError, ValueError):
        hb = None
    rate = round(hb / ref_tokens, 2) if hb and ref_tokens else None
    return {"name": row.get("name"), "theorem": me, "ref_tokens": ref_tokens, "ref_heartbeats": hb, "exchange_rate": rate,
            "toolchains": list(versions or []), "names": names, "recursive": recursive, "case_labels": labels, "targets": targets,
            "tactics": tactics, "combinator_count": n_comb}


def _ordinal(k: int) -> str:
    return f"{k}{'th' if 10 <= k % 100 <= 20 else {1: 'st', 2: 'nd', 3: 'rd'}.get(k % 10, 'th')}"


def reveal_turn(turns: int) -> int:
    """The turn index at which the reference is shown when nothing is banked yet: a third of the session's turns (at least 1)."""
    return max(1, math.ceil(int(turns) / REVEAL_FRACTION))


def render(f: dict, max_names: int = 80) -> str:
    """The facts sheet as the session reads it (names and numbers only)."""
    lines = ["FACTS FROM THE REFERENCE PROOF (computed by the harness from its text; names and numbers only, the proof itself is withheld):"]
    hb = f.get("ref_heartbeats")
    lines.append(f"- Reference proof: {f.get('ref_tokens')} tokens, {hb if hb is not None else '?'} heartbeats (score 33.33 = equal to the "
                 "reference on both; every token and every heartbeat below these numbers raises the score).")
    if f.get("exchange_rate"):
        lines.append(f"- Exchange rate on this row: 1 token = {f['exchange_rate']} heartbeats (saving one token is worth as much score as "
                     f"saving {f['exchange_rate']} heartbeats).")
    if f.get("toolchains"):
        lines.append(f"- Toolchains (every one must compile the proof unchanged): {', '.join(f['toolchains'])}.")
    nm = f.get("names") or []
    if nm:
        more = f" (+{len(nm) - max_names} more)" if len(nm) > max_names else ""
        lines.append(f"- Library / project names it refers to, in order of first use ({len(nm)}; names in the statement left out): "
                     + ", ".join(f"`{x}`" for x in nm[:max_names]) + more + ".")
    else:
        lines.append("- Library / project names it refers to: none beyond the statement's.")
    if f.get("recursive"):
        lines.append(f"- It calls the theorem itself (`{f.get('theorem')}`) on smaller arguments: a recursive proof.")
    tg = f.get("targets") or []
    if tg:
        seen: dict = {}
        for t in tg:
            if t.get("target"):
                k = f"`{t['tactic']}` on `{t['target']}` ({t['origin']})" + (f" generalizing {', '.join(t['generalizing'])}" if t.get("generalizing") else "")
            else:
                k = f"`{t['tactic']}` on {t['origin']}"
            seen[k] = seen.get(k, 0) + 1
        parts = [k + (f" x{v}" if v > 1 else "") for k, v in seen.items()]
        lines.append(f"- Case analysis / induction ({len(tg)}): " + "; ".join(parts[:12]) + (" …" if len(parts) > 12 else "") + ".")
    if f.get("case_labels"):
        lines.append("- Case labels it uses: " + ", ".join(f"`{x}`" for x in f["case_labels"]) + ".")
    tac = f.get("tactics") or {}
    if tac:
        lines.append("- Tactics it uses (name x count): " + ", ".join(f"`{k}` x{v}" for k, v in sorted(tac.items(), key=lambda kv: (-kv[1], kv[0])))
                     + (f"; `<;>` x{f['combinator_count']}" if f.get("combinator_count") else "") + ".")
    return "\n".join(lines)


                                                                                                                                        
                                                                                                                                          
PROOF_STORES = ("original.lean", "proofs.jsonl", "trajectories", "verified.jsonl")


def violation(command: str, row: dict, extra_paths=()) -> str | None:
    """A shell command that reads the row's own source (blind first session, counted not blocked): a reader (cat / grep / rg / sed / …)


"""
    c = command or ""
    if not _READERS.search(c):
        return None
    fp = (row.get("file_path") or "").strip()
    for p in [fp, Path(fp).name if fp else ""] + [str(x) for x in extra_paths if x] + list(PROOF_STORES):
        if p and p in c:
            return f"reads {p}"
    me = statement_name(row.get("statement") or "").split(".")[-1]
    full = row.get("name") or ""
    cands = set()
    for nme in {me, full.split(".")[-1]} - {""}:
        if len(nme) < 8 or re.fullmatch(r"[a-z]+", nme):
            parts = full.split(".")
            if len(parts) >= 2:
                cands.add(".".join(parts[-2:]))
        else:
            cands.add(nme)
    if "." in full:
        cands.add(full)
    for nme in sorted(cands, key=len, reverse=True):
        if re.search(rf"(?<![\w.]){re.escape(nme)}(?!\w)", c):                                                      
            return f"searches for {nme}"
    return None


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--rows", default=str(ROOT / "data/benchmark_warmup.jsonl"))
    ap.add_argument("--heartbeats", default=str(ROOT / "data/benchmark_heartbeats.jsonl"))
    ap.add_argument("--json", action="store_true")
    ap.add_argument("names", nargs="*")
    a = ap.parse_args(argv)
    rows = {json.loads(l)["name"]: json.loads(l) for l in open(a.rows) if l.strip()}
    hbs = {json.loads(l)["name"]: json.loads(l)["heartbeat"] for l in open(a.heartbeats) if l.strip()}
    for n in a.names or list(rows):
        r = rows[n]
        vs = [next(iter(d)) for d in r.get("version_info") or []]
        f = facts(r, hbs.get(n), vs)
        print(json.dumps(f, ensure_ascii=False) if a.json else f"== {n}\n{render(f)}\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
