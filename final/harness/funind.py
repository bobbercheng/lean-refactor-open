#!/usr/bin/env python3
"""Dialect pass, probe family `funind` (open run 3): deterministic `fun_induction` rewrites of an `induction` block, accept-gated by the end stage.




























"""
from __future__ import annotations

import hashlib, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scorer.forbidden import check_forbidden              
from scorer.tokenize import count_tokens, split_declaration              

FAMILY = "funind"
OPS = ("funind:using", "funind:swap", "funind:block")
MAX_CANDS = 12                                                                      
MAX_PER_OP = MAX_CANDS
MAX_FUNS = 4                                                                                                                     
MAX_CHECKS = 18                                                                                      
PROBE_K = 6                                  
PROBE_MAX_FILES = 3                              
CAP = 48                                                                                                                                   

KEYWORDS = {"fun", "λ", "if", "then", "else", "let", "have", "show", "from", "match", "with", "at", "by", "do", "in", "Type", "Prop", "Sort",
            "forall", "exists", "return", "using", "generalizing", "theorem", "lemma", "def", "where", "open", "true", "false", "True", "False"}
TYPE_ALIASES = {"ℕ": "Nat", "ℤ": "Int", "ℝ": "Real", "ℚ": "Rat", "ℂ": "Complex"}
OPEN, CLOSE = "([{⟨⦃", ")]}⟩⦄"


                                                                                                                                          
def _is_id_start(ch: str) -> bool:
    return ch.isalpha() and ch not in "λΠΣ" or ch == "_" or ch == "«"


def _is_id_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'.!?«»" or ch in "₀₁₂₃₄₅₆₇₈₉ᵢⱼₖₙₘ"


def lex(s: str) -> list[tuple[str, int, int]]:
    """[(token, start, end)]: identifiers (dotted), numbers, brackets, and runs of other symbols."""
    out, i, n = [], 0, len(s)
    while i < n:
        ch = s[i]
        if ch.isspace():
            i += 1; continue
        if s.startswith("--", i):
            j = s.find("\n", i); i = n if j < 0 else j; continue
        if s.startswith("/-", i):
            j = s.find("-/", i + 2); i = n if j < 0 else j + 2; continue
        if _is_id_start(ch):
            j = i + 1
            if ch == "«":
                j = s.find("»", i) + 1 or n
            while j < n and _is_id_char(s[j]):
                j += 1
            tok = s[i:j].rstrip(".")
            if not tok:
                tok = s[i]
            out.append((tok, i, i + len(tok))); i = i + len(tok); continue
        if ch.isdigit():
            j = i
            while j < n and (s[j].isdigit() or s[j] == "."):
                j += 1
            out.append((s[i:j], i, j)); i = j; continue
        if ch in OPEN or ch in CLOSE or ch in ",":
            out.append((ch, i, i + 1)); i += 1; continue
        j = i
        while j < n and not s[j].isspace() and not _is_id_start(s[j]) and not s[j].isdigit() and s[j] not in OPEN + CLOSE + ",":
            j += 1
        if j == i:
            j = i + 1
        out.append((s[i:j], i, j)); i = j
    return out


def _is_ident(t: str) -> bool:
    return bool(t) and _is_id_start(t[0]) and all(_is_id_char(c) or c == "»" for c in t[1:]) and t not in KEYWORDS


def binder_types(stmt: str) -> dict[str, str]:
    """name -> type text, from `(a b : T)`, `{a : T}`, `⦃a : T⦄`, `∀ a b : T,` binders of the statement."""
    out: dict[str, str] = {}
    i = 0
    while i < len(stmt):
        ch = stmt[i]
        if ch in "({⦃":
            depth, j = 0, i
            while j < len(stmt):
                if stmt[j] in OPEN: depth += 1
                elif stmt[j] in CLOSE:
                    depth -= 1
                    if depth == 0: break
                j += 1
            inner = stmt[i + 1:j]
            m = re.match(r"\s*([^\s:(){}\[\]][^:(){}\[\]]*?)\s*:\s*(.+)\Z", inner, re.DOTALL)
            if m and ":=" not in inner[:m.end(1) + 3]:
                names = m.group(1).split()
                if names and all(_is_ident(x) for x in names):
                    for x in names:
                        out.setdefault(x, m.group(2).strip())
            i += 1
            continue
        i += 1
    for m in re.finditer(r"∀\s+([^,:()]+?)\s*:\s*([^,]+),", stmt):
        for x in m.group(1).split():
            if _is_ident(x):
                out.setdefault(x, m.group(2).strip())
    return out


def type_head(t: str) -> str | None:
    t = t.strip()
    for k, v in TYPE_ALIASES.items():
        if t.startswith(k):
            return v
    m = re.match(r"@?([^\s()]+)", t)
    return m.group(1) if m and _is_ident(m.group(1)) else None


def applications(stmt: str) -> list[tuple[str, list[str], str]]:
    """[(head, [arg texts], args text)] for every identifier applied to >= 1 argument atom, nested ones included."""
    toks = lex(stmt)
    out, consumed = [], set()
    for k, (t, a, b) in enumerate(toks):
        if not _is_ident(t) or k in consumed:
            continue
        args, j = [], k + 1
        while j < len(toks):
            u, ua, ub = toks[j]
            if u in OPEN and u != "⦃":
                depth, e = 0, j
                while e < len(toks):
                    if toks[e][0] in OPEN: depth += 1
                    elif toks[e][0] in CLOSE:
                        depth -= 1
                        if depth == 0: break
                    e += 1
                if e >= len(toks): break
                args.append(stmt[ua:toks[e][2]]); j = e + 1; continue
            if _is_ident(u) or u[0].isdigit() or u == "_":
                args.append(u)
                if "." not in u:                                                                                             
                    consumed.add(j)
                j += 1; continue
            break
        if args:
            out.append((t, args, " ".join(args)))
    return out


                                                                                                                                         
IND_RE = re.compile(r"(?<![\w.'])(induction'?)\s+")


def _strip_comment(line: str) -> str:
    i = line.find("--")
    return line if i < 0 else line[:i]


def induction_sites(body: str) -> list[dict]:
    lines = body.split("\n")
    sites = []
    for i, line in enumerate(lines):
        code = _strip_comment(line)
        for m in IND_RE.finditer(code):
            if code[max(0, m.start() - 4):m.start()].endswith("fun_"):
                continue
            col = m.start()
            rest = code[m.end():]
            depth, end = 0, len(rest)                                                   
            for p, ch in enumerate(rest):
                if ch in OPEN: depth += 1
                elif ch in CLOSE: depth -= 1
                if depth == 0 and (rest.startswith("<;>", p) or ch == ";"):
                    end = p; break
            tac = rest[:end]
            mm = re.match(r"(?P<targets>.+?)(?:\s+using\s+(?P<using>[^\s]+))?(?:\s+generalizing\s+(?P<gen>.+?))?(?:\s+with\b(?P<with>.*))?\s*\Z",
                          tac, re.DOTALL)
            if not mm:
                continue
            targets = mm.group("targets").strip()
            t0 = targets.split(",")[0].strip()
            if ":" in t0 or not _is_ident(t0) or " " in t0:
                continue                                                                
                                                                                                                                    
                                                                                                                                      
                                                                                                         
            pre = code[:col].strip()
            line_ind = len(line) - len(line.lstrip(" "))
            focusing = bool(re.search(r"(?:^|\s)(?:·|\.|by|=>|focus)\s*$|=>", pre)) if pre else False
            seq_col = col if focusing else line_ind
            j = i
            for q in range(i + 1, len(lines)):
                s = lines[q]
                if not s.strip():
                    continue
                ind = len(s) - len(s.lstrip(" "))
                if ind >= seq_col and (ind > line_ind or not focusing or seq_col == line_ind):
                    j = q
                else:
                    break
            block = "\n".join(lines[i:j + 1])
            sites.append({"line": i, "end": j, "col": col, "kw": m.group(1), "var": t0, "targets": targets,
                          "using": mm.group("using"), "gen": (mm.group("gen") or "").split(), "with": mm.group("with"),
                          "tac_span": (m.start(), m.end() + len(tac.rstrip())), "block": block, "has_tail_on_line": end < len(rest)})
    return sites


def hint_names(block: str, extra: list[str]) -> list[str]:
    out: list[str] = []
    for m in re.finditer(r"\b(?:simp_all|simp|simpa|dsimp|grind|rw|rewrite|erw|simp_arith|norm_num|field_simp|unfold)\b[^\[\n]*?\[([^\]]*)\]", block):
        for it in m.group(1).split(","):
            it = re.sub(r"^\s*(?:←|<-|↓|=|-)\s*", "", it).strip()
            if it and " " not in it and _is_ident(it) and "." in it and it not in out:
                out.append(it)
    for m in re.finditer(r"\bunfold\s+([^\n]+)", block):
        for it in m.group(1).split():
            if _is_ident(it) and it not in out and it not in ("at",):
                out.append(it)
    for e in extra:
        if e not in out:
            out.append(e)
    return out[:6]


                                                                                                                                         
CLOSERS = [                                                                
    (1.0, "simp_all", "simp_all"),
    (1.2, "grind", "grind"),
    (1.5, "simp_all[F]", "simp_all [{F}]"),
    (1.7, "grind[F]", "grind [{F}]"),
    (2.0, "simp_all[hints]", "simp_all [{H}]"),
    (2.2, "grind[hints]", "grind [{H}]"),
    (3.0, "simp[F]<;>omega", "simp [{F}] <;> omega"),
    (3.2, "simp_all;try grind", "(simp_all; try grind)"),
    (3.5, "aesop", "aesop"),
]


def _split_args(text: str) -> list[str]:
    out, depth, cur = [], 0, ""
    for ch in text:
        if ch in OPEN: depth += 1
        elif ch in CLOSE: depth -= 1
        if ch == " " and depth == 0:
            if cur: out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def fun_targets(stmt: str, var: str, gen: list[str]) -> list[dict]:
    """Recursive-function candidates for an induction on `var`: [{"f", "args": [variants], "n"}] (unranked; the probe decides)."""
    btypes = binder_types(stmt)
    found: dict[str, dict] = {}
    for head, args, text in applications(stmt):
        if head in btypes or head == var or head.split(".")[0] in btypes or head.split(".")[0] == var:
            continue
        if var in args:
            e = found.setdefault(head, {"f": head, "args": [], "n": 0})
            e["n"] += 1
            if text not in e["args"]:
                e["args"].append(text)
    for t, a, b in lex(stmt):                     
        if t.startswith(var + ".") and t.count(".") == 1:
            th = type_head(btypes.get(var, "")) if var in btypes else None
            if th:
                f = f"{th}.{t.split('.', 1)[1]}"
                e = found.setdefault(f, {"f": f, "args": [], "n": 0, "dot": True})
                e["n"] += 1
                if var not in e["args"]:
                    e["args"].append(var)
    for e in found.values():                                                                                                        
        more = []
        for text in e["args"]:
            parts, changed = [], False
            for a in _split_args(text):
                if _is_ident(a) or a[0].isdigit() or a == "_":
                    parts.append(a); continue
                ids = [t for t, _, _ in lex(a) if _is_ident(t)]
                pick = next((x for x in ids if x in gen), None) or next((x for x in ids if x in btypes), None)
                parts.append(pick or a); changed |= bool(pick)
            if changed:
                v = " ".join(parts)
                if v not in e["args"] and v not in more:
                    more.append(v)
        e["args"] += more
    return list(found.values())


def head_body(decl: str, statement: str) -> tuple[str, str] | None:
    """(everything up to and including `:=`, the body) of a declaration whose statement is byte-identical to `statement`, else None."""
    d = decl.rstrip()
    b = split_declaration(d, statement)
    if b is None:
        return None
    return d[:len(d) - len(b)], b


def _mk(head, lines, site, newlines, a, b, kind, prio, F, args):
    new = lines[:a] + newlines + lines[b + 1:]
    first = newlines[0]                                                                                                              
    m = re.search(r"fun_induction\s.*?(?=\s<;>|\swith\b|\Z)", first)
    check, combo = None, (site["line"], kind)
    if m:
        cl = first[:m.end()]
        check = head + "\n".join(lines[:a] + [cl, " " * site["col"] + "all_goals sorry"] + lines[site["end"] + 1:])
        combo = (site["line"], m.group(0))
    return {"kind": kind, "prio": round(prio, 2), "f": F, "args": args, "site_line": site["line"], "decl": head + "\n".join(new),
            "combo": combo, "check_decl": check}


def generate(proof: str, statement: str, max_funs: int = MAX_FUNS) -> list[dict]:
    """Every candidate of `proof` (unprobed, deduplicated, statement-checked, forbidden-checked), best ranked first. Each carries
"""
    hb = head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    lines = body.split("\n")
    has_aesop = bool(re.search(r"\baesop\b", body))
    btypes = binder_types(statement)
    cands = []
    for s in induction_sites(body):
        funs = fun_targets(statement, s["var"], s["gen"])
        line = lines[s["line"]]
        a0, a1 = s["tac_span"]
        prefix = line[:s["col"]]
        Fu = s["using"][:-len(".induct")] if s["using"] and s["using"].endswith(".induct") else None
        if Fu and not any(f["f"] == Fu or f["f"].endswith("." + Fu) or Fu.endswith("." + f["f"]) for f in funs):
            newl = line[:a0] + f"fun_induction {Fu} {' '.join(t.strip() for t in s['targets'].split(','))}" + \
                (" generalizing " + " ".join(s["gen"]) if s["gen"] else "") + (" with" + s["with"] if s["with"] is not None else "") + line[a1:]
            cands.append(_mk(head, lines, s, [newl], s["line"], s["line"], "using", 0.2, Fu, s["targets"]))
        hints_all = hint_names(s["block"], [])
        for f in funs:
            f["hint_hits"] = sum(1 for h in hints_all if h == f["f"] or h.endswith("." + f["f"]) or f["f"].endswith("." + h)) + \
                s["block"].count(f["f"].split(".")[-1])
        funs.sort(key=lambda f: (-f["hint_hits"], -f["n"]))
        names_cases = re.search(r"(?m)^\s*(?:case|next)\b|^\s*\|", "\n".join(s["block"].split("\n")[1:])) or s["with"] is not None
        for fr, f in enumerate(funs[:max(1, int(max_funs))]):
            F = f["f"]
            hints = hint_names(s["block"], [F])
                                                                                                                                      
            lit = f["args"][0]
            compound = not all(_is_ident(x) or x[0].isdigit() for x in _split_args(lit))
            variants = (f["args"][1:2] + [lit]) if compound and len(f["args"]) > 1 else list(f["args"][:2])
            all_vars = all(_is_ident(x) and "." not in x for x in _split_args(lit))
            for ar, args in enumerate(variants):
                argvars = {t for t, _, _ in lex(args) if _is_ident(t)}
                argvars |= {t.split(".")[0] for t in argvars}                                                  
                for v in list(argvars):                                                                                        
                    argvars |= {t for t, _, _ in lex(btypes.get(v, "")) if _is_ident(t)}
                gen = [g for g in s["gen"] if g not in argvars]
                gtxt = (" generalizing " + " ".join(gen)) if gen else ""
                r = fr + ar                                                                                       
                fi = f"fun_induction {F} {args}{gtxt}"
                                                                                                                                 
                if Fu and (Fu == F or Fu.endswith("." + F) or F.endswith("." + Fu)):
                    newl = line[:a0] + f"fun_induction {Fu} {args}{gtxt}" + (" with" + s["with"] if s["with"] is not None else "") + line[a1:]
                    cands.append(_mk(head, lines, s, [newl], s["line"], s["line"], "using", 2.5 * r, F, args))
                               
                if not names_cases:
                    newl = line[:a0] + fi + line[a1:]
                    cands.append(_mk(head, lines, s, [newl], s["line"], s["line"], "swap", 0.5 + 2.5 * r, F, args))
                    if ar == 0 and all_vars:
                        newl = line[:a0] + f"fun_induction {F}{gtxt}" + line[a1:]
                        cands.append(_mk(head, lines, s, [newl], s["line"], s["line"], "swap", 2.6 + 2.5 * r, F, ""))
                                   
                for rank, lab, tpl in CLOSERS:
                    if "{H}" in tpl and len(hints) <= 1:
                        continue
                    if lab == "aesop" and not has_aesop:
                        continue
                    closer = tpl.replace("{F}", F).replace("{H}", ", ".join(hints))
                    cands.append(_mk(head, lines, s, [prefix + fi + " <;> " + closer], s["line"], s["end"], f"block:{lab}",
                                     rank + 2.5 * r, F, args))
                    if ar == 0 and all_vars and lab in ("simp_all", "grind"):
                        cands.append(_mk(head, lines, s, [prefix + f"fun_induction {F}{gtxt} <;> " + closer], s["line"], s["end"],
                                         f"block:{lab}", rank + 1.9 + 2.5 * r, F, ""))
    seen, out = set(), []
    for c in sorted(cands, key=lambda c: (c["prio"], c["site_line"])):
        d = c["decl"].rstrip()
        if d in seen or d == proof.rstrip():
            continue
        seen.add(d)
        b = split_declaration(d, statement)
        if b is None or check_forbidden(b):
            continue
        op = "funind:" + c["kind"].split(":")[0]
        note = f"{c['kind']} {c['f']} [{c['args']}]"
        out.append({"op": op, "decl": d + "\n", "note": note[:200], "tokens": count_tokens(b), "prio": c["prio"],
                    "combo": c["combo"], "check_decl": c["check_decl"]})
    return out


def check_valid(messages) -> bool:
    """A probe copy's verdict: it compiled (messages is a list, not None) and every error is a sorry one."""
    if messages is None:
        return False
    for m in messages:
        if m.get("severity") == "error" and "sorry" not in str(m.get("data") or ""):
            return False
    return True


def select(cands: list[dict], valid: set, cap: int = MAX_CANDS) -> list[dict]:
    """The candidates whose probe key is valid (a candidate without a check copy keeps its place), best ranked first, capped, then
"""
    kept = [c for c in cands if c.get("check_decl") is None or tuple(c["combo"]) in valid][:max(0, int(cap))]
    return sorted(kept, key=lambda c: c["tokens"])


def proof_key(proof: str) -> str:
    """sha256 of the stripped proof, 16 hex digits (harness/endstage.sha)."""
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def probe_hb_cap(heartbeats) -> int:
    """`maxHeartbeats` of a probe copy: the copy is the proof with one block cut to its first line + `all_goals sorry`."""
    try:
        h = max(0, int(heartbeats or 0))
    except (TypeError, ValueError):
        h = 0
    return max(2 * h + 1000, 5000)


def probe(proof: str, statement: str, compile_batch, *, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict:
    """The probe on `proof` (module docstring): {"funind_probe": candidates, "funind_probe_for": proof_key(proof)}, or {} when the proof

"""
    st = stats if stats is not None else {}
    for c in ("sites", "verified", "round2"):
        st.setdefault(c, 0)
    want = (ctx or {}).get("ops")
    if want and not any(str(o) in OPS or f"{FAMILY}:{o}" in OPS for o in want):
        return {}
    if not IND_RE.search(proof):
        return {}
    say = log or (lambda m: None)
    cands = generate(proof, statement)
    if want:
        cands = [c for c in cands if c["op"] in want or c["op"].split(":", 1)[1] in want]
    if not cands:
        return {}
    keys, texts = [], []
    for c in cands:
        k = tuple(c["combo"])
        if c.get("check_decl") is None or k in keys:
            continue
        if len(keys) >= MAX_CHECKS:
            break
        keys.append(k); texts.append(c["check_decl"])
    st["sites"] += len({k[0] for k in keys})
    got = list(compile_batch(texts) or []) if texts else []
    got += [None] * (len(texts) - len(got))
    valid = {k for k, msgs in zip(keys, got) if check_valid(msgs)}
    st["verified"] += len(valid)
    picked = select(cands, valid)
    say(f"funind probe: {len(cands)} candidate(s), {len(keys)} call(s) probed, {len(valid)} valid, {len(picked)} kept")
    out = [{k: c[k] for k in ("op", "decl", "note", "tokens")} for c in picked]
    return {"funind_probe": out, "funind_probe_for": proof_key(proof)} if out else {}


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = MAX_PER_OP, ctx: dict | None = None) -> list[dict]:
    """The probe's candidates for exactly this proof (ctx["funind_probe_for"] must match), in the probe's order, at most
"""
    c = ctx or {}
    if c.get("funind_probe_for") != proof_key(proof):
        return []
    out = [x for x in (c.get("funind_probe") or []) if isinstance(x, dict) and x.get("decl")]
    return out[:max(0, min(int(max_per_op), MAX_CANDS))]
