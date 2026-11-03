#!/usr/bin/env python3
"""Dialect pass, probe family `unhyg` (b98): under one `unhygienic`, naming sites lose their names and later uses take the names Lean gives (Lean is asked).















"""
from __future__ import annotations

import hashlib, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.dialect import blank, case_parts, extent, ident_char, indent, scope_end, uses              
from harness.tools.t4_nameless import parse_goals              
from scorer.tokenize import count_tokens, split_declaration              

FAMILY = "unhyg"
OP = "unhyg:rename"
OPS = (OP,)
MAX_PER_OP = 40
MAX_SITES = 12                                                                             
PROBE_K = 2                                                                                    
PROBE_MAX_FILES = 2                                                                                                            
SITE_WORDS = re.compile(r"\b(rename_i|case|next|intro)\b")
TRACE = "trace_state"
RENAME_RE = re.compile(r"^(\s*)rename_i\s+(.+?)\s*$")
SEQ_RENAME_RE = re.compile(r"^(\s*)(\S.*?)\s*<;>\s*rename_i\s+([^<;|]+?)\s*$")


def traces_at(messages, line: int) -> list:
    """Every goal display printed by a `trace_state` at declaration line `line` (a tactic run on several goals prints several)."""
    got = []
    for m in messages or []:
        ln = m.get("decl_line") if m.get("decl_line") is not None else (m.get("pos") or {}).get("line")
        if ln != line or m.get("severity") != "information":
            continue
        g = parse_goals(m.get("data"))
        if g:
            got.append(g)
            continue
                                                                                                                        
        segs, cur, after_goal = [], [], False
        for ln in str(m.get("data") or "").split("\n"):
            if after_goal and ln[:1] not in (" ", "\t"):
                segs.append(cur); cur = []; after_goal = False
            cur.append(ln)
            if ln.startswith("⊢"):
                after_goal = True
        if cur:
            segs.append(cur)
        parts = [parse_goals("\n".join(x)) for x in segs]
        if len(parts) > 1 and all(parts):
            got.extend(parts)
    return got


def has_top_unhyg(lines: list[str]) -> bool:
    if re.match(r"\s*by\s+unhygienic\s*$", lines[0]):
        return True
    first = next((l for l in lines[1:] if not blank(l)), "")
    return first.strip() == "unhygienic"


def with_unhyg(lines: list[str]) -> list[str] | None:
    if has_top_unhyg(lines):
        return list(lines)
    if lines[0].strip() == "by":
        return [lines[0].rstrip() + " unhygienic"] + lines[1:]
    return None


def rename_words(lines: list[str], mp: dict) -> list[str]:
    if not mp:
        return lines
    keys = sorted(mp, key=len, reverse=True)
    pat = re.compile("|".join(re.escape(k) for k in keys))
    out = []
    for l in lines:
        res, i = [], 0
        for m in pat.finditer(l):
            a, b = m.start(), m.end()
            before = l[a - 1] if a > 0 else " "
            after = l[b] if b < len(l) else " "
            if ident_char(before) or before == "." or ident_char(after):
                continue
            res.append(l[i:a]); res.append(mp[m.group(0)]); i = b
        res.append(l[i:])
        out.append("".join(res))
    return out


INTRO_NAMES_RE = re.compile(r"^(\s*)intro((?:\s+[^\s⟨⟩()\[\]{}:,]+){2,})\s*$")


def intro_form(lead: str, k: int) -> list[str]:
    """`k` nameless one-binder intros (under `unhygienic` each takes the binder's own name)."""
    return [lead + f"iterate {k} intro"] if k >= 3 else [lead + "intro"] * k


def sites_of(lines: list[str]) -> list[tuple]:
    out = []
    for i, l in enumerate(lines):
        m = SEQ_RENAME_RE.match(l)
        if m and extent(lines, i) == i + 1:
            out.append(("seqrename", i, m.group(3).split()))
            continue
        m = INTRO_NAMES_RE.match(l)
        if m and all(re.fullmatch(r"[^\W\d][\w'!?₀-₉]*", n) for n in m.group(2).split()):
            out.append(("intro", i, m.group(2).split()))
            continue
        m = RENAME_RE.match(l)
        if m and extent(lines, i) == i + 1:
            out.append(("rename", i, m.group(2).split()))
            continue
        cp = case_parts(lines, i)
        if cp and cp[3] and any(n != "_" for n in cp[3]):
            out.append(("case", i, cp[3]))
    return out


def case_block(lines, i, names_keep: bool, trace: bool):
    """The case header at i rewritten as a block: header (with or without names) + optional trace + the body at body indent."""
    d, kw, tag, names, inline, e = case_parts(lines, i)
    blk = lines[i + 1:e]
    nb = [l for l in blk if not blank(l)]
    bi = min((indent(l) for l in nb), default=d + 2)
    if inline.strip():
        col = lines[i].find(inline, lines[i].find("=>"))
        delta = col - bi if nb and min(indent(l) for l in nb) >= col else 0
        blk = [" " * max(bi, indent(l) - delta) + l.strip() if not blank(l) else l for l in blk]
        body = [" " * bi + inline.strip()] + blk
    else:
        body = blk
    hd = " " * d + kw + ((" " + tag) if tag else "") + ((" " + " ".join(names)) if names_keep and names else "") + " =>"
    return [hd] + ([" " * bi + TRACE] if trace else []) + body, e, len(body)


def generate(inc: str, statement: str, compile_batch, log=lambda d: None, max_sites: int = MAX_SITES, stats: dict | None = None) -> list[dict]:
    """The chain of site conversions (module docstring): every prefix of the chain that has fewer tokens than `inc` is one candidate.

"""
    st = stats if stats is not None else {}
    body0 = split_declaration(inc.rstrip(), statement)
    if body0 is None:
        return []
    head = inc.rstrip()[:len(inc.rstrip()) - len(body0)]
    orig = body0.split("\n")
    if with_unhyg(orig) is None:
        return []
    base_tok = count_tokens(body0)
    cur = with_unhyg(orig)
    off = len(cur) - len(orig)                                                      
    sites = sites_of(orig)[:max_sites]
    out, n_ok = [], 0
    acc = {}                                                                                                                            
    dl = lambda li: head.count("\n") + li + 1              
    shift = 0                                                                                                                     
    for kind, i, names in sites:
        ci = i + shift
        if kind == "intro":
            if not INTRO_NAMES_RE.match(cur[ci] if ci < len(cur) else ""):
                break
            lead = " " * indent(cur[ci]); form = intro_form(lead, len(names))
            O = orig[:i + 1] + [lead + TRACE] + orig[i + 1:]
            o_line = i + 1
            V = cur[:ci] + form + [lead + TRACE] + cur[ci + 1:]
            v_line = ci + len(form)
        elif kind == "seqrename":
            m = SEQ_RENAME_RE.match(cur[ci] if ci < len(cur) else "")
            if not m:
                break
            O = orig[:i] + [orig[i].rstrip() + " <;> " + TRACE] + orig[i + 1:]
            o_line = i
            V = cur[:ci] + [m.group(1) + m.group(2) + " <;> " + TRACE] + cur[ci + 1:]
            v_line = ci
        elif kind == "rename":
            if not RENAME_RE.match(cur[ci] if ci < len(cur) else ""):
                break
            O = orig[:i + 1] + [" " * indent(orig[i]) + TRACE] + orig[i + 1:]
            o_line = i + 1
            V = cur[:ci] + [" " * indent(cur[ci]) + TRACE] + cur[ci + 1:]
            v_line = ci
        else:
            if case_parts(cur, ci) is None:
                break
            ob, oe, _ = case_block(orig, i, True, True)
            O = orig[:i] + ob + orig[oe:]; o_line = i + 1
            vb, ve, _ = case_block(cur, ci, False, True)
            V = cur[:ci] + vb + cur[ve:]; v_line = ci + 1
        st["sites"] = st.get("sites", 0) + 1
        got = compile_batch([head + "\n".join(O), head + "\n".join(V)])
        got = list(got or []) + [None, None]
        tos = traces_at(got[0], dl(o_line)) if got[0] is not None else []
        tvs = traces_at(got[1], dl(v_line)) if got[1] is not None else []
        if not tos or len(tos) != len(tvs):
            dbg = [{"line": m.get("decl_line"), "sev": m.get("severity"), "data": str(m.get("data"))[:4000]}
                   for m in (got[0] or [])][:6]
            log({"probe": kind, "line": i, "fail": f"traces {len(tos)} / {len(tvs)}", "o_line": dl(o_line), "o_msgs": dbg,
                 "o_none": got[0] is None}); break
        mp = {}
        okay = True
        want = set(n for n in names if n != "_")
        for to, tv in zip(tos, tvs):                                                                                                     
            go, gv = to[0], tv[0]                                   
            if len(go["hyps"]) != len(gv["hyps"]):
                okay = False; break
            for (on, _), (vn, _) in zip(go["hyps"], gv["hyps"]):
                if on in want:
                    if "✝" in vn or not re.fullmatch(r"[^\W\d][\w'!?₀-₉]*", vn) or mp.get(on, vn) != vn:
                        okay = False; break
                    mp[on] = vn
                elif acc.get(on, on) != vn and "✝" not in on:
                    okay = False; break
            if not okay:
                break
        if not okay or not want <= set(mp):
            log({"probe": kind, "line": i, "fail": "align", "o": [h[0] for h in tos[0][0]["hyps"]][-8:],
                 "v": [h[0] for h in tvs[0][0]["hyps"]][-8:]}); break
        acc.update(mp)
        mp = {k: v for k, v in mp.items() if k != v}
        if kind == "intro":
            se = scope_end(cur, ci)
            want_all = set(names)
            for j in range(ci + 1, se):
                m2 = RENAME_RE.match(cur[j]); cp2 = case_parts(cur, j)
                again = set(m2.group(2).split()) if m2 else set(cp2[3]) if cp2 else set()
                if again & want_all:
                    se = j; break
            scope_text = "\n".join(cur[ci + 1:se])
            if any(uses(v, scope_text) and v not in mp for v in mp.values()):
                log({"probe": kind, "line": i, "skip": "capture", "map": mp})
                for k in list(mp):                                                                           
                    acc[k] = k
                continue
            form = intro_form(" " * indent(cur[ci]), len(names))
            cur = cur[:ci] + form + rename_words(cur[ci + 1:se], mp) + cur[se:]
            shift += len(form) - 1
        elif kind == "seqrename":
            se = scope_end(cur, ci)
            want_all = set(names)
            for j in range(ci + 1, se):
                m2 = RENAME_RE.match(cur[j]); cp2 = case_parts(cur, j)
                again = set(m2.group(2).split()) if m2 else set(cp2[3]) if cp2 else set()
                if again & want_all:
                    se = j; break
            m = SEQ_RENAME_RE.match(cur[ci])
            cur = cur[:ci] + [m.group(1) + m.group(2)] + rename_words(cur[ci + 1:se], mp) + cur[se:]
        elif kind == "rename":
            se = scope_end(cur, ci)
            want_all = set(names)
            for j in range(ci + 1, se):                                                                                  
                m2 = RENAME_RE.match(cur[j]); cp2 = case_parts(cur, j)
                again = set(m2.group(2).split()) if m2 else set(cp2[3]) if cp2 else set()
                if again & want_all:
                    se = j; break
            cur = cur[:ci] + rename_words(cur[ci + 1:se], mp) + cur[se:]
            shift -= 1
        else:
            vb, ve, nbody = case_block(cur, ci, False, False)
            vb = [vb[0]] + rename_words(vb[1:], mp)
            cur = cur[:ci] + vb + cur[ve:]
            shift += len(vb) - (ve - ci)
        n_ok += 1
        st["verified"] = st.get("verified", 0) + 1
        nb = "\n".join(cur).rstrip()
        t = count_tokens(nb)
        log({"probe": kind, "line": i, "map": mp, "tokens": t})
        if t < base_tok:
            out.append({"op": OP, "decl": head + nb + "\n", "note": f"{n_ok} site(s)", "tokens": t})
    return out


def proof_key(proof: str) -> str:
    """sha256 of the stripped proof, 16 hex digits (harness/endstage.sha)."""
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


def probe_hb_cap(heartbeats) -> int:
    """`maxHeartbeats` of a probe copy: the copy is the proof with one site rewritten and a trace, so twice the incumbent's + 1000."""
    try:
        h = max(0, int(heartbeats or 0))
    except (TypeError, ValueError):
        h = 0
    return 2 * h + 1000


def _short(d) -> str:
    if isinstance(d, dict):
        d = {k: v for k, v in d.items() if k not in ("o_msgs",)}
        return json.dumps(d, ensure_ascii=False)[:240]
    return str(d)[:240]


def probe(proof: str, statement: str, compile_batch, *, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict:
    """The chain on `proof` (module docstring): {"unhyg_probe": candidates, "unhyg_probe_for": proof_key(proof)}, or {} when the proof has
"""
    st = stats if stats is not None else {}
    for c in ("sites", "verified", "round2"):
        st.setdefault(c, 0)
    want = (ctx or {}).get("ops")
    if want and not any(str(o) in (OP, "rename") for o in want):
        return {}
    if not SITE_WORDS.search(proof):
        return {}
    say = log or (lambda m: None)
    got = generate(proof, statement, compile_batch, log=lambda d: say("unhyg probe: " + _short(d)), stats=st)
    return {"unhyg_probe": got, "unhyg_probe_for": proof_key(proof)} if got else {}


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = MAX_PER_OP, ctx: dict | None = None) -> list[dict]:
    """The probe's candidates for exactly this proof (ctx["unhyg_probe_for"] must match), fewest tokens first, at most max_per_op."""
    c = ctx or {}
    if c.get("unhyg_probe_for") != proof_key(proof):
        return []
    out = [x for x in (c.get("unhyg_probe") or []) if isinstance(x, dict) and x.get("decl")]
    return sorted(out, key=lambda x: x.get("tokens", 0))[:int(max_per_op)]
