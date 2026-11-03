#!/usr/bin/env python3
"""Dialect pass of the open package's end pipeline (b98): deterministic, model-free source-to-source rewrites of a proof, accept-gated by the end stage.


















































"""
from __future__ import annotations

import argparse, itertools, json, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scorer.tokenize import count_tokens, split_declaration              

FAMILY = "dialect"
MAX_CANDS = 400                                                           
MAX_PER_OP = 160                                                                    
MAX_COMBOS = 300                                                           
                                                                                                                                      
SECONDS = 600.0                                                                                                                  
ROW_MARGIN_S = 300.0                                                                  
COMPILES = 400                                                                       
PICK_COMPILES = 40                                                                                                               
PASSES = 4                                                        
T4_CAP = 120                                                           
UNHYG_CAP = 60                                                            
T4_PROBE_MAX_SITES = 32                                                                                                     
T4_PROBE_MAX_FILES = 8

BULLET_RE = re.compile(r"^(\s*)([·.])(\s+)(\S.*)$")
CASE_RE = re.compile(r"^(\s*)(case|next)\b([^=]*?)=>\s*(.*)$")
ARM_RE = re.compile(r"^(\s*)\|\s*([^=]*?)=>\s*(.*)$")
WITH_HEAD_RE = re.compile(r"^(\s*)((?:induction|cases|rcases|match)\b.*?)\s+with\s*$")
INTRO_RE = re.compile(r"^(\s*)(intro|intros)\s+([^\s].*)$")
RINTRO_RE = re.compile(r"^(\s*)rintro\s+(.*)$")
OBTAIN_RE = re.compile(r"^(\s*)obtain\s+(⟨[^⟨⟩]*⟩)\s*:=\s*(.*)$")


def ident_char(ch: str) -> bool:
    return ch.isalnum() or ch in "_'!?"


def uses(name: str, text: str) -> bool:
    """`name` occurs in `text` as an identifier (a whole word, also as the head of `name.field`), not as `x.name`."""
    if not name or name == "_":
        return False
    i = 0
    while True:
        j = text.find(name, i)
        if j < 0:
            return False
        before = text[j - 1] if j > 0 else " "
        after = text[j + len(name)] if j + len(name) < len(text) else " "
        if not ident_char(before) and before != "." and not ident_char(after):
            return True
        i = j + 1


def indent(line: str) -> int:
    return len(line) - len(line.lstrip(" "))


def blank(line: str) -> bool:
    return not line.strip()


def extent(lines: list[str], i: int) -> int:
    """End (exclusive) of the lines belonging to line i: the following lines indented deeper than it (blank lines inside kept)."""
    d = indent(lines[i]); j = i + 1; last = i + 1
    while j < len(lines):
        if blank(lines[j]):
            j += 1; continue
        if indent(lines[j]) > d:
            j += 1; last = j
        else:
            break
    return last


def scope_end(lines: list[str], i: int) -> int:
    """End of the block that line i belongs to: the following lines at its indent or deeper."""
    d = indent(lines[i]); j = i + 1; last = i + 1
    while j < len(lines):
        if blank(lines[j]):
            j += 1; continue
        if indent(lines[j]) >= d:
            j += 1; last = j
        else:
            break
    return last


def dedent(lines: list[str], delta: int, floor: int) -> list[str]:
    out = []
    for l in lines:
        if blank(l):
            out.append(l); continue
        k = indent(l)
        out.append(" " * max(floor, k - delta) + l.lstrip(" "))
    return out


def is_tactic_block(body: str) -> bool:
    return bool(re.match(r"\s*by\s*(\n|$)", body)) or bool(re.match(r"\s*by\s", body))


                                                                                                                         
def r_dollar(lines):
    out = []
    sites = [(i, m.start()) for i, l in enumerate(lines) for m in re.finditer(r"<\|(?!>)", l)]
    for i, p in sites:
        nl = list(lines); nl[i] = nl[i][:p] + "$" + nl[i][p + 2:]
        out.append((f"L{i}", nl))
    if len(sites) > 1:
        out.append(("all", [re.sub(r"<\|(?!>)", "$", l) for l in lines]))
    return out


def drop_bullet(lines, i):
    m = BULLET_RE.match(lines[i])
    if not m:
        return None
    d = len(m.group(1)); content_col = d + 1 + len(m.group(3))
    e = extent(lines, i)
    nl = lines[:i] + [" " * d + m.group(4)] + dedent(lines[i + 1:e], content_col - d, d + 1) + lines[e:]
    return nl


def bullets(lines):
    return [i for i, l in enumerate(lines) if BULLET_RE.match(l)]


def r_bulletdrop(lines):
    out = []
    bs = bullets(lines)
    for i in bs:
        nl = drop_bullet(lines, i)
        if nl:
            out.append((f"L{i}", nl))
                                                                                   
    groups = sibling_groups(lines, bs)
    for g in groups:
        if len(g) > 1:
            nl = list(lines)
            for i in reversed(g):
                nl = drop_bullet(nl, i) or nl
            out.append((f"group{g[0]}", nl))
    if len(bs) > 1:
        nl = list(lines)
        while True:
            b = bullets(nl)
            if not b:
                break
            nl = drop_bullet(nl, b[0])
        out.append(("all", nl))
    return out


def sibling_groups(lines, idxs):
    """Consecutive siblings among idxs: same indent, nothing at that indent or shallower in between except other members."""
    groups, cur = [], []
    for i in idxs:
        if cur:
            p = cur[-1]
            e = extent(lines, p)
            nxt = next((j for j in range(e, len(lines)) if not blank(lines[j])), None)
            if nxt == i and indent(lines[i]) == indent(lines[p]):
                cur.append(i); continue
            groups.append(cur)
        cur = [i]
    if cur:
        groups.append(cur)
    return groups


def case_parts(lines, i):
    """(indent, kw, binder names, inline tactic, block lines range end) for a `case`/`next` header line."""
    m = CASE_RE.match(lines[i])
    if not m:
        return None
    d, kw, args, inline = len(m.group(1)), m.group(2), m.group(3).split(), m.group(4)
    if kw == "case":
        if not args:
            return None
        if "|" in args:                                                                  
            tag, names = " ".join(args), []
        else:
            tag, names = args[0], args[1:]
    else:
        tag, names = None, args
    return d, kw, tag, names, inline, extent(lines, i)


def drop_case(lines, i):
    p = case_parts(lines, i)
    if not p:
        return None
    d, kw, tag, names, inline, e = p
    body = lines[i + 1:e]
    text = inline + "\n" + "\n".join(body)
    if any(uses(n, text) for n in names if n != "_"):
        return None
    nb = [l for l in body if not blank(l)]
    head = []
    if inline.strip():
        head = [" " * d + inline]
        delta = (min(indent(l) for l in nb) - d) if nb else 0
                                                                                                     
        col = len(lines[i]) - len(lines[i].lstrip(" ")) + lines[i].lstrip(" ").find(inline)
        delta = col - d if nb and min(indent(l) for l in nb) >= col else delta
    else:
        delta = (min(indent(l) for l in nb) - d) if nb else 0
    return lines[:i] + head + dedent(body, delta, d) + lines[e:]


def r_casedrop(lines):
    out = []
    idx = [i for i, l in enumerate(lines) if CASE_RE.match(l)]
    for i in idx:
        nl = drop_case(lines, i)
        if nl:
            out.append((f"L{i}", nl))
    if len(idx) > 1:
        nl = list(lines)
        for i in reversed(idx):
            r = drop_case(nl, i)
            nl = r or nl
        if nl != lines:
            out.append(("all", nl))
    return out


def body_text(lines, i, inline, e, d):
    """A header's body normalised: the inline tactic + block lines, dedented to a common base."""
    blk = [l for l in lines[i + 1:e] if not blank(l)]
    base = min((indent(l) for l in blk), default=0)
    return ([inline.strip()] if inline.strip() else []) + [" " * (indent(l) - base) + l.strip() for l in blk]


def r_caseor(lines):
    out = []
    idx = [i for i, l in enumerate(lines) if CASE_RE.match(l) and l.strip().startswith("case ")]
    for g in sibling_groups(lines, idx):
        if len(g) < 2:
            continue
        parts = {i: case_parts(lines, i) for i in g}
        if any(p is None for p in parts.values()):
            continue
                                                 
        run = [g[0]]
        def flush(run):
            if len(run) < 2:
                return
            d, kw, tag, names, inline, e = parts[run[0]]
            tags = " | ".join(parts[j][2] + ("".join(" " + n for n in parts[j][3])) for j in run)
            first = run[0]; last_e = parts[run[-1]][5]
            nl = lines[:first] + [lines[first].replace(lines[first].lstrip(" "), "", 1) + f"case {tags} =>" + (" " + inline if inline.strip() else "")] \
                + lines[first + 1:parts[first][5]] + lines[last_e:]
            out.append((f"L{first}x{len(run)}", nl))
        for i in g[1:]:
            a, b = parts[run[-1]], parts[i]
            if body_text(lines, run[-1], a[4], a[5], a[0]) == body_text(lines, i, b[4], b[5], b[0]) and a[3] == b[3]:
                run.append(i)
            else:
                flush(run); run = [i]
        flush(run)
    return out


def bullet_body(lines, i):
    m = BULLET_RE.match(lines[i]); e = extent(lines, i)
    d = len(m.group(1)); col = d + 1 + len(m.group(3))
    rest = [l for l in lines[i + 1:e] if not blank(l)]
    return [m.group(4).strip()] + [" " * max(0, indent(l) - col) + l.strip() for l in rest], e


def render_block(head: str, body: list[str], d: int) -> list[str]:
    """`head B` for a one-line body, else `head` + the body indented under it."""
    if len(body) == 1:
        return [" " * d + head + " " + body[0]]
    if head == "·":
        return [" " * d + "· " + body[0]] + [" " * (d + 2) + l for l in body[1:]]
    return [" " * d + head] + [" " * (d + 2) + l for l in body]


def block_end_after(lines, i):
    """True when nothing at line i's indent or shallower (of its block) follows line i's extent within the parent block."""
    e = extent(lines, i)
    nxt = next((j for j in range(e, len(lines)) if not blank(lines[j])), None)
    return nxt is None or indent(lines[nxt]) < indent(lines[i])


def r_samebullets(lines):
    out = []
    for g in sibling_groups(lines, bullets(lines)):
        if len(g) < 2:
            continue
        bodies = [bullet_body(lines, i) for i in g]
                                          
        k = 0
        while k < len(g):
            m = k
            while m + 1 < len(g) and bodies[m + 1][0] == bodies[k][0]:
                m += 1
            if m > k:
                run = g[k:m + 1]; body = bodies[k][0]; d = indent(lines[run[0]]); e = bodies[m][1]
                for comb in ("all_goals", "any_goals"):
                    out.append((f"{comb}L{run[0]}x{len(run)}", lines[:run[0]] + render_block(comb, body, d) + lines[e:]))
                                                                                                                            
                if k == 0 and m == len(g) - 1 and block_end_after(lines, run[-1]) and len(body) == 1:
                    t = run[0] - 1
                    while t >= 0 and blank(lines[t]):
                        t -= 1
                    if t >= 0 and indent(lines[t]) == d and extent(lines, t) == t + 1 and not BULLET_RE.match(lines[t]) \
                            and not CASE_RE.match(lines[t]) and not lines[t].rstrip().endswith(("=>", "with", "by", ":=")):
                        out.append((f"seqL{run[0]}", lines[:t] + [lines[t].rstrip() + " <;> " + body[0]] + lines[e:]))
            k = m + 1
    return out


def r_firstmerge(lines):
    out = []
    for g in sibling_groups(lines, bullets(lines)):
        if len(g) < 2 or not block_end_after(lines, g[-1]):
            continue
        bodies = [bullet_body(lines, i) for i in g]
        if any(len(b[0]) != 1 for b in bodies):
            continue
        uniq = list(dict.fromkeys(b[0][0] for b in bodies))
        if len(uniq) == len(g) and len(g) < 3:
            continue
        d = indent(lines[g[0]]); e = bodies[-1][1]
        alts = " | ".join(uniq)
        out.append((f"allL{g[0]}", lines[:g[0]] + [" " * d + f"all_goals first | {alts}"] + lines[e:]))
        t = g[0] - 1
        while t >= 0 and blank(lines[t]):
            t -= 1
        if t >= 0 and indent(lines[t]) == d and extent(lines, t) == t + 1 and not BULLET_RE.match(lines[t]) \
                and not CASE_RE.match(lines[t]) and not lines[t].rstrip().endswith(("=>", "with", "by", ":=")):
            out.append((f"seqL{g[0]}", lines[:t] + [lines[t].rstrip() + f" <;> first | {alts}"] + lines[e:]))
    return out


def r_altmerge(lines):
    out = []
    for i, l in enumerate(lines):
        m = WITH_HEAD_RE.match(l)
        if not m or m.group(2).startswith("match"):
            continue
        d = len(m.group(1)); e = i + 1
        while e < len(lines) and (blank(lines[e]) or indent(lines[e]) > d or (indent(lines[e]) == d and ARM_RE.match(lines[e]))):
            e += 1
        while e > i + 1 and blank(lines[e - 1]):
            e -= 1
        arms = [j for j in range(i + 1, e) if ARM_RE.match(lines[j]) and indent(lines[j]) <= d + 2]
        if len(arms) < 2:
            continue
        ad = indent(lines[arms[0]])
        if any(indent(lines[j]) != ad for j in arms):
            continue
        parsed = []
        okay = True
        for k, j in enumerate(arms):
            am = ARM_RE.match(lines[j]); ae = arms[k + 1] if k + 1 < len(arms) else e
            names = am.group(2).split()[1:]
            blk = [x for x in lines[j + 1:ae] if not blank(x)]
            base = min((indent(x) for x in blk), default=0)
            body = ([am.group(3).strip()] if am.group(3).strip() else []) + [" " * (indent(x) - base) + x.strip() for x in blk]
            if not body or any(uses(n, "\n".join(body)) for n in names if n != "_"):
                okay = False; break
            parsed.append(body)
        if not okay:
            continue
        head = m.group(2)
        if all(b == parsed[0] for b in parsed):
            b = parsed[0]
            if len(b) == 1:
                out.append((f"seqL{i}", lines[:i] + [" " * d + head + " <;> " + b[0]] + lines[e:]))
            out.append((f"allL{i}", lines[:i] + [" " * d + head] + render_block("all_goals", b, d) + lines[e:]))
        nl = lines[:i] + [" " * d + head]
        for b in parsed:
            nl += render_block("·", b, d)
        out.append((f"bulletsL{i}", nl + lines[e:]))
    return out


def r_samelines(lines):
    out = []
    i = 0
    while i < len(lines):
        if blank(lines[i]) or extent(lines, i) != i + 1:
            i += 1; continue
        j = i
        while j + 1 < len(lines) and lines[j + 1] == lines[i] and extent(lines, j + 1) == j + 2:
            j += 1
        if j > i and block_end_after(lines, j):
            d = indent(lines[i])
            out.append((f"L{i}x{j - i + 1}", lines[:i] + [" " * d + "all_goals " + lines[i].strip()] + lines[j + 1:]))
        i = j + 1
    return out


def names_in_pattern(p: str) -> list[str]:
    return [t for t in re.findall(r"[^\s⟨⟩,|()@\-]+", p) if t not in ("rfl", "_", "-")]


def r_intros(lines):
    out = []
    for i, l in enumerate(lines):
        m = INTRO_RE.match(l)
        if m and m.group(2) == "intro":
            names = m.group(3).split()
            if len(names) >= 2 and all(re.fullmatch(r"[^\s⟨⟩()]+", n) for n in names):
                rest = "\n".join(lines[i + 1:scope_end(lines, i)])
                if not any(uses(n, rest) for n in names):
                    out.append((f"L{i}", lines[:i] + [" " * len(m.group(1)) + "intros"] + lines[i + 1:]))
        m = RINTRO_RE.match(l)
        if m:
            pats = m.group(2)
            rest = "\n".join(lines[i + 1:scope_end(lines, i)])
            flat = re.findall(r"⟨[^⟨⟩]*⟩", pats)
            new = pats
            for f in flat:
                ns = names_in_pattern(f[1:-1])
                if "rfl" not in f and not any(uses(n, rest) for n in ns) and f != "⟨⟩":
                    new = new.replace(f, "⟨⟩", 1)
            if new != pats:
                out.append((f"rL{i}", lines[:i] + [" " * len(m.group(1)) + "rintro " + new] + lines[i + 1:]))
        m = OBTAIN_RE.match(l)
        if m:
            ns = names_in_pattern(m.group(2)[1:-1])
            rest = "\n".join(lines[i + 1:scope_end(lines, i)])
            if "rfl" not in m.group(2) and not any(uses(n, rest) for n in ns) and m.group(2) != "⟨⟩":
                out.append((f"oL{i}", lines[:i] + [" " * len(m.group(1)) + "obtain ⟨⟩ := " + m.group(3)] + lines[i + 1:]))
    if len(out) > 1:
                                                                
        nl = list(lines)
        for _, c in out:
            for k, (a, b) in enumerate(zip(lines, c)):
                if a != b:
                    nl[k] = b
        out.append(("all", nl))
    return out


def r_introobtain(lines):
    out = []
    for i in range(len(lines) - 1):
        m = INTRO_RE.match(lines[i])
        if not m or m.group(2) != "intro":
            continue
        names = m.group(3).split()
        j = i + 1
        while j < len(lines) and blank(lines[j]):
            j += 1
        if j >= len(lines) or indent(lines[j]) != indent(lines[i]):
            continue
        om = re.match(r"^(\s*)obtain\s+(\S.*?)\s*:=\s*(\S+)\s*$", lines[j])
        if not om or om.group(3) != names[-1]:
            continue
        h = names[-1]
        rest = "\n".join(lines[j + 1:scope_end(lines, i)])
        if uses(h, rest):
            continue
        new = " " * indent(lines[i]) + "rintro " + " ".join(names[:-1] + [om.group(2)])
        out.append((f"L{i}", lines[:i] + [new] + lines[j + 1:]))
    return out


def r_ctor(lines):
    out = []
    for i, l in enumerate(lines):
        m = re.match(r"^(\s*)refine\s+⟨\s*\?_\s*(?:,\s*\?_\s*)+⟩\s*$", l)
        if m:
            k = l.count("?_")
            if k == 2:
                out.append((f"L{i}", lines[:i] + [m.group(1) + "constructor"] + lines[i + 1:]))
            out.append((f"rL{i}", lines[:i] + [m.group(1) + "repeat' constructor"] + lines[i + 1:]))
    i = 0
    while i < len(lines):
        if lines[i].strip() == "constructor":
            j = i
            while j + 1 < len(lines) and lines[j + 1] == lines[i]:
                j += 1
            if j - i + 1 >= 3:
                out.append((f"runL{i}", lines[:i] + [" " * indent(lines[i]) + "repeat' constructor"] + lines[j + 1:]))
            i = j + 1
        else:
            i += 1
    return out


def r_rwmerge(lines):
    out = []
    rw = re.compile(r"^(\s*)(rw|rewrite|simp only|rwa)\s*\[(.*)\]\s*(at\s+.*)?$")
    for i in range(len(lines) - 1):
        a = rw.match(lines[i]); b = rw.match(lines[i + 1])
        if not a or not b or a.group(1) != b.group(1) or (a.group(4) or "") != (b.group(4) or ""):
            continue
        if a.group(2) != b.group(2) and not (a.group(2) in ("rw", "rewrite") and b.group(2) in ("rw", "rwa", "rewrite")):
            continue
        if "[" in a.group(3) or "[" in b.group(3):
            continue
        kw = b.group(2) if a.group(2) != "simp only" else "simp only"
        new = f"{a.group(1)}{kw} [{a.group(3)}, {b.group(3)}]" + (f" {a.group(4)}" if a.group(4) else "")
        out.append((f"L{i}", lines[:i] + [new] + lines[i + 2:]))
    return out


def r_ascription(lines):
    out = []
    for i, l in enumerate(lines):
        m = re.match(r"^(\s*)(have|haveI)\s+([^\s:]+)\s*:\s*(.+?)\s*:=\s*(\S.*)$", l)
        if m and not m.group(5).startswith("by") and "⟨" not in m.group(5)[:1]:
            out.append((f"hL{i}", lines[:i] + [f"{m.group(1)}{m.group(2)} {m.group(3)} := {m.group(5)}"] + lines[i + 1:]))
        if re.match(r"^\s*show\s+[^\n]*$", l) and " from " not in l and extent(lines, i) == i + 1:
            out.append((f"sL{i}", lines[:i] + lines[i + 1:]))
        m = re.match(r"^(\s*)(.*?)\bshow\s+.+?\s+from\s+(.*)$", l)
        if m:
            out.append((f"fL{i}", lines[:i] + [m.group(1) + m.group(2) + m.group(3)] + lines[i + 1:]))
    return out


def r_iterate(lines):
    out = []
    i = 0
    while i < len(lines):
        if blank(lines[i]) or extent(lines, i) != i + 1 or BULLET_RE.match(lines[i]) or CASE_RE.match(lines[i]):
            i += 1; continue
        j = i
        while j + 1 < len(lines) and lines[j + 1] == lines[i] and extent(lines, j + 1) == j + 2:
            j += 1
        k = j - i + 1
        if k >= 2 and (k - 1) * count_tokens(lines[i]) > 2:
            d = indent(lines[i])
            out.append((f"L{i}x{k}", lines[:i] + [" " * d + f"iterate {k} " + lines[i].strip()] + lines[j + 1:]))
        i = j + 1
    return out


def r_funext(lines):
    out = []
    for i, l in enumerate(lines):
        m = re.match(r"^(\s*)refine\s+funext\s+(?:λ|fun)\s*([^\s=]+)\s*(?:=>|↦)\s*\?_\s*$", l)
        if m:
            out.append((f"L{i}", lines[:i] + [m.group(1) + "funext " + m.group(2)] + lines[i + 1:]))
    return out


LIST_HEAD_RE = re.compile(r"\b(grind|simp|simp_all|simp_rw|simpa|dsimp|norm_num|field_simp|aesop|linarith|nlinarith|positivity|omega|gcongr|bound)"
                          r"(\s+only)?(\s*(?:\+\w+\s*)*)\s*\[")


def _list_items(text: str, start: int):
    """Top-level items of the bracket list opening at text[start] == '[': [(a, b)] spans, and the closing index."""
    depth, items, a = 0, [], start + 1
    for k in range(start, len(text)):
        ch = text[k]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
            if depth == 0:
                items.append((a, k)); return items, k
        elif ch == "," and depth == 1:
            items.append((a, k)); a = k + 1
    return None, None


def r_listdrop(lines):
    """One item of a closer's lemma list dropped; the whole list dropped; `only` dropped."""
    out = []
    for i, l in enumerate(lines):
        for m in LIST_HEAD_RE.finditer(l):
            st = m.end() - 1
            items, close = _list_items(l, st)
            if items is None:
                continue
            for k, (a, b) in enumerate(items):
                if len(items) == 1:
                    continue
                if k < len(items) - 1:
                    nl_ = l[:a] + l[items[k + 1][0]:]
                else:
                    nl_ = l[:items[k - 1][1]] + l[b:]
                nl_ = re.sub(r"\[\s+", "[", nl_)
                out.append((f"L{i}i{k}", lines[:i] + [nl_] + lines[i + 1:]))
            out.append((f"L{i}all", lines[:i] + [(l[:st].rstrip() + l[close + 1:]).rstrip()] + lines[i + 1:]))
            if m.group(2):
                out.append((f"L{i}only", lines[:i] + [l[:m.start(2)] + l[m.end(2):]] + lines[i + 1:]))
    return out


def r_firstdrop(lines):
    """One alternative of a `first` dropped (a single remaining one replaces the `first`)."""
    out = []
    for i, l in enumerate(lines):
                                      
        m = re.match(r"^(\s*)(.*?\bfirst)\s*\|(.*)$", l)
        if m and "|" in m.group(3) and "(" not in m.group(3):
            alts = [x.strip() for x in m.group(3).split("|")]
            if all(alts):
                for k in range(len(alts)):
                    rest = alts[:k] + alts[k + 1:]
                    new = (m.group(1) + m.group(2) + " | " + " | ".join(rest)) if len(rest) > 1 else \
                        (m.group(1) + m.group(2)[:-len("first")].rstrip() + (" " if m.group(2)[:-len("first")].strip() else "") + rest[0])
                    out.append((f"L{i}a{k}", lines[:i] + [new.rstrip()] + lines[i + 1:]))
                                                                              
        if l.strip() == "first" or l.rstrip().endswith(" first"):
            d = indent(l); alts = []; j = i + 1
            while j < len(lines) and re.match(r"^\s*\|", lines[j]) and indent(lines[j]) >= d:
                e = extent(lines, j); alts.append((j, e)); j = e
            if len(alts) >= 2:
                for k, (a, b) in enumerate(alts):
                    rest = [x for x in alts if x != (a, b)]
                    if len(rest) == 1:
                        ra, rb = rest[0]
                        alt_lines = [re.sub(r"^(\s*)\|\s*", r"\1", lines[ra])] + lines[ra + 1:rb]
                        head = l.rstrip()[:-len("first")].rstrip()
                        if head.strip():
                            new = [head + " " + alt_lines[0].strip()] + alt_lines[1:]
                        else:
                            new = [" " * d + alt_lines[0].strip()] + dedent(alt_lines[1:], indent(alt_lines[0]) - d, d)
                        out.append((f"L{i}a{k}", lines[:i] + new + lines[j:]))
                    else:
                        out.append((f"L{i}a{k}", lines[:a] + lines[b:]))
    return out


                                                                                                      
                                                                                                                                        
                                                                                                          
OPENERS, CLOSERS = "([{⟨", ")]}⟩"
CALC_KW_RE = re.compile(r"(?<![\w'.])calc(?![\w'!?])")
CALC_REL = ("=", "≤", "<", "≥", ">", "≠", "↔", "⊆", "⊂", "∣", "≃", "≈", "→")
TOP_REL = (" = ", " ≤ ", " < ", " ≥ ", " > ", " ≠ ", " ↔ ", " ⊆ ", " ∣ ")
TOP_CONN = (" ∧ ", " ∨ ", " → ", " ↔ ")
HOLE_SITE_RE = re.compile(r"^(\s*)(have|haveI|let|letI|obtain)(?![\w'!?])")
SHOW_SITE_RE = re.compile(r"^(\s*)(show|change)\s+\S")
LET_SITE_RE = re.compile(r"^(\s*)let\s+([^\s:=(){}\[\]⟨⟩,]+)\s*(:=|:)")
REW_HEAD_RE = re.compile(r"(?<![\w'.])(rw|rwa|rewrite|erw)\s*\[")
HOLE_CAP_SITE, HOLE_CAP = 12, 60


def _top_find(text: str, start: int, pred) -> int:
    """First index k >= start at bracket depth 0 (relative to start) where pred(text, k) holds, else -1."""
    d = 0
    for k in range(start, len(text)):
        ch = text[k]
        if ch in OPENERS:
            d += 1
        elif ch in CLOSERS:
            d -= 1
            if d < 0:
                return -1
        elif d == 0 and pred(text, k):
            return k
    return -1


def _top_assign(text: str, start: int = 0) -> int:
    return _top_find(text, start, lambda t, k: t.startswith(":=", k))


def _top_colon(text: str, start: int = 0) -> int:
    return _top_find(text, start, lambda t, k: t[k] == ":" and t[k + 1:k + 2] not in (":", "=") and t[k - 1:k] != ":")


def _match_close(text: str, p: int) -> int:
    """Index of the closer matching the opener at text[p], or -1."""
    d = 0
    for k in range(p, len(text)):
        if text[k] in OPENERS:
            d += 1
        elif text[k] in CLOSERS:
            d -= 1
            if d == 0:
                return k
    return -1


def _balance(text: str) -> int:
    return sum(1 for c in text if c in OPENERS) - sum(1 for c in text if c in CLOSERS)


def _is_step(line: str) -> bool:
    s = line.lstrip(" ")
    return s.startswith("_") and (len(s) == 1 or not ident_char(s[1]))


def _ident_positions(name: str, text: str) -> list[int]:
    """Start offsets of `name` as a whole identifier in text (also as the head of `name.field`; not as `x.name`)."""
    out, i = [], 0
    while True:
        j = text.find(name, i)
        if j < 0:
            return out
        before = text[j - 1] if j > 0 else " "
        after = text[j + len(name)] if j + len(name) < len(text) else " "
        if not ident_char(before) and before != "." and not ident_char(after):
            out.append(j)
        i = j + 1


def _calc_sites(lines):
    """Each `calc <head>` with `_ R rhs := proof` steps on the following lines (one column, deeper than the calc line)."""
    out = []
    for i, l in enumerate(lines):
        m = CALC_KW_RE.search(l)
        if not m or not l[m.end():].strip():
            continue
        E = extent(lines, i)
        while E > i + 1 and blank(lines[E - 1]):
            E -= 1
        region = range(i + 1, E)
        starts = [j for j in region if not blank(lines[j]) and _is_step(lines[j])]
        if not starts:
            continue
        sd = min(indent(lines[j]) for j in starts)
        steps = [j for j in starts if indent(lines[j]) == sd]
        if any(not blank(lines[j]) and indent(lines[j]) <= sd and j not in steps for j in region):
            continue
        head = "\n".join([l[m.end():]] + lines[i + 1:steps[0]])
        bal = _balance(l[m.end():] + "\n" + "\n".join(lines[i + 1:E]))
        tail = ""
        if bal < 0:
            last = lines[E - 1].rstrip()
            tail = last[len(last) + bal:]
            if len(tail) != -bal or any(c not in CLOSERS for c in tail):
                continue
        texts = []
        for k, s in enumerate(steps):
            e = steps[k + 1] if k + 1 < len(steps) else E
            t = "\n".join(lines[s:e]).rstrip()
            if k == len(steps) - 1 and tail:
                t = t[:len(t) - len(tail)].rstrip()
            a = _top_assign(t)
            if a < 0:
                break
            mm = re.match(r"\s*_\s*(\S+)", t[:a])
            rel = mm.group(1) if mm and mm.group(1) in CALC_REL else None
            texts.append({"text": t, "a": a, "rel_end": mm.end() if rel else None,
                          "rhs": t[mm.end():a].strip() if rel else None, "proof": t[a + 2:]})
        if len(texts) != len(steps):
            continue
        out.append({"i": i, "E": E, "kw_end": m.end(), "prefix": l[:m.start()], "head": head,
                    "head_is_term": _top_assign(head) < 0, "steps": texts, "tail": tail})
    return out


def _step_hole(st) -> str | None:
    if st["rel_end"] is None or st["rhs"] in ("_", ""):
        return None
    t = st["text"]
    return t[:st["rel_end"]] + " _ :=" + st["proof"]


def _render_calc(lines, c, head=None, steps=None, after=None):
    """lines with calc c rewritten: a new head (drops the head's continuation lines), new step texts, lines placed after the steps."""
    i = c["i"]; l = lines[i]
    first = lines[i][:c["kw_end"]] + (" " + head if head is not None else l[c["kw_end"]:])
    n_head = len(c["head"].split("\n"))
    region = [first] + ([] if head is not None else lines[i + 1:i + n_head])
    for t in (steps if steps is not None else [s["text"] for s in c["steps"]]):
        region += t.split("\n")
    region += after or []
    if c["tail"]:
        k = max(j for j, x in enumerate(region) if not blank(x))
        region[k] = region[k].rstrip() + c["tail"]
    return lines[:i] + region + lines[c["E"]:]


def _moved_proof(c, st, d: int) -> list[str] | None:
    """The proof of step st as tactic lines at indent d (a `by` block, or `exact <term>`)."""
    p = st["proof"]
    if p.lstrip().startswith("by") and (len(p.lstrip()) == 2 or not ident_char(p.lstrip()[2])):
        rest = p.lstrip()[2:]
        first, *more = rest.split("\n")
        more = [x for x in more if not blank(x)]
        if first.strip() and more:
            return None
        if first.strip():
            return [" " * d + first.strip()]
        if not more:
            return None
        base = min(indent(x) for x in more)
        return [" " * (d + indent(x) - base) + x.strip() for x in more]
    tl = p.split("\n")
    if not tl[0].strip():
        tl = tl[1:]
    tl = [x for x in tl if not blank(x)]
    if not tl:
        return None
    cont = tl[1:]
    base = min((indent(x) for x in cont), default=d + 4)
    return [" " * d + "exact " + tl[0].strip()] + [" " * (d + 4 + indent(x) - base) + x.strip() for x in cont]


def _calc_is_tactic(lines, c) -> bool:
    i = c["i"]
    if c["prefix"].strip():
        return False
    p = i - 1
    while p >= 0 and blank(lines[p]):
        p -= 1
    if p < 0:
        return False
    prev = lines[p].rstrip()
    if re.search(r"(?<![\w'])by$", prev):
        return True
    q = p
    while q >= 0 and (blank(lines[q]) or indent(lines[q]) > indent(lines[i])):
        q -= 1
    return q >= 0 and indent(lines[q]) == indent(lines[i]) and not prev.endswith((":=", "(", "$", "<|", "=>", ",", "·"))


def _calc_holes(lines, c):
    """Every hole edit of calc c at once: head -> `_`, middle term-proved steps' rhs -> `_`, the last step's rhs -> `_`."""
    sts = [s["text"] for s in c["steps"]]
    for k, st in enumerate(c["steps"]):
        is_last = k == len(c["steps"]) - 1
        if is_last or not st["proof"].lstrip().startswith("by"):
            h = _step_hole(st)
            if h:
                sts[k] = h
    head = "_" if c["head_is_term"] and c["head"].strip() != "_" else None
    return _render_calc(lines, c, head=head, steps=sts)


def r_calctail(lines):
    """(i) the last calc step's rhs -> `_`; (ii) the last step dropped and its proof run after the calc on the goal the calc tactic leaves

"""
    out = []
    for c in _calc_sites(lines):
        sts = [s["text"] for s in c["steps"]]
        n = len(sts); i = c["i"]
        h = _step_hole(c["steps"][-1])
        if h:
            out.append((f"L{i}last", _render_calc(lines, c, steps=sts[:-1] + [h])))
        if _calc_is_tactic(lines, c):
            mv = _moved_proof(c, c["steps"][-1], indent(lines[i]))
            if mv:
                if n >= 2:
                    out.append((f"L{i}drop", _render_calc(lines, c, steps=sts[:-1], after=mv)))
                elif c["head_is_term"]:
                    if c["tail"]:
                        mv[-1] = mv[-1].rstrip() + c["tail"]
                    out.append((f"L{i}only", lines[:i] + mv + lines[c["E"]:]))
        mids = []
        for k, st in enumerate(c["steps"][:-1]):
            if not st["proof"].lstrip().startswith("by"):
                hk = _step_hole(st)
                if hk:
                    mids.append(k)
                    out.append((f"L{i}mid{k}", _render_calc(lines, c, steps=sts[:k] + [hk] + sts[k + 1:])))
        if len(mids) > 1:
            s2 = list(sts)
            for k in mids:
                s2[k] = _step_hole(c["steps"][k])
            out.append((f"L{i}mids", _render_calc(lines, c, steps=s2)))
        if c["head_is_term"] and c["head"].strip() != "_":
            out.append((f"L{i}head", _render_calc(lines, c, head="_")))
        nl = _calc_holes(lines, c)
        if nl != lines and all(nl != x for _, x in out):
            out.append((f"L{i}holes", nl))
    sites = _calc_sites(lines)
    if sites:
        cur = list(lines)
        for idx in sorted((c["i"] for c in sites), reverse=True):
            c = next((x for x in _calc_sites(cur) if x["i"] == idx), None)
            if c is not None:
                cur = _calc_holes(cur, c)
        if cur != lines:
            out.append(("all", cur))
    return out


def _hole_spans(T: str, rel_only: bool) -> list[tuple[int, int]]:
    """Subterm spans of the type text T: bracket groups (not notation brackets glued to a symbol), the two sides of a single top-level
"""
    spans = []
    body0 = 0
    if T.lstrip()[:1] in ("∀", "∃"):
        k = _top_find(T, 0, lambda t, k: t[k] == ",")
        if k < 0:
            return []
        body0 = k + 1
    body = T[body0:]
    rels = [(k, r) for r in TOP_REL for k in [_top_find(body, 0, lambda t, k, r=r: t.startswith(r, k))] if k >= 0]
    conns = [r for r in TOP_CONN for k in [_top_find(body, 0, lambda t, k, r=r: t.startswith(r, k))] if k >= 0]
    if len(rels) == 1 and not [c for c in conns if c != rels[0][1]]:
        k, r = rels[0]
        for a, b in ((0, k), (k + len(r), len(body))):
            seg = body[a:b]
            a2 = a + len(seg) - len(seg.lstrip()); b2 = b - (len(seg) - len(seg.rstrip()))
            if b2 > a2:
                spans.append((body0 + a2, body0 + b2))
    if not rel_only:
        for p, ch in enumerate(T):
            if ch not in OPENERS:
                continue
            before = T[p - 1] if p > 0 else " "
            if not (before.isspace() or before in OPENERS or before == "$"):
                continue
            q = _match_close(T, p)
            if q < 0:
                continue
            after = T[q + 1] if q + 1 < len(T) else " "
            if after == "." or ident_char(after):
                continue
            spans.append((p, q + 1))
        k = _top_find(body, 0, lambda t, k: (t.startswith("fun", k) or t.startswith("λ", k)) and (k == 0 or not ident_char(t[k - 1]))
                      and not ident_char(t[k + (3 if t.startswith("fun", k) else 1):k + 4][:1] or " "))
        if k >= 0:
            spans.append((body0 + k, len(T.rstrip())))
    out = []
    for a, b in dict.fromkeys(spans):
        if count_tokens(T[a:b]) >= 2 and T[a:b].strip() not in ("_", T.strip()):
            out.append((a, b))
    return out


def _hole_sites(lines):
    """(line, site end, type start, type end, rel_only) for typed have / let / obtain (type between the top-level `:` and `:=`) and
"""
    out = []
    for i, l in enumerate(lines):
        e = extent(lines, i)
        text = "\n".join(lines[i:e])
        m = HOLE_SITE_RE.match(l)
        if m:
            c = _top_colon(text, m.end())
            a = _top_assign(text, m.end())
            if c < 0 or a < 0 or a < c:
                continue
            proof = text[a + 2:].lstrip()
            by = proof.startswith("by") and (len(proof) == 2 or not ident_char(proof[2]))
            out.append((i, e, c + 1, a, by))
            continue
        m = SHOW_SITE_RE.match(l)
        if m and not re.search(r"(?<![\w'])from(?![\w'])", text) and _top_assign(text) < 0 and _balance(text) == 0:
            out.append((i, e, m.end() - 1, len(text), False))
    return out


def r_typehole(lines):
    """A subterm of a have / let / obtain type -> `_` (each, largest first, then pairs; a `by`-proved one: only the two sides of its
"""
    cands = []
    for i, e, ta, tb, rel_only in _hole_sites(lines):
        text = "\n".join(lines[i:e])
        T = text[ta:tb]
        spans = sorted(_hole_spans(T, rel_only), key=lambda s: -count_tokens(T[s[0]:s[1]]))
        edits = [[s] for s in spans[:HOLE_CAP_SITE]]
        top = spans[:5] if not rel_only else []
        for x, y in itertools.combinations(top, 2):
            if x[1] <= y[0] or y[1] <= x[0]:
                edits.append(sorted([x, y]))
        site = []
        for ed in edits:
            nt = T
            for a, b in sorted(ed, reverse=True):
                nt = nt[:a] + "_" + nt[b:]
            new_text = text[:ta] + nt + text[tb:]
            site.append((count_tokens(new_text) - count_tokens(text), f"L{i}h{len(site)}", lines[:i] + new_text.split("\n") + lines[e:]))
        cands += sorted(site, key=lambda x: x[0])[:HOLE_CAP_SITE]
    cands.sort(key=lambda x: x[0])
    return [(note, nl) for _, note, nl in cands[:HOLE_CAP]]


def _list_spans(text: str):
    """(head kind, items) for every bracket list of a closer / rewriter in text: kind "rw" or "simp"; items [(a, b)]."""
    out = []
    for rx, kind in ((REW_HEAD_RE, "rw"), (LIST_HEAD_RE, "simp")):
        for m in rx.finditer(text):
            st = m.end() - 1
            items, close = _list_items(text, st)
            if items is not None:
                out.append((kind, st, close, items))
    return out


def _inline_let(lines, i):
    """lines with the `let x := v` at line i deleted and x replaced by `(v)` at its (at most two) uses; a lemma-list item `x` / `← x` is
"""
    m = LET_SITE_RE.match(lines[i])
    if not m:
        return None
    name = m.group(2)
    e = extent(lines, i)
    text = "\n".join(lines[i:e])
    a = _top_assign(text, m.start(2) + len(name))
    if a < 0:
        return None
    ty = None
    if m.group(3) == ":":
        c = _top_colon(text, m.start(2) + len(name))
        if c < 0 or c > a:
            return None
        ty = text[c + 1:a].strip()
    val = text[a + 2:].strip()
    if not val:
        return None
    if "\n" in val:
        vl = val.split("\n")
        if any(re.search(r"(?<![\w'])by$", x.rstrip()) for x in vl) or any(x.lstrip().startswith(("·", "|", "<;>")) for x in vl[1:]):
            return None
        val = " ".join(x.strip() for x in vl)
    atomic = count_tokens(val) == 1 or (val[0] in OPENERS and _match_close(val, 0) == len(val) - 1)
    rep = f"({val} : {ty})" if ty else (val if atomic else f"({val})")
    se = scope_end(lines, i)
    rest = "\n".join(lines[e:se])
    if re.search(r"(?<![\w'.])(?:let|have|haveI|set|letI)\s+" + re.escape(name) + r"(?![\w'!?])", rest):
        return None
    pos = _ident_positions(name, rest)
    drops, subs = [], []
    lists = _list_spans(rest)
    for p in pos:
        hit = None
        for kind, st, close, items in lists:
            for k, (ia, ib) in enumerate(items):
                if ia <= p < ib and rest[ia:ib].strip().replace("← ", "←") in (name, "←" + name):
                    hit = (kind, st, close, items, k)
        if hit:
            drops.append(hit)
        else:
            subs.append(p)
    if len(subs) > 2:
        return None
    edits = []
    for kind, st, close, items, k in drops:
        if len(items) == 1:
            if kind == "rw":
                return None
            edits.append((st, close + 1, ""))
        elif k < len(items) - 1:
            edits.append((items[k][0], items[k + 1][0], ""))
        else:
            edits.append((items[k - 1][1], items[k][1], ""))
    edits += [(p, p + len(name), rep) for p in subs]
    edits.sort(reverse=True)
    for (a1, b1, _), (a2, b2, _) in zip(edits, edits[1:]):
        if b2 > a1:
            return None
    new = rest
    for a1, b1, r in edits:
        new = new[:a1] + r + new[b1:]
    new_lines = [x.rstrip() if x.rstrip() != x and x.strip() else x for x in new.split("\n")] if rest else []
    new_lines = [re.sub(r"\[\s+", "[", x) for x in new_lines]
    return lines[:i] + new_lines + lines[se:]


def r_letinline(lines):
    """`let x := v` (no parameters) used at most twice in its scope: the let deleted and `(v)` (with its type: `(v : T)`) written at the
"""
    out = []
    for i, l in enumerate(lines):
        nl = _inline_let(lines, i)
        if nl is not None:
            out.append((f"L{i}", nl))
    cur, base = list(lines), count_tokens("\n".join(lines))
    for _ in range(20):
        best = None
        for i in range(len(cur)):
            nl = _inline_let(cur, i)
            if nl is not None:
                t = count_tokens("\n".join(nl))
                if t < base and (best is None or t < best[0]):
                    best = (t, nl)
        if best is None:
            break
        base, cur = best
    if cur != lines and all(cur != x for _, x in out):
        out.append(("all", cur))
    return out


RULES = [("dollar", r_dollar), ("iterate", r_iterate), ("funext", r_funext), ("bulletdrop", r_bulletdrop), ("casedrop", r_casedrop), ("caseor", r_caseor),
         ("samebullets", r_samebullets), ("firstmerge", r_firstmerge), ("altmerge", r_altmerge), ("samelines", r_samelines),
         ("intros", r_intros), ("introobtain", r_introobtain), ("ctor", r_ctor), ("rwmerge", r_rwmerge), ("ascription", r_ascription), ("listdrop", r_listdrop), ("firstdrop", r_firstdrop),
         ("calctail", r_calctail), ("typehole", r_typehole), ("letinline", r_letinline)]
COMBO_SKIP = {"typehole"}                                                                                


def _best_all(rule_fn, lines):
    """The rule's widest edit (its "all" variant, else its single edit saving the most tokens)."""
    res = rule_fn(lines)
    if not res:
        return None
    for note, nl in res:
        if note == "all":
            return nl
    return min(res, key=lambda r: count_tokens("\n".join(r[1])))[1]


def rule_candidates(proof: str, statement: str, max_cands: int = MAX_CANDS, rules=None) -> list[dict]:
    """Every rule's candidates (single sites, all-sites edits, then combinations of the all-sites edits), fewest tokens first: only

"""
    body = split_declaration(proof.rstrip(), statement)
    if body is None:
        return []
    head = proof.rstrip()[:len(proof.rstrip()) - len(body)]
    lines = body.split("\n")
    base_tok = count_tokens(body)
    seen = {body.rstrip()}
    out = []

    def add(op, note, nl):
        nb = "\n".join(nl).rstrip()
        if nb in seen:
            return
        seen.add(nb)
        if re.match(r"[ \t]*\n", nb):                                                  
            return
        t = count_tokens(nb)
        if t >= base_tok:
            return
        out.append({"op": f"dialect:{op}", "decl": head + nb + "\n", "note": note, "tokens": t})

    alls = {}
    for name, fn in RULES:
        if rules is not None and name not in rules:
            continue
        try:
            res = fn(lines)
        except Exception as e:                                                                        
            res = []
        for note, nl in res:
            add(name, note, nl)
        try:
            a = _best_all(fn, lines)
        except Exception:                
            a = None
        if a is not None and a != lines and name not in COMBO_SKIP:
            alls[name] = fn
                                                                                                      
    names = list(alls)
    combos = [c for k in (2, 3) for c in itertools.combinations(names, k)] + ([tuple(names)] if len(names) > 3 else [])
    combos = combos[:MAX_COMBOS]                                                                       
    for c in combos:
        cur = lines
        for n in c:
            try:
                nxt = _best_all(alls[n], cur)
            except Exception:                
                nxt = None
            if nxt is not None:
                cur = nxt
        if cur != lines and (rules is None or "combo" in rules):
            add("combo", "+".join(c), cur)
    out.sort(key=lambda c: c["tokens"])
    return out[:max_cands]




                                                                                                
OPS = tuple(f"{FAMILY}:{name}" for name, _ in RULES) + (f"{FAMILY}:combo",)


def _wanted(ctx: dict | None) -> set | None:
    """ctx["ops"] (an allow-list of op names, with or without the family prefix) as a set of full op names; None: every op."""
    want = (ctx or {}).get("ops")
    if not want:
        return None
    return {o if str(o).startswith(FAMILY + ":") else f"{FAMILY}:{o}" for o in want}


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = MAX_PER_OP, ctx: dict | None = None,
               max_cands: int = MAX_CANDS) -> list[dict]:
    """The family's candidates on `proof` (pure: no compile, no I/O): rule_candidates restricted to ctx["ops"], at most max_per_op per op,
"""
    want = _wanted(ctx)
    rules = None if want is None else {o.split(":", 1)[1] for o in want}
    out, per = [], {}
    for c in rule_candidates(proof, statement, max_cands=max_cands, rules=rules):
        if want is not None and c["op"] not in want:
            continue
        if per.get(c["op"], 0) >= int(max_per_op):
            continue
        per[c["op"]] = per.get(c["op"], 0) + 1
        out.append(c)
    return out


                                                                                                                         
def register(t4: bool = True):
    """Register the families in this process's harness.endstage (FAMILIES, PROBE_FAMILIES, CODE_FILES) and, with t4, widen T4's probe for
"""
    from harness import endstage as ES
    ES.FAMILIES.setdefault(FAMILY, {"module": "harness.dialect", "tier": 0})
    ES.FAMILIES.setdefault("unhyg", {"module": "harness.dialect_unhyg", "tier": 1})
    if "unhyg" not in ES.PROBE_FAMILIES:
        ES.PROBE_FAMILIES = tuple(ES.PROBE_FAMILIES) + ("unhyg",)
    for f in ("harness/dialect.py", "harness/dialect_unhyg.py"):
        if f not in ES.CODE_FILES:
            ES.CODE_FILES = tuple(ES.CODE_FILES) + (f,)
    if t4:
        from harness.tools import t4_nameless as T4
        T4.PROBE_MAX_SITES = max(int(T4.PROBE_MAX_SITES), T4_PROBE_MAX_SITES)
        T4.PROBE_MAX_FILES = max(int(T4.PROBE_MAX_FILES), T4_PROBE_MAX_FILES)
    return ES


def families(t4: bool = True, unhyg: bool = True) -> list[str]:
    return [FAMILY] + (["t4"] if t4 else []) + (["unhyg"] if unhyg else [])


def build_parser() -> argparse.ArgumentParser:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--run-dir", required=True, help="the end stage's run directory: rows/<k>.json ({problem}), finals.json (the proof per row)")
    ap.add_argument("--rows", required=True, help="rows JSONL")
    ap.add_argument("--heartbeats", required=True, help="their reference heartbeats JSONL")
    ap.add_argument("--out", required=True, help="output directory (the end stage's report.jsonl, finals.json, meter.json, end_config.json)")
    ap.add_argument("--problems", nargs="*", help="restrict to these rows")
    ap.add_argument("--jobs", type=int, default=1, help="rows at once")
    ap.add_argument("--anon", action="store_true", help="log rows as row#k")
    ap.add_argument("--scratch", help="compile-slot directory (harness/endstage.py --scratch)")
    ap.add_argument("--resume-anyway", action="store_true")
    ap.add_argument("--seconds", type=float, default=SECONDS, help="the tool phase's wall budget per row")
    ap.add_argument("--compiles", type=int, default=COMPILES, help="the tool phase's compile budget per row")
    ap.add_argument("--passes", type=int, default=PASSES, help="greedy passes while the incumbent changes")
    ap.add_argument("--t4", choices=("on", "off"), default="on", help="T4 (harness/tools/t4_nameless.py) after the rules, with a wider probe")
    ap.add_argument("--unhyg", choices=("on", "off"), default="on", help="the unhyg family (harness/dialect_unhyg.py) after T4")
    ap.add_argument("--accept-config", help="rc2: a frozen end-stage config (e.g. the open package's end_config_open.json) whose \"accept\" "
                                            "block (hb_eps / min_gain / screen_hb / screen_frac) the pass runs under: the method is then "
                                            "handed to harness/endstage.py as --config <out>/dialect_config.json (the end stage applies "
                                            "and records the block); default: the end stage's built-in constants")
    ap.add_argument("--ops", dest="family_ops", action="append", default=[], metavar="FAMILY=OP[,OP..]",
                    help="rc2: an op allow-list for one of the pass's families (repeatable; harness/endstage.py --ops), e.g. "
                         "t4=intro,rcases,all (the open frozen config's T4 keep set)")
    return ap


def ops_specs(specs) -> dict:
    """{family: [op, ..]} from --ops items "FAMILY=OP[,OP..]" (given order, duplicates dropped; the end stage validates the names)."""
    out: dict = {}
    for spec in specs or ():
        name, eq, ops = str(spec).partition("=")
        if not eq or not name.strip():
            raise ValueError(f"--ops: want FAMILY=OP[,OP..], got {spec!r}")
        L = out.setdefault(name.strip(), [])
        for o in ops.split(","):
            if o.strip() and o.strip() not in L:
                L.append(o.strip())
    return out


def accept_block(path) -> dict:
    """The "accept" block of a frozen end-stage config, validated by harness/open_config.parse (ValueError naming the key); a file
"""
    from harness import open_config as OC
    cfg = json.loads(Path(path).read_text())
    if not isinstance(cfg, dict) or not isinstance(cfg.get("accept"), dict) or not cfg["accept"]:
        raise ValueError(f"--accept-config {path}: no \"accept\" block")
    return OC.parse({"accept": cfg["accept"]}, path)["accept"]


def endstage_config(a) -> dict:
    """The pass's method as an end-stage config (harness/endstage.load_config keys): what endstage_argv's method flags say (families,

"""
    fams = families(a.t4 == "on", a.unhyg == "on")
    cfg = {"name": "dialect-pass", "description": "harness/dialect.py: the dialect pass's method under a frozen config's accept block (rc2)",
           "families": fams, "sweep": False, "crossover": False, "k": 0,
           "budgets": {"sweep": {"compiles": PICK_COMPILES, "seconds": float(a.seconds)},
                       "tools": {"compiles": int(a.compiles), "seconds": float(a.seconds)}, "passes": int(a.passes)}}
    caps = {f: n for f, n in (("t4", T4_CAP), ("unhyg", UNHYG_CAP)) if f in fams}
    if caps:
        cfg["caps"] = caps
    ops = {f: o for f, o in ops_specs(getattr(a, "family_ops", None)).items() if f in fams}
    if ops:
        cfg["ops"] = ops
    cfg["accept"] = accept_block(a.accept_config)
    cfg["_accept_from"] = str(a.accept_config)
    return cfg


def endstage_argv(a, config=None) -> list[str]:
    """The harness/endstage.py command line of the pass: the run's own flags as given, the method fixed here (as flags; with `config`,
"""
    fams = families(a.t4 == "on", a.unhyg == "on")
    argv = ["--run-dir", str(a.run_dir), "--rows", str(a.rows), "--heartbeats", str(a.heartbeats), "--out", str(a.out),
            "--jobs", str(int(a.jobs))]
    if config is not None:
        argv += ["--config", str(config)]
    else:
        argv += ["--tools", ",".join(fams), "--no-sweep", "--no-crossover", "--k", "0",
                 "--max-compiles", str(PICK_COMPILES), "--max-seconds", str(float(a.seconds)),
                 "--tools-max-compiles", str(int(a.compiles)), "--tools-max-seconds", str(float(a.seconds)), "--passes", str(int(a.passes))]
        caps = [f"{f}={n}" for f, n in (("t4", T4_CAP), ("unhyg", UNHYG_CAP)) if f in fams]
        if caps:
            argv += ["--family-cap", ",".join(caps)]
        for f, ops in ops_specs(getattr(a, "family_ops", None)).items():
            if f in fams:
                argv += ["--ops", f"{f}={','.join(ops)}"]
    if a.problems:
        argv += ["--problems", *a.problems]
    if a.anon:
        argv.append("--anon")
    if a.scratch:
        argv += ["--scratch", str(a.scratch)]
    if a.resume_anyway:
        argv.append("--resume-anyway")
    return argv


def main(argv=None) -> int:
    ap = build_parser()
    a = ap.parse_args(argv)
    ES = register(t4=a.t4 == "on")
    if not a.accept_config:
        return ES.main(endstage_argv(a))
    try:                                                                                                             
        cfg = endstage_config(a)
    except (OSError, ValueError) as e:
        ap.error(str(e))
    out = Path(a.out); out.mkdir(parents=True, exist_ok=True)
    p = out / "dialect_config.json"
    p.write_text(json.dumps(cfg, indent=1, ensure_ascii=False))
    return ES.main(endstage_argv(a, config=p))


if __name__ == "__main__":
    raise SystemExit(main())
