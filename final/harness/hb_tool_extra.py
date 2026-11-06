"""Additional syntax-only experiments, kept separate for measured ablation."""
from __future__ import annotations

import re

import harness.hb_tool_candidates as HC
from harness.hb_tool_candidates import Candidate, IDENT, _simp_call
from harness.hb_rewrite import _first_by, _tac_pos, _in_conv, _skip_ws, _line_end
from harness.normalize import _mask, _pairs


def extra_candidates(body: str) -> list[Candidate]:
    """Return local elimination and elaboration candidates, without compiling."""
    mask = _mask(body)
    pairs = _pairs(body, mask)
    fb = _first_by(body, mask)
    if fb < 0:
        return []
    out = []
    for m in re.finditer(r"(?m)^[ \t]*(have)(?:[ \t]+(" + IDENT + r"))?[ \t]*:=[ \t]*", body):
        start = m.start(1)
        if not _tac_pos(body, mask, start, fb):
            continue
        p = m.end()
        if p < len(body) and body[p] == "(" and p in pairs:
            end = pairs[p] + 1
            expr = body[p + 1:end - 1]
        else:
            atom = re.match(IDENT + r"(?:\." + IDENT + r")*?" + r"(?=\.choose_spec\b)", body[p:])
            if not atom:
                continue
            end = p + atom.end()
            expr = body[p:end]
        chain = re.match(r"(?:\.choose_spec\b)+", body[end:])
        if not chain:
            continue
        stop = end + chain.end()
        if body[stop:_line_end(body, stop)].strip():
            continue
        depth = chain.group().count(".choose_spec")
        if depth > 4 or any(mask[start:stop]):
            continue
        name = m.group(2) or "this"
        pattern = ", ".join(["_"] * depth + [name])
        out.append(Candidate("choose_producer", ((start, stop - start, f"obtain ⟨{pattern}⟩ := {expr}"),),
                             "eliminate existential projections while introducing the fact", 0))

    for m in re.finditer(r"(?<![\w.'?!])congr[ \t]+1(?=[ \t]*(?:\n|$))", body):
        if _tac_pos(body, mask, m.start(), fb) and not _in_conv(body, mask, m.start()):
            out.append(Candidate("congr_arg", ((m.start(), len(m.group()), "apply congrArg _"),),
                                 "use the expected equality to infer a common function", 3))

    for m in re.finditer(r"(?<![\w.'?!])by[ \t]+simp(?![\w'?!])(?=[ \t]*(?:\n|$|[)\]}]))", body):
        if not any(mask[m.start():m.end()]):
            out.append(Candidate("vacuous_function", ((m.start(), m.end() - m.start(), "nofun"),),
                                 "elaborate a vacuous function without simplifier search", 4))

    for tac in re.finditer(r"(?<![\w.'?!])(simp|simpa|simp_all)(?![\w'?!])", body):
        if not _tac_pos(body, mask, tac.start(), fb) or _in_conv(body, mask, tac.start()):
            continue
        cfgs, _, lb, _ = _simp_call(body, pairs, tac)
        configs = " ".join(body[a:b] for a, b in cfgs)
        if lb is not None and re.search(r"\bdisch\s*:=", configs) and re.search(r"\bonly\s*$", body[tac.end():lb]):
            inner = body[lb + 1:pairs[lb]].strip()
            if not re.search(r"(?:^|,)\s*\*\s*(?:,|$)", inner):
                out.append(Candidate("simp_context", ((pairs[lb], 0, ", *" if inner else "*"),),
                                     "offer local evidence to conditional simplification", 1))
        for cstart, cend in cfgs:
            m = re.fullmatch(r"\(\s*disch\s*:=\s*(fun_prop)\s*\)", body[cstart:cend])
            if not m or any(mask[cstart:cend]):
                continue
            a, b = cstart + m.start(1), cstart + m.end(1)
            out.append(Candidate("discharge_first", ((a, b - a, "first | assumption | fun_prop"),),
                                 "check local evidence before property automation", 5))
            out.append(Candidate("discharge_assumption", ((a, b - a, "assumption"),),
                                 "discharge rewrite side conditions from local evidence", 6))

    for m in re.finditer(r"(?<![\w.'?!])cases(?![\w'?!])", body):
        if _tac_pos(body, mask, m.start(), fb) and not _in_conv(body, mask, m.start()):
            out.append(Candidate("elimination_rcases", ((m.start(), len(m.group()), "rcases"),),
                                 "compare recursive elimination elaboration", 4))

    for m in re.finditer(r"(?<![\w.'?!])dsimp(?![\w'?!])", body):
        if not _tac_pos(body, mask, m.start(), fb) or _in_conv(body, mask, m.start()):
            continue
        cfgs, opts, lb, end = _simp_call(body, pairs, m)
        if cfgs or opts or lb is None or any(mask[m.start():end]):
            continue
        names = [s.strip() for s in body[lb + 1:pairs[lb]].split(",")]
        if not names or not all(re.fullmatch(r"(?:" + IDENT + r"\.)*" + IDENT, s) for s in names):
            continue
        out.append(Candidate("dsimp_unfold", ((m.start(), end - m.start(), "unfold " + " ".join(names)),),
                             "unfold explicit definitions without simplifier traversal", 3))

    # Settings come only from the generated table (RULES grind_config): each
    # Bool field of Lean.Grind.Config toggled away from its default, in
    # declaration order, accepted by every installed toolchain.  Full-toolchain
    # compilation still decides whether a setting helps a particular call.
    spec = HC.CONFIG.get("grind")   # read at call time (tests replace the table)
    for m in re.finditer(r"(?<![\w.'?!])grind(?![\w'?!])", body) if spec else ():
        if not _tac_pos(body, mask, m.start(), fb) or _in_conv(body, mask, m.start()):
            continue
        cfgs, opts, _, _ = _simp_call(body, pairs, m)
        configs = " ".join(body[a:b] for a, b in cfgs)
        if re.search(r"\bconfig\s*:=", configs):
            continue  # an arbitrary config expression may set any field

        def available(key):
            return key not in opts and not re.search(r"\b" + re.escape(key) + r"\s*:=", configs)

        for rank, (field, setting) in enumerate(spec["toggles"]):
            if available(field):
                out.append(Candidate("grind_config", ((m.end(), 0, " " + setting),),
                                     "grind setting: toggle " + field, 7 + rank, setting))
    return out
