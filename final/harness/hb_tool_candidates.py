"""Bounded, syntax-only heartbeat experiments; every result requires compilation.

This module knows no declarations or problem identities.  Offsets refer to the
input proof body (including its ``by``), and work with ``normalize.apply``.

Provenance (tools build rule, 2026-10-22): every token a family inserts comes
from the proof being edited, from a core keyword its rule names (RULES, the
named words in backticks), or from the generated table TABLES names
(harness/tools/tables/simp_config_fields.json: the simp / grind configuration
settings, by gen_simp_config.py's stated rule over every installed toolchain).
candidates() drops, with a warning, any candidate that inserts anything else
(unruled_tokens).  The settings were hand-picked before 2026-10-22; without the
table the two table families propose nothing (a warning at import).  The
discharge-depth family (simp_discharge) was removed in the 2026-10-22 review: its
grid named one configuration field by hand, a word of one union proof and of no
seed (provenance audit: red).
"""
from __future__ import annotations

from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
import sys

from harness.normalize import _mask, _pairs
from harness.hb_rewrite import (
    _first_by, _tac_pos, _in_conv, _skip_ws, _line_end, _ls,
    _indent_at, _code, CFG_RE,
)
from scorer.tokenize import tokens as _lex


@dataclass(frozen=True)
class Candidate:
    kind: str
    edits: tuple
    note: str
    priority: int = 0
    table_entry: str | None = None   # the table setting a table family inserted (provenance trace)


ROOT = Path(__file__).resolve().parents[1]
CONFIG_TABLE = ROOT / "harness/tools/tables/simp_config_fields.json"
# table family -> (the table list it reads, the tactics whose entries it inserts)
TABLE_KINDS = {"simp_config": ("toggles", ("simp", "simpa", "simp_all")), "grind_config": ("toggles", ("grind",))}
TABLES = {"simp_config_fields": {
    "rule": "per tactic (simp, simpa: Lean.Meta.Simp.Config; simp_all: Simp.ConfigCtx; grind: Lean.Grind.Config), every Bool field "
            "toggled away from its default (+f / -f), singly, in declaration order, kept when every installed toolchain has the "
            "field with that default, accepts the setting on True and does not close False with it (no field selected by name); "
            "simp_config and grind_config offer a call each toggle it does not already set (field names live in the table only)",
    "query": "python3 harness/tools/tables/gen_simp_config.py (harness/tools/tables/simp_config_query.lean)",
    "path": "harness/tools/tables/simp_config_fields.json",
    "ops": ("hb:simp_config", "hb:grind_config")}}


def load_config(path=CONFIG_TABLE) -> dict:
    """tactic -> {"toggles": ((field, setting), ...)} in table order, from the generated table (any other list is ignored);
    {} with a warning on stderr when it is missing, unreadable or has no settings (the table families then propose nothing)."""
    try:
        data = json.loads(Path(path).read_text())
        out = {}
        for tac, spec in sorted((data.get("tactics") or {}).items()):
            out[tac] = {key: tuple((e["field"], e["setting"]) for e in spec.get(key) or ()
                                   if isinstance(e.get("field"), str) and isinstance(e.get("setting"), str))
                        for key in ("toggles",)}
        if not any(v["toggles"] for v in out.values()):
            raise ValueError("no settings")
        return out
    except (OSError, ValueError, AttributeError, KeyError, TypeError) as e:
        print(f"[hb_tool_candidates] WARNING: table {path} unusable ({type(e).__name__}: {str(e)[:120]}); simp_config "
              f"and grind_config propose nothing", file=sys.stderr, flush=True)
        return {}


def table_status(path=CONFIG_TABLE) -> dict:
    """{"path", "ok", "sha256" (first 16 hex of the file) or None, "ops"}: ok when the table gives its families settings."""
    rec = {"path": str(path), "ok": bool(CONFIG) if Path(path) == CONFIG_TABLE else bool(load_config(path)), "sha256": None,
           "ops": list(TABLES["simp_config_fields"]["ops"])}
    try:
        rec["sha256"] = hashlib.sha256(Path(path).read_bytes()).hexdigest()[:16]
    except OSError:
        pass
    return rec


CONFIG = load_config()

# The rule of every family. A family may insert only tokens of the proof it edits, the words its rule names in backticks, and (table
# families) the table setting it carries; a fresh-name stem its rule names (FRESH_STEMS) may be extended with `_` until unused.
FRESH_STEMS = frozenset({"hb_w"})
RULES = {
    "choose_destruct": "a single-line `specialize` / `apply` .. `at` / `have` / `let` producer of a name whose every later use in its "
                       "layout block is a choose or choose_spec projection is destructured where it is produced: `obtain` `⟨` w `,` "
                       "name `⟩` `:=` producer; the uses become w and the name; w is the fresh name `hb_w` (extended with `_` until "
                       "unused); an `apply` .. `at` producer keeps its line before the destructuring",
    "simp_target": "a simp / simpa / dsimp call at `*` loses its location (deletes text, inserts nothing)",
    "simp_once": "`simp_all` becomes `simp` with the local context as a rule: `[` `*` `]` appended to a call without a list, else `*` "
                 "(followed by `,` before existing rules) added unless the list has it",
    "simp_config": "table simp_config_fields: each toggle of the call's tactic (simp, simpa, simp_all) that the call does not already "
                   "set, singly, inserted after the tactic name, in the table's sequence (priority 5 + the toggle's rank)",
    "ext_funext": "`ext` followed only by plain names becomes `funext` with the same names",
    "elimination": "the other core elimination tactic of the same family: `cases` becomes `induction`",
    "let_have": "a single-line `let` with `:=` becomes `have` (the same binding, its value hidden from later unfolding)",
    "choose_producer": "`have` name `:=` e followed by 1 to 4 choose_spec projections (the whole right side) becomes `obtain` `⟨` "
                       "`_` `,` .. name `⟩` `:=` e, one `_` per projection; an anonymous have names its fact `this`",
    "congr_arg": "`congr` 1 alone on its line becomes `apply` `congrArg` `_` (core apply, Init's congrArg, a hole)",
    "vacuous_function": "a term `by` `simp` closing a term becomes `nofun` (core term keyword)",
    "simp_context": "a simp / simpa / simp_all `only` call with a discharger gets `*` in its list (after `,` when the list has rules) "
                    "unless the list has it",
    "discharge_first": "a fun_prop discharger setting becomes `first` `|` `assumption` `|` fun_prop (the call's own discharger last)",
    "discharge_assumption": "a fun_prop discharger setting becomes `assumption`",
    "elimination_rcases": "`cases` becomes `rcases` (the recursive form of the same elimination)",
    "dsimp_unfold": "`dsimp` with only a list of plain names and no settings becomes `unfold` with the same names and location",
    "grind_config": "table simp_config_fields: each toggle of grind that the call does not already set, singly, inserted after the "
                    "tactic name, in the table's sequence (priority 7 + the toggle's rank); none when the call has a config := setting",
}


IDENT = r"[^\W\d][\w'₀-₉]*"
HEAD = re.compile(r"(?<![\w.'?!])(simp_all|simp|simpa|dsimp|ext|cases|let)(?![\w'?!])")
SCOPE_HEAD = re.compile(r"(?:case'?|next)\b|[·|]")


def _scope_end(body, mask, pos):
    """End of the same layout block, before another case or bullet."""
    indent = _indent_at(body, _ls(body, pos))
    p = _line_end(body, pos) + 1
    while p < len(body):
        end = _line_end(body, p)
        text = _code(body, mask, p, end).strip()
        depth = _indent_at(body, p)
        if text and (depth < indent or (depth == indent and SCOPE_HEAD.match(text))):
            return p
        p = end + 1
    return len(body)


def _fresh(body, stem):
    name = stem
    while re.search(r"(?<![\w'])" + re.escape(name) + r"(?![\w'])", body):
        name += "_"
    return name


def _choose(body, mask, fb):
    # Changing the producer avoids retaining an unused existential and keeps the
    # destructuring at a known tactic boundary.  Only single-line producers are
    # recognized; use sites are bounded by layout and must all be projections.
    for line in re.finditer(r"(?m)^[ \t]*(specialize|apply|have|let)\b[^\n]*", body):
        a = line.start(1)
        if not _tac_pos(body, mask, a, fb) or any(mask[a:line.end()]):
            continue
        text = body[a:line.end()].rstrip()
        name = expr = None
        prefix = ""
        m = re.fullmatch(r"specialize\s+(" + IDENT + r")\s+(.+)", text)
        if m:
            name, args = m.groups()
            expr = name + " " + args
        m = re.fullmatch(r"apply\s+(.+)\s+at\s+(" + IDENT + r")", text)
        if m:
            term, name = m.groups()
            # `apply` may infer explicit arguments which a term application
            # would require us to synthesize.  Preserve that elaboration.
            prefix = text + "\n" + " " * _indent_at(body, _ls(body, a))
            expr = name
        m = re.fullmatch(r"(?:have|let)\s+(" + IDENT + r")\s*:=\s*(.+)", text)
        if m:
            name, expr = m.groups()
        if name is None or expr is None or re.search(r"\bby\b|;|<;>|=>", expr):
            continue
        end = _scope_end(body, mask, a)
        uses = list(re.finditer(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'])", body[line.end():end]))
        if not uses:
            continue
        witness = _fresh(body, "hb_w")
        edits = [(a, line.end() - a, prefix + f"obtain ⟨{witness}, {name}⟩ := {expr}")]
        valid, count = True, 0
        for use in uses:
            p = line.end() + use.start()
            if mask[p]:
                continue
            tail = body[p + len(name):end]
            spec = re.match(r"\.choose_spec(?![\w'])", tail)
            value = re.match(r"\.choose(?![\w'])", tail)
            if spec:
                edits.append((p, len(name) + spec.end(), name))
            elif value:
                edits.append((p, len(name) + value.end(), witness))
            else:
                valid = False
                break
            count += 1
        if valid and count:
            yield Candidate("choose_destruct", tuple(edits), "destructure an existential before repeated projections", 0)


def _simp_call(body, pairs, m):
    """Recognize the config/options/list prefix without crossing a tactic line."""
    p = _skip_ws(body, m.end(), newlines=False)
    cfgs = []
    options = set()
    while p < len(body):
        if body[p] == "(" and p in pairs and CFG_RE.match(body, p):
            cfgs.append((p, pairs[p] + 1))
            p = _skip_ws(body, pairs[p] + 1, newlines=False)
            continue
        opt = re.match(r"([+-])([A-Za-z][\w]*)\b", body[p:])
        if opt:
            options.add(opt.group(2))
            p = _skip_ws(body, p + opt.end(), newlines=False)
            continue
        break
    only = re.match(r"only(?![\w'])", body[p:])
    if only:
        p = _skip_ws(body, p + only.end(), newlines=False)
    lb = p if p < len(body) and body[p] == "[" and p in pairs else None
    end = pairs[lb] + 1 if lb is not None else p
    return cfgs, options, lb, end


def candidates(body: str, max_candidates: int = 48) -> list[Candidate]:
    """Return deterministic, capped experiments; none is assumed semantically safe.

    Expensive families are interleaved by variant, so one long simp list cannot
    consume the budget.  Comments, strings, and term-level tactic names are not
    candidate sites.  Callers must compile and score the complete declaration.
    """
    if max_candidates <= 0:
        return []
    mask = _mask(body)
    pairs = _pairs(body, mask)
    fb = _first_by(body, mask)
    if fb < 0:
        return []
    out = list(_choose(body, mask, fb))
    for m in HEAD.finditer(body):
        p, head = m.start(), m.group(1)
        if not _tac_pos(body, mask, p, fb) or _in_conv(body, mask, p):
            continue
        if head in {"simp", "simpa", "simp_all", "dsimp"}:
            cfgs, opts, lb, end = _simp_call(body, pairs, m)
            configs = " ".join(body[a:b] for a, b in cfgs)
            loc = re.match(r"[ \t]*at[ \t]+\*(?![\w'])", body[end:])
            if loc and head != "simp_all":
                out.append(Candidate("simp_target", ((end, loc.end(), ""),), "simplify the target without revisiting every hypothesis", 1))
            if head == "simp_all":
                edits = [(p, len(head), "simp")]
                if lb is None:
                    edits.append((end, 0, " [*]"))
                else:
                    inner = body[lb + 1:pairs[lb]].strip()
                    if not re.search(r"(?:^|,)\s*\*\s*(?:,|$)", inner):
                        edits.append((lb + 1, 0, "*, " if inner else "*"))
                out.append(Candidate("simp_once", tuple(edits), "use local facts in one target simplification", 2))
            # The call's own settings always take precedence: a field the call
            # already sets (+f, -f or f := v) is never set again.  Settings come
            # only from the generated table (RULES simp_config).
            spec = CONFIG.get(head) if head != "dsimp" else None
            if spec:
                def available(key):
                    return key not in opts and not re.search(r"\b" + re.escape(key) + r"\s*:=", configs)
                for rank, (field, setting) in enumerate(spec["toggles"]):
                    if available(field):
                        out.append(Candidate("simp_config", ((m.end(), 0, " " + setting),),
                                             f"toggle {field} away from its default", 5 + rank, setting))
        elif head == "ext":
            # ext's patterns and optional : depth have no funext counterpart.
            tail = body[m.end():_line_end(body, p)]
            if re.fullmatch(r"(?:[ \t]+(?:" + IDENT + r"|_))+[ \t]*", tail):
                out.append(Candidate("ext_funext", ((p, 3, "funext"),), "introduce function arguments directly", 3))
        elif head == "cases":
            out.append(Candidate("elimination", ((p, 5, "induction"),), "compare induction elaboration for an elimination", 4))
        elif head == "let":
            # Existing letI/letR forms are excluded by the head regex.  A have
            # preserves evidence without requiring future zeta reduction.
            line = body[m.end():_line_end(body, p)]
            if ":=" in line and not re.search(r"\bby\b|;", line):
                out.append(Candidate("let_have", ((p, 3, "have"),), "keep a local fact opaque to definitional simplification", 4))
    # Import here: extras reuse the lexical helpers and Candidate above.  Keep
    # all families under one priority order and one candidate cap.
    from harness.hb_tool_extra import extra_candidates
    out.extend(extra_candidates(body))
    body_tokens = proof_tokens(body)
    seen = set()
    result = []
    for cand in sorted(out, key=lambda c: (c.priority, c.edits[0][0], c.note)):
        if len(result) >= max_candidates:
            break
        if cand.edits in seen:
            continue
        bad = unruled_tokens(body, cand, body_tokens)
        if bad:
            # Fail closed: a family edit that inserts an unruled word is a bug.
            print(f"[hb_tool_candidates] WARNING: {cand.kind} inserts tokens its rule does not name ({len(bad)}); dropped",
                  file=sys.stderr, flush=True)
            continue
        seen.add(cand.edits)
        result.append(cand)
    return result[:max_candidates]


def proof_tokens(body: str) -> set:
    """The tokens of body and every dotted run inside one (`a.b.c` gives a, b, c, a.b, b.c): a family may cut a qualified name."""
    out = set()
    for t in _lex(body):
        out.add(t)
        parts = t.split(".")
        if len(parts) > 1 and all(parts):
            out.update(".".join(parts[i:j]) for i in range(len(parts)) for j in range(i + 1, len(parts) + 1))
    return out


def rule_tokens(kind: str) -> frozenset:
    """The tokens RULES[kind] names: every token of its backticked spans."""
    return frozenset(t for span in re.findall(r"`([^`]+)`", RULES.get(kind, "")) for t in _lex(span))


def table_settings(kind: str, config: dict | None = None) -> frozenset:
    """Every setting the generated table offers a table family (on any of the family's tactics)."""
    if kind not in TABLE_KINDS:
        return frozenset()
    key, tactics = TABLE_KINDS[kind]
    cfg = CONFIG if config is None else config
    return frozenset(s for tac in tactics for _, s in (cfg.get(tac) or {}).get(key, ()))


def unruled_tokens(body: str, cand: Candidate, body_tokens=None, config: dict | None = None) -> list[str]:
    """The tokens cand's edits insert that are neither tokens of body (proof_tokens), nor named by RULES[cand.kind] (a named stem of
    FRESH_STEMS may be extended with `_`), nor tokens of the table setting cand carries when it is a setting of its family in the
    table. An unknown kind names nothing."""
    have = proof_tokens(body) if body_tokens is None else body_tokens
    named = set(rule_tokens(cand.kind))
    if cand.table_entry is not None and cand.table_entry in table_settings(cand.kind, config):
        named |= set(_lex(cand.table_entry))
    bad = []
    for _, _, ins in cand.edits:
        for t in _lex(ins):
            fresh = any(re.fullmatch(re.escape(stem) + "_*", t) for stem in FRESH_STEMS & named)
            if t not in have and t not in named and not fresh and t not in bad:
                bad.append(t)
    return bad


# ---- tools contract (provenance audit, 2026-10-22) -------------------------------------------------------------------------------------
# harness/provenance_audit.py runs this generator through the tools' candidates(proof, statement, ...) contract; harness/hb_tool.improve
# does not call the adapter (it calls candidates(body) directly), so the pipeline is unchanged by it.
KINDS = ("choose_destruct", "simp_target", "simp_once", "simp_config", "ext_funext", "elimination", "let_have",
         "choose_producer", "congr_arg", "vacuous_function", "simp_context", "discharge_first", "discharge_assumption",
         "elimination_rcases", "dsimp_unfold", "grind_config")
OPS = tuple("hb:" + k for k in KINDS)


def tool_candidates(proof, statement, *, exchange=None, max_per_op=40, ctx=None, max_candidates=48):
    """One round of harness/hb_tool.improve's proposals on `proof` as [{"op": "hb:<kind>", "decl", "note"}]: candidates(body) under the
    pipeline's default cap, each declaration rebuilt as improve does (head + apply), skipped as improve skips it (unchanged, repeated,
    statement changed, forbidden), then each op's first max_per_op in priority order. A table family's item carries its trace,
    "table_entry": {"table": "simp_config_fields", "entry": <the setting>} (the audit checks it against the table's strings).
    exchange and ctx are accepted and unused."""
    from collections import Counter
    from harness.normalize import apply
    from scorer.forbidden import check_forbidden
    from scorer.tokenize import split_declaration
    body = split_declaration(proof, statement)
    if body is None:
        return []
    head = proof[:len(proof) - len(body)]
    out, seen, per = [], {proof}, Counter()
    for cand in candidates(body, max_candidates):
        decl = head + apply(body, [cand])
        if decl in seen or per[cand.kind] >= max_per_op:
            continue
        seen.add(decl)
        new_body = split_declaration(decl, statement)
        if new_body is None or check_forbidden(new_body):
            continue
        per[cand.kind] += 1
        item = {"op": "hb:" + cand.kind, "decl": decl, "note": cand.note}
        if cand.table_entry is not None:
            item["table_entry"] = {"table": "simp_config_fields", "entry": cand.table_entry}
        out.append(item)
    return out
