#!/usr/bin/env python3
"""T6 nameless transpiler (b63, docs/adaptive_plan_93.md §4.1 item 13; B §3 CCS / SKI rows; pretest T8, probe/b63/dxr/T8.json): a









































"""
from __future__ import annotations

import hashlib, re, time

from harness.tools.t4_nameless import parse_goals, _PPID, _norm
from scorer.tokenize import count_tokens, split_declaration

OPS = ("t6:joint", "t6:transpile", "t6:exists", "t6:exists_imp")
TABLES: dict = {}                                                                                                                          
SEARCH_SECONDS = 180.0
MAX_CHECKS = 300                                               
N_OUT = 4
BAR = 0.05
MIN_TIMEOUT_S = 10.0
TIMEOUT_MULT = 4.0
MAX_IMP_SCAN = 40                                                      
MAX_BODY_LINES = 400

NAME = r"[^\W\d][\w'!?₀-₉]*"
INTRO_RE = re.compile(r"^(intro|intros|rintro)(?:\s+(.*))?$")
RENAME_RE = re.compile(r"^rename_i(\s+.*)?$")
CASE_RE = re.compile(r"^(case'?|next)(?:\s+(" + NAME + r"(?:\.[\w']+)*))?((?:\s+(?:" + NAME + r"|_))*)\s*=>\s*(.*)$")
BULLET_RE = re.compile(r"^·\s+(.*)$")
OBTAIN_RE = re.compile(r"^obtain\s+(⟨.*⟩|\(.*\))\s*:=\s*(.+)$")
RCASES_RE = re.compile(r"^rcases\s+(.+?)\s+with\s+(⟨.*⟩|\(.*\))$")
CASES_WITH_RE = re.compile(r"^(cases|induction)\s+(.+?)\s+with\s*(\|.*)?$")
ALT_RE = re.compile(r"^\|\s*(" + NAME + r")((?:\s+(?:" + NAME + r"|_))*)\s*=>\s*(.*)$")
EXISTS_RE = re.compile(r"^(exists|use)\s+(.+)$")
TRACE = "trace_state"
MULTI_GOAL = re.compile(r"^(all_goals|any_goals|repeat'|on_goal|pick_goal|swap|rotate_left|rotate_right|focus|iterate)\b")
LOOKAHEAD = 3
SITE_KINDS = ("intro", "rename_i", "case", "bullet", "obtain", "cases_with", "exists", "shared", "rename_i_chain")


class _Budget(Exception):
    """The search's deadline or reading budget is used up."""


def proof_key(proof: str) -> str:
    return hashlib.sha256(proof.strip().encode()).hexdigest()[:16]


                                                                                                                                  
def parse_block(lines: list[str], i: int, indent: int) -> tuple[list[dict], int]:
    """Steps at `indent` from line i: [{"text", "indent", "kids": [raw lines], "line": index}], next index."""
    steps = []
    while i < len(lines):
        ln = lines[i]
        if not ln.strip():
            i += 1
            continue
        ind = len(ln) - len(ln.lstrip())
        if ind < indent:
            break
        if ind > indent:
            raise ValueError(f"unexpected indentation at line {i}")
        if ln.strip().startswith("/--") and steps:
            steps[-1]["kids"].append(ln)
            i += 1
            continue
        kids, j = [], i + 1
        while j < len(lines) and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip()) > indent):
            if lines[j].strip():
                kids.append(lines[j])
            j += 1
        steps.append({"text": ln.strip(), "indent": indent, "kids": kids, "line": i})
        i = j
    return steps, i


def kid_steps(kids: list[str], lead: list | None = None) -> list[dict]:
    """The steps of a block's kid lines, at the block's indentation (its shallowest line). b66 (retro A7; found 2026-10-25 on a LeanPool dev



"""
    if not kids:
        return []
    ind = min(len(k) - len(k.lstrip()) for k in kids)
    k0 = next(i for i, k in enumerate(kids) if len(k) - len(k.lstrip()) == ind)
    if k0 and lead is not None:
        lead.extend(kids[:k0])
    return parse_block(kids, k0 if lead is not None else 0, ind)[0]


def step_text(st: dict) -> list[str]:
    return [" " * st["indent"] + st["text"]] + list(st["kids"])


def is_atomic(st: dict) -> bool:
    t = st["text"]
    return bool(re.match(r"^(all_goals|any_goals|try|first|repeat|iterate|focus|on_goal|classical|calc|have|show|suffices|refine|exact|apply|simp|grind|omega|conv)\b", t)) \
        or "<;>" in t or t.endswith("with grind") or t.startswith("#") or t.startswith("/--") or t.startswith("--")


def classify(st: dict) -> str:
    t = st["text"]
    if CASE_RE.match(t):
        return "case"
    if BULLET_RE.match(t):
        return "bullet"
    if is_atomic(st):
        return "atomic"
    if INTRO_RE.match(t):
        return "intro"
    if RENAME_RE.match(t):
        return "rename_i"
    if OBTAIN_RE.match(t) or RCASES_RE.match(t):
        return "obtain"
    if CASES_WITH_RE.match(t):
        return "cases_with"
    if EXISTS_RE.match(t):
        return "exists"
    return "plain"


def reindent(lines: list[str], indent: int) -> list[str]:
    if not lines:
        return []
    base = len(lines[0]) - len(lines[0].lstrip())
    return [" " * indent + ln[base:] if ln.startswith(" " * base) else " " * indent + ln.lstrip() for ln in lines]


def inner_steps(st: dict, kind: str) -> list[dict]:
    if "_inner" in st:
        return st["_inner"]
    st["_inner"] = _inner_steps(st, kind)
    return st["_inner"]


def _inner_steps(st: dict, kind: str) -> list[dict]:
    if kind == "case":
        rhs = CASE_RE.match(st["text"]).group(4).strip()
    else:
        rhs = BULLET_RE.match(st["text"]).group(1).strip()
    lead: list = []
    kids = kid_steps(st["kids"], lead if rhs else None)                                                                                   
    if rhs:
        head = {"text": rhs, "indent": (kids[0]["indent"] if kids else st["indent"] + 2), "kids": lead, "line": st["line"]}
        return [head] + kids
    return kids


def alternatives(st: dict):
    if "_alts" in st:
        return st["_alts"]
    st["_alts"] = _alternatives(st)
    return st["_alts"]


def _alternatives(st: dict):
    m = CASES_WITH_RE.match(st["text"])
    if not m:
        return None
    lines = ([m.group(3)] if m.group(3) else []) + list(st["kids"])
    alts, cur = [], None
    for ln in lines:
        s = ln.strip()
        am = ALT_RE.match(s)
        if am:
            cur = (am.group(1), am.group(2), [])
            alts.append(cur)
            if am.group(3).strip():
                cur[2].append({"text": am.group(3).strip(), "indent": 0, "kids": [], "line": st["line"]})
        elif cur is not None:
            cur[2].append(ln)
        else:
            return None
    out = []
    for tag, names, body in alts:
        raw = [b for b in body if isinstance(b, str)]
        inline = [b for b in body if isinstance(b, dict)]
        lead: list = []
        ks = kid_steps(raw, lead if inline else None)                                                                                       
        if lead:
            inline[-1] = dict(inline[-1], kids=list(inline[-1]["kids"]) + lead)
        out.append((tag, names, inline + ks))
    return out if out else None


def split_intro_args(args: str) -> list[str]:
    out, cur, depth = [], "", 0
    for ch in args:
        if ch in "(⟨[":
            depth += 1
        elif ch in ")⟩]":
            depth -= 1
        if ch.isspace() and depth == 0:
            if cur:
                out.append(cur)
            cur = ""
        else:
            cur += ch
    if cur:
        out.append(cur)
    return out


def split_top(s: str) -> list[str]:
    out, cur, depth = [], "", 0
    for ch in s:
        if ch in "(⟨[{":
            depth += 1
        elif ch in ")⟩]}":
            depth -= 1
        if ch == "," and depth == 0:
            out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


                                                                                                                                   
def subst(text: str, mp: dict) -> str:
    return _PPID.sub(lambda m: mp.get(m.group(1), m.group(1)), text) if mp else text


_BINDER = re.compile(r"(?:∃|∀|∑|∏|⨆|⨅|⋃|⋂|fun|λ)\s*(?:\(|⦃|\{)?\s*((?:(?:" + NAME + r")\s+)*(?:" + NAME + r"))")


def bound_names(text: str) -> set:
    """Names bound by a binder inside `text` (∃ x, ∀ (x y : T), fun x => ..): a hypothesis rename never reaches them."""
    out = set()
    for m in _BINDER.finditer(text):
        out.update(m.group(1).split())
    return out


def alpha(text: str, hyp_names) -> str:
    """Bound names canonicalised by binder order (β0, β1, ..) so that `∃ a, ..` and `∃ a_1, ..` compare equal; a bound name that is also
"""
    names: list = []
    for m in _BINDER.finditer(text):
        for n in m.group(1).split():
            if n not in names and n not in hyp_names:
                names.append(n)
    if not names:
        return text
    return subst(text, {n: f"β{k}" for k, n in enumerate(names)})


_LINE_BINDERS = (
    re.compile(r"\brename_i\b((?:\s+(?:" + NAME + r"|_))+)"),
    re.compile(r"\b(?:intro|intros|rintro)\b([^;⟩\]]*?)(?=$|<;>|;|\)|\])"),
    re.compile(r"\b(?:obtain|rcases|rintro)\b[^:]*?(⟨[^:]*⟩)"),
    re.compile(r"(?:\bfun\b|λ)([^=]*?)=>"),
    re.compile(r"(?:^|\s)(?:case'?|next)\s+(?:" + NAME + r"(?:\.[\w']+)*\s+)?((?:(?:" + NAME + r"|_)\s+)*)=>"),
    re.compile(r"\|\s*" + NAME + r"((?:\s+(?:" + NAME + r"|_))*)\s*=>"),
    re.compile(r"\b(?:have|let|set|suffices|generalize)\s+(" + NAME + r")\s*(?::|:=)"),
)


def line_binders(ln: str) -> set:
    """Names a tactic line BINDS (rename_i / intro names, obtain / rintro pattern names, fun binders, case / alternative names, have
"""
    out = set(bound_names(ln))
    for rx in _LINE_BINDERS:
        for m in rx.finditer(ln):
            seg = m.group(1)
            seg = re.sub(r":[^,⟩)]*", "", seg)                                   
            out.update(n for n in re.findall(NAME, seg) if n not in ("rfl", "fun", "by"))
    return out


def subst_line(ln: str, mp: dict) -> str:
    """`subst` on a verbatim proof line, skipping the names the line binds itself."""
    if not mp:
        return ln
    b = line_binders(ln)
    if not b:
        return subst(ln, mp)
    return subst(ln, {k: v for k, v in mp.items() if k not in b})


def subst_free(text: str, mp: dict) -> str:
    """`subst` restricted to names not bound inside the text itself (the goal display shows `∃ rt, ..` with the hypothesis `rt` renamed to
"""
    if not mp:
        return text
    b = bound_names(text)
    if not b:
        return subst(text, mp)
    mp2 = {k: v for k, v in mp.items() if k not in b}
    return subst(text, mp2)


def match_goal(O: dict, N: dict, rename: dict, budget: int = 4000):
    """Original goal O under the names so far mapped by `rename`, new goal N: the extended rename map, or None (hypotheses matched by
"""
    if len(O["hyps"]) != len(N["hyps"]):
        return None
    nodes = [0]
                                                                                                                           
    on_names = {h[0] for h in O["hyps"]}
    nn_names = {h[0] for h in N["hyps"]}
    O_t = (alpha(O["target"], ()), alpha(O["target"], on_names))
    O_h = [(n, (alpha(t, ()), alpha(t, on_names))) for n, t in O["hyps"]]
    N_t = (_norm(alpha(N["target"], ())), _norm(alpha(N["target"], nn_names)))
    N_h = [(_norm(alpha(t, ())), _norm(alpha(t, nn_names))) for _, t in N["hyps"]]

    def eq(o: tuple, mp: dict, n: tuple) -> bool:
        return _norm(subst_free(o[0], mp)) == n[0] or _norm(subst_free(o[1], mp)) == n[1]

    def go(i: int, mp: dict, free: list):
        if nodes[0] > budget:
            return None
        nodes[0] += 1
        if i == len(O_h):
            return mp if eq(O_t, mp, N_t) else None
        on, ot = O_h[i]
        cands = [k for k in free if eq(ot, mp, N_h[k])]
        if not cands:
            return None
        cands.sort(key=lambda k: (0 if N["hyps"][k][0] == mp.get(on, on) else 1, k))
        for k in cands:
            nn = N["hyps"][k][0]
            mp2 = dict(mp)
            if on != nn or on in mp2:
                mp2[on] = nn
            res = go(i + 1, mp2, [f for f in free if f != k])
            if res is not None:
                return res
        return None

    return go(0, dict(rename), list(range(len(N["hyps"]))))


def match_states(O: list[dict], N: list[dict], rename: dict, prefix: bool = False):
    """(positions of each O goal in N, merged rename map) or None."""
    if prefix:
        if len(N) < len(O):
            return None
        N = N[:len(O)]
    elif len(O) != len(N):
        return None
    used, pos, merged = set(), [], dict(rename)
    for g in O:
        order = sorted(range(len(N)), key=lambda k: (0 if N[k]["tag"] == g["tag"] else 1, k))
        hit = None
        for k in order:
            if k in used:
                continue
            mp = match_goal(g, N[k], rename)
            if mp is not None:
                hit = (k, mp)
                break
        if hit is None:
            return None
        used.add(hit[0])
        pos.append(hit[0])
        if not pos[:-1]:
            merged.update(hit[1])
        else:
            for a, b in hit[1].items():
                merged.setdefault(a, b)
    return pos, merged


                                                                                                                                 
class Oracle:
    """Elaborates candidate prefixes on the workbench and returns their goal lists; bounded by a deadline and a reading budget."""

    def __init__(self, wb, head: str, log=None, deadline: float | None = None, budget: list | None = None, timeout: float | None = None):
        self.wb, self.head, self.log = wb, head, log or (lambda *a: None)
        self.deadline, self.budget, self.timeout = deadline, budget, timeout
        self.calls = 0
        self.seconds = 0.0
        self.cache: dict = {}
        self.errors: dict = {}

    def decl(self, body_lines: list[str]) -> str:
        return self.head + "\n".join(body_lines)

    def _tick(self):
        if self.deadline is not None and time.time() >= self.deadline:
            raise _Budget("deadline")
        if self.budget is not None and self.budget[0] <= 0:
            raise _Budget("readings")

    def run(self, body_lines: list[str], want_trace: bool = True, trace_indent: int = 2) -> dict:
        key = ("T%d" % trace_indent if want_trace else "C", "\n".join(body_lines))
        if key in self.cache:
            return self.cache[key]
        self._tick()
        t0 = time.time()
        text = self.decl(body_lines + ([" " * trace_indent + TRACE] if want_trace else []))
        try:
            r = self.wb.check([text], messages=True, timeout=self.timeout)[0]
        except Exception as e:                
            cls = type(e).__name__
            self.errors[cls] = self.errors.get(cls, 0) + 1
            r = {"status": "error", "error": f"{cls}: {str(e)[:120]}", "messages": []}
        self.calls += 1
        if self.budget is not None:
            self.budget[0] -= 1
        self.seconds += time.time() - t0
        msgs = r.get("messages") or []
        n_head = self.head.count("\n")
        trace_line = n_head + len(body_lines) + 1
        goals = None
        errs = []
        for m in msgs:
            if m.get("severity") == "information" and m.get("decl_line") == trace_line:
                g = parse_goals(m.get("data"))
                if g is not None:
                    goals = g
            elif m.get("severity") == "error":
                errs.append((m.get("decl_line"), str(m.get("data"))[:200]))
        if r.get("status") not in ("ok", "fail") and not errs:
            errs.append((None, str(r.get("error") or r.get("status"))[:200]))
        if r.get("status") == "timeout":
            self.errors["timeout"] = self.errors.get("timeout", 0) + 1
                                                                                                                                         
        own = [e for e in errs if not e[1].startswith("unsolved goals")]
        out = {"ok": not own, "goals": goals if not own else None, "errors": errs, "tokens": r.get("tokens"),
               "heartbeats": r.get("heartbeats"), "closed": r.get("status") == "ok", "status": r.get("status"),
               "score": r.get("score_exact")}
        if goals == [] and not errs:
            out["closed"] = True
        self.cache[key] = out
        return out

    def compiles(self, body_lines: list[str]) -> dict:
        return self.run(body_lines, want_trace=False)


                                                                                                                                
def traced_original(steps: list[dict], out: list[str], ids: dict, indent: int = 2) -> None:
    """The original with `trace_state` after every step at every nesting level we transpile; `ids`: step identity -> trace line."""
    for st in steps:
        kind = classify(st)
        if kind in ("case", "bullet"):
            inner = inner_steps(st, kind)
            if kind == "case":
                out.append(" " * indent + st["text"].split("=>", 1)[0] + "=>")
            else:
                out.append(" " * indent + "·")
            traced_original(inner, out, ids, indent + 2)
        elif kind == "cases_with" and alternatives(st):
            m = CASES_WITH_RE.match(st["text"])
            out.append(" " * indent + f"{m.group(1)} {m.group(2)} with")
            for tag, names, body in alternatives(st):
                out.append(" " * (indent + 2) + f"| {tag}{names} =>")
                out.append(" " * (indent + 4) + TRACE)
                ids[(id(st), tag)] = len(out)
                traced_original(body, out, ids, indent + 4)
            continue
        else:
            out.extend(reindent(step_text(st), indent))
        out.append(" " * indent + TRACE)
        ids[id(st)] = len(out)


                                                                                                                                
class Transpiler:
    """mode "full": every rule; mode "exists": only the exists rule (original names, structure kept verbatim)."""

    def __init__(self, head: str, body_lines: list[str], oracle: Oracle, log=None, orig_head: str | None = None, mode: str = "full",
                 oracle_o: Oracle | None = None):
        self.head, self.oracle, self.mode = head, oracle, mode
        self.oracle_o = oracle_o                                                                              
        self.switch: int | None = None                                                                                    
        self.shift = 0                                                                                             
        orig_head = orig_head or head
        self.log = log or (lambda *a: None)
        self.steps = parse_block(body_lines, 0, 2)[0]
        self.stats = {"steps": 0, "rules": {}, "fallbacks": 0, "oracle_calls": 0, "notes": []}
        traced, ids = [], {}
        traced_original(self.steps, traced, ids)
        self.trace_ids = ids
        oracle._tick()
        t0 = time.time()
        r = oracle.wb.check([orig_head + "\n".join(traced)], messages=True, timeout=oracle.timeout)[0]
        oracle.calls += 1
        oracle.seconds += time.time() - t0
        if oracle.budget is not None:
            oracle.budget[0] -= 1
        self.orig_states: dict = {}
        n_head = orig_head.count("\n")
        for m in r.get("messages") or []:
            if m.get("severity") == "information":
                g = parse_goals(m.get("data"))
                if g is not None:
                    self.orig_states[m["decl_line"] - n_head] = g
        self.orig_ok = r.get("status") == "ok"
        self.stats["orig_traced_ok"] = self.orig_ok
        self.stats["orig_trace_points"] = len(self.orig_states)

    def orig_after(self, st: dict):
        O = self.orig_states.get(self.trace_ids.get(id(st)))
        if O is None and st.get("_closing"):
            return []
        return O

    def layout(self, body: list[str]) -> list[str]:
        """The physical lines: with a hygienic tail, `unhygienic` scoped over the prefix (indented once more), the tail at the outer level."""
        if self.switch is None:
            return body
        return ["  unhygienic"] + ["  " + ln for ln in body[:self.switch]] + body[self.switch:]

    def cur_oracle(self) -> Oracle:
        return self.oracle if self.switch is None else self.oracle_o

    def probe(self, body: list[str]) -> dict:
        return self.cur_oracle().run(self.layout(body), trace_indent=2 + self.shift)

    def emit(self, var: list[str]) -> list[str]:
        return [" " * self.shift + ln for ln in var] if self.shift else list(var)

    def compiles(self, body: list[str]) -> dict:
        return self.cur_oracle().compiles(self.layout(body))

    def can_switch(self, st: dict) -> bool:
        """A step that fails under `unhygienic` because it names inaccessible hypotheses (`rename_i` / `case tag names =>` / `next names =>`
"""
        if self.switch is not None or self.oracle_o is None or self.mode != "full":
            return False
        txt = "\n".join(step_text(st))
        return "rename_i" in txt or bool(re.search(r"^\s*(case'?|next)\s+\S.*=>", txt, re.M))

    def try_variant(self, body, variant, targets, rename, prefix, rest_n):
        r = self.probe(body + self.emit(variant))
        if r["ok"] and r["goals"] is None and (r.get("closed") or self.shift > 0):                                           
            r = dict(r, goals=[])
        if not r["ok"] or r["goals"] is None:
            return None
        for j, O in targets:
            if O is None:
                continue
            N = r["goals"]
            if prefix:
                if len(N) - rest_n != len(O):
                    continue
                m = match_states(O, N, rename, prefix=True)
            else:
                m = match_states(O, N, rename)
            if m is not None:
                return j, m[1], N
        return None

    def note(self, rule: str, ok: bool):
        d = self.stats["rules"].setdefault(rule, {"tried": 0, "used": 0})
        d["tried"] += 1
        if ok:
            d["used"] += 1

    def run_block(self, steps, body, rename, rest_n, prefix):
        i, aligned = 0, True
        if steps:
            steps[-1].setdefault("_closing", True)
        while i < len(steps):
            st = steps[i]
            kind = classify(st)
            self.stats["steps"] += 1
            targets = [(j, self.orig_after(steps[i + j])) for j in range(0, min(LOOKAHEAD + 1, len(steps) - i))]
            variants = self.variants(st, steps[i:], body, rename, kind)
            structured = kind in ("case", "bullet", "cases_with") and self.mode == "full"
            if not structured:
                fb = [(ln if kind == "intro" else subst_line(ln, rename)) for ln in reindent(step_text(st), 2)]
                variants.append(("fallback", fb, 0))
            variants.sort(key=lambda v: (count_tokens("\n".join(v[1])), -v[2]))
            done = None
            for rule, var, consume in variants:
                tg = [(j, self.orig_after(steps[i + j])) for j in range(consume, min(consume + LOOKAHEAD + 1, len(steps) - i))]
                res = self.try_variant(body, var, tg, rename, prefix, rest_n)
                self.note(rule, res is not None)
                if res is not None:
                    done = (rule, var, res)
                    break
            if done is None and structured:
                if kind in ("case", "bullet"):
                    prev = self.orig_after(steps[i - 1]) if i > 0 else None
                    res = self.case_block(st, kind, body, rename, rest_n, prefix, prev)
                    if res is not None and not res[2] and not prefix and self.can_switch(st):                                               
                        self.switch = len(body)
                        res2 = self.case_block(st, kind, body, rename, rest_n, prefix, prev)
                        ok2 = res2 is not None and (res2[2] or self.compiles(res2[0])["ok"])
                        self.switch = None
                        ok1 = self.compiles(res[0])["ok"]
                        if ok2 and (res2[2] or not ok1):
                            self.switch = len(body)
                            self.stats["hygienic_tail_at"] = st["line"]
                            res = res2
                else:
                    res = self.cases_with_block(st, body, rename, rest_n, prefix) if alternatives(st) else None
                if res is None or not res[2]:
                                                                                                                                              
                    var = [subst_line(ln, rename) for ln in reindent(step_text(st), 2)]
                    r2 = self.try_variant(body, var, targets, rename, prefix, rest_n)
                    self.note("block_verbatim", r2 is not None)
                    if r2 is not None:
                        done = (kind + "_verbatim", var, r2)
                if done is None and res is not None:
                    body, rename, ok = res
                    aligned = aligned and ok
                    i += 1
                    continue
            if done is None:
                var = [(ln if kind == "intro" else subst_line(ln, rename)) for ln in reindent(step_text(st), 2)]
                res = self.try_variant(body, var, targets, rename, prefix, rest_n)
                self.stats["fallbacks"] += 1
                if res is None and not prefix and self.can_switch(st):                                                          
                    self.switch = len(body)
                    res = self.try_variant(body, var, targets, rename, prefix, rest_n)
                    if res is None:
                        self.switch = None
                    else:
                        self.stats["hygienic_tail_at"] = st["line"]
                if res is None:
                    r = self.probe(body + self.emit(var))
                    body = body + self.emit(var)
                    aligned = False
                    O0 = self.orig_after(st)
                    self.stats["notes"].append(f"step {st['line']} ({kind}): no alignment (orig {None if O0 is None else len(O0)} goals, "
                                               f"new {None if r['goals'] is None else len(r['goals'])}; "
                                               f"{_err_class_text((r['errors'] or [(None, '?')])[0][1])})")
                    i += 1
                    continue
                done = ("fallback", var, res)
            rule, var, (j, rename, _) = done
            body = body + self.emit(var)
            i += 1 + j
        return body, rename, aligned

    def case_block(self, st, kind, body, rename, rest_n, prefix, prev=None):
        r = self.probe(body)
        if not r["ok"] or not r["goals"]:
            return None
        N = r["goals"]
        k = 0
        if kind == "case":
            m = CASE_RE.match(st["text"])
            tag = m.group(2)
            if tag:
                hits = [i for i, g in enumerate(N) if g["tag"] and (g["tag"] == tag or g["tag"].endswith("." + tag))]
                if not hits and prev is not None:
                    oi = [i for i, g in enumerate(prev) if g["tag"] and (g["tag"] == tag or g["tag"].endswith("." + tag))]
                    ms = match_states(prev, N, rename, prefix=prefix) if oi else None
                    if ms is not None:
                        hits = [ms[0][oi[0]]]
                if not hits:
                    self.stats["notes"].append(f"step {st['line']}: case tag not found")
                    return None
                k = hits[0]
        var = []
        if k:
            var = ["  rotate_left" if k == 1 else f"  rotate_left {k}"]
        inner = inner_steps(st, kind)
        if inner and st["text"].split()[0] in ("case", "next", "·"):
            inner[-1]["_closing"] = True
        total = len(N)
        focus = any(MULTI_GOAL.match(s_["text"]) for s_ in inner)                                                                
        if focus:
            self.shift += 2
            try:
                body2, _rename_in, ok = self.run_block(inner, body + self.emit(var) + [" " * self.shift + "·"], dict(rename), rest_n=0, prefix=True)
            finally:
                self.shift -= 2
            self.note("case_focus" if kind == "case" else "bullet_focus", True)
        else:
            body2, _rename_in, ok = self.run_block(inner, body + self.emit(var), dict(rename), rest_n=total - 1, prefix=True)
            self.note("case_inline" if kind == "case" else "bullet_inline", True)
                                                                                                                         
        rename2 = dict(rename)
        O = self.orig_after(st)
        r2 = self.probe(body2)
        if O is not None and r2["goals"] is not None:
            m = match_states(O, r2["goals"], rename, prefix=prefix)
            if m is None:
                self.stats["notes"].append(f"step {st['line']} ({kind}): block end does not align")
                ok = False
            else:
                rename2 = m[1]
        return body2, rename2, ok

    def cases_with_block(self, st, body, rename, rest_n, prefix):
        m = CASES_WITH_RE.match(st["text"])
        alts = alternatives(st)
        var = self.emit([f"  {m.group(1)} {subst(m.group(2), rename)}"])
        r = self.probe(body + var)
        if not r["ok"] or r["goals"] is None:
            return None
        N = r["goals"]
        body2 = body + var
        ok = True
        by_tag = {tag: (names, steps) for tag, names, steps in alts}
        order = [g["tag"].split(".")[-1] if g["tag"] else None for g in N[:len(alts)]]
        for tag in order:
            if tag not in by_tag:
                return None
            names, steps = by_tag[tag]
            O = self.orig_states.get(self.trace_ids.get((id(st), tag)))
            r_now = self.probe(body2)
            rename_alt = dict(rename)                                            
            if O is not None and r_now["goals"]:
                mm = match_states(O, r_now["goals"], rename, prefix=True)
                if mm is not None:
                    rename_alt = mm[1]
                else:
                    self.stats["notes"].append(f"step {st['line']}: alternative does not align")
                    ok = False
            body2, _r, ok1 = self.run_block(steps, body2, rename_alt, rest_n=len(N) - 1, prefix=True)
            ok = ok and ok1
        self.note("cases_with_inline", True)
        return body2, dict(rename), ok

    def variants(self, st, rest, body, rename, kind):
        t = st["text"]
        V: list = []
        if kind == "exists":
            m = EXISTS_RE.match(t)
            wits = split_top(subst(m.group(2), rename))
            V.extend(self.exists_variants(body, wits, rename))
            return V
        if self.mode != "full":
            return V
        if kind == "intro":
            run = []
            for s in rest:
                if classify(s) == "intro" and not s["kids"]:
                    run.append(s)
                else:
                    break
            pats, total_names = [], 0
            for s in run:
                m = INTRO_RE.match(s["text"])
                toks = split_intro_args(m.group(2) or "")
                total_names += len(toks)
                for a in toks:
                    if a.startswith("(") or a.startswith("⟨"):
                        pats.append(a)
            if run and not pats:
                if total_names == 1 and len(run) == 1:
                    V.append(("intro", ["  intro"], 0))
                V.append(("intros", ["  intros"], len(run) - 1))
                V.append(("repeat_intro", ["  repeat' intro"], len(run) - 1))
            elif run and len(pats) == 1 and len(run) == 1:
                for tac in ("intros", "repeat' intro"):
                    name = self.pattern_hyp(body, run[0], tac)
                    if name:
                        V.append((f"{tac.split()[0]}_cases", [f"  {tac}", f"  cases {name}"], 0))
                        V.append((f"{tac.split()[0]}_obtain", [f"  {tac}", f"  obtain ⟨⟩ := {name}"], 0))
        elif kind == "rename_i":
            V.append(("drop_rename_i", [], 0))
        elif kind == "obtain":
            m = OBTAIN_RE.match(t) or RCASES_RE.match(t)
            pat, e = (m.group(1), m.group(2)) if OBTAIN_RE.match(t) else (m.group(2), m.group(1))
            e = subst(e, rename)
            depth = pat.count("⟨")
            if "|" in pat or depth <= 1:
                V.append(("cases_term", [f"  cases {e}"], 0))
            V.append(("obtain_nameless", [f"  obtain ⟨⟩ := {e}"], 0))
            V.append(("rcases_nameless", [f"  rcases {e} with ⟨⟩"], 0))
        elif kind == "atomic" and st["kids"] and re.match(r"^(all_goals|any_goals)\s*$", t):
            V.extend(self.shared_block_variants(st, rename))
        elif kind == "atomic" and "rename_i" in t and not st["kids"]:
            t2 = re.sub(r"\s*<;>\s*rename_i(?:\s+(?:" + NAME + r"|_))+", "", t)
            if t2 != t:
                V.append(("drop_rename_i_chain", ["  " + subst_line(t2, rename)], 0))
        return V

    def shared_block_variants(self, st, rename):
        kids = kid_steps(st["kids"])
        if not kids:
            return []
        m = re.match(r"^apply\s+(.+?)\s+at\s+(" + NAME + r")$", kids[0]["text"])
        if not m:
            return []
        F, X = m.group(1), m.group(2)
        lines = ["  " + st["text"], f"    have := {subst(F, rename)} ‹_›"]
        for k in kids[1:]:
            for ln in reindent(step_text(k), 4):
                lines.append(subst_line(ln, {**rename, X: "this"}))
        return [("shared_block_assumption", lines, 0)]

    def pattern_hyp(self, body, st, tac="intros"):
        m = INTRO_RE.match(st["text"])
        toks = split_intro_args(m.group(2) or "")
        idx = next(i for i, a in enumerate(toks) if a.startswith("(") or a.startswith("⟨"))
        r = self.probe(body + self.emit([f"  {tac}"]))
        if not r["ok"] or not r["goals"]:
            return None
        hyps = r["goals"][0]["hyps"]
        intro_hyps = hyps[-len(toks):] if len(hyps) >= len(toks) else hyps
        if len(intro_hyps) != len(toks):
            return None
        return intro_hyps[idx][0]

    def exists_variants(self, body, wits, rename):
        V = []
        explicit = [w for w in wits if w.strip() != "_"]
        for rule, base in (("repeat", ["  repeat' constructor"]), ("c1", ["  constructor"]), ("c2", ["  constructor", "  constructor"])):
            r = self.probe(body + self.emit(base))
            if not r["ok"] or r["goals"] is None:
                continue
            n = len(r["goals"])
            if not explicit:
                V.append((f"exists_{rule}", base, 0))
                continue
            if len(explicit) == 1:
                for k in range(min(n, 4)):
                    rot = [] if k == 0 else (["  rotate_left"] if k == 1 else [f"  rotate_left {k}"])
                    V.append((f"exists_{rule}_exact", base + rot + [f"  exact {explicit[0]}"], 0))
            elif len(explicit) == 2:
                for k in range(min(n, 4)):
                    rot = [] if k == 0 else (["  rotate_left"] if k == 1 else [f"  rotate_left {k}"])
                    for k2 in range(min(n, 3)):
                        rot2 = [] if k2 == 0 else (["  rotate_left"] if k2 == 1 else [f"  rotate_left {k2}"])
                        V.append((f"exists_{rule}_exact2", base + rot + [f"  exact {explicit[0]}"] + rot2 + [f"  exact {explicit[1]}"], 0))
        return V

    def transpile(self) -> dict:
        """{"body": logical lines, "lines": physical lines, "head": the head the lines compile under, "aligned", "final"}."""
        body, rename, aligned = self.run_block(self.steps, [], {}, rest_n=0, prefix=False)
        final = self.compiles(body)
        self.stats["oracle_calls"] = self.oracle.calls
        self.stats["oracle_seconds"] = round(self.oracle.seconds, 1)
        self.stats["hygienic_tail"] = self.switch is not None
        head = self.head if self.switch is None else self.oracle_o.head
        return {"body": body, "lines": self.layout(body), "head": head, "aligned": aligned, "final": final}


                                                                                                                                 
def inductive_constructors(prefix_text: str, name: str) -> list[tuple[str, int]]:
    """Constructors of `inductive name` in the row's file prefix with their number of explicit fields (library source only)."""
    m = re.search(r"inductive\s+" + re.escape(name) + r"\b.*?where\s*\n(.*?)(?=\n(?![|\s])|\n\s*\n|\Z)", prefix_text, re.S)
    if not m:
        return []
    out = []
    for ln in m.group(1).split("\n"):
        am = re.match(r"\s*\|\s*(" + NAME + r")\s*(?:\(.*?\))*\s*:\s*(.*)$", ln)
        if am:
            typ = am.group(2)
            depth, arrows = 0, 0
            for ch in typ:
                if ch in "(⟨[{":
                    depth += 1
                elif ch in ")⟩]}":
                    depth -= 1
                elif ch == "→" and depth == 0:
                    arrows += 1
            out.append((am.group(1), arrows))
    return out


def better(a: dict, b: dict) -> bool:
    if not a.get("closed"):
        return False
    if not b.get("closed") or b.get("score") is None or a.get("score") is None:
        return a.get("tokens") is not None and (b.get("tokens") is None or a["tokens"] < b["tokens"])
    return (round(a["score"], 6), -a["tokens"]) > (round(b["score"], 6), -b["tokens"])


DELETABLE = re.compile(r"^\s*(constructor|rfl|trivial|try\b.*|assumption|simp|exact\s+\S+)$")


def repair(oracle: Oracle, body: list[str], rounds: int = 4) -> tuple[list[str], dict]:
    """Bounded local repair after a structural change: delete deletable lines (closers, `constructor`, `try ..`) in the window of the two
"""
    n_head = oracle.head.count("\n")
    for _ in range(rounds):
        rc = oracle.compiles(body)
        if rc["closed"]:
            return body, rc
        own = [e for e in rc["errors"] if e[0] is not None and e[0] > n_head]
        if not own:
            return body, rc
        li = own[0][0] - n_head - 1
        if not (0 <= li < len(body)):
            return body, rc
        window = [k for k in range(max(0, li - 2), li + 1) if DELETABLE.match(body[k])]
        options = [[k] for k in reversed(window)] + [[a, b] for a in window for b in window if a < b]
        best, best_key = None, None
        for dele in options:
            cand = [ln for k, ln in enumerate(body) if k not in dele]
            r2 = oracle.compiles(cand)
            own2 = [e for e in r2["errors"] if e[0] is not None and e[0] > n_head]
            if r2["closed"]:
                return cand, r2
            if own2:
                moved = own2[0][0] - n_head - 1 + len(dele)
                key = (moved, -len(dele))
                if moved > li and (best_key is None or key > best_key):
                    best, best_key = cand, key
        if best is None:
            return body, rc
        body = best
    return body, oracle.compiles(body)


def choose_collapse_rewrite(body: list[str]):
    for i in range(len(body) - 1):
        m = re.match(r"^(\s*)(?:use|exists) (" + NAME + r")\.choose, \?_, \2\.choose_spec\.2$", body[i])
        if not m:
            continue
        E, ind = m.group(2), m.group(1)
        if body[i + 1].strip() == f"exact {E}.choose_spec.1":
            return body[:i] + [f"{ind}exact {E}"] + body[i + 2:]
        if i + 2 < len(body) and re.match(r"^\s*try apply (\S+)$", body[i + 1]) and body[i + 2].strip() == f"exact {E}.choose_spec.1":
            F = re.match(r"^\s*try apply (\S+)$", body[i + 1]).group(1)
            return body[:i] + [f"{ind}first | exact {E} | exact {E}.imp fun _ => And.imp_left {F}"] + body[i + 3:]
    return None


def exists_imp_pass(oracle: Oracle, body: list[str], prefix_text: str) -> tuple[list[str], dict]:
    """Before the first goal split, on a single goal `∃ x, A ∧ R .. x`: `apply Exists.imp; intro; exact And.imp_right .c` for a one-field

"""
    info = {"tried": 0, "kept": False, "points": 0}
    for i in range(1, min(len(body), MAX_IMP_SCAN)):
        r = oracle.run(body[:i])
        if not r["ok"] or not r["goals"] or len(r["goals"]) != 1:
            continue
        tgt = r["goals"][0]["target"]
        m = re.match(r"^∃ (" + NAME + r"), (.+?) ∧ (" + NAME + r") (.+)$", tgt)
        if not m:
            continue
        x, R = m.group(1), m.group(3)
        if not m.group(4).rstrip().endswith(x):
            continue
        info["points"] += 1
        cons = [c for c, k in inductive_constructors(prefix_text, R) if k == 1]
        if not cons:
            info["no_one_field_constructor"] = True
        for c in cons:
            info["tried"] += 1
            rest = [re.sub(r"\b" + re.escape(R) + r"\." + re.escape(c) + r"\s+", "", ln) for ln in body[i:]]
            rest = [re.sub(r"(?<![\w.])\." + re.escape(c) + r"\s+", "", ln) for ln in rest]
            cand0 = body[:i] + ["  apply Exists.imp", "  intro", f"  exact And.imp_right .{c}"] + rest                                                                                                                                                        
            best = None
            for variant in (cand0, choose_collapse_rewrite(cand0)):
                if variant is None:
                    continue
                cand, rc = repair(oracle, variant)
                if rc["closed"] and rc["tokens"] is not None and (best is None or rc["tokens"] < best[1]["tokens"]):
                    best = (cand, rc)
            if best is not None:
                cand2, _ = unshare_pass(oracle, best[0])
                rc2 = oracle.compiles(cand2)
                if rc2["closed"] and better(rc2, best[1]):
                    best = (cand2, rc2)
                r0 = oracle.compiles(body)
                if better(best[1], r0):
                    info.update(kept=True, at=i, tokens=best[1]["tokens"], heartbeats=best[1]["heartbeats"], score=best[1]["score"])
                    return best[0], info
        break
    return body, info


def unshare_pass(oracle: Oracle, body: list[str]) -> tuple[list[str], dict]:
    info = {"tried": 0, "kept": False}
    for i, ln in enumerate(body):
        if not re.match(r"^\s*(all_goals|any_goals)\s*$", ln):
            continue
        ind = len(ln) - len(ln.lstrip())
        j = i + 1
        while j < len(body) and (len(body[j]) - len(body[j].lstrip())) > ind:
            j += 1
        blk = body[i + 1:j]
        if not blk:
            continue
        fm = re.match(r"^\s*first \| (.+?) \| (.+)$", blk[-1])
        if not fm:
            continue
        A, B = fm.group(1), fm.group(2)
        for seq in ((A, B), (B, A)):
            info["tried"] += 1
            cand = body[:i] + ([ln] + blk[:-1] if blk[:-1] else []) + [" " * ind + seq[0], " " * ind + seq[1]] + body[j:]
            rc = oracle.compiles(cand)
            r0 = oracle.compiles(body)
            if better(rc, r0):
                info.update(kept=True, at=i, tokens=rc["tokens"], heartbeats=rc["heartbeats"], score=rc["score"])
                return cand, info
    return body, info


def choose_collapse_pass(oracle: Oracle, body: list[str]) -> tuple[list[str], dict]:
    info = {"tried": 0, "kept": False}
    cand = choose_collapse_rewrite(body)
    if cand is None:
        return body, info
    info["tried"] += 1
    cand, rc = repair(oracle, cand)
    r0 = oracle.compiles(body)
    if better(rc, r0):
        info.update(kept=True, tokens=rc["tokens"], heartbeats=rc["heartbeats"], score=rc["score"])
        return cand, info
    return body, info


                                                                                                                                
def _err_class_text(e: str) -> str:
    e = (e or "").lower()
    for k, lab in (("unknown identifier", "unknown_ident"), ("unknown constant", "unknown_ident"), ("unsolved goals", "unsolved"),
                   ("type mismatch", "type_mismatch"), ("failed to unify", "unify"), ("could not unify", "unify"),
                   ("timeout", "timeout"), ("heartbeats", "heartbeats"), ("unexpected token", "syntax"), ("expected", "syntax"),
                   ("no goals", "no_goals"), ("failed to synthesize", "synth"), ("deadline", "deadline"), ("readings", "budget")):
        if k in e:
            return lab
    return "other"


def split_body(decl: str, statement: str):
    """(head ending in `:= by\\n`, body lines at indent 2) of a tactic-block declaration, or (None, reason)."""
    body = split_declaration(decl, statement)
    if body is None:
        return None, "statement not found in the declaration"
    head = decl[:len(decl) - len(body)]
    b = body.lstrip()
    if b.startswith(":="):
        b = b[2:]
    elif head.rstrip().endswith(":="):
        head = head.rstrip()[:-2].rstrip()
    else:
        return None, "no `:=`"
    s = b.lstrip()
    if not (s.startswith("by") and (len(s) == 2 or s[2].isspace())):
        return None, "term-mode body"
    rest = s[2:]
    lines = rest.split("\n")
    first = lines[0].strip()
    tail = [ln for ln in lines[1:]]
    if first:                                                                         
        ind = min((len(l) - len(l.lstrip()) for l in tail if l.strip()), default=2)
        tail = [" " * ind + first] + tail
    body_lines = [ln.rstrip() for ln in tail]
    while body_lines and not body_lines[-1].strip():
        body_lines.pop()
    if not body_lines:
        return None, "empty block"
    base = min(len(l) - len(l.lstrip()) for l in body_lines if l.strip())
    out = []
    for ln in body_lines:
        if not ln.strip():
            continue
        out.append(" " * (2 + len(ln) - len(ln.lstrip()) - base) + ln.lstrip())
    if len(out) > MAX_BODY_LINES:
        return None, "body too long"
    head = head.rstrip() + " := by\n"
    return head, out


def _count_sites(steps: list[dict], acc: dict, exists_text: list) -> None:
    for st in steps:
        kind = classify(st)
        t = st["text"]
        if kind in ("intro",):
            m = INTRO_RE.match(t)
            if (m.group(2) or "").strip():                                                     
                acc["intro"] = acc.get("intro", 0) + 1
        elif kind in ("rename_i", "obtain", "exists", "cases_with"):
            acc[kind] = acc.get(kind, 0) + 1
            if kind == "exists":
                exists_text.append(t)
        elif kind in ("case", "bullet"):
            acc[kind] = acc.get(kind, 0) + 1
            _count_sites(inner_steps(st, kind), acc, exists_text)
            continue
        elif kind == "atomic":
            if st["kids"] and re.match(r"^(all_goals|any_goals)\s*$", t):
                ks = kid_steps(st["kids"])
                if ks and re.match(r"^apply\s+(.+?)\s+at\s+(" + NAME + r")$", ks[0]["text"]):
                    acc["shared"] = acc.get("shared", 0) + 1
            if "rename_i" in t and not st["kids"]:
                acc["rename_i_chain"] = acc.get("rename_i_chain", 0) + 1
        if kind == "cases_with" and alternatives(st):
            for _tag, _names, body in alternatives(st):
                _count_sites(body, acc, exists_text)


def sites(proof: str, statement: str) -> dict:
    """{"fire", "why", "sites": {kind: count}, "exists": [...], "has_exists_goal": the statement's conclusion has ∃, "lines"}; no Lean."""
    head, body = split_body(proof, statement)
    if head is None:
        return {"fire": False, "why": body, "sites": {}}
    try:
        steps = parse_block(body, 0, 2)[0]
        acc: dict = {}
        ex: list = []
        _count_sites(steps, acc, ex)                                                                                    
    except ValueError:
        return {"fire": False, "why": "parse error (indentation)", "sites": {}, "lines": len(body)}
    has_ex = "∃" in statement or "∃" in proof or "Exists" in statement or "Exists" in proof
    out = {"sites": acc, "exists": ex, "has_exists_goal": has_ex, "lines": len(body), "steps": len(steps)}
    if not acc and not has_ex:
        out.update(fire=False, why="no site (no named intro / rename_i / case tag / obtain pattern / exists / ∃)")
        return out
    out.update(fire=True, why=None)
    return out


def search_precheck(proof: str, statement: str) -> str | None:
    """The end stage's lazy workbench start (harness/endstage.py, module docstring "speed"): the reason search() stops before any workbench
"""
    info = sites(proof, statement)
    return None if info.get("fire") else (info.get("why") or "no site")


def _timeout(ctx: dict | None) -> float:
    cs = (ctx or {}).get("compile_s")
    return max(MIN_TIMEOUT_S, TIMEOUT_MULT * float(cs) + 4.0) if isinstance(cs, (int, float)) else MIN_TIMEOUT_S * 3


def _prefix_text(wb, ctx: dict | None) -> str:
    """The row's library file prefix (constructors of the row's inductives for the Exists.imp rule); "" when unavailable."""
    if ctx and isinstance(ctx.get("prefix_text"), str):
        return ctx["prefix_text"]
    row = getattr(wb, "row", None)
    if not isinstance(row, dict):
        return ""
    try:
        from scorer import compile as C
        return C.file_prefix(row, getattr(wb, "version", None) or list(row["version_info"][0])[0]) or ""
    except Exception:                
        return ""


def strip_unhygienic(head: str, lines: list[str], uh_head: str, orig_head: str):
    """The lines without their `unhygienic` (the head's, or a scoped `  unhygienic` block de-indented); None when there is none."""
    if head == uh_head:
        return list(lines)
    if lines and lines[0] == "  unhygienic":
        out, i = [], 1
        while i < len(lines) and lines[i].startswith("    "):
            out.append(lines[i][2:])
            i += 1
        return out + lines[i:]
    return None


def _stage(stats: dict, name: str, t0: float, rc: dict | None, extra: dict | None = None) -> None:
    rec = {"seconds": round(time.time() - t0, 2)}
    if rc is not None:
        rec.update(closed=bool(rc.get("closed")), tokens=rc.get("tokens"), heartbeats=rc.get("heartbeats"))
        if not rc.get("closed") and rc.get("errors"):
            rec["error"] = _err_class_text(rc["errors"][0][1])
    if extra:
        rec.update(extra)
    stats.setdefault("stages", {})[name] = rec


def search(proof: str, statement: str, wb, *, meter_reading: dict | None = None, exchange=None, ctx: dict | None = None,
           stats: dict | None = None, log=None, deadline: float | None = None, max_checks: int = MAX_CHECKS, n_out: int = N_OUT,
           stage_caps: dict | None = None, trace: list | None = None) -> dict:
    """The t5 contract: {"t6_found": [{"op", "decl", "note", "est"}], "t6_found_for": proof_key(proof)}, survivors by estimate."""
    t0 = time.time()
    st = stats if stats is not None else {}
    log = log or (lambda *a: None)
    for k_, v_ in (("sites", {}), ("variants", 0), ("readings", 0), ("compiled", 0), ("survivors", 0), ("skips", {}), ("errors", {}),
                   ("budget_out", False), ("searches", 0), ("rules", {}), ("fallbacks", 0)):
        st.setdefault(k_, v_ if not isinstance(v_, dict) else dict(v_))
    st["searches"] += 1

    def skip(why):
        st["skips"][why] = st["skips"].get(why, 0) + 1
        st["seconds"] = round(time.time() - t0, 2)
        log(f"t6: skipped ({why})")
        return {}

    info = sites(proof, statement)
    if not info.get("fire"):
        return skip(info.get("why") or "?")
    for k_, v_ in info["sites"].items():
        st["sites"][k_] = st["sites"].get(k_, 0) + v_
    head, body = split_body(proof, statement)
    orig_head = head
    uh_head = head[:-len(":= by\n")] + ":= by unhygienic\n"
    dl = deadline if deadline is not None else time.time() + SEARCH_SECONDS
    budget = [max_checks]
    to = _timeout(ctx)
    cands: list[dict] = []                                               
    full_mode = bool(info["sites"])
    oracle = Oracle(wb, uh_head, log, deadline=dl, budget=budget, timeout=to)
    oracle_o = Oracle(wb, orig_head, log, deadline=dl, budget=budget, timeout=to)
    prefix_text = None
    stepwise_body = None
    try:
                                                                                              
        if full_mode:
            t1 = time.time()
            T = Transpiler(uh_head, body, oracle, log, orig_head=orig_head, mode="full", oracle_o=oracle_o)
            st["orig_traced_ok"] = T.orig_ok
            res = T.transpile()
            if T.switch is not None:
                st["hygienic_tail"] = st.get("hygienic_tail", 0) + 1
            for r_, d_ in T.stats["rules"].items():
                R = st["rules"].setdefault(r_, {"tried": 0, "used": 0})
                R["tried"] += d_["tried"]
                R["used"] += d_["used"]
            st["fallbacks"] += T.stats["fallbacks"]
            st["aligned"] = res["aligned"]
            st["unaligned_steps"] = len(T.stats["notes"])
            unchanged = res["body"] == body
            _stage(st, "transpile", t1, res["final"], {"aligned": res["aligned"], "steps": T.stats["steps"], "unchanged": unchanged,
                                                       "hygienic_tail": T.switch is not None})
            if res["final"]["closed"] and unchanged:
                st["skips"]["transpile: nothing dropped"] = st["skips"].get("transpile: nothing dropped", 0) + 1
            elif res["final"]["closed"]:
                t_head, t_lines = res["head"], res["lines"]
                t_oracle = oracle if T.switch is None else oracle_o
                stepwise_body = t_lines
                cands.append({"op": "t6:transpile", "head": t_head, "body": t_lines, "note": "nameless transpile"
                              + (" (hygienic tail)" if T.switch is not None else "")})
                t2 = time.time()
                body2 = list(t_lines)
                prefix_text = _prefix_text(wb, ctx)
                p_imp = p_ch = p_un = {"kept": False}
                if T.switch is None:                                                                                           
                    if info["has_exists_goal"]:
                        body2, p_imp = exists_imp_pass(t_oracle, body2, prefix_text)
                    body2, p_ch = choose_collapse_pass(t_oracle, body2)
                    body2, p_un = unshare_pass(t_oracle, body2)
                else:
                    st["skips"]["post-passes: hygienic tail layout"] = st["skips"].get("post-passes: hygienic tail layout", 0) + 1
                rc = t_oracle.compiles(body2)
                kept = [n for n, p in (("exists_imp", p_imp), ("choose", p_ch), ("unshare", p_un)) if p.get("kept")]
                _stage(st, "joint", t2, rc, {"post_passes_kept": kept, "exists_imp_points": p_imp.get("points", 0),
                                              "exists_imp_tried": p_imp.get("tried", 0)})
                if rc["closed"] and body2 != t_lines:
                    cands.insert(0, {"op": "t6:joint", "head": t_head, "body": body2, "note": "transpile + " + "+".join(kept)})
                elif rc["closed"]:
                    cands[0]["note"] = cands[0]["note"] + " (joint: no post-pass applied)"
                    cands[0]["op"] = "t6:joint"
                                                                                                             
                for c in list(cands):
                    plain = strip_unhygienic(c["head"], c["body"], uh_head, orig_head)
                    if plain is not None:
                        rh = oracle_o.compiles(plain)
                        if rh["closed"]:
                            c["head"], c["body"], c["note"] = orig_head, plain, c["note"] + " (no unhygienic)"
                            st["no_unhygienic"] = st.get("no_unhygienic", 0) + 1
                                                                   
        if info["sites"].get("exists"):
            t3 = time.time()
            Tx = Transpiler(orig_head, body, oracle_o, log, orig_head=orig_head, mode="exists")
            rx = Tx.transpile()
            used = {r_: d_ for r_, d_ in Tx.stats["rules"].items() if d_["used"] and r_.startswith("exists_")}
            _stage(st, "exists", t3, rx["final"], {"exists_rules_used": sorted(used)})
            if rx["final"]["closed"] and used and rx["body"] != body:
                cands.append({"op": "t6:exists", "head": orig_head, "body": rx["body"], "note": "exists -> constructor"})
                                                             
        if info["has_exists_goal"]:
            t4 = time.time()
            if prefix_text is None:
                prefix_text = _prefix_text(wb, ctx)
            b3, p3 = exists_imp_pass(oracle_o, list(body), prefix_text)
            b3, p3c = choose_collapse_pass(oracle_o, b3)
            rc3 = oracle_o.compiles(b3) if (p3.get("kept") or p3c.get("kept")) else None
            _stage(st, "exists_imp", t4, rc3, {"points": p3.get("points", 0), "tried": p3.get("tried", 0), "kept": bool(p3.get("kept")),
                                                 "choose_kept": bool(p3c.get("kept"))})
            if rc3 is not None and rc3["closed"]:
                cands.append({"op": "t6:exists_imp", "head": orig_head, "body": b3, "note": "Exists.imp pre-shaping"})
    except _Budget as e:
        st["budget_out"] = True
        st["errors"]["budget"] = st["errors"].get("budget", 0) + 1
        log(f"t6: budget out ({e}) after {oracle.calls + oracle_o.calls} oracle readings")
    for o in (oracle, oracle_o):
        for k_, v_ in o.errors.items():
            st["errors"][k_] = st["errors"].get(k_, 0) + v_
    st["oracle_calls"] = oracle.calls + oracle_o.calls
    st["oracle_seconds"] = round(oracle.seconds + oracle_o.seconds, 2)
    st["readings"] += oracle.calls + oracle_o.calls
                                                        
    seen, uniq = set(), []
    for c in cands:
        d = c["head"] + "\n".join(c["body"])
        if d.strip() == proof.strip() or d in seen:
            continue
        seen.add(d)
        uniq.append(dict(c, decl=d))
    st["variants"] += len(uniq)
    if not uniq:
        if not st["budget_out"]:
            st["skips"]["no compiling candidate"] = st["skips"].get("no compiling candidate", 0) + 1
        st["peak_rss_mb"] = getattr(wb, "peak_rss_mb", None)
        st["seconds"] = round(time.time() - t0, 2)
        log(f"t6: no candidate ({st['oracle_calls']} oracle readings, {st['seconds']} s)")
        return {"t6_found": [], "t6_found_for": proof_key(proof)}
                                                                                         
    from harness.tools import famkit as K
    scr = K.Screen(wb, proof, meter_reading=meter_reading, deadline=dl, max_checks=max(len(uniq), budget[0]), timeout=to, log=log)
    rs = scr.read([c["decl"] for c in uniq])
    by = {c["decl"]: c for c in uniq}
    found = []
    for r in rs:
        c = by[r["decl"]]
        if trace is not None:
            trace.append({"op": c["op"], "src": c["note"], "status": r.get("status"), "error": str(r.get("error") or "")[:160],
                          "d_score": r.get("d_score"), "tokens": r.get("tokens")})
        st.setdefault("screened", []).append({"op": c["op"], "status": r.get("status"), "d_score": r.get("d_score"), "tokens": r.get("tokens"),
                                              "hb_est": r.get("heartbeats_est")})
        if r.get("status") == "ok" and (r.get("d_score") or 0) > BAR:
            found.append({"op": c["op"], "decl": c["decl"], "note": c["note"] + f"; est {r['d_score']:+.3f}", "est": r["d_score"],
                          "tokens": r.get("tokens"), "heartbeats_est": r.get("heartbeats_est")})
    order = {op: i for i, op in enumerate(OPS)}
    found.sort(key=lambda c: (order.get(c["op"], 9), -c["est"]))                                                                             
    for k_ in ("compiled", "timeouts", "calls"):
        st[k_] = st.get(k_, 0) + scr.stats[k_]
    st["budget_out"] = st["budget_out"] or scr.stats["budget_out"]
    st["readings"] += scr.stats["readings"]
    for k_, v_ in scr.stats["errors"].items():
        st["errors"][k_] = st["errors"].get(k_, 0) + v_
    st["survivors"] += len(found)
    st["wb_seconds"] = round(st.get("wb_seconds", 0.0) + scr.stats["seconds"] + st["oracle_seconds"], 2)
    st["peak_rss_mb"] = getattr(wb, "peak_rss_mb", None)
    st["seconds"] = round(time.time() - t0, 2)
    log(f"t6: {len(found)} survivor(s) of {len(uniq)} candidate(s) [{', '.join(c['op'] for c in uniq)}], {st['oracle_calls']} oracle "
        f"readings, {st['seconds']} s")
    return {"t6_found": found[:n_out], "t6_found_for": proof_key(proof)}


def candidates(proof: str, statement: str, *, exchange: float | None = None, max_per_op: int = N_OUT, ctx: dict | None = None) -> list[dict]:
    """[{"op", "decl", "note"}]: the search's survivors (ctx["t6_found"] for this proof). Without a workbench nothing is proposed: every
"""
    ctx = ctx or {}
    if ctx.get("t6_found_for") == proof_key(proof) and isinstance(ctx.get("t6_found"), list):
        out = []
        for c in ctx["t6_found"][:max_per_op]:
            if isinstance(c, dict) and isinstance(c.get("decl"), str) and c["decl"].strip() != proof.strip():
                out.append({"op": c.get("op") or "t6:joint", "decl": c["decl"], "note": str(c.get("note") or "")[:300]})
        return out
    return []


def explain(proof: str, statement: str, ctx: dict | None = None) -> dict:
    """Coverage diagnosis without Lean: the sites per rule kind (or the skip reason) and which candidate kinds the search would try."""
    info = sites(proof, statement)
    kinds = []
    if info.get("fire"):
        if info["sites"]:
            kinds += ["t6:joint", "t6:transpile"]
        if info["sites"].get("exists"):
            kinds.append("t6:exists")
        if info.get("has_exists_goal"):
            kinds.append("t6:exists_imp")
    return {"ok": True, "fire": bool(info.get("fire")), "why": info.get("why"), "sites": info.get("sites") or {},
            "n_sites": sum((info.get("sites") or {}).values()), "has_exists_goal": info.get("has_exists_goal"),
            "lines": info.get("lines"), "would_try": kinds}
