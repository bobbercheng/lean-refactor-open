#!/usr/bin/env python3
"""Batch screening for the end stage's tool families (docs/tools_build_plan.md, round R2).



















































"""
from __future__ import annotations

import hashlib, math, re, time
from dataclasses import dataclass, field

SCREEN_K = 24                                
MAX_DEPTH = 2                                                                              
TARGET_S = 600                                                                              
SUFFIX = "_lra_scr"
MARK = "LRA_SCREEN"
_MARK_RE = re.compile(r"^" + MARK + r" (\d+)$")

_DECL_KW = re.compile(r"(?:^|(?<=[\s\]]))(theorem|lemma|def|abbrev|instance|example)\b")
_DECL_NAME = re.compile(r"\s+((?:«[^»]*»|[^\s(){}\[\]⦃:,«])+)")
_INST_PRIO = re.compile(r"\s*\(\s*priority\s*:=[^)]*\)")
_ID_BEFORE = r"(?<![\w'!?.])"                                                                                 
_ID_AFTER = r"(?![\w'!?])"
_IN_LINE = re.compile(r"[ \t]*(?:omit|include|unseal|variable|set_option|open)\b[^\n]*\bin[ \t]*$")


def sha(text: str) -> str:
    """The end stage's candidate hash (harness/endstage.sha)."""
    return hashlib.sha256(text.strip().encode()).hexdigest()[:16]


                                                                                                                                     
def mask(text: str, attrs: list | None = None) -> str:
    """`text` with comments (`--` lines, nested `/- -/` blocks, docstrings), string literals and `@[...]` attribute lists replaced by

"""
    out, i, n = list(text), 0, len(text)

    def blank(a, b):
        for j in range(a, b):
            if out[j] != "\n":
                out[j] = " "
    while i < n:
        c = text[i]
        if text.startswith("--", i):
            j = text.find("\n", i)
            j = n if j < 0 else j
            blank(i, j); i = j
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j):
                    depth += 1; j += 2
                elif text.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            blank(i, j); i = j
        elif c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(n, j + 1)
            blank(i, j); i = j
        elif text.startswith("@[", i):
            depth, j = 0, i + 1
            while j < n:
                depth += {"[": 1, "]": -1}.get(text[j], 0)
                j += 1
                if depth == 0:
                    break
            blank(i, j)
            if attrs is not None:
                attrs.append((i, j))
            i = j
        else:
            i += 1
    return "".join(out)


def declared(statement: str) -> list[tuple[str, str | None, int]]:
    """(keyword, name as written or None, position of the name) for each declaration keyword of `statement` (comments, strings and
"""
    s, out = mask(statement), []
    for k in _DECL_KW.finditer(s):
        kw, pos = k.group(1), k.end()
        if kw == "example":
            out.append((kw, None, pos)); continue
        if kw == "instance":
            pm = _INST_PRIO.match(s, pos)
            pos = pm.end() if pm else pos
        m = _DECL_NAME.match(s, pos)
        name = (m.group(1).rstrip(".") or None) if m else None
        out.append((kw, name, m.start(1) if m else pos))
    return out


def attr_spans(text: str) -> list[tuple[int, int]]:
    """(start, end) of every `@[...]` attribute list of `text` outside comments and strings."""
    spans: list = []
    mask(text, spans)
    return spans


def drop_attrs(text: str, spans=None) -> str:
    """`text` with the given attribute lists (default: all of them) blanked to spaces, newlines kept; a line left blank is emptied."""
    spans = attr_spans(text) if spans is None else spans
    if not spans:
        return text
    out = list(text)
    for a, b in spans:
        for j in range(a, b):
            if out[j] != "\n":
                out[j] = " "
    lines = "".join(out).split("\n")
    touched = {k for a, b in spans for k in range(text.count("\n", 0, a), text.count("\n", 0, b) + 1)}
    return "\n".join("" if i in touched and not l.strip() else l for i, l in enumerate(lines))


def screen_statement(statement: str) -> tuple[str | None, str | None]:
    """(the statement as every copy writes it, why not screenable): the attribute lists of its LAST declaration (the one the

"""
    m = mask(statement)
    kws = [k.start(1) for k in _DECL_KW.finditer(m)]
    if any(kw == "instance" and n is not None for kw, n, _ in declared(statement)):
        return None, "the statement declares an instance (every copy's instance would be in scope for the copies after it)"
    spans = attr_spans(statement)
    if not spans:
        return statement, None
    last = kws[-1] if kws else len(statement)
    prev = kws[-2] if len(kws) > 1 else -1                                                                         
    if any(b <= prev for _, b in spans):
        return None, "an attribute on an earlier declaration of the statement (dropping it could change the candidate, keeping it leaks)"
    return drop_attrs(statement, [(a, b) for a, b in spans if b <= last]), None


def _suffixed(name: str, suffix: str) -> str:
    return name[:-1] + suffix + "»" if name.endswith("»") else name + suffix


def rename_copy(decl: str, statement: str, suffix: str) -> str | None:
    """`decl` (which starts with `statement`) with every name the statement declares renamed `<name><suffix>`: each whole-identifier



"""
    if not decl.startswith(statement):
        return None
    decls = declared(statement)
    if any(kw != "example" and n is None for kw, n, _ in decls):
        return None
    names = [n for kw, n, _ in decls if n]
    if not names:
        return decl                                                       
    pats = []
    for n in dict.fromkeys(names):
        pats.append(n)
        last = n.rsplit(".", 1)[-1] if "." in n and not n.startswith("«") else None
        if last and len(last) >= 3 and last not in names:
            pats.append(last)
    m = mask(decl)
    hits = []
    for p in sorted(dict.fromkeys(pats), key=len, reverse=True):                                    
        for h in re.finditer(_ID_BEFORE + re.escape(p) + _ID_AFTER, m):
            if not any(a < h.end() and h.start() < b for a, b, _ in hits):
                hits.append((h.start(), h.end(), p))
    heads = {pos for kw, n, pos in decls if n}
    if not heads <= {a for a, _, _ in hits}:
        return None
    out = decl
    for a, b, p in sorted(hits, reverse=True):
        out = out[:a] + _suffixed(decl[a:b], suffix) + out[b:]
    return out


def strip_in_tail(core: str) -> tuple[str, list[str]]:
    """(core without its trailing `… in` combinator lines, those lines in order); comment-only and blank lines between them go too."""
    lines, tail = core.split("\n"), []
    ml = mask(core).split("\n")
    i = len(lines)
    while i > 0:
        t = ml[i - 1]
        if not t.strip():
            i -= 1
            continue
        if _IN_LINE.match(t):
            tail.insert(0, lines[i - 1].rstrip())
            i -= 1
            continue
        break
    if not tail:
        return core, []
    return "\n".join(lines[:i]) + "\n", tail


def hb_bound(metrics, reading: dict | None) -> int | None:
    """The `maxHeartbeats` value of the screen (module docstring, "bound"), from the meter's metrics(tokens, heartbeats, Z) -> {L, H,
"""
    try:
        target = 3.0 * float(reading["score_exact"])
        m0, m1 = metrics(0, 0, 100.0), metrics(0, 10 ** 6, 100.0)
        slope = (float(m0["H"]) - float(m1["H"])) / 10 ** 6                                                   
        if not slope > 0 or not math.isfinite(slope):
            return None
        L0 = float(m0["L"])
        h = (float(m0["H"]) - (target - L0 - 100.0)) / slope
        h = max(h, float(reading.get("heartbeats") or 0))
        return int(math.ceil(2 * h)) + 1000 if math.isfinite(h) else None
    except (TypeError, KeyError, ValueError, ZeroDivisionError):
        return None


                                                                                                                                     
@dataclass
class Layout:
    """The shared part of a batch file on one pin: `head` (header or file prefix + blank line), the `… in` lines repeated before every copy,
"""
    version: str
    head: str
    in_lines: list = field(default_factory=list)
    modifiers: str = ""
    lean_args: tuple = ()
    quiet: bool = False

    @property
    def first_line(self) -> int:
        return self.head.count("\n") + 1


def layout(row: dict, version: str) -> Layout:
    """The batch layout of `row` on `version` (raises when the project file or environment is missing)."""
    from scorer import compile as C
    if row["source"] == "putnambench":
        return Layout(version, row["header"].rstrip() + "\n\n")
    core, modifiers = C.split_modifiers(C.file_prefix(row, version))
    attach = bool(C._ATTACHED_IN.search(core))
    core2, tail = strip_in_tail(core)
    lean_args, quiet = C.lakefile_options(row["source"], version), False
    if C.force_warn_sorry() and C._warn_sorry_off(lean_args):
        lean_args, quiet = C._with_warn_sorry(lean_args), True
    return Layout(version, core2.rstrip("\n") + "\n\n", tail if attach else [], modifiers, tuple(lean_args), quiet)


def block(renamed: str, L: Layout, idx: int, hb_cap: int | None) -> tuple[str, int]:
    """(copy idx's text, the 0-based line of its marker within it); the modifiers' attribute lists are dropped (module docstring,
"""
    pre = "".join(l + "\n" for l in L.in_lines)
    if hb_cap:
        pre += f"set_option maxHeartbeats {int(hb_cap)} in\n"
    pre += "set_option Elab.async false in\n"
    text = pre + drop_attrs(L.modifiers) + renamed.rstrip() + "\n\n"
    return text + f'#print "{MARK} {idx}"\n\n', text.count("\n")


def build(texts: list[str], statement: str, L: Layout, hb_cap: int | None):
    """(body, copies, spans): the batch file, its copies part, and per text (first line, marker line), 1-based file lines; a text that
"""
    blocks, spans = [], []
    line = L.first_line
    st2, _ = screen_statement(statement)
    for i, t in enumerate(texts):
        t = t.strip()
        r = None
        if st2 is not None and t.startswith(statement):
            r = rename_copy(st2 + t[len(statement):], st2, f"{SUFFIX}{i}")
        if r is None:
            spans.append(None)
            continue
        b, mk = block(r, L, i, hb_cap)
        spans.append((line, line + mk))
        line += b.count("\n")
        blocks.append(b)
    copies = "".join(blocks).rstrip() + "\n"
    return L.head + copies, copies, spans


def verdicts(res, spans: list, first_line: int) -> tuple[dict, str | None]:
    """({index: (verdict, error)}, inconclusive kind or None) from a finished batch compile (scorer.compile.CompileResult or alike:

"""
    from scorer.compile import _is_sorry_msg
    if getattr(res, "timed_out", False):
        return {}, "timeout"
    marks, bad = set(), []
    for m in getattr(res, "messages", None) or []:
        line = (m.get("pos") or {}).get("line") or 0
        data = str(m.get("data", ""))
        sev = m.get("severity")
        mm = _MARK_RE.match(data.strip())
        if sev == "information" and mm:
            marks.add(int(mm.group(1)))
            continue
        if sev == "error" or (_is_sorry_msg(m) and line >= first_line):
            bad.append((line, data, m.get("kind")))
    if any(l < first_line for l, _, _ in bad):
        e = next(d for l, d, _ in bad if l < first_line)
        return {}, "env: " + e[:200]
    if not bad and not getattr(res, "ok", False):                                                                    
        return {}, "crash: " + str((getattr(res, "errors", None) or ["?"])[0])[:200]
    out, prev = {}, None
    for i, sp in enumerate(spans):
        if sp is None:
            continue
        s, mk = sp
        clean = prev is None or prev in marks
        errs = [(l, d, k) for l, d, k in bad if s <= l < mk]
        if not clean:
            out[i] = ("unknown", "the previous copy did not end at its marker")
        elif errs:
            l, d, k = errs[0]
            hb = k == "runtime.maxHeartbeats" or "maximum number of heartbeats" in d
            out[i] = ("hb_bound" if hb else "fail", f"{l - s + 1}: {d}"[:300])
        elif i in marks:
            out[i] = ("pass", None)
        else:
            out[i] = ("unknown", "its marker did not print")
        prev = i
    return out, None


                                                                                                                                     
class BatchScreener:
    """One row's screen on one pin. screen(items, need=, charge=, hb_cap=, compile_s=) -> {key: verdict dict}; verdict dict:


"""

    def __init__(self, row: dict, compile_fn, *, version: str | None = None, timeout: int = 900, k: int = SCREEN_K,
                 max_depth: int = MAX_DEPTH, cache: dict | None = None, log=None, layout_fn=None):
        self.row, self.statement = row, row["statement"]
        self.version = version
        self.compile_fn, self.timeout = compile_fn, int(timeout)
        self.k, self.max_depth = max(1, int(k)), max(0, int(max_depth))
        self.cache = cache if cache is not None else {}
        self.log = log or (lambda m: None)
        self._layout_fn = layout_fn or layout
        self._layout = None
        self._layout_err = None
        self.stats = {"batches": 0, "compiles": 0, "seconds": 0.0, "splits": 0, "inconclusive": 0, "copies": 0, "leaks": 0}
        self.broken = None                                                                
        self._stmt_why = screen_statement(self.statement)[1]                                                                       

    def _lay(self):
        if self._layout is None and self._layout_err is None:
            try:
                self._layout = self._layout_fn(self.row, self.version)
            except Exception as e:                                                                    
                self._layout_err = f"{type(e).__name__}: {e}"[:200]
        return self._layout

    def screenable(self, text: str) -> str | None:
        """None when `text` can go into a batch, else why not (it then goes to the measurement unscreened)."""
        from scorer.compile import SORRY_SWITCH_RE
        from scorer.forbidden import check_forbidden, strip_lean_comments
        from scorer.tokenize import split_declaration
        body = split_declaration(text, self.statement)
        if body is None:
            return "statement differs"
        if self._stmt_why:
            return self._stmt_why
        if check_forbidden(body):
            return "forbidden"
        if SORRY_SWITCH_RE.search(strip_lean_comments(body)):
            return "names a sorry-warning switch"
        if attr_spans(body):
            return "an attribute list inside the proof (it would act on the copies after it)"
        if rename_copy(text, self.statement, SUFFIX + "0") is None:
            return "the declared name cannot be renamed (anonymous instance)"
        return None

    def _modifiers_why(self, L: Layout) -> str | None:
        """The layout's modifiers attach to the statement's first declaration: their attribute lists can be dropped only when that is
"""
        if attr_spans(L.modifiers) and len(declared(self.statement)) > 1:
            return "an attribute on an earlier declaration of the statement (the declaration's modifiers)"
        return None

    def batch_size(self, compile_s: float | None) -> int:
        """Candidates per batch: K, and TARGET_S / compile time less the two control copies (module docstring, "size")."""
        cs = float(compile_s) if isinstance(compile_s, (int, float)) and compile_s > 0 else 60.0
        return max(2, min(self.k, int(TARGET_S // cs) - 2))

    def batch_timeout(self, items: list[dict], compile_s: float | None, extra: int = 0) -> int:
        cs = float(compile_s) if isinstance(compile_s, (int, float)) and compile_s > 0 else 60.0
        allow = cs * extra
        for it in items:
            to = it.get("timeout_s")
            allow += min(float(to), cs) if isinstance(to, (int, float)) and to > 0 else cs
        return int(max(1, min(self.timeout, math.ceil(cs + allow) + 30)))

    def screen(self, items: list[dict], *, need=None, charge=None, hb_cap: int | None = None, compile_s: float | None = None,
               control: str | None = None) -> dict:
        """items: [{"key", "text", "timeout_s"?}] (key: the candidate hash). Verdicts are cached by key. control: a declaration that
"""
        out, todo = {}, []
        if control is not None and self.screenable(control) is not None:
            control = None
        for it in items:
            key = it["key"]
            if key in self.cache:
                out[key] = dict(self.cache[key], cached=True)
                continue
            why = self.screenable(it["text"]) if self.broken is None else f"screening stopped on this row: {self.broken}"
            if why is None and self._lay() is None:
                why = f"no layout: {self._layout_err}"
            if why is None:
                why = self._modifiers_why(self._layout)
            if why is not None:
                out[key] = {"verdict": "unscreened", "error": why}
                continue
            if any(t["key"] == key for t in todo):
                continue
            todo.append(it)
        kb = self.batch_size(compile_s)
        queue = [(todo[i:i + kb], 0) for i in range(0, len(todo), kb)]
        while queue:
            batch, depth = queue.pop(0)
            if self.broken is not None:
                for it in batch:
                    out[it["key"]] = {"verdict": "unscreened", "error": f"screening stopped on this row: {self.broken}"}
                continue
            if need:
                need(1)
            L = self._lay()
            off = 1 if control is not None else 0
            tail = len(batch) + 1 if off else None                                                    
            texts = ([control] if off else []) + [it["text"] for it in batch] + ([control] if off else [])
            body, copies, spans = build(texts, self.statement, L, hb_cap)
            to = self.batch_timeout(batch, compile_s, extra=2 * off)
            t0 = time.time()
            res, n = self.compile_fn(body, copies, L, to)
            secs = time.time() - t0
            if charge:
                charge(int(n))
            self.stats["batches"] += 1
            self.stats["compiles"] += int(n)
            self.stats["seconds"] += secs
            self.stats["copies"] += len(batch)
            got, inc = verdicts(res, spans, L.first_line)
            if inc is None and off:
                cv, cerr = got.get(0, ("unknown", "not in the file"))
                if cv != "pass":                                                                                                      
                    self.broken = f"the incumbent's own copy is {cv} in the batch file ({str(cerr)[:160]})"
                    self.stats["broken"] = self.broken
                    inc = "env: " + self.broken
                else:
                    tv, terr = got.get(tail, ("unknown", "not in the file"))
                    if tv in ("fail", "hb_bound"):                                                                                   
                        self.stats["leaks"] += 1
                        self.log(f"screen: the incumbent's trailing copy failed ({str(terr)[:100]}); this batch's fails are unknown")
                        why = f"the incumbent's trailing copy failed in this batch ({str(terr)[:120]}): a copy may have changed later ones"
                        got = {i: (("unknown", why) if v[0] in ("fail", "hb_bound") else v) for i, v in got.items()}
                got = {i - off: v for i, v in got.items() if off <= i < tail}
            if inc is not None:
                self.stats["inconclusive"] += 1
                self.log(f"screen: batch of {len(batch)} inconclusive ({inc[:120]})")
            if inc is not None and inc.startswith("env"):
                for it in batch:
                    self._set(out, it, "unknown", inc, len(batch), depth)
                continue
            unknown = []
            for i, it in enumerate(batch):
                v, err = got.get(i, ("unknown", inc or "not in the file"))
                if v == "unknown":
                    unknown.append((it, err))
                else:
                    self._set(out, it, v, err, len(batch), depth)
            if not unknown:
                continue
            if depth < self.max_depth and (len(unknown) > 1 or len(batch) > 1):
                us = [it for it, _ in unknown]
                h = (len(us) + 1) // 2
                parts = [p for p in (us[:h], us[h:]) if p]
                self.stats["splits"] += 1
                for p in reversed(parts):
                    queue.insert(0, (p, depth + 1))
                continue
            for it, err in unknown:
                own = it.get("timeout_s")
                if inc == "timeout" and len(batch) == 1 and isinstance(own, (int, float)) and own > 0 and to >= own:
                    self._set(out, it, "timeout", f"timed out alone after {to} s (its own timeout {own:g} s)", 1, depth)
                else:
                    self._set(out, it, "unknown", err, len(batch), depth)
        return out

    def _set(self, out, it, verdict, err, size, depth):
        v = {"verdict": verdict, "error": err, "batch": size, "depth": depth}
        out[it["key"]] = v
        self.cache[it["key"]] = v


def meter_compile_fn(meter):
    """compile_fn for BatchScreener on harness/endstage.Meter's path: direct (its Evaluator: slot gate, memory gate, the given timeout) or
"""
    def run(body: str, copies: str, L: Layout, timeout: int):
        from scorer import compile as C
        path = meter.freeze()
        row = meter.row
        ev, n0, n = None, 0, 0
        try:
            if path == "direct":
                ev = meter._evaluator(); n0 = ev.compiles
                t_ev, ev.timeout = ev.timeout, int(timeout)
                try:
                    r = ev._run(row, L.version, body, L.lean_args, L.first_line, L.quiet)
                finally:
                    ev.timeout = t_ev
                n = ev.compiles - n0
            elif row["source"] == "putnambench":
                r, n = C.compile_putnam(row["header"], copies, L.version, count=False, timeout=int(timeout)), 1
            else:
                r = C._lean_in_project(row["source"], L.version, body, L.lean_args, int(timeout), first_line=L.first_line,
                                       quiet_prefix_sorry=L.quiet)
                n = 1
        except Exception as e:                                                                                         
            r = C.CompileResult(False, None, 0.0, [f"environment: {type(e).__name__}: {e}"[:300]],
                                messages=[{"severity": "error", "pos": {"line": 0}, "data": f"environment: {type(e).__name__}"}])
            n = (ev.compiles - n0) if ev is not None else 0
        meter.compiles += n
        return r, n
    return run
