#!/usr/bin/env python3
"""v4_rescreen (post-step v4, branch open-post-v4-v4rescreen, 2026-11-04): v3's screened lane ops given their screen back on rows where
the stock screen copy loses the declaration's context. Adds no edit of its own: it re-runs those ops' own query + candidates for the row,
with thread-local replacements of the screen-copy builders (harness/post/t4ind.py's `_relaxed` pattern: installed once per process, a
switch that only this module's calls turn on; every other caller, the v3 ops' own calls included, gets the stock builders unchanged).

    has_sites(proof, statement) -> bool                                           (pure)
    query(proof, statement, run, *, versions=None, ctx=None, stats=None, log=None) -> dict
    candidates(proof, statement, *, exchange=None, max_per_op=None, ctx=None) -> [{"op", "decl", "note"}]   (pure)

  context   the stock copy `theorem lraD4M<i> <signature> := <body>` (harness/post/d4_measure.renamed) drops three things the real
            declaration has in its file:
            (a) the namespace prefix of a dotted name (`theorem A.B.foo` elaborates its body with `A.B` open: `bar` means `A.B.bar`);
            (b) the `... in` combinators attached to the declaration (`open X in`, `set_option .. in`, `omit .. in`, `include .. in`,
                `unseal .. in`, `variable .. in`): the row's file prefix ends with them, so in the screen file they apply to the
                first command after it (the dummy theorem, or a marker command) and not to the copies;
            (c) `private` (in the statement or among the prefix's trailing modifiers): the copy is public and, in a `module` file,
                cannot use the file's private constants.
            The fixed copy is `<attached lines> [private] theorem <prefix.>lraD4M<i> <signature> := <body>`: the prefix kept, every
            attached `... in` line repeated before EVERY copy, `private` kept. The measured `#eval` reads the copy's name as
            `<current namespace> ++ <prefix.>lraD4M<i>` (or its private form). Plain marker files start with a dummy theorem that
            takes the prefix's trailing modifiers (docstring, attributes, `open .. in`, `private`), as d4_measure's measured file does.
            The measured file has a SENTINEL reading line (index 999) before copy 0: a file prefix with its own `sorry` warnings
            otherwise fails the control under opus_screen.measured_parse's error rule (MEASURED: a project file whose earlier
            declarations use `sorry`); the trigger's check file has it too, so such a prefix alone never triggers this op.
  switch    d4_measure.renamed / d4_measure.text, opus_screen.plain_text and sonnet_listdrop.plain_text are replaced in their modules by
            switches (installed once per process when this module is imported): with no fixed context on the current thread they call
            the stock function (byte-identical behaviour); inside this module's calls they build the fixed copies. The process-level
            memo sets of those ops (opus_screen._PLAIN_ONLY, sonnet_listdrop._FAILED) are replaced by set subclasses that behave as the
            stock sets outside this module's calls and keep separate contents inside them (a fixed-copy reading never feeds a stock
            screen, nor the other way round).
  attached-only targets (ATTACHED_ONLY: their own copies already keep the dotted prefix and `private`; only the attached `... in`
            lines are lost; re-run only on a row that has some): argon_hbelab /
            argon_hpcert (`_renamed_decl` switched to put the attached lines before each copy; their `_NO_CMD_ELAB` memo a switch set).
  trigger   (query; charged through `run`) only when the row has such a context (pure check on the statement and the row's own file
            prefix) and one of the target ops has a site; then ONE check file reads the stock measured control and the fixed one
            side by side (d4_measure's `#eval` reading). The stock control reads: v3's screens work on this row (no site, nothing
            else compiled). Neither reads: a second file reads the stock plain control (opus_screen's marker file, exactly as the
            stock op writes it) and the fixed plain control. The stock plain control reads: no site. Else, when a fixed control read,
            every target op with a site runs its own query + candidates under the fixed context (mode "measured" or "plain"; in plain
            mode the opus screen goes plain at once and sonnet_surface, whose plain screen needs the bare name, is left out). The
            verdict (stock / measured / plain / none) is memoised per statement and pin for the process (a row's later rounds skip
            the check).
  budget    the targets are re-run ONCE per row (the first round that triggers; memo per statement for the process) and only while
            the row has at least MIN_LEFT of its compiles left. MEASURED on VM1, in combined v3 + v4 runs on the four triggered rows
            (`--ops all` from the raw run-3 snapshot): with re-runs in every round, one row ran out of its 240 compiles after
            round 2 and lost the round-3 adoption v3 alone had (v3 alone used 215).
            Every screened candidate is proposed, also one the stock op may have proposed unscreened in the same round (an opus op
            whose screen does not read proposes its first pure candidates): its re-reading costs a compile, never a wrong verdict,
            and the op's proposals do not depend on which other ops ran (a subset ORDER or a reserve skip reads the same).
  output    the target ops' candidates (each op's first PER_OP, its own best-first order), op `v4_rescreen` (note `<target op>:<its op
            tag>; <its note>`), interleaved round-robin over the target ops in TARGETS order, MAX_CANDS at most (= READS: a triggered
            row's re-run screens and readings come out of the row's own compile budget, which the v3 ops share). The gate is unchanged.

Model-free and deterministic; reads only the proof, the statement and the row's own file prefix (no row name, table or proof text)."""
from __future__ import annotations

import importlib, re, sys, threading
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from harness.post import opus_screen as SC  # noqa: E402
from harness.post import sonnet_listdrop as LD  # noqa: E402
from scorer.tokenize import split_declaration  # noqa: E402

FAMILY = "v4_rescreen"
# the v3 ops whose screens build their copies with the replaced builders (d4_measure.renamed / text, the two plain marker files), in
# the order their candidates are proposed (round-robin; MEASURED on VM1 2026-11-04 on the four triggered rows: the list drops and the
# hoist / goal merge gave the adopted readings, the `?`-certificate list prunes the next best, the heartbeat-only rewrites +0.004
# at most, so they come last)
TARGETS = ("sonnet_listdrop", "opus_hoist", "opus_goalmerge", "argon_hpcert", "opus_rundrop", "opus_stepdrop", "opus_scaffold",
           "opus_armfold", "sonnet_surface", "argon_funind", "argon_hbelab")
# ops whose own copies already keep the dotted prefix and `private`: only the attached `... in` lines are missing, so they are re-run
# only on a row that has some
ATTACHED_ONLY = ("argon_hbelab", "argon_hpcert")
# Not targets (MEASURED, VM1 2026-11-04, on the two rows with attached lines): the v2 op hintgrind (re-run with them it resolved its
# names but gave 0 clean answers, 26 to 134 s each) and sol_harvest (with the attached combinators its shared query read, but its
# only candidates failed to compile in every round)
PER_OP = 3        # each target's best candidates at most (its own order)
MIN_LEFT = 140    # the re-run starts only while the row has at least this many of its compiles left (ROW_COMPILES 240)
PLAIN_SKIP = ("sonnet_surface",)   # its plain screen checks `#check @lraD4M<i>` (the bare name): measured mode only
MAX_CANDS = 8     # = READS["v4_rescreen"]: on a triggered row the re-run screens cost compiles of the row's budget too
DUMMY = "theorem lraV4RDummy : True := trivial\n"
# a reading line for an index no file reaches: the file prefix's own messages (a project's `declaration uses sorry` warnings) come
# before it, so opus_screen.measured_parse's error rule (an error or sorry warning before a reading fails that reading) no longer
# charges them to the control; d4_measure.parse ignores the index (>= the file's variant count)
SENTINEL = '#print "LRAD4M\\t999\\t0\\t0\\tsep"\n'
PMARK = "LRAV4R"

# the `... in` combinators a declaration's file attaches to it (one line each), at the end of the prefix's core or among its modifiers
_IN_LINE = re.compile(r"^[ \t]*(?:set_option|omit|include|unseal|variable|open)\b[^\n]*\bin[ \t]*$")
_OPEN_IN = re.compile(r"open\s+[\w.\s]+?\s+in\b")
_DOC = re.compile(r"/--(?:(?!-/).)*-/", re.S)
_HEAD_MODS = re.compile(r"\A(?:\s+|/--(?:(?!-/).)*-/|@\[[^\]]*\])*((?:(?:private|protected|noncomputable|nonrec)\s+)*)(?:theorem|lemma)\s",
                        re.S)

VARIANT = r'''
set_option Elab.async false in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let s : String := LRAD4MSRC
  let i : Nat := LRAD4MI
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command s with
  | .error _ => Lean.logInfo (Lean.toMessageData s!"LRAD4M\t{i}\t0\t0\tparse")
  | .ok stx =>
    let n1 := (← Lean.getCurrNamespace) ++ LRAD4MNAME
    let (ok, dh) ← Lean.withoutModifyingEnv do
      let t0 ← IO.getNumHeartbeats
      Lean.Elab.Command.elabCommand stx
      let t1 ← IO.getNumHeartbeats
      let env ← Lean.getEnv
      let n2 := Lean.mkPrivateName env n1
      let n := if env.contains n2 then n2 else n1
      let mut ok := false
      if env.contains n then
        ok := !((← Lean.collectAxioms n).contains ``sorryAx)
      pure (ok, t1 - t0)
    Lean.logInfo (Lean.toMessageData s!"LRAD4M\t{i}\t{if ok then 1 else 0}\t{dh / 1000}")
'''


# ------------------------------------------------------------------------------------------------------------------------------ context
class Ctx:
    """The declaration's screen-copy context: `attached` (the `... in` lines, one per line, each ending in a newline) and `private`;
    `mode` ("measured" / "plain") once the trigger has read a fixed control."""

    def __init__(self, attached: str = "", private: bool = False, mode: str = "measured"):
        self.attached, self.private, self.mode = attached, bool(private), mode


def attached_lines(core: str, mods: str) -> str:
    """The `... in` lines the file attaches to the declaration: the consecutive such lines that end the prefix's core (in file order),
    then the `open .. in` among its trailing modifiers (docstrings removed first). One per line, whitespace-normalised."""
    tail = []
    for ln in reversed(core.rstrip().split("\n")):
        if _IN_LINE.match(ln):
            tail.append(ln)
            continue
        break
    lines = list(reversed(tail)) + [m.group(0) for m in _OPEN_IN.finditer(_DOC.sub(" ", mods or ""))]
    return "".join(" ".join(x.split()) + "\n" for x in lines)


def mods_private(mods: str) -> bool:
    return bool(re.search(r"(?<![\w.])private\b", _DOC.sub(" ", mods or "")))


def stmt_private(statement: str) -> bool:
    m = _HEAD_MODS.match(statement)
    return bool(m and "private" in m.group(1).split())


def decl_name(statement: str) -> str | None:
    m = MS.DECL_RE.match(statement)
    if not m or ".{" in m.group(0):
        return None
    return re.split(r"\s+", m.group(0).strip())[-1]


def row_ctx(row: dict | None, version: str | None) -> Ctx:
    """The context of the row's declaration on `version` (the row's own file prefix; a header-only row or a missing prefix: none)."""
    if not row or row.get("source") == "putnambench" or not row.get("file_path") or not version:
        return Ctx("", stmt_private((row or {}).get("statement") or ""))
    try:
        from scorer import compile as C
        core, mods = C.split_modifiers(C.file_prefix(row, version))
    except Exception:  # noqa: BLE001  (no prefix: the statement's own modifiers only)
        core, mods = "", ""
    return Ctx(attached_lines(core, mods), stmt_private(row.get("statement") or "") or mods_private(mods))


def has_context(statement: str, cx: Ctx) -> bool:
    """True when the stock copy differs from the declaration in its file: a dotted name, attached `... in` lines, or `private`."""
    nm = decl_name(statement)
    return bool(nm) and ("." in nm or bool(cx.attached) or cx.private)


# ------------------------------------------------------------------------------------------------------------------------------ builders
def rel_name(statement: str, i) -> str | None:
    """`<prefix.>lraD4M<i>` (the dotted name's namespace prefix kept), or None (no theorem / lemma; universe parameters; `_root_`)."""
    nm = decl_name(statement)
    if nm is None or nm.startswith("_root_"):
        return None
    pre = nm.rsplit(".", 1)[0] + "." if "." in nm else ""
    return f"{pre}lraD4M{i}"


def renamed_fixed(statement: str, i, cx: Ctx) -> str | None:
    """The fixed copy's head: attached lines, `private` when the declaration is, `theorem <prefix.>lraD4M<i>` + the signature."""
    m = MS.DECL_RE.match(statement)
    rn = rel_name(statement, i)
    if not m or rn is None:
        return None
    priv = "private " if (cx.private or stmt_private(statement)) else ""
    return cx.attached + f"{priv}theorem {rn}" + statement[m.end():]


def name_expr(rel: str) -> str:
    expr = "Lean.Name.anonymous"
    for p in [p for p in rel.split(".") if p]:
        expr = f"(Lean.Name.str {expr} {K.lean_str(p)})"
    return expr


def text_fixed(statement: str, bodies: list[str], cx: Ctx) -> str | None:
    """d4_measure.text with the fixed copies (same TEXT dummy first, same LRAD4M reading lines; MS.parse reads them)."""
    srcs = []
    for i, b in enumerate(bodies):
        r = renamed_fixed(statement, i, cx)
        if r is None:
            return None
        srcs.append((r.rstrip() + " :=" + b, rel_name(statement, i)))
    return MS.TEXT + SENTINEL + "".join(VARIANT.replace("LRAD4MSRC", K.lean_str(s)).replace("LRAD4MI", str(i)).replace("LRAD4MNAME", name_expr(rn))
                             for i, (s, rn) in enumerate(srcs))


def opus_plain_fixed(statement: str, bodies: list[str], cx: Ctx) -> str | None:
    """opus_screen.plain_text with the fixed copies, after a dummy theorem that takes the prefix's trailing modifiers."""
    out = []
    for i, b in enumerate(bodies):
        r = renamed_fixed(statement, i, cx)
        if r is None:
            return None
        out.append(f'#check "{SC.MARK}{i}"\n' + r.rstrip() + " :=" + SC.selfref(statement, b, i).rstrip() + "\n")
    out.append(f'#check "{SC.MARK}{len(bodies)}"\n')
    return DUMMY + "\n" + "\n".join(out)


def listdrop_plain_fixed(statement: str, bodies: list[str], cx: Ctx) -> str | None:
    """sonnet_listdrop.plain_text with the fixed copies, after a dummy theorem that takes the prefix's trailing modifiers."""
    out = []
    for i, b in enumerate(bodies):
        r = renamed_fixed(statement, i, cx)
        if r is None:
            return None
        out.append(f'#print "LRASL {i}"\n' + r.rstrip() + " :=" + b.rstrip("\n") + "\n")
    out.append('#print "LRASL end"\n')
    return DUMMY + "".join(out)


def argon_renamed_fixed(stock, statement: str, body: str, i):
    """argon_hbelab / argon_hpcert `_renamed_decl` (it keeps the dotted prefix and `private`) with the attached lines before the copy."""
    got = stock(statement, body, i)
    cx = _cx()
    if got is None or cx is None or not cx.attached:
        return got
    return cx.attached + got[0], got[1]


# ------------------------------------------------------------------------------------------------------------------------------ switch
_TLS = threading.local()


def _cx() -> Ctx | None:
    return getattr(_TLS, "cx", None)


class _fixed:
    """Inside: the replaced builders build fixed copies for `cx` on this thread only."""

    def __init__(self, cx: Ctx):
        self.cx = cx

    def __enter__(self):
        self.prev = _cx()
        _TLS.cx = self.cx
        return self.cx

    def __exit__(self, *exc):
        _TLS.cx = self.prev
        return False


class _SwitchSet(set):
    """A stock memo set outside this module's calls; inside them, a separate set (the fixed copies' own memo)."""

    def __init__(self, it=()):
        super().__init__(it)
        self.fixed: set = set()

    def __contains__(self, x):
        return (x in self.fixed) if _cx() is not None else set.__contains__(self, x)

    def add(self, x):
        if _cx() is not None:
            self.fixed.add(x)
        else:
            set.add(self, x)


def _renamed_switch(statement: str, i):
    cx = _cx()
    return renamed_fixed(statement, i, cx) if cx is not None else _renamed_switch.stock(statement, i)


def _text_switch(statement: str, bodies: list[str]):
    cx = _cx()
    if cx is None:
        return _text_switch.stock(statement, bodies)
    if cx.mode == "plain":   # the fixed measured control did not read: no measured file (listdrop / goalmerge then go plain at once)
        return None
    return text_fixed(statement, bodies, cx)


def _opus_plain_switch(statement: str, bodies: list[str]):
    cx = _cx()
    return opus_plain_fixed(statement, bodies, cx) if cx is not None else _opus_plain_switch.stock(statement, bodies)


def _listdrop_plain_switch(statement: str, bodies: list[str]):
    cx = _cx()
    return listdrop_plain_fixed(statement, bodies, cx) if cx is not None else _listdrop_plain_switch.stock(statement, bodies)


def _wrap(mod, attr: str, fixed) -> None:
    """mod.attr -> a switch: the stock function outside this module's calls, fixed(stock, *args) inside them."""
    stock = getattr(mod, attr)
    if getattr(stock, "_v4r_switch", False):
        return

    def sw(*a, **k):
        return fixed(stock, *a, **k) if _cx() is not None else stock(*a, **k)
    sw._v4r_switch = True
    sw.stock = stock
    setattr(mod, attr, sw)


def _install_attached_only() -> None:
    """The attached-only targets' builders and memos (each module imported here; a missing one is skipped)."""
    for name in ("argon_hbelab", "argon_hpcert"):
        try:
            m = importlib.import_module(f"harness.post.{name}")
            _wrap(m, "_renamed_decl", argon_renamed_fixed)
            if hasattr(m, "_NO_CMD_ELAB") and not isinstance(m._NO_CMD_ELAB, _SwitchSet):
                m._NO_CMD_ELAB = _SwitchSet(m._NO_CMD_ELAB)
        except Exception:  # noqa: BLE001  (that target then reads with its stock builders inside this op too)
            pass


def _install() -> None:
    _install_attached_only()
    if getattr(MS.renamed, "_v4r_switch", False):
        return
    _renamed_switch.stock, _text_switch.stock = MS.renamed, MS.text
    _opus_plain_switch.stock, _listdrop_plain_switch.stock = SC.plain_text, LD.plain_text
    for f in (_renamed_switch, _text_switch, _opus_plain_switch, _listdrop_plain_switch):
        f._v4r_switch = True
    MS.renamed, MS.text = _renamed_switch, _text_switch
    SC.plain_text, LD.plain_text = _opus_plain_switch, _listdrop_plain_switch
    if not isinstance(SC._PLAIN_ONLY, _SwitchSet):
        SC._PLAIN_ONLY = _SwitchSet(SC._PLAIN_ONLY)
    if not isinstance(LD._FAILED, _SwitchSet):
        LD._FAILED = _SwitchSet(LD._FAILED)


_install()


def stock_renamed(statement: str, i):
    return _renamed_switch.stock(statement, i)


def stock_text(statement: str, bodies: list[str]):
    return _text_switch.stock(statement, bodies)


def stock_opus_plain(statement: str, bodies: list[str]):
    return _opus_plain_switch.stock(statement, bodies)


# ------------------------------------------------------------------------------------------------------------------------------ trigger
def check_text_measured(statement: str, body0: str, cx: Ctx) -> str | None:
    """ONE measured file: the stock control (copy 0, d4_measure's own copy and `#eval`) and the fixed control (copy 1), after the
    SENTINEL (the file prefix's own messages are not charged to copy 0)."""
    st = stock_text(statement, [SC.selfref(statement, body0, 0)])
    rn = rel_name(statement, 1)
    fx = renamed_fixed(statement, 1, cx)
    if st is None or rn is None or fx is None:
        return None
    src = fx.rstrip() + " :=" + SC.selfref(statement, body0, 1)
    if not st.startswith(MS.TEXT):
        return None
    return MS.TEXT + SENTINEL + st[len(MS.TEXT):] + VARIANT.replace("LRAD4MSRC", K.lean_str(src)).replace("LRAD4MI", "1").replace("LRAD4MNAME", name_expr(rn))


def check_text_plain(statement: str, body0: str, cx: Ctx) -> str | None:
    """ONE plain file: the stock plain control exactly as opus_screen writes it (first in the file), then a dummy theorem and the
    fixed control between this module's own markers."""
    st = stock_opus_plain(statement, [body0])
    fx = renamed_fixed(statement, 2, cx)
    if st is None or fx is None:
        return None
    return (st + "\n" + DUMMY + f'#check "{PMARK}0"\n' + fx.rstrip() + " :=" + SC.selfref(statement, body0, 2).rstrip() + "\n"
            + f'#check "{PMARK}1"\n')


def parse_fixed_plain(messages) -> bool | None:
    """The fixed plain control of check_text_plain: True / False, None when its markers are missing."""
    marks, bad = {}, []
    for m in messages or []:
        if not isinstance(m, dict):
            continue
        txt = K.msg_text(m)
        ln = SC._line(m)
        if ln is None:
            continue
        if f'"{PMARK}' in txt and m.get("severity") == "information":
            try:
                marks[int(txt.split(f'"{PMARK}', 1)[1].split('"', 1)[0])] = ln
            except Exception:  # noqa: BLE001
                pass
            continue
        sev = m.get("severity")
        if sev == "error" or (sev == "warning" and "sorry" in txt):
            bad.append(ln)
    if 0 not in marks or 1 not in marks:
        return None
    return not any(marks[0] < x < marks[1] for x in bad)


_VERDICT: dict = {}
_VLOCK = threading.Lock()
_RAN: set = set()     # statements whose targets were re-run once in this process (a row's later rounds propose nothing more)


def trigger(statement: str, body0: str, cx: Ctx, run, version, log=None) -> str:
    """"stock" (the stock control reads: v3's screens work), "measured" / "plain" (the fixed control reads in that mode, the stock one
    does not), or "none" (neither reads). 1 compile, 2 when the measured file reads neither control. Memoised per statement + pin."""
    key = (statement, version, cx.attached, cx.private)
    with _VLOCK:
        if key in _VERDICT:
            return _VERDICT[key]
    v = "none"
    t = check_text_measured(statement, body0, cx)
    if t is not None:
        rd = SC.measured_parse(getattr(run(t, version), "messages", None), 2)
        if (rd.get(0) or {}).get("ok"):
            v = "stock"
        elif (rd.get(1) or {}).get("ok"):
            v = "measured"
    if v == "none":
        t = check_text_plain(statement, body0, cx)
        if t is not None:
            msgs = getattr(run(t, version), "messages", None)
            st = SC.plain_parse(msgs, 1)
            if st is not None and st.get(0):
                v = "stock"
            elif parse_fixed_plain(msgs):
                v = "plain"
    if log:
        log(f"{FAMILY}: trigger {v} (attached {cx.attached.count(chr(10))} line(s), private {cx.private}, name {decl_name(statement)})")
    with _VLOCK:
        _VERDICT[key] = v
    return v


# ------------------------------------------------------------------------------------------------------------------------------ op API
def _mod(name: str):
    return importlib.import_module(f"harness.post.{name}")


def _target_has_site(name: str, proof: str, statement: str) -> bool:
    try:
        mod = _mod(name)
        if hasattr(mod, "has_sites"):
            return bool(mod.has_sites(proof, statement))
        return bool(mod.candidates(proof, statement, ctx={}))
    except Exception:  # noqa: BLE001
        return False


def has_sites(proof: str, statement: str) -> bool:
    """Pure: a theorem / lemma copy can be built and one target op has a site (the row's context is read by query)."""
    if split_declaration(proof, statement) is None or rel_name(statement, 0) is None:
        return False
    return any(_target_has_site(n, proof, statement) for n in TARGETS)


def query(proof: str, statement: str, run, *, versions=None, ctx=None, stats=None, log=None) -> dict:
    """The trigger, then the target ops' own query + candidates under the fixed context. {"v4r_key", "v4r_cands": {op: [cands]}}."""
    body0 = split_declaration(proof, statement)
    if body0 is None:
        return {}
    meter = getattr(run, "meter", None)
    vs = list(versions or getattr(meter, "versions", None) or [None])
    cx = row_ctx(getattr(meter, "row", None), vs[0])
    if not has_context(statement, cx):
        return {}
    ops = [n for n in TARGETS if _target_has_site(n, proof, statement) and not (n in ATTACHED_ONLY and not cx.attached.strip())]
    if not ops:
        return {}
    with _VLOCK:
        if statement in _RAN:   # once per row: its later rounds belong to the v1-v3 ops (and to the confirmations)
            return {}
    bud = getattr(run, "budget", None)
    try:
        left = int(bud.max) - int(bud.meter.compiles) if bud is not None else None
    except Exception:  # noqa: BLE001
        left = None
    if left is not None and left < MIN_LEFT:
        if log:
            log(f"{FAMILY}: skipped (row compiles left {left} < {MIN_LEFT})")
        return {}
    v = trigger(statement, body0, cx, run, vs[0], log=log)
    if v not in ("measured", "plain"):
        return {"v4r_key": K.proof_key(proof), "v4r_cands": {}, "v4r_trigger": v}
    with _VLOCK:
        _RAN.add(statement)
    if log:
        log(f"{FAMILY}: re-running {len(ops)} target(s) under the fixed {v} screen ({left} row compiles left)")
    cx = Ctx(cx.attached, cx.private, mode=v)
    out: dict = {}
    qctx = dict(ctx or {})
    for n in ops:
        if (v == "plain" and n in PLAIN_SKIP) or (n in ATTACHED_ONLY and not cx.attached.strip()):
            continue
        mod = _mod(n)
        rn = run
        try:
            with _fixed(cx):
                if v == "plain":
                    SC._PLAIN_ONLY.add(statement)   # the fixed measured control did not read: the opus screens go plain at once
                got = (mod.query(proof, statement, rn, versions=vs, ctx=dict(qctx), stats={}, log=log) or {}) if hasattr(mod, "query") else {}
                cs = mod.candidates(proof, statement, ctx=got) or []
        except Exception as e:  # noqa: BLE001  (a target op's fault: no candidates from it; budget stops propagate)
            if e.__class__.__name__ == "_Stop":
                raise
            if log:
                log(f"{FAMILY}: {n} failed ({type(e).__name__}: {str(e)[:160]})")
            continue
        cs = [c for c in cs if c.get("decl")][:PER_OP]
        if cs:
            out[n] = [dict(c, op=FAMILY, note=f"{n}:{c.get('op') or n}; {c.get('note', '')}"[:200]) for c in cs if c.get("decl")]
        if log:
            log(f"{FAMILY}: {n} under the fixed {v} screen: {len(cs)} candidate(s)")
    if stats is not None:
        stats[FAMILY] = {"trigger": v, "ops": {k: len(x) for k, x in out.items()}}
    return {"v4r_key": K.proof_key(proof), "v4r_cands": out, "v4r_trigger": v}


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    """The query's candidates (only for the proof it read), round-robin over the target ops in TARGETS order; [] without a query."""
    c = ctx or {}
    if c.get("v4r_key") != K.proof_key(proof):
        return []
    per = c.get("v4r_cands") or {}
    lists = [list(per[n]) for n in TARGETS if per.get(n)]
    out, seen, k = [], set(), 0
    cap = int(max_per_op or MAX_CANDS)
    while len(out) < cap and any(k < len(x) for x in lists):
        for x in lists:
            if k < len(x) and len(out) < cap:
                d = x[k]["decl"].rstrip()
                if d not in seen:
                    seen.add(d)
                    out.append(x[k])
        k += 1
    return out
