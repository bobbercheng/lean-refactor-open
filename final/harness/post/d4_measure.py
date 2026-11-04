#!/usr/bin/env python3
# Vendored, unchanged except for this comment and the `harness.post` imports, from the closed line's bet D4 code (branch closed-bets-d4 402c44d2, harness/tools/d4_measure.py) for the open post-step harness/open_post.py (2026-11-03).
"""Bets D4C / D4N helper (not an end-stage family; harness/tools/__init__.py lists only families): heartbeat readings of several
variants of one declaration in ONE plain compile, the env-query path (harness/endstage.py env_query: Meter.command after the row's file
prefix, the primary pin, charged as one compile to the tool phase and the family's cap). The closerprep and simpnorm families use it as a
PREFILTER: their candidate spaces (insertions x ddmin drops; subsets of generic lemmas) are too large to screen and measure one by one on
a row whose compile takes tens of seconds, so the query reads them all in one file and the family proposes only those predicted to read
higher (predicted(): the scorer's own linear L and H through the row's exchange rate). The proposals are then measured by the end stage
as every candidate is (batch screen, paired scorer.accept.decide against the incumbent, all-pin confirmation): nothing here is trusted.

  text      one `#eval` per variant (Elab.async off; its own command, so a variant whose elaboration throws, e.g. a heartbeat or
            recursion limit, ends only its own command) that parses the variant as a command (`theorem lraD4M<i> ...`: the statement
            with the name replaced), elaborates it with Lean.Elab.Command.elabCommand between two IO.getNumHeartbeats readings (the
            scorer's own measurement, scorer/compile.MEASURE_ELAB, without a new `elab`: a module file needs no import for it), and logs
            "LRAD4M <i> <ok> <heartbeats / 1000>"; ok = the theorem is in the environment and Lean.collectAxioms finds no sorryAx (an
            elaboration error leaves a sorried theorem); no line = not ok. Each theorem's elaboration starts its own heartbeat allowance
            (the row's maxHeartbeats), as in a real compile. Each variant is elaborated under Lean.withoutModifyingEnv: nothing it
            adds (its theorem, auxiliary lemmas Lean caches by type, ...) reaches the next one, so a variant never reads another's
            cached work (2026-11-02, GB10: without it a variant after its neighbours read up to 20% below its own compile). Variant 0
            is the incumbent (the control).
  budget    at most max(2, MEASURE_S / (half the incumbent's compile seconds)) variants per file, MAX_VARIANTS at most (the control
            included), so the file stays within the query's wall timeout.
Pure text building and parsing; no compile here."""
from __future__ import annotations

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.post import d4_kit as K  # noqa: E402
from scorer.tokenize import count_tokens  # noqa: E402

MEASURE_S = 210.0      # seconds of variants per file (QUERY_TIMEOUT 300 of the families: import time and the control fit)
MAX_VARIANTS = 16      # variants per file at most (the control included)
DEFAULT_VARIANT_S = 15.0   # seconds per variant when the incumbent's compile time is unknown
DECL_RE = re.compile(r"\A(?:\s+|/--(?:(?!-/).)*-/|@\[[^\]]*\]|(?:private|protected|noncomputable|nonrec)\b)*(?:theorem|lemma)\s+"
                     r"[^\s(:{\[⦃]+(?:\{[^}]*\})?", re.S)

TEXT = "theorem lraD4MDummy : True := trivial\n"
VARIANT = r'''
set_option Elab.async false in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let s : String := LRAD4MSRC
  let i : Nat := LRAD4MI
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command s with
  | .error _ => Lean.logInfo (Lean.toMessageData s!"LRAD4M\t{i}\t0\t0\tparse")
  | .ok stx =>
    let n := (← Lean.getCurrNamespace) ++ Lean.Name.mkSimple ("lraD4M" ++ toString i)
    let (ok, dh) ← Lean.withoutModifyingEnv do
      let t0 ← IO.getNumHeartbeats
      Lean.Elab.Command.elabCommand stx
      let t1 ← IO.getNumHeartbeats
      let mut ok := false
      if (← Lean.getEnv).contains n then
        ok := !((← Lean.collectAxioms n).contains ``sorryAx)
      pure (ok, t1 - t0)
    Lean.logInfo (Lean.toMessageData s!"LRAD4M\t{i}\t{if ok then 1 else 0}\t{dh / 1000}")
'''


def renamed(statement: str, i: int) -> str | None:
    """The statement as `theorem lraD4M<i> ...` (modifiers and attributes dropped), else None (not a theorem / lemma; universe
    parameters in the name)."""
    m = DECL_RE.match(statement)
    if not m or ".{" in m.group(0):
        return None
    return f"theorem lraD4M{i}" + statement[m.end():]


def budget(ctx: dict | None) -> int:
    """Variants per file (the control included): module docstring, "budget". A variant in the file costs about half a standalone
    compile (the imports are loaded once: 7 s against 23 s on a 100k-heartbeat row, 2026-11-02)."""
    cs = (ctx or {}).get("compile_s")
    per = max(1.0, float(cs) / 2.0) if isinstance(cs, (int, float)) and cs > 0 else DEFAULT_VARIANT_S
    return max(2, min(MAX_VARIANTS, int(MEASURE_S / per)))


def text(statement: str, bodies: list[str]) -> str | None:
    """The measuring file's text for the bodies (each the text after the statement, `:=` excluded, as split_declaration gives it)."""
    srcs = []
    for i, b in enumerate(bodies):
        r = renamed(statement, i)
        if r is None:
            return None
        srcs.append(r.rstrip() + " :=" + b)
    return TEXT + "".join(VARIANT.replace("LRAD4MSRC", K.lean_str(src)).replace("LRAD4MI", str(i)) for i, src in enumerate(srcs))


def parse(messages, n: int) -> dict:
    """{i: {"ok": bool, "hb": int}} for the variants that logged a reading (a parse failure reads ok False)."""
    out = {}
    for m in messages or []:
        for ln in K.msg_text(m).split("\n"):
            p = ln.strip().split("\t")
            if len(p) >= 4 and p[0] == "LRAD4M" and p[1].isdigit() and int(p[1]) < n and p[3].isdigit():
                out[int(p[1])] = {"ok": p[2] == "1", "hb": int(p[3])}
    return out


def predicted(ctl: dict, body0: str, body: str, reading: dict, exchange: float | None) -> float | None:
    """The predicted score change (in heartbeat units: positive reads higher) of a variant over the control: the heartbeats saved minus
    the tokens added times the exchange rate (reference heartbeats / reference tokens: the scorer's L and H are linear in both); None
    when either reading failed. Without an exchange rate (no reference heartbeats: H has no slope) minus the tokens added."""
    if not (ctl.get("ok") and reading.get("ok")):
        return None
    dt = count_tokens(body) - count_tokens(body0)
    if not exchange:   # no reference heartbeats: H has no slope, only tokens count
        return float(-dt)
    return float(ctl["hb"] - reading["hb"]) - dt * float(exchange)
