#!/usr/bin/env python3
"""The finer sorry check of the axiom guard (2026-11-24): which constants a declaration's `sorryAx` comes from.

Why. `#print axioms` names `sorryAx` and nothing more. On a problem whose reference proof already reads `sorryAx` (a lemma of the
library proved by `sorry`), the guard's allowance lets a proof through that reads the same list, also one whose own value became
`sorry` (Lean's error recovery, with no message: held-out row 42's fault) or that uses another lemma proved by `sorry`. This module
names the SORRY SOURCES S(D) of the declaration D, so the guard can compare them with the reference proof's.

The Lean program (program()), appended after the proof text in a compile of its own, for each name `#print axioms` would be given
(resolved the same way, `realizeGlobalConst` in the file's own scope, private names included), and for each constant D it resolves to:
  - walks the constants of the file being compiled (the proof's own, its auxiliary declarations, the library file's declarations
    above it) reached from D through their types and values (the kernel's copy, as `collectAxioms` takes it; theorem bodies
    included); each one whose own type or value names `sorryAx` is a source;
  - does not walk into an IMPORTED constant: it is a source iff its axioms include `sorryAx`. From v4.30 Lean's `collectAxioms`
    reads the axiom lists stored in the imported .olean files (the only way in a `module` file, where imported theorem bodies are
    not loaded); before v4.30 `collectAxioms` walks bodies, once per call, so the program walks the imported closure once instead
    (one shared reachability pass, `fuel` bounds it);
  - marks a source of the file OWN when the proof text declared it: the declaration range of the constant, or else of its nearest
    name prefix that has one (D for D.proof_1, D.go, D.match_1, ...; for a private name also its user-facing name's prefixes),
    starts at or after the proof text's first line (`proof_line`); a source with no range on any prefix (its origin unknown) is
    OWN too. A source of the library file's prefix (before that line) or an imported one is never OWN, also when its name has D
    as a prefix (a library lemma `D.aux`, review 2026-11-24);
  - prints one line per resolved constant: `LRA-FINER <nonce> {json}`, then an end line `LRA-FINER <nonce> {"end": true, ...}`.
The program names every identifier from the root (`_root_.…`), opens nothing, and resolves no name literal (`sorryAx` is a plain
name), so the file's namespaces, `open`s and declarations (a `structure Name`, an opened `Json`) neither change what it resolves nor
break it (review 2026-11-24); it runs with `maxHeartbeats 0`, so a proof's own heartbeat setting does not stop it.
The nonce is new for every compile: a proof text cannot PRINT a line the parser takes for the program's. It could still change what
the program does by registering an elaborator, a macro, syntax, an instance or another hook before it (review 2026-11-24: a
`@[command_elab Lean.Parser.Command.eval]` handler read the nonce out of the program's own syntax and logged fake lines; the same
trick fakes `#print axioms`). hooks() and finer_hooks() read such texts; the guard reads them BAD without compiling them.

parse() reads those lines (only at or after the program's first line); decide() is the rule (see axiom_guard.py's module text)."""
from __future__ import annotations

import json, re, secrets

VERSION = 2                 # of the program and of its output; a marker of another version is not read (1: OWN by name prefix)
MARK = "LRA-FINER"
FUEL = 4_000_000            # constants expanded at most per walk (the file's own, then the imported closure before v4.30)
PRIVATE_TAG = " (private)"  # a private constant of the compiled file: its prefix names the scratch file's module, so it is dropped

PROGRAM = r"""
set_option maxHeartbeats 0 in
#eval show _root_.Lean.Elab.Command.CommandElabM _root_.Unit from do
  let t0 ← _root_.IO.monoMsNow
  let tag : _root_.String := "@MARK@ @NONCE@ "
  let fuel : _root_.Nat := @FUEL@
  let proofLine : _root_.Nat := @LINE@
  let env := (← _root_.Lean.MonadEnv.getEnv).setExporting _root_.Bool.false
  let kenv := env.checked.get
  let sorryN : _root_.Lean.Name := `sorryAx
  let isLocal : _root_.Lean.Name → _root_.Bool := fun c => (env.getModuleIdxFor? c).isNone
  let shown : _root_.Lean.Name → _root_.String := fun c =>
    match _root_.Lean.privateToUserName? c with
    | .some u => if isLocal c then u.toString ++ "@PRIVATE@" else c.toString
    | .none => c.toString
  let strs : _root_.Array _root_.Lean.Name → _root_.Lean.Json := fun cs =>
    _root_.Lean.Json.arr (cs.map fun c => _root_.Lean.Json.str (shown c))
  let num : _root_.Nat → _root_.Lean.Json := fun n => _root_.Lean.ToJson.toJson n
  let flag : _root_.Bool → _root_.Lean.Json := fun b => _root_.Lean.Json.bool b
  let say : _root_.String → _root_.Lean.Elab.Command.CommandElabM _root_.Unit := fun s =>
    _root_.Lean.logInfo (_root_.Lean.MessageData.ofFormat (_root_.Std.Format.text (tag ++ s)))
  let usesOf : _root_.Lean.Name → _root_.Option (_root_.Array _root_.Lean.Name) := fun c =>
    match kenv.find? c with
    | .some (.axiomInfo v) => .some v.type.getUsedConstants
    | .some (.defnInfo v) => .some (v.type.getUsedConstants ++ v.value.getUsedConstants)
    | .some (.thmInfo v) => .some (v.type.getUsedConstants ++ v.value.getUsedConstants)
    | .some (.opaqueInfo v) => .some (v.type.getUsedConstants ++ v.value.getUsedConstants)
    | .some (.quotInfo _) => .some #[]
    | .some (.ctorInfo v) => .some v.type.getUsedConstants
    | .some (.recInfo v) => .some v.type.getUsedConstants
    | .some (.inductInfo v) => .some (v.type.getUsedConstants ++ v.ctors.toArray)
    | .none => .none
  let lineOf : _root_.Lean.Name → _root_.Lean.Elab.Command.CommandElabM (_root_.Option _root_.Nat) := fun c => do
    let mut cands : _root_.Array _root_.Lean.Name := #[]
    for n0 in [c, _root_.Lean.privateToUserName c] do
      let mut x := n0
      repeat
        if x.isAnonymous then break
        cands := cands.push x
        x := x.getPrefix
    for y in cands do
      match (← _root_.Lean.findDeclarationRanges? y) with
      | .some r => return (.some r.range.pos.line)
      | .none => _root_.Pure.pure ()
    return .none
  let stored : _root_.Bool := _root_.Lean.version.major > 4 || _root_.Lean.version.minor ≥ 30
  let isMod : _root_.Bool := env.header.isModule
  if isMod && !stored then
    let e := _root_.Lean.Json.mkObj [("v", num @VERSION@), ("end", flag _root_.Bool.true), ("markers", num 0),
      ("unresolved", _root_.Lean.Json.arr #[]), ("stored", flag stored), ("module", flag isMod), ("walked", num 0),
      ("complete", flag _root_.Bool.false), ("proof_line", num proofLine), ("lean", _root_.Lean.Json.str _root_.Lean.versionString),
      ("ms", num 0),
      ("error", _root_.Lean.Json.str "a module file before v4.30: imported theorem bodies are not loaded and no axiom list is stored")]
    say e.compress
    return
  let mut dep : _root_.Std.HashMap _root_.Lean.Name _root_.Bool := {}
  let mut edges : _root_.Std.HashMap _root_.Lean.Name (_root_.Array _root_.Lean.Name) := {}
  let mut nMarkers : _root_.Nat := 0
  let mut unresolved : _root_.Array _root_.String := #[]
  let mut walked : _root_.Nat := 0
  let mut full : _root_.Bool := _root_.Bool.true
  for q in (@QUERIES@ : _root_.List _root_.Lean.Name) do
    let ds ← try _root_.Lean.Elab.Command.liftCoreM (_root_.Lean.realizeGlobalConst (_root_.Lean.mkIdent q)) catch _ => _root_.Pure.pure []
    if ds.isEmpty then
      unresolved := unresolved.push q.toString
      continue
    for d in ds do
      let t1 ← _root_.IO.monoMsNow
      let mut seen : _root_.Std.HashSet _root_.Lean.Name := {}
      let mut stack : _root_.Array _root_.Lean.Name := #[d]
      let mut localSrc : _root_.Array _root_.Lean.Name := #[]
      let mut missing : _root_.Array _root_.Lean.Name := #[]
      let mut frontier : _root_.Array _root_.Lean.Name := #[]
      let mut fseen : _root_.Std.HashSet _root_.Lean.Name := {}
      let mut steps : _root_.Nat := 0
      let mut complete : _root_.Bool := _root_.Bool.true
      repeat
        match stack.back? with
        | .none => break
        | .some c =>
          stack := stack.pop
          if seen.contains c then continue
          seen := seen.insert c
          steps := steps + 1
          if steps > fuel then
            complete := _root_.Bool.false
            break
          match usesOf c with
          | .none => missing := missing.push c
          | .some us =>
            if us.contains sorryN then localSrc := localSrc.push c
            for u in us do
              if u != sorryN then
                if isLocal u then
                  unless seen.contains u do stack := stack.push u
                else
                  unless fseen.contains u do
                    fseen := fseen.insert u
                    frontier := frontier.push u
      let todo := frontier.filter fun u => !dep.contains u
      if stored then
        for u in todo do
          dep := dep.insert u ((← _root_.Lean.collectAxioms u).contains sorryN)
      else if !todo.isEmpty then
        let mut st : _root_.Array _root_.Lean.Name := todo
        let mut wsteps : _root_.Nat := 0
        repeat
          match st.back? with
          | .none => break
          | .some c =>
            st := st.pop
            if edges.contains c then continue
            wsteps := wsteps + 1
            if wsteps > fuel then
              complete := _root_.Bool.false
              break
            let us := (usesOf c).getD #[]
            edges := edges.insert c us
            for u in us do
              unless edges.contains u do st := st.push u
        walked := walked + wsteps
        let rev : _root_.Std.HashMap _root_.Lean.Name (_root_.Array _root_.Lean.Name) := edges.fold (init := {}) fun acc c us =>
          us.foldl (init := acc) fun acc2 u => acc2.insert u ((acc2.getD u #[]).push c)
        let mut reach : _root_.Std.HashSet _root_.Lean.Name := {}
        reach := reach.insert sorryN
        let mut queue : _root_.Array _root_.Lean.Name := #[sorryN]
        repeat
          match queue.back? with
          | .none => break
          | .some x =>
            queue := queue.pop
            for p in rev.getD x #[] do
              unless reach.contains p do
                reach := reach.insert p
                queue := queue.push p
        for u in todo do
          dep := dep.insert u (reach.contains u)
      let importedSrc := frontier.filter fun u => dep.getD u _root_.Bool.true
      let srcs := localSrc ++ importedSrc
      let mut own : _root_.Array _root_.Lean.Name := #[]
      let mut unranged : _root_.Array _root_.Lean.Name := #[]
      for c in localSrc do
        match (← lineOf c) with
        | .some l => if l ≥ proofLine then own := own.push c
        | .none =>
          own := own.push c
          unranged := unranged.push c
      let axs ← _root_.Lean.collectAxioms d
      full := full && complete
      let t2 ← _root_.IO.monoMsNow
      let j := _root_.Lean.Json.mkObj [("v", num @VERSION@), ("q", _root_.Lean.Json.str q.toString),
        ("decl", _root_.Lean.Json.str (shown d)), ("decl_local", flag (isLocal d)), ("sources", strs srcs), ("own", strs own),
        ("local", strs localSrc), ("unranged", strs unranged), ("missing", strs missing), ("axioms", strs axs),
        ("n_local", num seen.size), ("n_frontier", num frontier.size), ("complete", flag complete), ("ms", num (t2 - t1))]
      say j.compress
      nMarkers := nMarkers + 1
  let t3 ← _root_.IO.monoMsNow
  let e := _root_.Lean.Json.mkObj [("v", num @VERSION@), ("end", flag _root_.Bool.true), ("markers", num nMarkers),
    ("unresolved", _root_.Lean.Json.arr (unresolved.map _root_.Lean.Json.str)), ("stored", flag stored), ("module", flag isMod),
    ("walked", num walked), ("complete", flag full), ("proof_line", num proofLine),
    ("lean", _root_.Lean.Json.str _root_.Lean.versionString), ("ms", num (t3 - t0))]
  say e.compress
"""


META_IMPORT = "public meta import Lean.Elab.Command\n"   # = scorer.compile.MEASURE_IMPORT: in a `module` file, after the module line
PLAIN_IMPORT = "import Lean.Elab.Command\n"              # in a plain file, first
_MODULE_LINE = re.compile(r"\A(?:\s+|--[^\n]*\n|/-(?:(?!-/).)*-/)*module[ \t]*\n", re.DOTALL)   # = scorer.compile._MODULE_LINE


def with_lean_import(head: str) -> str:
    """`head` (a file's header or prefix) with Lean's command elaborator imported, for a file whose imports do not bring it (measured:
    leanpool v4.35.0-rc3, plain and `module`; a Strata v4.29.1 `module` file): "unknown namespace `Command`". Only used when the
    program did not run without it (finer_reading retries once), as scorer.compile does for its measuring command."""
    m = _MODULE_LINE.match(head)
    return head[:m.end()] + META_IMPORT + head[m.end():] if m else PLAIN_IMPORT + head


def new_nonce() -> str:
    return secrets.token_hex(8)


def name_literal(name: str) -> str:
    """A Lean name literal for a name as the statement writes it (`foo`, `Ns.foo`, `«x y».z`, `_root_.foo`)."""
    if not name or any(ch in name for ch in "\n\r`") or name.strip() != name:
        raise ValueError(f"not a name to print: {name!r}")
    return "`" + name


def program(names: list[str], nonce: str, proof_line: int) -> str:
    """The Lean program for the printed names `names` (the plain and the namespace-qualified name, as `#print axioms` gets them).
    `proof_line`: the compiled file's first line after the library file's prefix (the proof text's modifiers and text start there):
    a source of the file declared at or after it is OWN."""
    if not re.fullmatch(r"[0-9a-f]{8,64}", nonce or ""):
        raise ValueError("the nonce must be hex")
    if not isinstance(proof_line, int) or isinstance(proof_line, bool) or proof_line < 1:
        raise ValueError(f"the proof's first line must be a line number, not {proof_line!r}")
    qs = "[" + ", ".join(name_literal(n) for n in dict.fromkeys(names)) + "]"
    return (PROGRAM.replace("@MARK@", MARK).replace("@NONCE@", nonce).replace("@FUEL@", str(FUEL)).replace("@VERSION@", str(VERSION))
            .replace("@PRIVATE@", PRIVATE_TAG).replace("@LINE@", str(proof_line)).replace("@QUERIES@", qs).lstrip("\n"))


# -------------------------------------------------------------------------------------------- texts that can change what is read
# A proof text is compiled before the readings' own commands (`#print axioms`, the program above) in the same file. A text that
# registers an elaborator, a macro, syntax or another hook can change what those commands do and print (review 2026-11-24: a
# `@[command_elab Lean.Parser.Command.eval]` handler faked the program's lines; `@[command_elab Lean.Parser.Command.printAxioms]`
# fakes `#print axioms`). The Arena's forbidden list rejects the keyword forms but not the attribute forms (`@[command_elab ...]
# private def`, `open X in attribute [...]`), nor a text the guard reads without it (the reference proof). hooks() is read for
# every reading of the guard (with the finer check on); finer_hooks() adds what can change the program's own elaboration
# (instances, unification hints, `deriving`, a `_root_` inside a name; not `unsafe`: an unsafe definition changes the program
# only through an instance or a compiler attribute, both read, and aesop writes `(add unsafe ...)`) and is read for every finer
# reading.
_HOOK_WORDS = re.compile(
    r"#\s*eval\b|\beval%|\b(?:macro|macro_rules|elab|elab_rules|syntax|declare_syntax_cat|notation\d*|binder_predicate|initialize|"
    r"builtin_initialize|run_cmd|run_elab|run_meta|run_tacq?|by_elabq?|d?simproc(?:_decl|_pattern)?|register_\w+|"
    r"command_elab|term_elab|app_unexpander|app_delab|delab|csimp|implemented_?[Bb]y|extern|builtin_\w+|\w+_parser|\w+_elab|"
    r"\w*code_action|\w+_formatter|\w+_parenthesizer|\w+_unexpander|\w+_delab|quot_precheck)\b")
_MIXFIX = re.compile(r"(?<![\w.'!?])(?:infixl|infixr|infix|prefix|postfix)\s*(?::\s*(?:\([^)\n]*\)|[\w.]+))?\s*"
                     r"(?:\(\s*\w+\s*:=[^)\n]*\)\s*)*\"")
_SCOPE_WORDS = re.compile(r"\b(?:instance|default_instance|unif_hint|deriving)\b|[\w'!?»]\s*\.\s*«?_root_\b")
_ATTR_OPEN = re.compile(r"@\[|(?<![\w.'!?])attribute\s*\[")
_BLANK = re.compile(r'"(?:\\.|[^"\\])*"|«[^»]*»|\'(?:\\.|[^\'\\\n])\'')   # strings, «names», char literals: their brackets do not count
# attribute names (the first word of an entry of `@[...]` / `attribute [...]`) that register a hook or change compiled code
_HOOK_ATTRS = frozenset({"command_elab", "term_elab", "tactic", "macro", "delab", "app_delab", "app_unexpander", "init", "extern",
                         "implemented_by", "implementedBy", "csimp", "export", "incremental", "formatter", "parenthesizer",
                         "combinator_formatter", "combinator_parenthesizer", "run_builtin_parser_attribute_hooks",
                         "run_parser_attribute_hooks", "env_linter", "quot_precheck"})
_HOOK_ATTR_ENDS = ("_elab", "_parser", "_delab", "_formatter", "_parenthesizer", "_unexpander", "_precheck", "code_action", "_init")


def _attr_names(code: str) -> list[str]:
    """The first word of every entry of every attribute list (`@[a, b x]`, `attribute [local a] x`) of `code` (comments removed),
    brackets matched with strings and char literals blanked and «names» unquoted without their brackets and commas (`@[«tactic» x]`
    names `tactic`); `local`, `scoped` and `-` dropped."""
    s = _BLANK.sub(lambda m: re.sub(r"[\[\](){},\s]", "", m.group()[1:-1]) if m.group().startswith("«") else "x" * len(m.group()), code)
    out = []
    for m in _ATTR_OPEN.finditer(s):
        i, depth, entry = m.end(), 1, []
        entries = []
        while i < len(s) and depth:
            ch = s[i]
            if ch in "[({":
                depth += 1
            elif ch in "])}":
                depth -= 1
            if depth == 1 and ch == ",":
                entries.append("".join(entry))
                entry = []
            elif depth:
                entry.append(ch)
            i += 1
        entries.append("".join(entry))
        for e in entries:
            e = re.sub(r"\A\s*(?:(?:local|scoped)\b\s*|-\s*)*", "", e)
            w = re.match(r"[\w.'!?]+", e)
            if w:
                out.append(w.group().split(".")[-1])
    return out


def _strip(text: str) -> str:
    from scorer.forbidden import strip_lean_comments   # the scorer's comment remover (strings kept)
    return strip_lean_comments(text or "")


def hooks(text: str | None) -> str | None:
    """Why `text` can change how a later command of the same file is parsed or elaborated, or what compiled code does (None: it
    cannot, by this reading): a macro, elaborator, syntax, notation or simproc declaration, code run at elaboration (`#eval`,
    `run_cmd`, ...), or an attribute that registers an elaborator, macro, parser, delaborator or a compiler hook."""
    s = _strip(text)
    m = _HOOK_WORDS.search(s) or _MIXFIX.search(s)
    if m:
        return f"its text declares or runs metaprogramming ({m.group().strip()[:40]!r}), which can change what the reading prints"
    for n in _attr_names(s):
        if n in _HOOK_ATTRS or n.endswith(_HOOK_ATTR_ENDS) or n.startswith("builtin_"):
            return f"its text registers the attribute {n!r}, which can change what the reading prints"
    return None


def finer_hooks(text: str | None) -> str | None:
    """hooks(), and what can change the elaboration of the program itself: an instance (any form), a unification hint, `deriving`
    or a name with `_root_` inside it (it would come first in the resolution of the program's `_root_.` names)."""
    h = hooks(text)
    if h:
        return h
    m = _SCOPE_WORDS.search(_strip(text))
    if m:
        return f"its text declares {m.group().strip()[:40]!r}, which can change how the finer program elaborates"
    return None


# ----------------------------------------------------------------------------------------------------------------------- the output
_FIELDS = {"q": str, "decl": str, "decl_local": bool, "sources": list, "own": list, "local": list, "unranged": list, "missing": list,
           "axioms": list, "complete": bool}
_END_FIELDS = {"markers": int, "unresolved": list, "complete": bool, "proof_line": int}


def _msg_line(m: dict) -> int | None:
    pos = m.get("pos") if isinstance(m, dict) else None
    line = pos.get("line") if isinstance(pos, dict) else None
    return line if isinstance(line, int) and not isinstance(line, bool) else None


def _strings(x) -> bool:
    return isinstance(x, list) and all(isinstance(s, str) for s in x)


def parse(messages: list, first_line: int, nonce: str, proof_line: int | None = None) -> dict:
    """The program's output in Lean's messages: {"markers": [...], "end": {...}} or {"error": why}. Only `information` messages at or
    after `first_line` (the program's first line) that start with this compile's nonce are read; any other line is ignored. Fails
    (an "error") on: no end line, a line that does not parse, a field of the wrong type, a marker of another version, two end lines,
    two markers for the same (printed name, declaration), a count that differs from the end line's, no marker at all, an end line
    whose `proof_line` is not `proof_line` (when given)."""
    head = f"{MARK} {nonce} "
    markers, ends = [], []
    for m in messages or []:
        if not isinstance(m, dict) or m.get("severity") != "information":
            continue
        line = _msg_line(m)
        data = str(m.get("data", ""))
        if line is None or line < first_line or not data.startswith(head):
            continue
        try:
            j = json.loads(data[len(head):].strip())
        except ValueError:
            return {"error": "a marker line does not parse"}
        if not isinstance(j, dict) or j.get("v") != VERSION:
            return {"error": f"a marker of another version ({j.get('v') if isinstance(j, dict) else type(j).__name__})"}
        (ends if j.get("end") is True else markers).append(j)
    if not ends:
        return {"error": "no end line" + (" (the program did not finish)" if markers else ": the program did not run")}
    if len(ends) > 1:
        return {"error": "two end lines"}
    end = ends[0]
    if end.get("error"):
        return {"error": f"the program: {str(end['error'])[:160]}"}
    for k, t in _END_FIELDS.items():
        if not isinstance(end.get(k), t) or (t is int and isinstance(end.get(k), bool)):
            return {"error": f"the end line's {k!r} is not a {t.__name__}"}
    if not _strings(end["unresolved"]):
        return {"error": "the end line's 'unresolved' is not a list of names"}
    if proof_line is not None and end["proof_line"] != proof_line:
        return {"error": f"the program read the proof's first line as {end['proof_line']}, not {proof_line}"}
    seen = set()
    for j in markers:
        for k, t in _FIELDS.items():
            if not isinstance(j.get(k), t) or (t is list and not _strings(j[k])):
                return {"error": f"a marker's {k!r} is not a {t.__name__}" + (" of names" if t is list else "")}
        if (j["q"], j["decl"]) in seen:
            return {"error": f"two markers for {j['q']} -> {j['decl']}"}
        seen.add((j["q"], j["decl"]))
        if (not set(j["local"]) <= set(j["sources"]) or not set(j["own"]) <= set(j["local"])
                or not set(j["unranged"]) <= set(j["own"])):
            return {"error": "a marker's own, local or unranged sources are not among its sources"}
    if end["markers"] != len(markers):
        return {"error": f"the end line counts {end['markers']} marker(s), {len(markers)} read"}
    if not markers:
        return {"error": "no printed name resolved to a declaration" + (f" ({', '.join(end['unresolved'])})" if end["unresolved"] else "")}
    return {"markers": markers, "end": end}


EVIDENCE = ("its text names a way to hide Lean's sorry message", "Lean's sorry message on its declaration",
            "its compile reports an error in the declaration")


def wanting(why: str | None) -> bool:
    """A side of decide() that is not available for want of a reading (time, a failure), not for evidence against the proof."""
    return why is not None and why != "read" and why not in EVIDENCE


def sources_of(fr, side: str) -> tuple[dict | None, str]:
    """({"sources": frozenset, "own": frozenset, "decls": [...]}, "read") of one finer reading, or (None, why it is not available).
    side "proof": the union over the markers (every printed name's sources count against the proof); side "reference": the
    intersection (a name that resolves to another constant never widens what is allowed); OWN: the union on both sides."""
    if fr is None:
        return None, "not read within the time budget"
    if not isinstance(fr, dict):
        return None, "no reading"
    for k, why in (("error", None), ("hook", None), ("timed_out", "its compile timed out"),
                   ("switch", "its text names a way to hide Lean's sorry message"), ("sorry_warning", "Lean's sorry message on its declaration"),
                   ("decl_errors", "its compile reports an error in the declaration")):
        if fr.get(k):
            return None, (str(fr[k])[:160] if why is None else why)
    ms = fr.get("markers")
    if not isinstance(ms, list) or not ms:
        return None, "no marker"
    bad = [m for m in ms if not m.get("complete") or m.get("missing") or m.get("decl_local") is not True]
    if bad:
        m = bad[0]
        return None, (f"the walk from {m.get('decl')} did not finish (fuel)" if not m.get("complete") else
                      f"constants of the file not in the kernel's environment: {sorted(m.get('missing'))[:3]}" if m.get("missing") else
                      f"the printed name {m.get('q')} resolves to {m.get('decl')}, a constant of another file")
    sets = [frozenset(m["sources"]) for m in ms]
    srcs = frozenset.union(*sets) if side == "proof" else frozenset.intersection(*sets)
    own = frozenset().union(*(frozenset(m["own"]) for m in ms))
    if "sorryAx" in set().union(*(m["axioms"] for m in ms)) and not frozenset.union(*sets):
        return None, "its axioms read sorryAx, but it names no source (the program missed one)"
    return {"sources": srcs, "own": own, "decls": sorted({m["decl"] for m in ms})}, "read"


def _same_axioms(fr, axioms) -> str | None:
    """None when the finer reading's axioms (the union over its markers) are the axiom reading's `axioms` (None: not checked); else why
    not: the finer compile did not elaborate the declaration as the axiom reading's compile did."""
    if axioms is None or not isinstance(fr, dict) or not fr.get("markers"):
        return None
    got = set().union(*(m["axioms"] for m in fr["markers"]))
    return None if got == set(axioms) else f"its finer compile reads the axioms {sorted(got)}, its axiom reading {sorted(axioms)}"


def decide(proof_fr, ref_fr, proof_axioms=None, ref_axioms=None) -> tuple[bool, str, dict]:
    """(OK?, why, fields for the report) on one pin where the proof passes the allowance with sorryAx: OK iff both finer readings are
    available, the reference's OWN sources are empty, the proof's OWN sources are empty and the proof's sources are a subset of
    the reference's. Every other case fails closed. `proof_axioms` / `ref_axioms`: the axiom readings' lists on the pin; a finer
    reading whose own axioms differ from them is not available (its compile is not the one the axiom reading judged)."""
    p, pwhy = sources_of(proof_fr, "proof")
    r, rwhy = sources_of(ref_fr, "reference")
    if p is not None and (d := _same_axioms(proof_fr, proof_axioms)):
        p, pwhy = None, d
    if r is not None and (d := _same_axioms(ref_fr, ref_axioms)):
        r, rwhy = None, d
    fields = {"finer_sources": sorted(p["sources"]) if p else None, "finer_own": sorted(p["own"]) if p else None,
              "finer_reference_sources": sorted(r["sources"]) if r else None, "finer_reference_own": sorted(r["own"]) if r else None,
              "finer_reading": pwhy, "finer_reference_reading": rwhy}
    if p is None:
        return False, f"its finer sorry reading is not available ({pwhy})", fields
    if r is None:
        return False, f"the reference proof's finer sorry reading is not available ({rwhy})", fields
    if r["own"]:
        return False, (f"the reference proof's own text rests on sorry (OWN sources {sorted(r['own'])}): the finer check cannot tell "
                       "a new sorry from it"), fields
    if p["own"]:
        return False, (f"its own text rests on sorry (OWN sources {sorted(p['own'])}); the reference proof's sources: "
                       f"{sorted(r['sources'])}"), fields
    new = sorted(p["sources"] - r["sources"])
    if new:
        return False, f"sorry sources {new} that the reference proof does not use (it uses {sorted(r['sources'])})", fields
    return True, f"sorry sources as the reference proof: {sorted(p['sources'])} (the reference's: {sorted(r['sources'])})", fields
