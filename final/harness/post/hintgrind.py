#!/usr/bin/env python3
"""Post-step v2 op "hintgrind": Lean-suggested closer collapse with harvested hints (open post-step, branch open-post-v2-hintgrind). A
tactic span of the proof (harness/post/spans.py: region / arm / havebody / suffix) is replaced by ONE closer that Lean itself prints for
that span's goal, given as hints the global constants the span already writes. Model-free, $0, deterministic; every token of a candidate
is either Lean tactic syntax listed here (the probe tactics and their `only` / `<;>` / `all_goals` combinators) or printed by Lean at run
time for the row's own goal, or a name the proof being edited already writes (resolved in the row's own environment). No row name, no
lemma list, no proof text, no table.

  sites     spans.spans(body) (wrapper-transparent parse), each >= 2 steps or >= 8 lexer tokens, minus a span that is already one closer
            of the probe families. EXCHANGE PRE-SCREEN: a span whose replacement saves d tokens is probed with closer class c only when
            d x rate >= HB_EST[c] (rate = reference heartbeats / reference tokens, the driver's `exchange`; HB_EST are generic constants,
            ESTIMATED). A row whose input primary compile takes more than SKIP_COMPILE_S is skipped (its probe files would hold 2 copies).
  harvest   H(span), in order of first occurrence, at most MAX_H_ALL names (a probe list keeps the first MAX_H its tactic accepts):
            (1) the identifiers written in the span (comments and strings masked; numerals, tactic words and names the proof or
            statement binds are not candidates); (2) every `.c` dot constructor and every field `f` of `x.f` (x a local, or a closing
            bracket) expanded to `Ns.c` / `Ns.f` for each capitalised namespace component Ns written in the statement or the proof (a
            dotted name that is no constant is also tried by its prefixes: `foo.mp` -> `foo`); a field that resolves under several
            components keeps only the component most of the span's fields and written names resolve under (the dominant namespace). QUERY A (one plain compile per proof key, the primary pin, the statement's own namespace opened): one
            `#eval` resolves each candidate with Lean.resolveGlobalConst and reports its kind, whether its type is a proposition and how
            many hypotheses it has; on a module file whose imports lack the Lean API (the `#eval` fails) error-free traced lines
            (`first | (have := (@name : (_ : Prop)); trace ..) | skip`) report the propositions instead. Kept: propositions (theorems,
            axioms, constructors of inductive predicates) and, for names written in the span, definitions (grind / simp unfold them). The
            `→` forward modifier is put on propositions with a hypothesis (or an unknown count).
  probe     QUERY B: renamed copies of the proof (the statement's own namespace kept, attributes dropped), each with one span replaced by
            a probe tactic, each preceded by `set_option maxHeartbeats N in` (N = the incumbent's heartbeats plus the span's exchange
            value, x 1.25, + 5000, clamped to [PROBE_HB_MIN, PROBE_HB_MAX]; the option stays in the probe file only), on the row's
            OLDEST pin (a suggestion that elaborates there is the least likely to break another pin). Menu, in this order over the ranked
            spans: (0) the plain `grind?` (region: `HEAD <;> grind?` too; no hint: the cheapest probe and, MEASURED, the likeliest to
            answer); (1) `grind? [H]` (and for a region with a head: `HEAD <;> grind? [H]`, `HEAD` + `all_goals grind? [H]`); (2)
            `grind? [→ H]` (region: `HEAD <;>` too), and for arm / region / have-body spans `grind? [H_all]` (H_all: the harvest of the
            whole proof; a region whose head is `induction x` / `cases x` also gets `(gen := 2)` and `have := x.chain` facts, the
            proof's own projection chains, numeric-tail chains first); (3) `simp_all? [H]`; (4) `simp? [H]` (non-region spans, SIMP_PROBE); (5)
            Lean core's `try?` (TRY_PROBE, off: MEASURED 0 answers in 120 copies, VM1 run v1v). Copies go to files in menu order: the
            first file sized by estimate (pack: per copy the input's compile minus Query A's header seconds, plus the copy's heartbeat
            cap at HB_PER_S), every later one from the last read file's own wall per copy (per_file_measured: the machine's load as
            it is); a timed-out file's copies are retried first at half the size; at most MAX_COPIES copies a file, MAX_FILES files,
            PROBE_WALL_S seconds per row; a first file whose copies all fail with one unknown-identifier error stops the row (the
            renamed copy itself does not elaborate). Pass 1 only: the answers are cached by span text for the row's later passes
            (a proof none of whose spans was probed, i.e. another input of the row, is probed afresh). Messages map to copies
            by line (a `#check` marker fixes the file offset). A copy is CLEAN when it has no error and no sorry warning (a failed `grind?`
            prints `grind => sorry`); only clean copies give candidates.
  generate  per clean copy, the first suggestion of each message that is a one-line `grind ... only [..]` / `simp_all only [..]` /
            `simp only [..]` (no `#` anchor, no `=>` script, no sorry, no `?`); several messages (one per goal under `<;>` /
            `all_goals`) give the union of their lists. Candidates: Lean's text in place of the span (with the region head), then at most
            BLIND_PER_SPAN blind shorter variants (the list without `only`, kept to the names that came from H; the plain `grind [H]` for
            a region). SCREEN: every candidate is measured in one-file batches on the primary pin (d4_measure's `#eval` reading, the
            incumbent first as the control) and only those predicted to read higher (heartbeats saved minus tokens added at the exchange
            rate) are proposed, best first; a batch whose control does not read leaves its candidates unscreened (after the screened
            ones, fewest tokens first). COMBOS: the screened singles predicted higher whose spans are disjoint, greedy best first (at
            most COMBO_MAX), applied together, screened in one more file and put first when predicted above the best single (the
            driver adopts one candidate per pass, and a collapse changes the text of the spans around it).
The driver (harness/open_post.py) reads at most READS["hintgrind"] proposals and adopts only through its gate (exact statement,
forbidden list, every pin, paired re-reading, sorry audit). No harm: no site, no answer, a timeout or a budget stop proposes nothing.
    python3 harness/post/hintgrind.py --proof-file P --statement-file S [--exchange R]     sites, harvest candidates and the probe plan"""
from __future__ import annotations

import argparse, hashlib, json, re, sys, threading, time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from harness.post import d4_kit as K  # noqa: E402
from harness.post import d4_measure as MS  # noqa: E402
from harness.post import spans as SP  # noqa: E402
from scorer.tokenize import count_tokens, split_declaration  # noqa: E402

OP = "hintgrind"
OPS = ("hintgrind:grind", "hintgrind:grind-fwd", "hintgrind:grind-all", "hintgrind:simp_all", "hintgrind:simp", "hintgrind:region",
       "hintgrind:try", "hintgrind:blind")
HB_EST = {"grind": 3000, "simp_all": 1500, "simp": 500}   # heartbeats (thousands) a closer of that class costs: generic, ESTIMATED
EST_CLOSER_TOKENS = 4      # tokens assumed for the replacing closer in the pre-screen (`grind only [x]` is 4 + the list)
MAX_H = 24                 # hints per probe list (after the tactic's own acceptance filter)
MAX_H_ALL = 40             # harvested names kept per span before that filter
MAX_NS = 16                # namespace components used for dot / field expansion
MAX_QUERY_NAMES = 600
MAX_SPANS = 48
MAX_FILES = 6
MAX_COPIES = 24
FILE_S = 210.0
SKIP_COMPILE_S = 60.0
PROBE_HB_MIN = 20000
PROBE_HB_MAX = 400000
BLIND_PER_SPAN = 2
SIMP_PROBE = True          # menu 4: `simp? [H]` (last; MEASURED: 0 answers in 274 + 366 copies on sub29, one banked arm on run 3)
TRY_PROBE = False          # menu 5: Lean core's `try?` on spans of at most TRY_MAX_LINES lines, in files of their own (last)
TRY_MAX_LINES = 8
TRY_MAX_COPIES = 12
TRY_PER_FILE = 4
MAX_FACT_CHAINS = 3        # region menu: `have := X.chain` facts before an `induction X` / `cases X` head
SCREEN_FILES = 2
COMBO_MAX = 6              # combos: at most this many disjoint spans in one candidate
COMBO_PREFIX = 2           # combos: besides the full greedy set, its prefixes of 2 .. COMBO_PREFIX + 1 spans
BODY_MIN_S = 1.0           # probe packing (pack): a copy costs at least this many seconds and BODY_MIN_FRAC of the input's compile
BODY_MIN_FRAC = 0.25
HB_PER_S = 20000.0         # heartbeats (thousands) a probe copy burns per second at its cap, a loaded-machine estimate (MEASURED order:
                           # ~40000 per second on an idle VM1 core, run r20v)
QUERY_TIMEOUT = 300
MAX_REPROBES = 1           # fresh probes of a row whose current proof shares no span with the probed one (query)
PROBE_WALL_S = 600.0       # no probe file starts after this many seconds of the row's probing (MEASURED: the slowest rows of run v2a
                           # spent 700 s in 6 files for 11-86 copies and answered nothing; the row's wall budget is shared)
CLOSER_HEADS = ("grind", "simp_all", "simp", "simpa", "aesop", "omega", "decide", "norm_num", "linarith", "trivial", "rfl", "exact")

_ID = re.compile(r"(?<![\w'!?.])(?![λΠΣ_])([^\W\d][\w'!?]*(?:\.(?:[^\W\d][\w'!?]*|\d+))*)")
_DOT = re.compile(r"(?<![\w'!?)\]}⟩›])\.([^\W\d][\w'!?]*)")
_FIELD_AFTER_BRACKET = re.compile(r"[)\]}⟩›]\.([^\W\d][\w'!?]*)")
_ANCHOR = re.compile(r"#[0-9a-f]{4}")
_SUGG = re.compile(r"^(grind(?:\s*\([^()]*\))*|simp_all|simp)\s+only(?:\s*\[(.*)\])?$", re.S)
TACTIC_WORDS = frozenset("""
at by do fun λ then else if let have show from with using only generalizing case next match this calc
intro intros rintro exact apply refine refine' obtain rcases cases induction simp simp_all simpa dsimp grind omega rfl constructor
left right use exists rw rewrite rwa erw unfold delta change clear revert set subst subst_vars generalize specialize exfalso contradiction
assumption trivial decide norm_num linarith nlinarith positivity ring ring_nf field_simp aesop tauto exact_mod_cast push_cast norm_cast
split by_cases by_contra push_neg injection injections nofun nomatch all_goals any_goals first try repeat iterate unhygienic classical
suffices sorry admit Type Prop Sort true false fun_induction fun_cases cases' induction' conv congr ext funext gcongr bound
split_ands simp_rw rename_i rintro' refine_lift exacts constructorm casesm rcases' obtain' nth_rewrite nth_rw simp_arith
""".split())
NO_HINT = frozenset(("rfl", "trivial", "id", "True", "False", "And", "Or", "Not", "Iff", "Eq", "Ne", "Exists", "absurd", "True.intro",
                     "And.intro", "Or.inl", "Or.inr", "Exists.intro", "HEq", "Function", "Classical", "Decidable"))

_LOCK = threading.Lock()
_CACHE: dict = {}   # statement sha -> {"probed": bool, "results": {(span text, menu): result}, "qa": {...}}


def _sha(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()[:16]


# ------------------------------------------------------------------------------------------------------------------------------ names
def decl_name(statement: str) -> tuple[str, str, str] | None:
    """(keyword, namespace prefix (may be ""), last component) of a theorem / lemma statement, else None."""
    m = MS.DECL_RE.match(statement)
    if not m:
        return None
    hm = re.search(r"(theorem|lemma)\s+([^\s(:{\[⦃]+)$", m.group(0))
    if not hm:
        return None
    name = hm.group(2)
    if ".{" in name or name.startswith("_root_") or "«" in name:
        return None
    ns, _, last = name.rpartition(".")
    return hm.group(1), ns, last


def renamed(statement: str, tag: str) -> str | None:
    """The statement as `theorem <Ns.>tag ...` (docstrings and attributes dropped; visibility modifiers kept: a public copy of a private
    theorem cannot name the module's private declarations; the namespace prefix kept), else None."""
    m = MS.DECL_RE.match(statement)
    dn = decl_name(statement)
    if not m or dn is None:
        return None
    _kw, ns, _last = dn
    pre = re.sub(r"/--(?:(?!-/).)*-/|@\[[^\]]*\]", " ", m.group(0), flags=re.S)
    mods = [w for w in re.findall(r"\b(private|protected|noncomputable|nonrec)\b", pre.split("theorem")[0].split("lemma")[0])]
    return " ".join(mods + ["theorem"]) + f" {(ns + '.') if ns else ''}{tag}" + statement[m.end():]


def _bound(body: str, statement: str) -> set:
    """Names the proof or the statement binds (approximate, generous): binder groups of the statement, intro / obtain / rcases / case /
    alternative / have / let / set / fun / generalize names of the proof."""
    out = set()
    code = SP._code(statement) + "\n" + SP._code(body)
    for m in re.finditer(r"[({\[⦃]\s*([^():{}\[\]⦃⦄]+?)\s*:", code):
        out.update(w for w in m.group(1).split() if _ID.fullmatch(w))
    for m in re.finditer(r"(?<![\w'])(?:intro|intros|rintro|fun|λ|∀|∃|∃!|case|case'|next|have|haveI|let|set|obtain|generalize|"
                         r"rcases|cases|induction|with|at)\b([^\n:=,]*)", code):
        out.update(w for w in re.findall(r"[^\W\d][\w'!?]*", m.group(1)))
    for m in re.finditer(r"⟨([^⟨⟩]*)⟩", code):
        out.update(w for w in re.findall(r"(?<![\w.])([^\W\d][\w'!?]*)(?![\w.])", m.group(1)))
    for m in re.finditer(r"^\s*\|\s*([^\n=]*)=>", code, re.M):
        out.update(w for w in re.findall(r"[^\W\d][\w'!?]*", m.group(1))[1:])
    return out - {"_"}


def namespaces(statement: str, body: str) -> list[str]:
    """Capitalised identifier components (two characters or more, not a bound local) written in the statement or the proof, most frequent
    first (ties: first occurrence)."""
    code = SP._code(statement) + "\n" + SP._code(body)
    bd = _bound(body, statement)
    cnt: dict = {}
    order: dict = {}
    for m in _ID.finditer(code):
        for c in m.group(1).split("."):
            if len(c) > 1 and c[0].isupper() and c not in TACTIC_WORDS and c not in NO_HINT and c not in bd:
                cnt[c] = cnt.get(c, 0) + 1
                order.setdefault(c, len(order))
    return sorted(cnt, key=lambda c: (-cnt[c], order[c]))[:MAX_NS]


def written(text: str, bound: set) -> tuple[list[str], list[str]]:
    """(direct candidate names, dot / field components) written in `text` (masked code), in order of first occurrence. A dotted
    identifier gives its longest non-numeric prefix as a direct name (unless its first component is a bound local) and, when its first
    component is lower-case or bound (a local with field notation), its later components as fields; components after a numeric
    projection are fields too."""
    code = SP._code(text)
    direct, fields = [], []

    def field(c):
        if c and not c.isdigit() and c not in fields:
            fields.append(c)

    for m in _ID.finditer(code):
        comps = m.group(1).split(".")
        first = comps[0]
        if first in TACTIC_WORDS:
            continue
        k = next((i for i, c in enumerate(comps) if c.isdigit()), len(comps))
        if first in bound or (first[:1].islower() and len(comps) > 1):
            for c in comps[1:]:
                field(c)
        else:
            for c in comps[k:]:
                field(c)
        if first in bound:
            continue
        name = ".".join(comps[:k])
        if name and name not in direct and name not in NO_HINT:
            direct.append(name)
    for rx in (_DOT, _FIELD_AFTER_BRACKET):
        for m in rx.finditer(code):
            field(m.group(1))
    return direct, fields


def query_names(proof: str, statement: str) -> list[str]:
    """Every name Query A resolves for this proof: the direct names of the whole body and Ns.f for each namespace component Ns and each
    dot / field component f, at most MAX_QUERY_NAMES (direct names first)."""
    body = split_declaration(proof, statement)
    if body is None:
        return []
    bd = _bound(body, statement)
    direct, fields = written(body, bd)
    nss = namespaces(statement, body)
    out, seen = [], set()
    for n in direct:
        comps = n.split(".")
        for j in range(len(comps), 0, -1):   # the name, then its prefixes (`foo.mp` resolves as `foo` when `foo.mp` is no constant)
            p = ".".join(comps[:j])
            if p not in seen:
                seen.add(p); out.append(p)
    for f in fields:
        for ns in nss:
            n = f"{ns}.{f}"
            if n not in seen:
                seen.add(n); out.append(n)
    return out[:MAX_QUERY_NAMES]


QUERY_A = r'''theorem lraHGDummy : True := trivial
#check lraHGDummy
LRAHGOPEN
#eval show Lean.Elab.Command.CommandElabM Unit from do
  for s in LRAHGNAMES do
    try
      let ns ← Lean.resolveGlobalConst (Lean.mkIdent s.toName)
      for n in ns do
        let r ← Lean.Elab.Command.liftTermElabM do
          let ci ← Lean.getConstInfo n
          let isP ← Lean.Meta.isProp ci.type
          let nh ← Lean.Meta.forallTelescope ci.type fun xs _ => do
            let mut k := 0
            for x in xs do
              if ← Lean.Meta.isProp (← Lean.Meta.inferType x) then
                k := k + 1
            return k
          let kind := match ci with
            | .thmInfo _ => "thm"
            | .axiomInfo _ => "axiom"
            | .ctorInfo _ => "ctor"
            | .inductInfo _ => "induct"
            | .defnInfo _ => "def"
            | .opaqueInfo _ => "opaque"
            | .recInfo _ => "rec"
            | _ => "other"
          return s!"{kind}\t{if isP then 1 else 0}\t{nh}"
        Lean.logInfo (Lean.toMessageData s!"LRAHGA\t{s}\t{n}\t{r}")
    catch _ => pure ()
LRAHGLINES
LRAHGCLOSE
'''
PROP_LINE = ('example : True := by\n  first | (have := (@NAME : (_ : Prop)); trace "LRAHGP\tIDX") | skip\n  trivial\n'
             'example : True := by\n  first | (grind only [NAME]; trace "LRAHGG\tIDX") | trivial\n'
             'example : True := by\n  first | (grind only [→ NAME]; trace "LRAHGF\tIDX") | trivial\n'
             'example : True := by\n  first | (simp only [NAME]; trace "LRAHGS\tIDX") | trivial\n')


def query_a_text(statement: str, names: list[str]) -> str | None:
    """Query A: the statement's namespace opened; one `#eval` that resolves every name with Lean.resolveGlobalConst and reports kind,
    proposition and hypothesis count (on a module file that does not import the Lean API it fails once, harmlessly), then, module-safe
    and error-free, one `example` per name whose `first | (have := (@name : (_ : Prop)); trace ..) | skip` traces the index of every name
    that is a proposition (a flood of errors would stop Lean before the end of the file)."""
    dn = decl_name(statement)
    if dn is None or not names:
        return None
    ns = dn[1]
    lst = "[" + ", ".join(K.lean_str(n) for n in names) + "]"
    lines = "".join(PROP_LINE.replace("NAME", n).replace("IDX", str(i)) for i, n in enumerate(names))
    return (QUERY_A.replace("LRAHGNAMES", lst).replace("LRAHGOPEN", f"namespace {ns}" if ns else "")
            .replace("LRAHGCLOSE", f"end {ns}" if ns else "").replace("LRAHGLINES", lines))


def parse_query_a(messages, names: list[str] | None = None) -> dict:
    """{written name: {"full", "kind", "prop": bool, "hyps": int}}: from the `#eval` report when it answered (the first resolution of
    each name), else from the traced `example` lines (kind "prop", hypotheses unknown: -1)."""
    out: dict = {}
    tags = {"LRAHGP": set(), "LRAHGG": set(), "LRAHGF": set(), "LRAHGS": set()}
    for m in messages or []:
        for ln in K.msg_text(m).split("\n"):
            p = ln.split("\t")
            if len(p) >= 6 and p[0] == "LRAHGA" and p[1] not in out:
                try:
                    out[p[1]] = {"full": p[2], "kind": p[3], "prop": p[4] == "1", "hyps": int(p[5])}
                except ValueError:
                    continue
            elif len(p) >= 2 and p[0] in tags and p[1].strip().isdigit():
                tags[p[0]].add(int(p[1].strip()))
    if not names:
        return out
    tested = any(tags[t] for t in ("LRAHGG", "LRAHGF", "LRAHGS"))
    for i, n in enumerate(names):
        if n not in out and i in tags["LRAHGP"]:
            out[n] = {"full": n, "kind": "prop", "prop": True, "hyps": -1}
        if n in out:
            # grind / simp accept the name as a hint (the traced `grind only [n]` / `grind only [→ n]` / `simp only [n]` on `True`)
            out[n]["grind"] = (i in tags["LRAHGG"]) if tested else True
            out[n]["fwd"] = (i in tags["LRAHGF"]) if tested else out[n]["hyps"] != 0
            out[n]["simp"] = (i in tags["LRAHGS"]) if tested else True
    return out


def hints(span_text: str, statement: str, body: str, qa: dict, nss: list[str] | None = None) -> list[dict]:
    """H(span): [{"name", "prop", "hyps"}] in order of first occurrence (module docstring, "harvest"), at most MAX_H."""
    bd = _bound(body, statement)
    direct, fields = written(span_text, bd)
    nss = nss if nss is not None else namespaces(statement, body)
    out, fulls = [], set()

    def usable(n, direct_name):
        r = qa.get(n)
        if not r or (r.get("grind") is False and r.get("simp") is False):
            return False
        return bool((r["prop"] and r["kind"] in ("thm", "axiom", "ctor", "prop"))
                    or (direct_name and r["kind"] in ("def", "opaque") and not r["prop"]))

    def take(n, direct_name):
        r = qa.get(n)
        if not usable(n, direct_name) or r["full"] in fulls:
            return
        fulls.add(r["full"])
        out.append({"name": n, "prop": r["prop"], "hyps": r["hyps"], "kind": r["kind"], "grind": r.get("grind", True),
                    "fwd": r.get("fwd", r["hyps"] != 0), "simp": r.get("simp", True)})

    for n in direct:
        comps = n.split(".")
        hit = next((".".join(comps[:j]) for j in range(len(comps), 0, -1) if ".".join(comps[:j]) in qa), None)
        if hit is not None:
            take(hit, True)
    # a field `x.f` / dot constructor `.c` names ONE constant (in the namespace of x's type / of the expected type): a field that
    # resolves under several namespace components keeps only the component under which most of the span's fields resolve (ties: the
    # component written most in the statement and proof). MEASURED (VM1 dev runs on one region): the other namespaces' namesakes cost
    # E-matching budget and the hint cap
    res = {f: [ns for ns in nss if usable(f"{ns}.{f}", False)] for f in fields}
    hits: dict = {}
    for f, nl in res.items():
        for ns in nl:
            hits[ns] = hits.get(ns, 0) + 1
    for h in out:   # the namespaces of the names written in full count too
        if "." in h["name"]:
            c = h["name"].split(".")[0]
            hits[c] = hits.get(c, 0) + 1
    rank = {ns: i for i, ns in enumerate(nss)}
    for f in fields:
        nl = res.get(f) or []
        if len(nl) > 1:
            nl = [min(nl, key=lambda ns: (-hits.get(ns, 0), rank[ns]))]
        for ns in nl:
            take(f"{ns}.{f}", False)
    return out[:MAX_H_ALL]


def hint_list(H: list[dict], fwd: bool = False, tactic: str = "grind") -> str:
    """` [h1, h2, ..]` of the hints the tactic accepts (Query A's traced tests), the first MAX_H of them; fwd: `→` on those that accept
    it."""
    if tactic == "simp":
        items = [h["name"] for h in H if h.get("simp", True)]
    else:
        items = [("→ " if fwd and h.get("fwd", h["hyps"] != 0) else "") + h["name"] for h in H if h.get("grind", True)]
    items = items[:MAX_H]
    return " [" + ", ".join(items) + "]" if items else ""


# ------------------------------------------------------------------------------------------------------------------------------ sites
def _is_closer_span(sp: dict) -> bool:
    if sp["steps"] != 1:
        return False
    m = re.match(r"[^\W\d][\w'!?]*", sp["text"])
    return bool(m) and m.group(0) in ("grind", "simp_all", "simp", "simpa", "aesop")


def sites(proof: str, statement: str, exchange=None) -> list[dict]:
    """The probe-able spans of the proof after the exchange pre-screen (module docstring), ranked by tokens saved (most first). Each
    span gets "classes" (the closer classes that pass) and "d" (tokens saved, estimated)."""
    body = split_declaration(proof, statement)
    if body is None or decl_name(statement) is None:
        return []
    out = []
    for sp in SP.spans(body):
        if _is_closer_span(sp):
            continue
        d = sp["tokens"] - EST_CLOSER_TOKENS
        if sp["kind"] == "region" and sp.get("head"):
            d_reg = sp["tokens"] - count_tokens(sp["head"]) - EST_CLOSER_TOKENS - 1
        else:
            d_reg = None
        cls = []
        for c, est in HB_EST.items():
            dd = d if c != "grind" or d_reg is None else max(d, d_reg)
            if dd <= 0:
                continue
            if exchange and dd * float(exchange) < est:
                continue
            cls.append(c)
        if not cls:
            continue
        out.append(dict(sp, d=d, d_region=d_reg, classes=cls))
    out.sort(key=lambda s: (-max(s["d"], s["d_region"] or 0), s["lo"]))
    return out[:MAX_SPANS]


def has_sites(proof: str, statement: str) -> bool:
    """Pure pre-check for the driver (no exchange known there): some span exists."""
    return bool(sites(proof, statement, None))


# ------------------------------------------------------------------------------------------------------------------------------ probe
def probe_cap(inc_hb, d: int, exchange) -> int:
    try:
        base = float(inc_hb or 0)
    except (TypeError, ValueError):
        base = 0.0
    if not exchange:
        return PROBE_HB_MAX // 2
    v = int(1.25 * (base + max(0, d) * float(exchange))) + 5000
    return max(PROBE_HB_MIN, min(PROBE_HB_MAX, v))


_CHAIN = re.compile(r"[)\]⟩]\.([^\W\d][\w'!?]*)((?:\.\d+)*)(?![\w'!?])")
_TARGET = re.compile(r"^(?:induction|cases|fun_induction|fun_cases)\s+([^\W\d][\w'!?]*)(?=\s|$)")


def chains(body: str, qa: dict, nss: list[str], limit: int = MAX_FACT_CHAINS) -> list[str]:
    """Projection chains `.f` / `.f.2.1` written in the proof whose field f resolves, as `Ns.f` for a namespace component Ns, to a
    proposition with hypotheses (a fact about its argument), first occurrence first, at most `limit`."""
    out = []
    code = SP._code(body)
    found = []   # (offset, field, numeric tail): after a closing bracket, or after a lower-case (local) head
    for m in _CHAIN.finditer(code):
        found.append((m.start(), m.group(1), m.group(2) or ""))
    for m in _ID.finditer(code):
        comps = m.group(1).split(".")
        if not comps[0][:1].islower():
            continue
        for j in range(1, len(comps)):
            if not comps[j].isdigit():
                k = j + 1
                while k < len(comps) and comps[k].isdigit():
                    k += 1
                found.append((m.start(), comps[j], "".join("." + c for c in comps[j + 1:k])))
    cnt: dict = {}
    first: dict = {}
    for pos, f, nums in sorted(found):
        ok = any((qa.get(f"{ns}.{f}") or {}).get("prop") and (qa.get(f"{ns}.{f}") or {}).get("hyps", 0) != 0 for ns in nss)
        ch = "." + f + nums
        if ok:
            cnt[ch] = cnt.get(ch, 0) + 1
            first.setdefault(ch, pos)
    # a chain that ends in numeric projections extracts a conjunct of a fact (the proof's own `x.f.2.1`): first; then the most
    # written; then the first written
    out = sorted(cnt, key=lambda ch: (0 if re.search(r"\.\d+$", ch) else 1, -cnt[ch], first[ch]))
    return out[:limit]


def plan(proof: str, statement: str, spans: list[dict], qa: dict, exchange=None, inc_hb=None) -> list[dict]:
    """The probe copies, in menu order: [{"key": (span text, menu), "menu", "span", "prefix", "rep" (= prefix + the probe tactic: the
    span's replacement), "H", "cap"}]. "prefix" is what a candidate keeps in front of Lean's printed closer (a region's head and its
    combinator, and the facts stated before it)."""
    body = split_declaration(proof, statement)
    nss = namespaces(statement, body)
    menus = {0: [], 1: [], 2: [], 3: [], 4: [], 5: []}
    seen = set()
    H_all = hints(body, statement, body, qa, nss)
    fact_chains = chains(body, qa, nss)
    for sp in spans:
        H = hints(sp["text"], statement, body, qa, nss)
        sp["H"] = H
        ind = " " * sp["indent"]
        cap = probe_cap(inc_hb, max(sp["d"], sp.get("d_region") or 0), exchange)

        def add(level, menu, prefix, probe, cls, hs=None):
            if cls not in sp["classes"]:
                return
            rep = prefix + probe
            k = (sp["lo"], sp["hi"], rep)
            if k in seen:
                return
            seen.add(k)
            menus[level].append({"key": (sp["text"], menu), "menu": menu, "span": sp, "prefix": prefix, "rep": rep,
                                 "H": H if hs is None else hs, "cap": cap})

        head = sp.get("head") if sp["kind"] == "region" else None
        # a suffix (or a whole region) of a flat block may close several goals: probe under `all_goals` (one message per goal; a
        # candidate drops the combinator when only one goal answered); an arm / have body closes exactly one goal
        ag = "all_goals " if sp["kind"] in ("suffix", "region") else ""
        # (0) the plain closer first: no hints (MEASURED, VM1 run v1v: grind? copies with no hint answered 4 of 9 times, with 1-8
        # hints 5 of 139, with more than 8 none of 235; hints mostly cost heartbeats), then the hinted forms
        add(0, "grind0", ag, "grind?", "grind", hs=[])
        if head:
            add(0, "region<;>0", head + " <;> ", "grind?", "grind", hs=[])
        hl = hint_list(H)
        add(1, "grind", ag, "grind?" + hl, "grind")
        if head:
            add(1, "region<;>", head + " <;> ", "grind?" + hl, "grind")
            add(1, "region-all", head + "\n" + ind + "all_goals ", "grind?" + hl, "grind")
        fl = hint_list(H, fwd=True)
        if fl != hl:
            add(2, "grind-fwd", ag, "grind?" + fl, "grind")
            if head:
                add(2, "region<;>fwd", head + " <;> ", "grind?" + fl, "grind")
        al = hint_list(H_all)
        if sp["kind"] in ("arm", "region", "havebody") and al != hl:
            add(2, "grind-all", ag, "grind?" + al, "grind")
            if head:
                add(2, "region<;>all", head + " <;> ", "grind?" + al, "grind")
        tm = _TARGET.match(head or "")
        if head and tm:
            # facts about the split target, stated before the split (the proof's own projection chains), and a deeper E-matching
            # generation; the first chain with gen := 2 early (MEASURED: the banked region collapses of runs v2a / r3a were this form;
            # without gen := 2 the same probe ran out of heartbeats in a dev run)
            for k, ch in enumerate(fact_chains):
                pre = f"have := {tm.group(1)}{ch}\n{ind}"
                add(1 if k == 0 else 2, "region<;>factgen", pre + head + " <;> ", "grind? (gen := 2)" + fl, "grind")
                if k == 0:
                    add(2, "region<;>fact", pre + head + " <;> ", "grind?" + fl, "grind")
            add(2, "region<;>gen", head + " <;> ", "grind? (gen := 2)" + fl, "grind")
        sl = hint_list(H, tactic="simp")
        add(3, "simp_all", ag, "simp_all?" + sl, "simp_all")
        if SIMP_PROBE and sp["kind"] != "region":
            add(4, "simp", ag, "simp?" + sl, "simp")
        if TRY_PROBE and sp["text"].count("\n") < TRY_MAX_LINES and sp["kind"] != "region":
            add(5, "try", "", "try?", "simp")
    return menus[0] + menus[1] + menus[2] + menus[3] + menus[4] + menus[5][:TRY_MAX_COPIES]


def per_file(compile_s) -> int:
    cs = float(compile_s) if isinstance(compile_s, (int, float)) and compile_s > 0 else 15.0
    return max(2, min(MAX_COPIES, int(FILE_S / cs)))


def per_file_measured(file_s, header_s, n: int, k: int) -> int:
    """Copies for the next probe file from the last read file's wall: (FILE_S - header) / (that file's seconds per copy), within
    [2, MAX_COPIES]; k unchanged without a reading."""
    try:
        fs = float(file_s)
    except (TypeError, ValueError):
        return k
    hs = float(header_s) if isinstance(header_s, (int, float)) and 0 < header_s < fs else 0.0
    if n <= 0 or fs <= 0:
        return k
    per = max(0.25, (fs - hs) / n)
    return max(2, min(MAX_COPIES, int((FILE_S - hs) / per)))


def body_seconds(compile_s, header_s) -> float:
    """Seconds one copy of the proof costs in a probe file: the input's primary compile minus the file header's share (Query A's wall
    time: the same imports and prefix, almost no proof), at least BODY_MIN_FRAC of the compile and BODY_MIN_S."""
    cs = float(compile_s) if isinstance(compile_s, (int, float)) and compile_s > 0 else 15.0
    hs = float(header_s) if isinstance(header_s, (int, float)) and 0 < header_s < cs else 0.0
    return max(BODY_MIN_S, BODY_MIN_FRAC * cs, cs - hs)


def pack(copies: list[dict], compile_s, header_s, file_s: float | None = None) -> list[list[dict]]:
    """The copies in files, in order: a file holds at most MAX_COPIES copies and at least 2, and its estimated wall (the header, then
    per copy the proof's own seconds plus its heartbeat cap at HB_PER_S) stays within FILE_S. Without a header reading: per_file."""
    if not isinstance(header_s, (int, float)) or header_s <= 0:
        kf = per_file(compile_s)
        return [copies[i:i + kf] for i in range(0, len(copies), kf)]
    bs = body_seconds(compile_s, header_s)
    fs = FILE_S if file_s is None else float(file_s)
    out, cur, t = [], [], float(header_s)
    for c in copies:
        e = bs + float(c.get("cap") or 0) / HB_PER_S
        if cur and (len(cur) >= MAX_COPIES or (t + e > fs and len(cur) >= 2)):
            out.append(cur); cur, t = [], float(header_s)
        cur.append(c); t += e
    if cur:
        out.append(cur)
    return out


PROBE_HEAD = "theorem lraHGDummy : True := trivial\n#check lraHGDummy\n"


def probe_file(proof: str, statement: str, copies: list[dict], base: int = 0) -> tuple[str, list[tuple[int, int]]] | None:
    """(file text, [(first line, last line)] per copy, 1-based within the text)."""
    hb = K.head_body(proof, statement)
    if hb is None:
        return None
    _head, body = hb
    parts, ranges = [PROBE_HEAD], []
    line = PROBE_HEAD.count("\n") + 1
    for i, c in enumerate(copies):
        st = renamed(statement, f"lraHG{base + i}")
        if st is None:
            return None
        sp = c["span"]
        newb = SP.replace(body, sp, c["rep"])
        txt = f"\nset_option maxHeartbeats {int(c['cap'])} in\n{st} :={newb.rstrip()}\n"
        first = line + 1
        line += txt.count("\n")
        ranges.append((first, line))
        parts.append(txt)
    return "".join(parts), ranges


def _msg_line(m) -> int | None:
    try:
        return int((m.get("pos") or {}).get("line"))
    except (TypeError, ValueError, AttributeError):
        return None


def parse_probe(messages, ranges: list[tuple[int, int]]) -> list[dict] | None:
    """Per copy: {"clean": bool, "errors": n, "sugg": [[suggestion texts] per Try-this message]}; None when the marker is missing."""
    from harness.tools import t3_suggest as T3
    marker = None
    for m in messages or []:
        if m.get("severity") == "information" and "lraHGDummy : True" in K.msg_text(m):
            marker = _msg_line(m)
            break
    if marker is None:
        return None
    off = marker - 2
    out = [{"clean": True, "errors": 0, "sugg": [], "msgs": 0, "err": None} for _ in ranges]
    for m in messages or []:
        ln = _msg_line(m)
        if ln is None:
            continue
        rl = ln - off
        k = next((i for i, (a, b) in enumerate(ranges) if a <= rl <= b), None)
        if k is None:
            continue
        sev, data = m.get("severity"), K.msg_text(m)
        if sev == "error" or (sev == "warning" and re.search(r"declaration uses\b.*sorry", data, re.S)):
            out[k]["clean"] = False
            out[k]["errors"] += 1
            if out[k]["err"] is None:
                out[k]["err"] = f"{rl - ranges[k][0]}: " + " ".join(data.split())[:200]
            continue
        if sev != "information":
            continue
        items = T3.parse_message(data, None)
        if not items:
            continue
        out[k]["msgs"] += 1
        good = [it["text"] for it in items if _usable(it["text"])]
        anyt = [it["text"] for it in items if it.get("kept") and _usable(it["text"], any_tactic=True)]
        if any("sorry" in it["text"] for it in items):
            out[k]["clean"] = False
        out[k]["sugg"].append(good)
        out[k].setdefault("any", []).append(anyt)
    return out


def _usable(text: str, any_tactic: bool = False) -> bool:
    """A suggestion usable as a candidate: one line, no `=>` script, no sorry, no search `?`, no `#` anchor, no inaccessible name; a
    `grind ... only` / `simp_all only` / `simp only` form unless any_tactic (the `try?` menu: any such one-line tactic)."""
    t = " ".join(text.split())
    if "=>" in t or "sorry" in t or "?" in re.sub(r"\?_", "", t) or _ANCHOR.search(t) or "✝" in t or "--" in t or "\n" in text.strip():
        return False
    return True if any_tactic else bool(_SUGG.match(t))


# ------------------------------------------------------------------------------------------------------------------------------ query
def _split_items(s: str) -> list[str]:
    out, d, cur = [], 0, ""
    for ch in s:
        if ch in "([{⟨":
            d += 1
        elif ch in ")]}⟩":
            d -= 1
        if ch == "," and d == 0:
            if cur.strip():
                out.append(cur.strip())
            cur = ""
        else:
            cur += ch
    if cur.strip():
        out.append(cur.strip())
    return out


def _base(item: str) -> str:
    return re.sub(r"^(?:[←→↓⇐=_\-]+\s*)+", "", item.strip()).strip()


def merge(suggs: list[str]) -> tuple[str, list[str]] | None:
    """(the head, e.g. `grind only` / `grind (gen := 2) only` / `simp_all only`, the union of the lists) of several suggestions with the
    same head; None when the heads differ or one does not parse."""
    head, items = None, []
    for s in suggs:
        m = _SUGG.match(" ".join(s.split()))
        if not m:
            return None
        h = m.group(1) + " only"
        if head is None:
            head = h
        elif h != head:
            return None
        for it in _split_items(m.group(2) or ""):
            if it not in items:
                items.append(it)
    return (head, items) if head else None


def _render(head: str, items: list[str]) -> str:
    return head + (" [" + ", ".join(items) + "]" if items else "")


def _from_H(items: list[str], H: list[dict]) -> list[str]:
    names = [h["name"] for h in H]
    keep = []
    for it in items:
        b = _base(it)
        if any(b == n or b.endswith("." + n) or n.endswith("." + b) for n in names):
            keep.append(it)
    return keep


def build(proof: str, statement: str, results: list[dict]) -> list[dict]:
    """Candidates {"op", "decl", "note", "tokens"} from the clean probe results on THIS proof (spans located by text), fewest tokens first
    within Lean's own texts, then the blind variants."""
    hb = K.head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    cur = {sp["text"]: sp for sp in SP.spans(body)}
    printed, blind, seen = [], [], set()
    for r in results:
        if r.get("menu") == "try":
            sp0 = cur.get(r["span_text"])
            if sp0 is None or not r.get("clean") or len(r.get("any") or []) != 1:
                continue
            for t in sorted(dict.fromkeys(r["any"][0]), key=count_tokens)[:3]:
                nb = SP.replace(body, sp0, t)
                decl = head + nb
                if decl in seen or nb.strip() == body.strip():
                    continue
                seen.add(decl)
                printed.append({"op": "hintgrind:try", "decl": decl, "tokens": count_tokens(nb), "lo": sp0["lo"], "hi": sp0["hi"], "rep": t,
                                "note": f"{sp0['kind']} try printed @L{K.line_of(body, sp0['lo'])} {sp0['tokens']}t -> {count_tokens(t)}t"})
            continue
        if not r.get("clean") or not r.get("sugg"):
            continue
        sp0 = cur.get(r["span_text"])
        if sp0 is None:
            continue
        firsts = [s[0] for s in r["sugg"] if s]
        if len(firsts) != len(r["sugg"]):
            continue
        mg = merge(firsts)
        if mg is None:
            continue
        h, items = mg
        menu = r["menu"]
        H = r.get("H") or []

        pre = r.get("prefix") or ""
        if pre == "all_goals " and len(r["sugg"]) == 1:
            pre = ""   # one goal answered: the combinator is not needed

        def wrap(t):
            return pre + t

        op = "hintgrind:region" if menu.startswith("region") else ("hintgrind:" + (menu if menu in ("grind-fwd", "grind-all") else h.split()[0].split("(")[0].strip()))
        main = wrap(_render(h, items))
        vs = [(printed, op, main, "printed")]
        plain_head = h[:-len(" only")]
        keep = _from_H(items, H)
        bl = [wrap(_render(plain_head, keep))]
        if menu.startswith("region") and H:
            bl.append(wrap(plain_head + hint_list(H, fwd=menu.endswith(("fwd", "fact", "gen", "factgen")))))
        for b in bl[:BLIND_PER_SPAN]:
            vs.append((blind, "hintgrind:blind", b, "blind"))
        for lst, o, rep, kind in vs:
            nb = SP.replace(body, sp0, rep)
            decl = head + nb
            if decl in seen or nb.strip() == body.strip():
                continue
            seen.add(decl)
            tok = count_tokens(nb)
            lst.append({"op": o, "decl": decl, "tokens": tok, "lo": sp0["lo"], "hi": sp0["hi"], "rep": rep,
                        "note": f"{sp0['kind']} {menu} {kind} @L{K.line_of(body, sp0['lo'])} {sp0['tokens']}t -> {count_tokens(rep)}t"})
    printed.sort(key=lambda c: c["tokens"])
    blind.sort(key=lambda c: c["tokens"])
    base_tok = count_tokens(body)
    return [c for c in printed + blind if c["tokens"] < base_tok]


# ------------------------------------------------------------------------------------------------------------------------------ screen
SCREEN_VARIANT = r'''
set_option Elab.async false in
#eval show Lean.Elab.Command.CommandElabM Unit from do
  let s : String := LRAHGSRC
  let i : Nat := LRAHGI
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command s with
  | .error _ => Lean.logInfo (Lean.toMessageData s!"LRAD4M\t{i}\t0\t0\tparse")
  | .ok stx =>
    let n := (← Lean.getCurrNamespace) ++ (LRAHGNS).toName ++ Lean.Name.mkSimple ("lraHGM" ++ toString i)
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


def screen_text(statement: str, bodies: list[str]) -> str | None:
    """d4_measure's one-file measurement (same `#eval` reading and LRAD4M lines, MS.parse reads them) with the statement's namespace kept."""
    dn = decl_name(statement)
    if dn is None:
        return None
    srcs = []
    for i, b in enumerate(bodies):
        r = renamed(statement, f"lraHGM{i}")
        if r is None:
            return None
        srcs.append(r.rstrip() + " :=" + b)
    return "theorem lraHGMDummy : True := trivial\n" + "".join(
        SCREEN_VARIANT.replace("LRAHGSRC", K.lean_str(s)).replace("LRAHGI", str(i)).replace("LRAHGNS", K.lean_str(dn[1]))
        for i, s in enumerate(srcs))


def screen(proof: str, statement: str, cands: list[dict], run, exchange, compile_s, version=None, stats=None, log=None) -> list[dict]:
    """The candidates measured in one-file batches on the primary pin (module docstring, "SCREEN"): predicted-higher ones best first, then
    the unscreened ones in order; failing / predicted-lower ones dropped."""
    say = log or (lambda *a: None)
    stats = stats if stats is not None else {}
    if not cands:
        return []
    body0 = split_declaration(proof, statement)
    n = MS.budget({"compile_s": compile_s})
    scored, unscreened, files = [], [], 0
    pool = cands[:SCREEN_FILES * (n - 1)]
    for i in range(0, len(pool), n - 1):
        chunk = pool[i:i + n - 1]
        bodies = [split_declaration(c["decl"], statement) for c in chunk]
        text = screen_text(statement, [body0] + bodies)
        if text is None:
            unscreened += chunk
            continue
        try:
            r = run(text, version)
        except Exception:  # noqa: BLE001  (the caller's budget stop is re-raised by run itself as its own type)
            raise
        files += 1
        rd = MS.parse(getattr(r, "messages", None), len(chunk) + 1)
        ctl = rd.get(0) or {"ok": False}
        if not ctl.get("ok"):
            unscreened += chunk
            continue
        for k, (c, b) in enumerate(zip(chunk, bodies), 1):
            pr = MS.predicted(ctl, body0, b, rd.get(k) or {"ok": False}, exchange)
            c2 = dict(c, predicted=pr, screen_hb=(rd.get(k) or {}).get("hb"))
            if pr is not None and pr > 0:
                scored.append((pr, i + k, c2))
    scored.sort(key=lambda x: (-x[0], x[1]))
    stats.update(screen_files=files, screen_up=len(scored), screen_unscreened=len(unscreened), screen_in=len(pool))
    say(f"hintgrind: screen {len(pool)} candidate(s) in {files} file(s): {len(scored)} predicted higher, {len(unscreened)} unscreened")
    return [c for _, _, c in scored] + unscreened


# ------------------------------------------------------------------------------------------------------------------------------ query
def query(proof: str, statement: str, run, versions=None, ctx: dict | None = None, stats: dict | None = None, log=None) -> dict:
    """Query A + Query B (pass 1 of the row; later passes read the cache) + the screen. Returns {"cands": [...], "stats": {...}}; {} when
    the row has no site or is skipped. run(text, version) is the driver's charged compile (it may raise the driver's budget stop)."""
    ctx = dict(ctx or {})
    say = log or (lambda *a: None)
    stats = stats if stats is not None else {}
    exchange, compile_s, inc_hb = ctx.get("exchange"), ctx.get("compile_s"), ctx.get("inc_hb")
    versions = list(versions or [None])
    primary, oldest = versions[0], versions[-1]
    if isinstance(compile_s, (int, float)) and compile_s > SKIP_COMPILE_S:
        stats["skipped"] = f"compile {compile_s:.0f} s > {SKIP_COMPILE_S:.0f} s"
        return {}
    sps = sites(proof, statement, exchange)
    stats["spans"] = len(sps)
    if not sps:
        return {}
    key = _sha(statement)
    with _LOCK:
        ent = _CACHE.setdefault(key, {"probed": False, "results": [], "qa": None, "texts": set(), "reprobes": 0})
        if ent["probed"] and not ({sp["text"] for sp in sps} & ent["texts"]) and ent["reprobes"] < MAX_REPROBES:
            # none of this proof's spans was probed: another input of the row (a second post-step in this process), or a later pass
            # after a collapse that touched every span (a block's last steps are in all its suffixes); probed afresh, once
            ent.update(probed=False, results=[], qa=None, texts=set(), reprobes=ent["reprobes"] + 1)
    t0 = time.time()
    if not ent["probed"]:
        ent["probed"] = True
        ent["texts"] = {sp["text"] for sp in sps}
        names = query_names(proof, statement)
        qa = {}
        qt = query_a_text(statement, names)
        header_s = None
        if qt is not None:
            r = run(qt, primary)
            qa = parse_query_a(getattr(r, "messages", None), names)
            header_s = getattr(r, "seconds", None)
            if bool(getattr(r, "timed_out", False)):
                header_s = None
        ent["qa"] = qa
        stats["qa_names"], stats["qa_resolved"] = len(names), len(qa)
        copies = plan(proof, statement, sps, qa, exchange, inc_hb)
        kf = per_file(compile_s)
        main = [c for c in copies if c["menu"] != "try"]
        tries = [c for c in copies if c["menu"] == "try"]
        # file sizes: the first from the estimate (pack); after each read file, from that file's own wall per copy (the machine's load
        # as it is now); after a timed-out file, half its size, its copies first again
        rest = list(main)
        k = len((pack(rest, compile_s, header_s) or [[]])[0]) or 2
        results, files, lost, pairs, sent = [], 0, 0, [], 0
        i = 0
        tried_try = not tries
        while files < MAX_FILES and (rest or not tried_try):
            if time.time() - t0 > PROBE_WALL_S:
                stats["probe_wall_stop"] = True
                break
            if rest and (tried_try or files < MAX_FILES - 1):
                chunk, rest = rest[:k], rest[k:]
            else:
                chunk, tried_try = tries[:max(1, min(TRY_PER_FILE, kf))], True
            i += len(chunk)
            pf = probe_file(proof, statement, chunk, base=i - len(chunk))
            if pf is None:
                break
            text, ranges = pf
            r = run(text, oldest)
            files += 1
            sent += len(chunk)
            got = parse_probe(getattr(r, "messages", None), ranges)
            if got is None:
                lost += len(chunk)
                to = bool(getattr(r, "timed_out", False))
                say(f"hintgrind: probe file {files} gave no reading ({len(chunk)} copies; timed out: {to})")
                if to and chunk[0]["menu"] != "try" and len(chunk) > 2:
                    k = max(2, len(chunk) // 2)
                    rest = chunk + rest
                continue
            k = per_file_measured(getattr(r, "seconds", None), header_s, len(chunk), k)
            if files == 1 and len(got) >= 2 and all(not g["clean"] for g in got) and len({g.get("err") for g in got}) == 1 \
                    and re.search(r"[Uu]nknown (?:identifier|constant)", got[0].get("err") or ""):
                # every copy fails with the same error at the same line: the renamed copy itself does not elaborate here (a name the
                # statement or an untouched step needs, the proof's own recursive call); no further file can answer
                stats["copy_broken"] = got[0]["err"][:120]
                say(f"hintgrind: every copy fails alike ({got[0]['err'][:100]}); probing stopped")
                rest = []
            for c, g in zip(chunk, got):
                pairs.append((c, g))
                results.append({"span_text": c["span"]["text"], "menu": c["menu"], "head": c["span"].get("head"), "H": c["H"],
                                "prefix": c.get("prefix", ""),
                                "clean": g["clean"], "sugg": g["sugg"], "msgs": g["msgs"], "kind": c["span"]["kind"], "err": g.get("err"),
                                "any": g.get("any") or []})
        stats["copies"] = sent
        ent["results"] = results
        _dump(statement, pairs, stats)
        stats.update(probe_files=files, probe_lost=lost, clean=sum(1 for x in results if x["clean"] and x["sugg"]))
        say(f"hintgrind: {len(sps)} span(s), {len(qa)}/{len(names)} name(s) resolved, {sent} probe copies in {files} file(s) "
            f"on {oldest}: {stats['clean']} clean answer(s) in {time.time() - t0:.1f} s")
    cands = build(proof, statement, ent["results"])
    stats["raw_cands"] = len(cands)
    if not cands:
        return {"cands": [], "stats": stats}
    cands = screen(proof, statement, cands, run, exchange, compile_s, version=primary, stats=stats, log=say)
    cands = with_combos(proof, statement, cands, run, exchange, compile_s, version=primary, stats=stats, log=say)
    return {"cands": cands, "stats": stats}


def combos(proof: str, statement: str, scored: list[dict]) -> list[dict]:
    """Candidates that replace SEVERAL disjoint spans at once (the driver adopts one candidate per pass, and a replacement changes the
    text of every span around it, so separate collapses of one row would mostly be lost): the screened singles predicted higher, best
    first, taken greedily when their spans neither overlap nor touch one already taken, at most COMBO_MAX spans; the full greedy set and
    its best COMBO_PREFIX prefixes of 2 or more spans."""
    hb = K.head_body(proof, statement)
    if hb is None:
        return []
    head, body = hb
    pick = []
    for c in scored:
        if c.get("predicted") is None or c["predicted"] <= 0 or "lo" not in c:
            continue
        if any(not (c["hi"] < q["lo"] or c["lo"] > q["hi"]) for q in pick):
            continue
        pick.append(c)
        if len(pick) >= COMBO_MAX:
            break
    out, seen = [], set()
    sizes = sorted({len(pick)} | {k for k in range(2, len(pick)) if k <= COMBO_PREFIX + 1})
    for k in sizes:
        if k < 2:
            continue
        sel = sorted(pick[:k], key=lambda q: -q["lo"])
        nb = body
        for q in sel:
            nb = nb[:q["lo"]] + q["rep"] + nb[q["hi"]:]
        decl = head + nb
        if decl in seen:
            continue
        seen.add(decl)
        out.append({"op": "hintgrind:combo", "decl": decl, "tokens": count_tokens(nb), "combo": k,
                    "note": f"combo {k} spans: " + "; ".join(q.get("note", "")[:40] for q in pick[:k])})
    return out


def with_combos(proof: str, statement: str, cands: list[dict], run, exchange, compile_s, version=None, stats=None, log=None) -> list[dict]:
    """The screened list with the combos (combos()) screened in one more file and put first when predicted above the best single."""
    stats = stats if stats is not None else {}
    cs = combos(proof, statement, cands)
    if not cs:
        return cands
    got = screen(proof, statement, cs, run, exchange, compile_s, version=version, stats={}, log=log)
    best = max((c["predicted"] for c in cands if c.get("predicted") is not None), default=0.0)
    up = [c for c in got if c.get("predicted") is not None and c["predicted"] > best]
    stats.update(combos=len(cs), combos_up=len(up))
    return up + cands


def _dump(statement: str, pairs: list, stats: dict) -> None:
    """Dev measurement only: with LRA_HG_DUMP set, every read probe copy's answer is appended to that JSON-lines file."""
    import os
    path = os.environ.get("LRA_HG_DUMP")
    if not path:
        return
    with _LOCK, open(path, "a") as fh:
        for c, r in pairs:
            fh.write(json.dumps({"st": _sha(statement), "kind": c["span"]["kind"], "menu": c["menu"], "tokens": c["span"]["tokens"],
                                 "steps": c["span"]["steps"], "nH": len(c["H"]), "cap": c["cap"], "rep": c["rep"][:300],
                                 "clean": r.get("clean"), "msgs": r.get("msgs"), "sugg": r.get("sugg"), "err": r.get("err")},
                                ensure_ascii=False) + "\n")


def candidates(proof: str, statement: str, ctx: dict | None = None) -> list[dict]:
    """The proposals (query's screened candidates), as {"op", "decl", "note"}."""
    out = []
    for c in (ctx or {}).get("cands") or []:
        note = c.get("note", "")
        if c.get("predicted") is not None:
            note += f" pred {c['predicted']:+.0f}"
        out.append({"op": c["op"], "decl": c["decl"], "note": note})
    return out


def reset_cache() -> None:
    with _LOCK:
        _CACHE.clear()


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--proof-file", required=True)
    ap.add_argument("--statement-file", required=True)
    ap.add_argument("--exchange", type=float, default=None)
    a = ap.parse_args(argv)
    proof, st = Path(a.proof_file).read_text().rstrip(), Path(a.statement_file).read_text().rstrip()
    for sp in sites(proof, st, a.exchange):
        print(json.dumps({k: sp[k] for k in ("kind", "steps", "tokens", "d", "classes", "head")}, ensure_ascii=False))
    print(json.dumps({"query_names": query_names(proof, st)}, ensure_ascii=False))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
