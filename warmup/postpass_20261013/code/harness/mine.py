#!/usr/bin/env python3
"""Closer mining: find the blocks of a compiling proof that a single closer replaces (length axis, 2026-10-07).

Motivation: proofs were ~40% of the reference length and a score of 90 needs ~20%, so prompts and tools come before fine-tuning.
The model rarely tries one-line closers on its own blocks; this does it mechanically with the existing compile path:

  1. block probes   every outermost `case … =>`, `have … := by` and `·` block, body replaced by a closer — one compile per closer,
                    all blocks at once (Lean recovers after a failed block, so errors attribute to their block's lines);
  2. suffix probes  for flat tactic sequences: lines k..end of the top level replaced by `all_goals first | <closers>` (one compile each);
  3. whole proof    `by <closer>` for the whole body.
Then the cheapest successful replacements are combined greedily (largest saving first, each kept only if the candidate still compiles)
and the result is scored with the normal lean_check (no banking unless a verified_path is given).

  python3 harness/mine.py <problem> [--proof-file F] [--from bank|best] [--closers grind,simp_all,aesop,omega,exact?] [--jobs 6]
"""
from __future__ import annotations
import argparse, json, re, sys
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.leantools import ROWS, lean_check  # noqa: E402
from scorer.compile import ELAN_BIN, env_dir, project_env_dir, file_prefix  # noqa: E402
from probe.verify_candidates import newest_first  # noqa: E402
import os, subprocess, uuid  # noqa: E402


def lean_run(name: str, code: str, timeout: int = 600, options: list[str] | None = None) -> list[dict]:
    """Compile `code` after the problem's header; return ALL messages as {severity, line (relative to code), data}.
    Unlike leantools.lean_run this never truncates: grind failures print kilobytes of diagnostics, and the 12 kB cap there
    silently dropped later errors, which made failed blocks look like successes (found 2026-10-07 on Fsub progress)."""
    row = ROWS[name]; primary = newest_first(row["version_info"])[0]
    if row["source"] == "putnambench":
        wd = env_dir(primary); head = row["header"].rstrip() + "\n\n"
    else:
        wd = project_env_dir(row["source"], primary); head = file_prefix(row, primary).rstrip("\n") + "\n\n"
    scratch = wd / "LRAScratch"; scratch.mkdir(exist_ok=True)
    f = scratch / f"m_{uuid.uuid4().hex[:10]}.lean"; f.write_text(head + code.rstrip() + "\n")
    env = dict(os.environ, PATH=f"{ELAN_BIN}:{os.environ.get('PATH','')}")
    try:
        pr = run_lean(["lake", "env", "lean", "--json", f"-M{os.environ.get('LRA_LEAN_MEMORY_MB', '16000')}", *[f"-Dweak.{o}" for o in (options or [])], str(f.relative_to(wd))], cwd=wd, env=env, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        f.unlink(missing_ok=True); return [{"severity": "error", "line": 0, "data": "timeout"}]
    f.unlink(missing_ok=True)
    off = head.count("\n"); out = []
    for line in pr.stdout.splitlines():
        if line.startswith("{"):
            try:
                m = json.loads(line)
            except json.JSONDecodeError:
                continue
            out.append({"severity": m.get("severity"), "line": (m.get("pos") or {}).get("line", 0) - off, "data": str(m.get("data", ""))})
    if pr.returncode != 0 and not any(m["severity"] == "error" for m in out):
        out.append({"severity": "error", "line": 0, "data": f"exit {pr.returncode}: {pr.stderr[:300]}"})
    return out
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402
from scorer.memgate import run_lean  # noqa: E402

DEFAULT_CLOSERS = ["grind", "simp_all", "aesop", "omega", "fun_prop", "norm_num", "linarith", "positivity", "tauto", "exact?"]
SUFFIX_CLOSER = "all_goals first | grind | simp_all | aesop | omega | fun_prop"


def _indent(l: str) -> int:
    return len(l) - len(l.lstrip(" "))


def body_lines(decl: str, statement: str) -> tuple[list[str], list[str]] | None:
    """Split a declaration into (head lines up to and including the `:= by` line, body lines). Tactic proofs only."""
    lines = decl.rstrip("\n").split("\n")
    for i, l in enumerate(lines):
        if re.search(r":=\s*by\s*$", l):
            return lines[: i + 1], lines[i + 1:]
    return None


def outer_blocks(body: list[str]) -> list[dict]:
    """Outermost blocks at the base indentation: {start, end (exclusive), header (text kept, may span lines), kind}.
    case X => …            header `case X =>`
    have/suffices … := …   header = everything up to the first `:=` (multi-line statements allowed), plus ` by`
    · …                    header `·`"""
    if not body:
        return []
    base = min(_indent(l) for l in body if l.strip())
    out, i = [], 0
    while i < len(body):
        l = body[i]; ind = _indent(l); s = l.strip()
        if ind != base or not s:
            i += 1; continue
        j = i + 1
        while j < len(body) and (not body[j].strip() or _indent(body[j]) > ind):
            j += 1
        text = "\n".join(body[i:j])
        m_case = re.match(r"(case\s+.+?=>)\s*(.*)$", s)
        if m_case and (j > i + 1 or m_case.group(2)):
            out.append({"start": i, "end": j, "header": " " * ind + m_case.group(1), "kind": "case"})
        elif re.match(r"(have|suffices)\b", s) and ":=" in text and re.search(r"\s:\s", text[: text.index(":=")]):   # typed only
            k = text.index(":=") + 2
            head = text[:k].rstrip()
            rest = text[k:].lstrip()
            if rest.startswith("by"):
                head += " by"; rest = rest[2:].strip()
            else:
                head += " by"
            if rest:
                out.append({"start": i, "end": j, "header": head, "kind": "have"})
        elif s.startswith("·") and (j > i + 1 or s[1:].strip()):
            out.append({"start": i, "end": j, "header": " " * ind + "·", "kind": "bullet"})
        i = j
    return out


def _replace(head, body, blocks, closer_for):
    """Rebuild the declaration with blocks replaced by `header closer`; return (decl, {block_index: line_in_code of the closer})."""
    new, lines_of = [], {}
    starts = {b["start"]: (idx, b) for idx, b in enumerate(blocks)}
    i = 0
    while i < len(body):
        if i in starts and closer_for(starts[i][0]) is not None:
            idx, b = starts[i]
            hl = b["header"].split("\n")
            new.extend(hl[:-1]); new.append(f"{hl[-1]} {closer_for(idx)}")
            lines_of[idx] = len(head) + len(new)          # 1-based line of the closer in the declaration
            i = b["end"]
        else:
            new.append(body[i]); i += 1
    return "\n".join(head + new), lines_of


def _errors_by_line(msgs: list[dict]) -> dict[int, list[str]]:
    errs: dict[int, list[str]] = {}
    for m in msgs:
        if m["severity"] == "error":
            errs.setdefault(m["line"], []).append(m["data"])
    return errs


def _try_this(msgs: list[dict], line: int) -> str | None:
    for m in msgs:
        if m["severity"] == "info" and m["line"] == line and m["data"].startswith("Try this:"):
            return re.sub(r"\s+", " ", m["data"][len("Try this:"):]).strip()
    return None


_KEYWORDS = {"by", "fun", "at", "with", "using", "only", "then", "else", "if", "match", "do", "let", "have", "show", "from",
             "exact", "apply", "intro", "intros", "obtain", "rcases", "cases", "induction", "generalizing", "simp", "simp_all",
             "grind", "aesop", "omega", "rfl", "rw", "rwa", "refine", "use", "left", "right", "constructor", "case", "all_goals",
             "any_goals", "first", "next", "subst", "generalize", "calc", "conv", "enter", "lhs", "rhs", "suffices", "this", "true", "false",
             "Type", "Prop", "Sort", "fun_prop", "norm_num", "linarith", "positivity", "tauto", "ring", "field_simp", "congr", "ext"}
_TOKEN = re.compile(r"[A-Za-z_\u0370-\u03ff][\w'!?\u0370-\u03ff\u1d62-\u1d6a\u2080-\u209c.]*")


def _names_in(text: str) -> list[str]:
    """Candidate global names used in a proof fragment: dotted names (Red.abs, List.Subset.app), both halves of dot-calls
    (body_let.mp -> body_let; l.canonical_form_abs -> canonical_form_abs), and underscore lemma names. Numeric projections
    (`.2.1`) are dropped. Resolution (below) filters out locals."""
    out = []
    for t in _TOKEN.findall(text):
        parts = [x for x in t.strip(".").split(".") if x and not x.isdigit()]
        if not parts or parts[0] in _KEYWORDS:
            continue
        if len(parts) >= 2 and parts[0][:1].isupper():
            out.append(".".join(parts))                 # Namespace.name, constructors like Red.case_inl
        elif len(parts) >= 2:
            out.append(parts[0]); out.append(parts[-1])  # lemma.mp -> lemma ; local.field_lemma -> field_lemma
        elif "_" in parts[0] and parts[0][:1].islower():
            out.append(parts[0])
    return [n for n in dict.fromkeys(out) if n not in _KEYWORDS and not n[:1].isdigit() and len(n) > 1]


def _decl_namespaces(statement: str) -> list[str]:
    """`lemma Typing.progress …` -> ['Typing']; names inside that declaration resolve relative to these namespaces."""
    m = re.match(r"\s*(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable )*(?:theorem|lemma|def)\s+([^\s(:{\[]+)", statement)
    if not m:
        return []
    segs = m.group(1).split(".")[:-1]
    return [".".join(segs[:k]) for k in range(len(segs), 0, -1)]


def resolvable(name: str, names: list[str]) -> dict[str, str]:
    """Map candidate -> the form that `#check @…` accepts in the problem's context: the name itself, or the name qualified by the
    declaration's own namespaces (inside `Typing.progress`, `canonical_form_abs` means `Typing.canonical_form_abs`). One compile."""
    names = [n for n in names if n][:150]
    if not names:
        return {}
    tries = []
    for n in names:
        tries.append((n, n))
        for ns in _decl_namespaces(ROWS[name]["statement"]):
            tries.append((n, f"{ns}.{n}"))
    msgs = lean_run(name, "\n".join(f"#check @{q}" for _, q in tries))
    bad = {m["line"] for m in msgs if m["severity"] == "error"}
    out: dict[str, str] = {}
    for i, (n, q) in enumerate(tries, 1):
        if i not in bad and n not in out:
            out[n] = q
    return out


LINTER_OPTS = [f"linter.tacticAnalysis.{o}=true" for o in
               ("tryAtEachStepGrind", "tryAtEachStepSimpAll", "terminalToGrind", "rwMerge", "mergeWithGrind", "introMerge")]
_SUGG = re.compile(r"^`(?P<old>.+?)`(?: \(\+(?P<n>\d+) later steps?\))? can be replaced with `(?P<new>.+?)`", re.S)


def linter_phase(name: str, decl: str, log=print) -> tuple[str, list[str]]:
    """Mathlib's TacticAnalysis passes (research 2026-10-07): one compile with the try-at-every-step / merge linters on, then apply
    each suggestion greedily (largest token saving first), keeping it only if the measured score rises. Mathlib-based rows only
    (Strata has no Mathlib). Returns (new decl, applied descriptions)."""
    if ROWS[name]["source"] == "strata":
        return decl, []
    msgs = lean_run(name, decl, options=LINTER_OPTS)
    sugg = []
    for m in msgs:
        if m["line"] < 1 or m["severity"] not in ("information", "info", "warning"):
            continue
        mm = _SUGG.match(m["data"].strip())
        if mm:
            sugg.append((m["line"], mm.group("old"), int(mm.group("n") or 0), mm.group("new")))
    sugg = list(dict.fromkeys(sugg))
    def apply(text, s_):
        ln, old, n, new = s_
        lines = text.split("\n")
        if ln > len(lines) or old.lstrip("· ").strip() not in lines[ln - 1]:
            return None
        o = old.lstrip("· ").strip(); i = lines[ln - 1].index(o)
        lines[ln - 1] = lines[ln - 1][:i] + new + lines[ln - 1][i + len(o):]
        if n:   # drop the N following steps at the same indentation (approximation; the score check rejects a wrong cut)
            ind = len(lines[ln - 1]) - len(lines[ln - 1].lstrip()); k = ln; dropped = 0
            while k < len(lines) and dropped < n:
                if lines[k].strip() and len(lines[k]) - len(lines[k].lstrip()) <= ind:
                    del lines[k]; dropped += 1
                elif lines[k].strip():
                    del lines[k]
                else:
                    k += 1
        return "\n".join(lines)
    def score(text):
        r = lean_check(name, text, {"best": {"score": 999.0, "proof": None}, "attempts": []}, {"run_id": "mine", "kind": "mine"}, None)
        return r.get("predicted_score_if_compatible") if r.get("ok") else None
    cur = decl; cur_s = score(decl); applied = []
    if cur_s is None:
        return decl, []
    ranked = sorted(sugg, key=lambda s_: -(count_tokens(s_[1]) - count_tokens(s_[3]) + 3 * s_[2]))
    for s_ in ranked:
        if count_tokens(s_[1]) - count_tokens(s_[3]) + 3 * s_[2] <= 0:
            continue
        cand = apply(cur, s_)
        if cand is None:
            continue
        sc = score(cand)
        if sc and sc > cur_s:
            cur, cur_s = cand, sc; applied.append(f"line {s_[0]}: `{s_[1][:40]}` -> `{s_[3]}`" + (f" (+{s_[2]} steps)" if s_[2] else ""))
    log(f"  linter phase: {len(sugg)} suggestions, {len(applied)} applied" + (f" ({'; '.join(applied)})" if applied else ""))
    return cur, applied


def mine(name: str, decl: str, closers=DEFAULT_CLOSERS, jobs: int = 6, log=print) -> dict:
    row = ROWS[name]
    decl0 = decl
    decl, linted = linter_phase(name, decl, log=log)
    sp = body_lines(decl, row["statement"])
    if sp is None:
        return {"error": "not a `:= by` tactic proof"}
    head, body = sp
    blocks = outer_blocks(body)
    base_tokens = count_tokens(split_declaration(decl.rstrip(), row["statement"]) or "")
    log(f"{name}: {base_tokens} tokens, {len(body)} body lines, {len(blocks)} outer blocks")
    found = {}  # block idx -> list of (replacement_text, saving)

    def block_probe(closer):
        code, lines_of = _replace(head, body, blocks, lambda idx: closer)
        msgs = lean_run(name, code)
        errs = _errors_by_line(msgs)
        res = []
        for idx, ln in lines_of.items():
            if ln in errs:
                continue
            repl = closer
            if closer == "exact?":
                repl = _try_this(msgs, ln)
                if not repl or "sorry" in repl:
                    continue
            b = blocks[idx]
            old = "\n".join(body[b["start"]: b["end"]])
            saving = count_tokens(old) - count_tokens(f"{b['header'].strip()} {repl}")
            if saving > 0:
                res.append((idx, repl, saving))
        return closer, res

    top = [i for i, l in enumerate(body) if l.strip() and _indent(l) == min(_indent(x) for x in body if x.strip())]

    def suffix_probe(k):
        code = "\n".join(head + body[:k] + [" " * _indent(body[k]) + SUFFIX_CLOSER])
        msgs = lean_run(name, code)
        ok = not _errors_by_line(msgs)
        saving = count_tokens("\n".join(body[k:])) - count_tokens(SUFFIX_CLOSER)
        return k, ok, saving

    with ThreadPoolExecutor(jobs) as ex:
        bres = list(ex.map(block_probe, closers)) if blocks else []
        sres = list(ex.map(suffix_probe, top[1:])) if len(top) > 1 else []
        whole = list(ex.map(lambda c: (c, not _errors_by_line(lean_run(name, "\n".join(head[:-1] + [re.sub(r":=\s*by\s*$", f":= by {c}", head[-1])])))), [c for c in closers if c != "exact?"]))
    for closer, res in bres:
        for idx, repl, saving in res:
            found.setdefault(idx, []).append((repl, saving))

    # Lemma-hinted closers (Fable-style `grind [lemmas]`, 2026-10-07): the names a block already uses, resolved in context,
    # handed to grind / simp_all — bare grind fails on domain goals because it does not know the domain lemmas.
    ok_names = resolvable(name, _names_in("\n".join(body)))
    hints = {idx: [ok_names[n] for n in _names_in("\n".join(body[b["start"]: b["end"]])) if n in ok_names] for idx, b in enumerate(blocks)}
    _ns = lambda hs: [h for h in hs if "." in h and h.split(".")[0][:1].isupper()] or hs
    variants = {
        "grind[->ns]": lambda hs: f"grind [{', '.join('→ ' + h for h in _ns(hs))}]",   # worked by hand on Fsub let'
        "grind[->h]": lambda hs: f"grind [{', '.join('→ ' + h for h in hs)}]",
        "grind[h]": lambda hs: f"grind [{', '.join(hs)}]",
        "simp_all[h]": lambda hs: f"simp_all [{', '.join(hs)}]",
    }

    def hinted_probe(vname):
        mk = variants[vname]
        code, lines_of = _replace(head, body, blocks, lambda idx: mk(hints[idx]) if hints.get(idx) else None)
        msgs = lean_run(name, code); errs = _errors_by_line(msgs); res = []
        for idx, ln in lines_of.items():
            if ln in errs:
                continue
            b = blocks[idx]; repl = mk(hints[idx])
            saving = count_tokens("\n".join(body[b["start"]: b["end"]])) - count_tokens(f"{b['header'].strip()} {repl}")
            if saving > 0:
                res.append((idx, repl, saving))
        return vname, res

    tail_hints = {k: [ok_names[n] for n in _names_in("\n".join(body[k:])) if n in ok_names] for k in top[1:]}

    def hinted_suffix(args_):
        k, vname = args_
        hs = tail_hints.get(k) or []
        if not hs:
            return k, vname, False, 0, None
        closer = "all_goals " + variants[vname](hs)
        code = "\n".join(head + body[:k] + [" " * _indent(body[k]) + closer])
        ok = not _errors_by_line(lean_run(name, code))
        return k, vname, ok, count_tokens("\n".join(body[k:])) - count_tokens(closer), closer

    with ThreadPoolExecutor(jobs) as ex:
        hres = list(ex.map(hinted_probe, list(variants))) if any(hints.values()) else []
        hsuf = list(ex.map(hinted_suffix, [(k, v) for k in top[1:] for v in variants]))
    for vname, res in hres:
        for idx, repl, saving in res:
            found.setdefault(idx, []).append((repl, saving))
    hinted_tails = sorted([(k, sav, cl) for k, v, ok, sav, cl in hsuf if ok and sav > 0], key=lambda x: -x[1])
    log(f"  resolvable hint names: {len(ok_names)} | hinted block hits: {sum(len(r) for _, r in hres)} | hinted tail cuts: {len(hinted_tails)}")
    for idx in found:
        found[idx].sort(key=lambda x: -x[1])
    suffix_ok = sorted([(k, s) for k, ok, s in sres if ok and s > 0], key=lambda x: -x[1])
    whole_ok = [c for c, ok in whole if ok]
    log(f"  block hits: {sum(1 for _ in found)} of {len(blocks)} | suffix cuts that compile: {len(suffix_ok)} | whole-proof closers: {whole_ok}")

    # Combine by SCORE, not by "it compiles": generic closers are heartbeat-heavy (Wick, cycle 29 sweep: 499 -> 490 tokens but
    # 75.39 -> 70.61). Every step is scored with the real measurement; exploration uses a best of 999 so lean_check skips the
    # extra-toolchain compiles, and only the final candidate gets the full (Z-including) score.
    def score_of(cand):
        r = lean_check(name, cand, {"best": {"score": 999.0, "proof": None}, "attempts": []}, {"run_id": "mine", "kind": "mine"}, None)
        return (r.get("predicted_score_if_compatible") if r.get("ok") else None), r

    def whole(c):
        return "\n".join(head[:-1] + [re.sub(r":=\s*by\s*$", f":= by {c}", head[-1])])

    def build(cut, sel, tail_closer=SUFFIX_CLOSER):
        tail = [" " * _indent(body[cut]) + tail_closer] if cut < len(body) else []
        code, _ = _replace(head, body[:cut], blocks, lambda idx: sel.get(idx))
        return "\n".join(code.split("\n") + tail)

    s0, _ = score_of(decl)
    if s0 is None:
        return {"error": "the input candidate does not compile", "base_tokens": base_tokens}
    cur, cur_s, how = decl, s0, [f"linter: {x}" for x in linted]
    for c in whole_ok:
        sc, _ = score_of(whole(c))
        if sc and sc > cur_s:
            cur, cur_s, how = whole(c), sc, [f"whole proof: {c}"]
    if not how:
        cut, tail_cl = len(body), SUFFIX_CLOSER
        tails = sorted([(k, sav, SUFFIX_CLOSER) for k, sav in suffix_ok] + list(hinted_tails), key=lambda x: -x[1])
        for k, sav, cl in tails[:4]:
            sc, _ = score_of(build(k, {}, cl))
            if sc and sc > cur_s:
                cur, cur_s, cut, tail_cl, how = build(k, {}, cl), sc, k, cl, [f"tail cut at body line {k + 1}: `{cl[:60]}` (-{sav} tokens)"]
        sel = {}
        for idx, opts in sorted(found.items(), key=lambda kv: -kv[1][0][1]):
            if blocks[idx]["end"] > cut:
                continue
            for repl, sav in sorted(opts, key=lambda x: -x[1])[:3]:
                trial = dict(sel); trial[idx] = repl
                sc, _ = score_of(build(cut, trial, tail_cl))
                if sc and sc > cur_s:
                    cur, cur_s, sel = build(cut, trial, tail_cl), sc, trial
                    how.append(f"block {idx + 1} -> {repl} (-{sav} tokens)")
                    break
    log(f"  base score {s0} -> mined {cur_s} ({'; '.join(how) or 'no improving cut'})")
    best = None
    if cur is not decl0 and cur != decl0:
        r = lean_check(name, cur, {"best": {"score": 33.33, "proof": None}, "attempts": []}, {"run_id": "mine", "kind": "mine"}, None)
        if r.get("ok"):
            best = {"proof": cur, "tokens": r.get("tokens"), "score": r.get("score") or r.get("predicted_score_if_compatible"), "how": "; ".join(how)}
            log(f"  final: tokens={r.get('tokens')} score={best['score']}")
    return {"base_tokens": base_tokens, "base_score": s0, "blocks": len(blocks), "block_hits": {i: found[i][0] for i in found},
            "suffix_ok": suffix_ok[:5], "hinted_tails": [(k, sav) for k, sav, _ in hinted_tails[:5]], "whole_ok": whole_ok, "best": best}

def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("problem"); ap.add_argument("--proof-file"); ap.add_argument("--closers", default=",".join(DEFAULT_CLOSERS)); ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--out")
    ap.add_argument("--bank", help="run id: bank an improving mined proof as a verified record (probe/runs/<id>/verified.jsonl), provenance = source record's model + mode 'agent+mine'")
    a = ap.parse_args()
    if a.proof_file:
        decl = Path(a.proof_file).read_text()
    else:
        from bank.store import load_all
        recs = [r for r in load_all() if r["problem"] == a.problem and "glm" in str((r.get("provenance") or {}).get("model", "")).lower()]
        src = max(recs, key=lambda r: r["score"]); decl = src["proof"]
    res = mine(a.problem, decl, a.closers.split(","), a.jobs)
    print(json.dumps({k: v for k, v in res.items() if k != "best"}, ensure_ascii=False)[:1500])
    if res.get("best"):
        print("BEST:", json.dumps({k: v for k, v in res["best"].items() if k != "proof"}))
        if a.out:
            Path(a.out).write_text(res["best"]["proof"])
        if a.bank and not a.proof_file:
            pv = dict(src.get("provenance") or {}); pv.update({"run_id": a.bank, "mode": "agent+mine", "source_sha": src.get("sha256", "")[:16],
                                                               "mine": res["best"]["how"][:300]})
            vp = ROOT / "probe" / "runs" / a.bank / "verified.jsonl"
            r = lean_check(a.problem, res["best"]["proof"], {"best": {"score": float(src["score"]), "proof": None}, "attempts": []}, pv, vp)
            print("BANKED" if r.get("new_best") else "not banked (did not beat the source record on the full score)", r.get("score"))


if __name__ == "__main__":
    main()
