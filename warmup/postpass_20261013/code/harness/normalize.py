#!/usr/bin/env python3
"""Lexer normalizer (2026-10-09; docs/break_90_panel.md, item 1).

Deterministic, model-free rewrites of a proof body that the arena lexer (scorer/tokenize.py) counts as fewer tokens while Lean
elaborates the same term. None of the 2,724 verified records used them (the panel's count):
  lam     `fun x =>`      -> `λx =>`       Lean excludes λ from identifiers and reads `λx` as `λ x`; the lexer's isalnum rule makes
                                            `λx` one token: -1 per site (also `λ_ =>`, `λx y =>`, `λx : T =>`)
  bare    `f (fun x => e)` -> `f fun x => e` a trailing fun argument needs no parentheses in Lean 4: -2 per site
  dollar  `f a (g x)`     -> `f a $ g x`   `$` is core syntax (Init/Notation.lean) and expands to the same application: -1 per site
  ltri    `f <| g x`      -> `f $ g x`     the lexer counts `<|` as 2 tokens: -1 per site
  semi    `a; b`          -> `a` newline `b` at a's column (layout instead of the `;` token): -1 per site
Nothing is trusted: all sites are applied and compiled on the primary toolchain; sites that break it are bisected out; the result must
compile on every listed toolchain (Z unchanged) and score strictly higher than the input. Mathlib's style linters warn on `$` and
`λ` (linter.style.dollarSyntax / lambdaSyntax); warnings do not fail a compile.
  python3 harness/normalize.py --problem NAME --file proof.lean           one proof; prints the report, writes --out if given
  python3 harness/normalize.py --bests a100|flash|union [--jobs 4]        current bests -> probe/normalize/<set>.jsonl
"""
from __future__ import annotations

import argparse, json, re, sys, time
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from harness.leantools import ROWS, HBS, comp  # noqa: E402
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402
from scorer.score import len_pct, hb_pct_local, compat_pct, problem_score  # noqa: E402
from probe.verify_candidates import newest_first  # noqa: E402

OPEN, CLOSE = "([{⟨", ")]}⟩"
# words after which a parenthesised term is that tactic's own argument, not an application argument (`exact (f x)` must stay)
KEYWORDS = set("""exact exacts apply refine refine' use exists show from have let obtain rcases rintro intro intros cases induction at using
with simp simp_all simpa dsimp rw rwa erw rewrite calc by fun return if then else match do case case' next constructor unfold
specialize generalize subst contradiction exfalso trivial decide omega linarith nlinarith positivity norm_num ring field_simp
aesop grind tauto congr ext funext gcongr suffices change convert refine_lift classical push_neg by_contra by_cases split_ifs
all_goals any_goals repeat iterate first try focus on_goal pick_goal swap rotate_left rotate_right assumption rfl and or not
in fun_induction induction' cases' replace set filter_upwards haveI letI""".split())
SEQ_COMBINATORS = ("all_goals", "any_goals", "repeat", "iterate", "try", "first", "focus", "on_goal", "case'", "next", "<;>")


@dataclass
class Site:
    kind: str
    edits: tuple   # ((pos, delete_len, insert_text), ...) on the body, positions in the original body
    note: str


def _mask(body: str) -> list[bool]:
    """True where the character is inside a comment or a string literal (never rewritten)."""
    m = [False] * len(body); i = 0; n = len(body)
    while i < n:
        if body.startswith("--", i):
            j = body.find("\n", i); j = n if j < 0 else j
            for k in range(i, j): m[k] = True
            i = j
        elif body.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if body.startswith("/-", j): depth += 1; j += 2
                elif body.startswith("-/", j): depth -= 1; j += 2
                else: j += 1
            for k in range(i, j): m[k] = True
            i = j
        elif body[i] == '"':
            j = i + 1
            while j < n and body[j] != '"':
                j += 2 if body[j] == "\\" else 1
            for k in range(i, min(j + 1, n)): m[k] = True
            i = j + 1
        else:
            i += 1
    return m


def _pairs(body: str, mask: list[bool]) -> dict[int, int]:
    """Matching bracket pairs of every kind, open index -> close index (unbalanced input: best effort)."""
    st, out = [], {}
    for i, ch in enumerate(body):
        if mask[i]:
            continue
        if ch in OPEN:
            st.append((ch, i))
        elif ch in CLOSE:
            want = OPEN[CLOSE.index(ch)]
            while st and st[-1][0] != want:
                st.pop()
            if st:
                out[st.pop()[1]] = i
    return out


def _top_level(s: str, chars: str) -> bool:
    """Does s contain one of chars outside nested brackets (comma, colon of a type ascription, section dot)?"""
    d = 0
    for i, ch in enumerate(s):
        if ch in OPEN: d += 1
        elif ch in CLOSE: d -= 1
        elif d == 0 and ch in chars:
            if ch == ":" and s[i + 1:i + 2] == "=":   # `:=` is not an ascription
                continue
            return True
    return False


def _prev_word(body: str, i: int) -> str:
    j = i - 1
    while j >= 0 and body[j] in " \t":
        j -= 1
    if j < 0 or body[j] == "\n":
        return ""
    if body[j] in CLOSE:
        return ")"
    k = j
    while k >= 0 and (body[k].isalnum() or body[k] in "_.'!?₀₁₂₃₄₅₆₇₈₉"):
        k -= 1
    return body[k + 1:j + 1]


def _term_ends_after(body: str, j: int) -> bool:
    """After the closing bracket at j, does the enclosing term end (so `$` cannot swallow anything that followed)?"""
    k = j + 1
    while k < len(body) and body[k] in " \t":
        k += 1
    if k >= len(body) or body[k] == "\n":
        return True
    if body[k] in ")]}⟩,;":
        return True
    rest = body[k:k + 4]
    return rest.startswith("<;>") or rest.startswith("|") and not rest.startswith("|>") or bool(re.match(r"(at|with|using)\b", body[k:k + 6]))


def sites(body: str) -> list[Site]:
    mask = _mask(body); pairs = _pairs(body, mask); out: list[Site] = []
    # lam: `fun x` -> `λx` (x an identifier or `_`)
    for mt in re.finditer(r"(?<![\w.'])fun(\s+)(?=[^\W\d]|_)", body):
        if not mask[mt.start()]:
            out.append(Site("lam", ((mt.start(), len(mt.group(0)), "λ"),), body[mt.start():mt.start() + 12].replace("\n", " ")))
    # ltri: ` <| ` -> ` $ `
    for mt in re.finditer(r"(?<=\s)<\|(?=\s)", body):
        if not mask[mt.start()]:
            out.append(Site("ltri", ((mt.start(), 2, "$"),), body[max(0, mt.start() - 8):mt.start() + 8].replace("\n", " ")))
    # dollar / bare: a parenthesised last argument of an application
    for i, j in pairs.items():
        if body[i] != "(" or i == 0 or body[i - 1] not in " \t":
            continue
        head = _prev_word(body, i)
        if not head or head in KEYWORDS or not (head == ")" or head[-1].isalnum() or head[-1] in "_'!?₀₁₂₃₄₅₆₇₈₉"):
            continue
        inner = body[i + 1:j]
        if not inner.strip() or _top_level(inner, ",:·") or not _term_ends_after(body, j):
            continue
        if re.match(r"\s*(fun|λ)\b", inner) or inner.lstrip().startswith("λ"):
            out.append(Site("bare", ((i, 1, ""), (j, 1, "")), body[i:i + 24].replace("\n", " ")))
        else:
            out.append(Site("dollar", ((i, 1, "$ "), (j, 1, "")), body[i:i + 24].replace("\n", " ")))
    # semi: `a; b` -> newline at a's column, only at bracket depth 0 and outside sequence combinators
    line_start = 0
    for line in body.split("\n"):
        depth = 0; seg_col = None
        for c, ch in enumerate(line):
            p = line_start + c
            if mask[p]:
                continue
            if ch in OPEN: depth += 1
            elif ch in CLOSE: depth -= 1
            if seg_col is None and not ch.isspace() and ch not in "·":
                seg_col = c
            if ch == ";" and depth == 0 and not line[max(0, c - 1):c + 2].startswith("<;") and line[c - 1:c] != "<":
                head = line[seg_col:c] if seg_col is not None else ""
                if not head.strip() or "|" in head or "=>" in head and re.search(r"\b(fun|λ)\b", head) or head.lstrip().startswith(SEQ_COMBINATORS):
                    continue
                after = line[c + 1:]
                if not after.strip() or after.lstrip().startswith(("<;>", "|")):
                    continue
                gap = len(after) - len(after.lstrip())
                out.append(Site("semi", ((p, 1 + gap, "\n" + " " * seg_col),), line.strip()[:40]))
        line_start += len(line) + 1
    return out


def apply(body: str, chosen: list[Site]) -> str:
    edits = sorted((e for s in chosen for e in s.edits), key=lambda e: e[0], reverse=True)
    for pos, dl, ins in edits:
        body = body[:pos] + ins + body[pos + dl:]
    return body


def evaluate(name: str, decl: str, versions: list[str], full: bool) -> dict:
    row = ROWS[name]; body = split_declaration(decl.rstrip(), row["statement"])
    if body is None:
        return {"ok": False, "error": "statement differs"}
    r = comp(row, decl, versions[0])
    out = {"ok": r.ok, "tokens": count_tokens(body), "heartbeats": r.heartbeats, "error": (r.errors[0][:200] if r.errors else None)}
    if r.ok:
        L = len_pct(row["proof_length"], out["tokens"]); H = hb_pct_local(name, r.heartbeats, HBS.get(name))
        compat = {versions[0]: True}
        if full:
            for v in versions[1:]:
                compat[v] = comp(row, decl, v, count=False).ok
        Z = compat_pct(compat) if full else 100.0
        out.update(L=round(L, 2), H=round(H, 2), Z=Z, compat=compat, score=problem_score(True, L, H, Z))
    return out


def normalize(name: str, decl: str, log=print) -> dict:
    row = ROWS[name]; versions = newest_first(row["version_info"]); stmt = row["statement"]
    body = split_declaration(decl.rstrip(), stmt)
    if body is None:
        return {"problem": name, "status": "statement differs"}
    head = decl.rstrip()[: len(decl.rstrip()) - len(body)]
    base = evaluate(name, decl, versions, full=True)
    ss = sites(body)
    res = {"problem": name, "before": {k: base.get(k) for k in ("ok", "tokens", "heartbeats", "Z", "score")}, "sites": len(ss), "compiles": 1 + len(versions) - 1}
    if not base.get("ok") or not ss:
        res.update(status="input does not compile" if not base.get("ok") else "no sites", after=res["before"], proof=decl)
        return res
    cache: dict[str, dict] = {}

    def ok_with(chosen: list[Site]) -> bool:
        cand = head + apply(body, chosen)
        if cand not in cache:
            cache[cand] = evaluate(name, cand, versions, full=False); res["compiles"] += 1
        return bool(cache[cand].get("ok"))

    def grow(kept: list[Site], cand: list[Site]) -> list[Site]:   # bisection: keep the largest compiling extension found greedily
        if not cand or ok_with(kept + cand):
            return kept + cand
        if len(cand) == 1:
            return kept
        mid = len(cand) // 2
        return grow(grow(kept, cand[:mid]), cand[mid:])

    kept = grow([], ss)
    if not kept:
        res.update(status="no site compiles", after=res["before"], proof=decl); return res
    final = head + apply(body, kept)
    ev = evaluate(name, final, versions, full=True); res["compiles"] += len(versions)
    while ev.get("ok") and ev.get("Z", 0) < base.get("Z", 100) and kept:   # a pin broke: drop sites one kind at a time, cheapest first
        kinds = sorted({s.kind for s in kept}); dropped = False
        for k in kinds:
            trial = [s for s in kept if s.kind != k]
            evt = evaluate(name, head + apply(body, trial), versions, full=True); res["compiles"] += len(versions)
            if evt.get("ok") and evt.get("Z", 0) >= base.get("Z", 100):
                kept, ev, dropped = trial, evt, True; break
        if not dropped:
            kept = []
            break
    if not kept or not ev.get("ok") or ev.get("score", 0) <= base.get("score", 0):
        res.update(status="no gain" if kept else "pins broke", after=res["before"], proof=decl, tried=len(kept)); return res
    by = {}
    for s in kept:
        by[s.kind] = by.get(s.kind, 0) + 1
    res.update(status="improved", after={k: ev.get(k) for k in ("ok", "tokens", "heartbeats", "Z", "score")}, applied=by,
               gain=round(ev["score"] - base["score"], 2), proof=head + apply(body, kept))
    return res


def current_bests(which: str) -> dict[str, str]:
    out: dict[str, str] = {}
    if which == "a100":
        for st in (ROOT / "harness/work_fresh-a100").glob("*/state.json"):
            s = json.loads(st.read_text()); b = (s.get("best") or {}).get("proof")
            if b: out[s["problem"]] = b
    elif which == "flash":
        sys.path.insert(0, str(ROOT))
        from bank.store import load_all
        for name in ROWS:
            recs = [r for r in load_all(name) if (r.get("provenance") or {}).get("model") == "glm-5.3-flash@z.ai"
                    and (r.get("provenance") or {}).get("mode") == "agent" and r.get("proof") and r.get("score")]
            if recs: out[name] = max(recs, key=lambda r: r["score"])["proof"]
    elif which == "wu-sol":   # 2026-10-13 ($0 passes): the held closed warm-up entry, agent.py + Sol ladder, own worktree
        for st in (Path.home() / "source/lra-ab/wu-hx/harness/hwork/wu-sol").glob("*/state.json"):
            s = json.loads(st.read_text()); b = (s.get("best") or {}).get("proof")
            if b: out[s["problem"]] = b
    elif which == "union":   # closed-model comparison only: results never enter the bank
        best: dict[str, tuple[float, str]] = {}
        for f in list((ROOT / "probe/runs").glob("ccline-*/verified.jsonl")) + list((ROOT / "probe/runs").glob("cxline-*/verified.jsonl")):   # passes, relay, census, bounty, normalize
            for l in f.open():
                r = json.loads(l)
                if r.get("primary_ok") and r["score"] > best.get(r["problem"], (0, ""))[0]:
                    best[r["problem"]] = (r["score"], r["proof"])
        out = {k: v[1] for k, v in best.items()}
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem"); ap.add_argument("--file"); ap.add_argument("--out")
    ap.add_argument("--bests", choices=["a100", "flash", "union", "wu-sol"])
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("--only", nargs="*", default=None)
    ap.add_argument("--tag", default="", help="suffix of the output file, so a later run over new bests keeps the earlier results")
    a = ap.parse_args()
    if a.problem and a.file:
        r = normalize(a.problem, Path(a.file).read_text())
        print(json.dumps({k: v for k, v in r.items() if k != "proof"}, indent=1))
        if a.out and r.get("status") == "improved":
            Path(a.out).write_text(r["proof"].rstrip() + "\n")
        return 0
    if not a.bests:
        ap.error("--problem with --file, or --bests")
    bests = current_bests(a.bests)
    if a.only:
        bests = {k: v for k, v in bests.items() if any(o in k for o in a.only)}
    outp = ROOT / "probe/normalize" / f"{a.bests}{a.tag}.jsonl"; outp.parent.mkdir(parents=True, exist_ok=True)
    t0 = time.time(); results = []

    def one(item):
        name, decl = item
        r = normalize(name, decl); r["set"] = a.bests; r["t"] = time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())
        b, f = r.get("before") or {}, r.get("after") or {}
        print(f"{name[:44]:44s} {r.get('status'):18s} tok {b.get('tokens')} -> {f.get('tokens')}  hb {b.get('heartbeats')} -> {f.get('heartbeats')}  "
              f"score {b.get('score')} -> {f.get('score')}  {r.get('applied', '')}  compiles {r.get('compiles')}", flush=True)
        return r
    with ThreadPoolExecutor(a.jobs) as ex:
        results = list(ex.map(one, sorted(bests.items())))
    with outp.open("w") as fh:
        for r in results:
            fh.write(json.dumps(r, ensure_ascii=False) + "\n")
    n = len(ROWS); gain = sum(r.get("gain", 0) for r in results)
    print(f"\n{a.bests}: {sum(r.get('status') == 'improved' for r in results)}/{len(results)} improved; summed gain {gain:+.2f} = {gain / n:+.3f} on the "
          f"{n}-problem line; {time.time() - t0:.0f}s -> {outp}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
