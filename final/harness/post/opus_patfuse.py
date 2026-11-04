#!/usr/bin/env python3
"""Op "opus_patfuse" of the open post-step (gap lane opus, 2026-11-04): fuse a destructuring step into the pattern that bound its
hypothesis.

Mechanism (the gap): the open proofs bind a hypothesis and destructure it in a separate later step (`intro x hx` ... `obtain ⟨a, b⟩ :=
hx`; `obtain ⟨⟨_, s⟩, hv, heq⟩ := h` ... `obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq`; `rcases e with ⟨a, h⟩` ... `rcases h with h1 | h2`);
the closed proofs write the nested pattern once (`rintro x ⟨a, b⟩`, `⟨⟨_, s⟩, hv, ⟨rfl, rfl⟩⟩`). Static count over the bundle (a
use step whose hypothesis has no other later mention): open_r2post 12 sites / 6 rows, open_r3snap 10 / 7, closed sets 1-3 sites.

Rule (pure; one line each, no comments in the body):
  use step   `obtain P := [F] h` | `rcases [F] h with P` | `cases' h with a b` (-> P = ⟨a, b⟩) | `subst h` (-> P = rfl) |
             `cases h` (-> P = ⟨⟩); F = at most one (dotted) identifier
             applied to h (`Prod.mk.inj`, `X.mp`, `id`, ..): it is dropped, rcases then destructures h's own type (Lean decides).
  binder     the nearest earlier line that mentions h, which must bind it: `intro .. h ..` (-> `rintro`), `rintro .. h ..`, or the
             pattern of `obtain PAT [: T] := e` / `rcases e with PAT`; h is mentioned exactly once on it and nowhere after it except
             in the use step.
  rewrite    h in the binder -> P (parenthesised in `rintro` when it has a top-level `|`; spliced when h is the last component of a
             `⟨..⟩` and P is a `⟨..⟩`), the use step deleted.
Candidates: the joint rewrite (all sites, applied greedily), then each single site, most tokens saved first; only candidates with
fewer tokens than the proof. No query: the post-step's gate decides (every pin, paired re-reading, audit). No table, no row name, no
lemma list: every token of a candidate is the proof's own or rcases syntax."""
from __future__ import annotations

# provenance: research lane gaplane2-opus (worktree lra-gl2-opus), commit ed5d5bc, ported unchanged into open-post-v3 (2026-11-04)

import re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from scorer.tokenize import split_declaration, count_tokens  # noqa: E402

FAMILY = "patfuse"
ID = r"[^\W\d][\w'.₀-₉ᵢ-ᵪ!?]*"
NAME = r"[^\W\d][\w'₀-₉ᵢ-ᵪ]*"
USE_RE = [
    ("obtain", re.compile(rf"^(?P<ind>\s*)obtain\s+(?P<pat>.+?)\s*:=\s*(?:(?P<f>{ID})\s+)?(?P<h>{NAME})\s*$")),
    ("rcases", re.compile(rf"^(?P<ind>\s*)rcases\s+(?:(?P<f>{ID})\s+)?(?P<h>{NAME})\s+with\s+(?P<pat>.+?)\s*$")),
    ("cases'", re.compile(rf"^(?P<ind>\s*)cases'\s+(?P<h>{NAME})\s+with\s+(?P<a>{NAME}|_)\s+(?P<b>{NAME}|_)\s*$")),
    ("subst", re.compile(rf"^(?P<ind>\s*)subst\s+(?P<h>{NAME})\s*$")),      # -> rfl
    ("cases", re.compile(rf"^(?P<ind>\s*)cases\s+(?P<h>{NAME})\s*$")),       # -> ⟨⟩
]
FIXED_PAT = {"subst": "rfl", "cases": "⟨⟩"}
SKIP_NAMES = {"this", "_", "rfl", "with", "at", "fun", "by", "if", "then", "else"}
BAL_O, BAL_C = "([{⟨⦃", ")]}⟩⦄"
PAT_OK = re.compile(r"[\w'₀-₉ᵢ-ᵪ⟨⟩()|,\s\-@!?.]+")   # rcases pattern syntax (names, ⟨⟩, (), |, -, _, rfl, @)


def word_re(h: str) -> re.Pattern:
    return re.compile(r"(?<![\w.'₀-₉])" + re.escape(h) + r"(?![\w'₀-₉!?])")


def _top_bar(p: str) -> bool:
    d = 0
    for ch in p:
        if ch in BAL_O:
            d += 1
        elif ch in BAL_C:
            d -= 1
        elif ch == "|" and d == 0:
            return True
    return False


def _top_colon(p: str) -> bool:
    d = 0
    for i, ch in enumerate(p):
        if ch in BAL_O:
            d += 1
        elif ch in BAL_C:
            d -= 1
        elif ch == ":" and d == 0 and p[i + 1:i + 2] != "=":
            return True
    return False


def _balanced(p: str) -> bool:
    d = 0
    for ch in p:
        if ch in BAL_O:
            d += 1
        elif ch in BAL_C:
            d -= 1
            if d < 0:
                return False
    return d == 0


def _bind_span(line: str):
    """(kind, start, end) of the binder region of `line` (where a pattern variable may sit), or None."""
    m = re.match(r"^(\s*)(intro|rintro)\s+", line)
    if m:
        return m.group(2), m.end(), len(line.rstrip())
    m = re.match(r"^(\s*)obtain\s+", line)
    if m:
        k = line.find(":=", m.end())
        if k < 0:
            return None
        pat = line[m.end():k]
        # an `obtain PAT : T := e`: the pattern ends at the first top-level ` : `
        d = 0
        for i, ch in enumerate(pat):
            if ch in BAL_O:
                d += 1
            elif ch in BAL_C:
                d -= 1
            elif ch == ":" and d == 0:
                return "obtain", m.end(), m.end() + i
        return "obtain", m.end(), k
    m = re.match(r"^(\s*)rcases\s+.*?\swith\s+", line)
    if m:
        return "rcases", m.end(), len(line.rstrip())
    return None


def sites(body: str) -> list[dict]:
    """Every fusable (binder line, use line) pair of the body."""
    if body is None or "--" in body or "/-" in body or "\t" in body:
        return []
    L = body.split("\n")
    out = []
    for j, line in enumerate(L):
        for kind, rx in USE_RE:
            m = rx.match(line)
            if not m:
                continue
            h = m.group("h")
            if h in SKIP_NAMES:
                break
            P = f"⟨{m.group('a')}, {m.group('b')}⟩" if kind == "cases'" else FIXED_PAT.get(kind) or m.group("pat").strip()
            if not P or not _balanced(P) or not (PAT_OK.fullmatch(P) or _top_colon(P) and ";" not in P and "<;>" not in P):
                break
            w = word_re(h)
            bi = next((i for i in range(j - 1, -1, -1) if w.search(L[i])), None)
            if bi is None or len(w.findall(L[bi])) != 1:
                break
            if any(w.search(L[k]) for k in range(bi + 1, len(L)) if k != j):
                break
            if len(w.findall(line)) != 1:
                break
            sp = _bind_span(L[bi])
            if sp is None:
                break
            bk, a, b = sp
            hm = w.search(L[bi], a)
            if hm is None or hm.end() > b:
                break
            # the use must sit at the binder's column or deeper (same block or nested)
            if len(line) - len(line.lstrip()) < len(L[bi]) - len(L[bi].lstrip()):
                break
            out.append({"bind": bi, "use": j, "h": h, "pat": P, "f": m.groupdict().get("f"), "bkind": bk, "pos": (hm.start(), hm.end())})
            break
    return out


def apply_site(body: str, s: dict) -> str | None:
    L = body.split("\n")
    bl = L[s["bind"]]
    a, b = s["pos"]
    if bl[a:b] != s["h"]:
        return None
    P = s["pat"]
    if _top_colon(P):
        P = f"({P})"
    inner = bl[:a].rstrip().endswith(("⟨", ",", "|")) and bl[b:].lstrip().startswith(("⟩", ",", "|"))
    if P.startswith("⟨") and P.endswith("⟩") and P[1:-1].strip() and _balanced(P[1:-1]) and bl[b:].lstrip().startswith("⟩") and bl[:a].rstrip().endswith(","):
        rep = P[1:-1]   # ⟨x, h⟩ with h := ⟨a, b⟩ -> ⟨x, a, b⟩ (rcases nests to the right)
    elif _top_bar(P) and (s["bkind"] in ("intro", "rintro") or not inner) and not P.startswith("("):
        rep = f"({P})"
    else:
        rep = P
    new = bl[:a] + rep + bl[b:]
    if s["bkind"] == "intro":
        new = re.sub(r"^(\s*)intro\b", r"\1rintro", new, count=1)
    L[s["bind"]] = new
    del L[s["use"]]
    return "\n".join(L)


def rewrites(body: str) -> list[tuple[str, str, str]]:
    """[(variant, new body, note)]: the joint rewrite first, then the singles (most tokens saved first)."""
    ss = sites(body)
    if not ss:
        return []
    t0 = count_tokens(body)
    singles = []
    for s in ss:
        nb = apply_site(body, s)
        if nb is not None and count_tokens(nb) < t0:
            singles.append(("patfuse:single", nb, f"{s['h']}: line {s['use']} into line {s['bind']} ({s['bkind']})"))
    singles.sort(key=lambda x: count_tokens(x[1]))
    out = []
    # joint: apply greedily, re-detecting sites after each fusion
    cur, n = body, 0
    for _ in range(len(ss) + 2):
        cs = sites(cur)
        done = False
        for s in cs:
            nb = apply_site(cur, s)
            if nb is not None and count_tokens(nb) < count_tokens(cur):
                cur, n, done = nb, n + 1, True
                break
        if not done:
            break
    if n >= 2:
        out.append(("patfuse:joint", cur, f"{n} fusions"))
    seen = {b for _, b, _ in out}
    for x in singles:
        if x[1] not in seen:
            seen.add(x[1]); out.append(x)
    return out


# ------------------------------------------------------------------------------------------------------------------------------ op API
def has_sites(proof: str, statement: str) -> bool:
    try:
        return bool(sites(split_declaration(proof, statement)))
    except Exception:  # noqa: BLE001
        return False


def candidates(proof: str, statement: str, *, exchange=None, max_per_op=None, ctx=None) -> list[dict]:
    try:
        body = split_declaration(proof, statement)
        if body is None:
            return []
        out = []
        for v, nb, note in rewrites(body):
            out.append({"op": v, "decl": statement.rstrip() + " :=" + nb.rstrip(), "note": note})
        return out[: (max_per_op or 6)]
    except Exception:  # noqa: BLE001
        return []
