#!/usr/bin/env python3
"""gap6 step detector (operator 2026-11-01 ~05:30 UTC: "break these rules as small groups ... run each step with score measure after";
docs/open_gap6_prompt.md). Reads a row's current best proof and returns the ONE structural move that applies (or none), with the
sites in that proof, as a short step message for one GLM session (appended after the dialect card by agent.py --open-card).
Deterministic, $0, general: the patterns are Lean syntax, the sites come from the open proof itself, no closed-line text.
    python3 detect.py BESTS.json [LEMMAS.json] OUTDIR     BESTS = {name: proof}; LEMMAS = {name: [lemma names]} (harness-run rg results)
Writes OUTDIR/<safe name>.md (the step message) and OUTDIR/plan.json ({name: {step, sites, ...}})."""
import json, re, sys
from pathlib import Path

TAIL = "Start with ONE lean_check_variants batch of 2-4 variants of this one change, keep what compiles and scores higher, then continue as usual."


def lines_of(proof: str) -> list:
    body = proof.split(":= by", 1)
    off = proof[:len(body[0])].count("\n") if len(body) == 2 else 0
    return [(i + 1, l) for i, l in enumerate(proof.splitlines()) if i >= off]


def site(n: int, l: str, w: int = 60) -> str:
    s = l.strip()
    return f"line {n} `{s[:w]}{'...' if len(s) > w else ''}`"


def restate(proof: str) -> list:
    pat = re.compile(r"^\s*(calc\b|show\b|let\b|set\b|have\s+\S+\s*:(?!=)|obtain\s.*:\s*∃|with_reducible calc\b)|\bcalc\s+_")
    hits = [(n, l) for n, l in lines_of(proof) if pat.search(l)]
    # the costliest first: calc / show / let / set, then typed have / obtain by the length of the restated text
    hits.sort(key=lambda x: (0 if re.search(r"\b(calc|show|let|set)\b", x[1].split(":=")[0]) else 1, -len(x[1]), x[0]))
    return [site(n, l) for n, l in hits]


def funind(proof: str, stmt: str) -> dict | None:
    if "fun_induction" in proof:
        return None
    unf = [f for f in re.findall(r"\bunfold\s+([\w.']+)", proof) if f.split(".")[-1] in stmt]
    ind = re.findall(r"\b(?:induction|cases)\s+([\w']+)", proof)
    if unf and ind:
        return {"f": unf[0], "on": ind[0]}
    return None


def mirror(proof: str) -> list:
    out = []
    rot = [site(n, l) for n, l in lines_of(proof) if re.search(r"\brotate_(left|right)\b", l)]
    if len(rot) >= 2:
        out.append(f"goals reordered with `rotate_left`/`rotate_right` ({len(rot)} times)")
    alts = [l for _, l in lines_of(proof) if re.match(r"\s*\|\s*exact\b", l)]
    if len(alts) >= 2:
        out.append(f"`first | exact ... | exact ...` alternatives that differ in one name ({len(alts)} lines)")
    if re.search(r"constructor\s*<;>", proof):
        out.append("both directions proved by one `constructor <;>` with per-direction alternatives")
    return out


def bundled(proof: str) -> dict | None:
    c, e = proof.count("∘ₗ"), len(re.findall(r"\.ext\b", proof))
    return {"comp": c, "ext": e} if c >= 2 or (c and e) else None


def plan(name: str, proof: str, lemmas: list) -> dict | None:
    stmt = proof.split(":= by", 1)[0]
    fi = funind(proof, stmt)
    if fi:
        return {"step": "funind", **fi, "msg": (
            f"ONE MOVE FOR THIS SESSION: your best proves this by induction/cases on `{fi['on']}` and then unfolds `{fi['f']}` by hand. "
            f"Try `fun_induction {fi['f']}` instead: its cases follow the equations of `{fi['f']}`, so `unfold` and `split` go; close the "
            "cases with shared `all_goals` / `any_goals` lines. Once the induction no longer uses the hypothesis, try dropping it "
            "(`rintro -`). " + TAIL)}
    bd = bundled(proof)
    if bd:
        return {"step": "elements", **bd, "msg": (
            f"ONE MOVE FOR THIS SESSION (heartbeats): your best composes bundled maps (`∘ₗ` {bd['comp']} times, `.ext` {bd['ext']} times); "
            "elaborating those compositions is expensive. Work on elements instead: expand the arguments into their sum over the basis "
            "and use a congruence lemma for sums, or one `simp only` on the elements; a fact used for several instances goes in one local "
            "`∀` statement proved once. " + TAIL)}
    mi = mirror(proof)
    if mi:
        lem = ("Lemmas in the relation's own file that may reduce the goal to one direction: " + ", ".join(f"`{x}`" for x in lemmas[:12])
               + ". Try one of them as the first step. ") if lemmas else ""
        return {"step": "mirror", "evidence": mi, "lemmas": lemmas[:12], "msg": (
            "ONE MOVE FOR THIS SESSION: your best does mirror-image work twice (" + "; ".join(mi) + "). " + lem +
            "Merge mirror cases: flip one side with `case' <a> | <b> => apply symm`, then prove both in one `case <a> | <b> => ...`; name "
            "cases instead of reordering goals; replace paired `exact` alternatives by one `all_goals` block of `try apply` steps. " + TAIL)}
    rs = restate(proof)
    if len(rs) >= 2:
        return {"step": "restate", "sites": rs, "msg": (
            "ONE MOVE FOR THIS SESSION: stop restating terms. Your best spells out expressions Lean already has at " + "; ".join(rs[:6]) +
            ". Remove them: rewrite in place with `conv_lhs => enter [...]; rw [...]` or `rw [...] at h`; chain lemmas with `.trans` / "
            "`.mp` inside one `refine` / `exact`; close with `simpa only [...] using <term>`; write `have h x := lemma x` without a type. " + TAIL)}
    return None


def plan_all(name: str, proof: str, lemmas: list) -> list:
    """gap6 chain mode (operator 2026-11-01 ~07:15 UTC): every move that applies to this proof, in priority order (funind, elements, mirror,
    restate), each with its one-move message; the chain runs them one after another on the evolving best."""
    stmt = proof.split(":= by", 1)[0]
    out = []
    fi = funind(proof, stmt)
    if fi:
        out.append(plan(name, proof, lemmas))
    bd = bundled(proof)
    if bd:
        out.append({"step": "elements", **bd, "msg": plan_msg_elements(bd)})
    mi = mirror(proof)
    if mi:
        lem = ("Lemmas in the relation's own file that may reduce the goal to one direction: " + ", ".join(f"`{x}`" for x in lemmas[:12])
               + ". Try one of them as the first step. ") if lemmas else ""
        out.append({"step": "mirror", "evidence": mi, "lemmas": lemmas[:12], "msg": (
            "ONE MOVE FOR THIS SESSION: your best does mirror-image work twice (" + "; ".join(mi) + "). " + lem +
            "Merge mirror cases: flip one side with `case' <a> | <b> => apply symm`, then prove both in one `case <a> | <b> => ...`; name "
            "cases instead of reordering goals; replace paired `exact` alternatives by one `all_goals` block of `try apply` steps. " + TAIL)})
    rs = restate(proof)
    if len(rs) >= 2:
        out.append({"step": "restate", "sites": rs, "msg": (
            "ONE MOVE FOR THIS SESSION: stop restating terms. Your best spells out expressions Lean already has at " + "; ".join(rs[:6]) +
            ". Remove them: rewrite in place with `conv_lhs => enter [...]; rw [...]` or `rw [...] at h`; chain lemmas with `.trans` / "
            "`.mp` inside one `refine` / `exact`; close with `simpa only [...] using <term>`; write `have h x := lemma x` without a type. " + TAIL)})
    return [x for x in out if x]


def plan_msg_elements(bd: dict) -> str:
    return (f"ONE MOVE FOR THIS SESSION (heartbeats): your best composes bundled maps (`∘ₗ` {bd['comp']} times, `.ext` {bd['ext']} times); "
            "elaborating those compositions is expensive. Work on elements instead: expand the arguments into their sum over the basis "
            "and use a congruence lemma for sums, or one `simp only` on the elements; a fact used for several instances goes in one local "
            "`∀` statement proved once. " + TAIL)


def safe(n: str) -> str:
    return re.sub(r"[^A-Za-z0-9_.-]", "_", n)


if __name__ == "__main__":
    bests = json.loads(Path(sys.argv[1]).read_text())
    lemmas = json.loads(Path(sys.argv[2]).read_text()) if len(sys.argv) > 3 else {}
    out = Path(sys.argv[-1]); out.mkdir(parents=True, exist_ok=True)
    P = {}
    for n, p in bests.items():
        r = plan(n, p, lemmas.get(n, []))
        P[n] = r
        if r:
            (out / f"{safe(n)}.md").write_text(r["msg"] + "\n")
        print(f"{n.split('.')[-1][:34]:34s} {r['step'] if r else '-':9s} {(r['msg'][:150] + '...') if r else ''}")
    (out / "plan.json").write_text(json.dumps(P, indent=1, ensure_ascii=False))
