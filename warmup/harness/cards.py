"""Technique cards (Tier 2, panel proposal R1): playbook v1 as short, pattern-specific advice injected at run start.

Every rule comes from a verified panel finding (docs/panel/*.md, docs/panel_final.md). Cards describe proof PATTERNS, never a warm-up problem, so they
carry to the 50 unseen problems. The harness detects the patterns from the statement and the current proof and shows at most three cards plus the
always-on token/heartbeat card.
"""
from __future__ import annotations

import re

ALWAYS = ("TOKEN AND HEARTBEAT RULES (measured): a dotted name is ONE token (`h.choose_spec.2.1`, `x.mem_span`), so projections beat `obtain ⟨…⟩`; "
          "`·` and `;` are tokens, a newline is free; positional arguments and `_`/`..` beat `(f := …)` named arguments; `i.2` beats `by omega`; "
          "`use s', a, b` beats `exact ⟨_, a, b⟩` (explicit witness only); `exact (…).symm` beats a `rw` + `exact`. Heartbeats hide in elaboration, not only "
          "in tactics: `•` or `*` inside a lambda triggers an instance search (302 vs 46 hb measured), each `set` costs ~165 hb, a failed `apply` ~27 hb. "
          "Before trading tokens for heartbeats or back, read `axis` in lean_check (exchange rate, points left) and run lean_profile. "
          "`try`/`first`/`any_goals` around `exact ⟨…, by tac⟩` do NOT backtrack when the inner `by` fails (the error is logged, not thrown): use "
          "`refine ⟨…, ?_⟩; tac`. Batch variants as independent single edits, never stacked; print a goal (lean_goals) before building a term for it.")

CARDS = {
    "inductive": ("INDUCTIVE RELATIONS / TYPING DERIVATIONS: (1) if the proof calls the theorem itself, switch to `induction h generalizing x` and use the "
                  "induction hypotheses (370-440 hb vs 700-800 for self-calls). (2) After a case split, close all trivial cells with ONE shared closer "
                  "(`all_goals exact ⟨_, .refl _, by constructor <;> assumption⟩`, or `case'` to send sub-goals to `first | apply lemma <;> assumption | …`); "
                  "write out only the real cases. (3) Lemmas whose conclusion is ∃ or a constructor need FORWARD hints: `grind [→ lemma]`; read the library's "
                  "`@[grind]` attributes first. (4) For constructor goals use `solve_by_elim [C.c1, C.c2]` or `⟨_, by solve_by_elim [...]⟩` instead of hand-built "
                  "terms (most failures are misbound IHs / argument order). (5) `case X.Y` tags bind the LAST n unnamed hypotheses; induction hypotheses are "
                  "interleaved; check names with lean_goals. (6) Hypothesis `0 < n → P n`: try `Nat.le_induction`."),
    "calc": ("CALC CHAINS: a calc that restates a long goal at every step is the costliest structure in a proof (63% of one reference's tokens). Remove it: "
             "rewrite the goal directly (`change`, `rw`/`simp only` with the step lemmas, `conv_lhs => enter [..]` or `conv` under a sum/integral binder), or "
             "keep a short calc with `_` for intermediate right-hand sides. Close with `linear_combination` + one cancellation fact, or "
             "`convert … using 1; ring`. Use the library's generated lemmas (`@[to_fun]` makes `fun_deriv_sub`-style names) instead of `change` + base lemma."),
    "algebra": ("ALGEBRAIC REWRITING: one shared curated `simp only [...]` closer for all side goals (zero/add/smul cases of an induction) beats "
                "`simp_all` (22.6k hb measured) and `grind` (fails); delete lemmas one at a time from long `simp only` lists (unused ones are common); "
                "prefer general lemma names (`mul_smul_comm`, `smul_mul_assoc`) over `Algebra.*` variants (−800 hb measured); state a helper once over "
                "abstract arguments and apply it with `rw`; merge an apply/refine/rw/exact chain into one `exact` term (−308 hb); rewrite on the side where "
                "Lean infers the function (`rwa [← lemma]` on the goal instead of `rw … at h` with an explicit `(P := …)`); specialise recursive simp lemmas "
                "to the argument (`simp only [lemma u] at h`) so they cannot loop."),
    "sets": ("LISTS, SETS, CARDINALITIES: search the library for a lemma matching the block's conclusion before golfing the block (`card_le_mul_card_image_of_maps_to`, "
             "`card_le_card_of_surjOn`, ordered pigeonhole `Finite.exists_lt_map_eq_of_forall_mem` each replaced a whole block); `panic!`/`default` "
             "branches are often definitionally `[]`, so `List.nil_subset` closes 'impossible' cases; small helpers about lists often close by `:= by grind`; "
             "`Finset.mem_*`/`List.mem_*` simp lemmas plus `omega` absorb index bookkeeping."),
    "analysis": ("ANALYSIS (derivatives, integrals, smoothness): find the closing lemma by its conclusion and rank by typeclass match "
                 "(`Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero` removed a whole integrability block); bump functions: "
                 "`exists_contDiff_tsupport_subset` on a neighbourhood instead of ε-balls + `ContDiffBump`; smoothness indices: literal `3` unifies where `2+1` "
                 "fails (`ENat.LEInfty`); `fun_prop` does not see through structure coercions; pin constants with `(c := v)` to avoid instance search; "
                 "`field_simp` as a closer costs 3.8-4.5 points, plain `simp` instead of `simp only` 2.8."),
    "numbertheory": ("NUMBER THEORY / DIVISIBILITY: let the strongest closer absorb bookkeeping: feed raw facts into `ring`/`omega`, use `convert … using 1; ring` "
                     "instead of spelling out an equation; coprimality (`IsCoprime …|.pow_right.dvd_of_dvd_mul_right`) can replace a prime case split; "
                     "`Finset.dvd_sum` for sums; collect facts then one `omega` (omega cannot use powers or nonlinear terms: state them as facts first)."),
    "corollary": ("COROLLARY OF SIBLING LEMMAS: the file defines lemmas the reference does not use; when several share the statement's symbols, the theorem may "
                  "follow from them without induction (one problem went 33 → 73 in one compile this way). Rewrite-then-apply chains become transport: "
                  "`(e₁ ▸ e₂).trans (comm …) ▸ t` or `⟨_, rfl, …⟩` instead of `simp`."),
}

_DETECT = {
    "inductive": r"\binduction\b|\bcases\b|\brcases\b|\bobtain\b.*\birreducible|\bTyping\b|\bRed\b|⭢|\bIsBisimulation|\bTr\b",
    "calc": r"\bcalc\b",
    "algebra": r"\bring\b|\bsmul\b|•|\bmul_comm\b|\bAlgebra\.|\bspan\b|\blinear_combination\b|\bnoncomm_ring\b",
    "sets": r"\bFinset\.|\bList\.|⊆|\bcard\b|\bSet\.|\bFintype\b|∈",
    "analysis": r"\bderiv\b|\bfderiv\b|\bintegral\b|∫|\bContDiff\b|\bContinuous\b|\bDifferentiable\b|\bHasDerivAt\b",
    "numbertheory": r"∣|\bPrime\b|\bNat\.Prime\b|\bZMod\b|\bdvd\b|\bgcd\b|\bIsCoprime\b",
}


def select(statement: str, proof: str, context: str = "", k: int = 3) -> list[str]:
    """Up to k pattern cards ranked by how strongly the statement + proof match, plus 'corollary' when the file context has many lemmas sharing the
    statement's symbols. The ALWAYS card is returned separately by `cards_for`."""
    text = statement + "\n" + proof
    scores = {c: len(re.findall(rx, text)) for c, rx in _DETECT.items()}
    picked = [c for c, s in sorted(scores.items(), key=lambda kv: -kv[1]) if s > 0][:k]
    if context:
        generic = {"theorem", "lemma", "List", "Prop", "Type", "Nat", "Bool", "Option", "Finset", "Set", "Fin"}
        syms = set(re.findall(r"[A-Za-z_][\w.']{3,}", statement)) - generic
        lemmas = [m.group(0)[:500] for m in re.finditer(r"(?:theorem|lemma)\s+\S+.*?:=", context, re.S)]   # whole multi-line signature
        overlap = sum(1 for l in lemmas if len(syms & set(re.findall(r"[A-Za-z_][\w.']{3,}", l))) >= 2)
        if overlap >= 5 and len(picked) < k + 1:
            picked.append("corollary")
    return picked


def cards_for(statement: str, proof: str, context: str = "") -> str:
    picked = select(statement, proof, context)
    return "\n\n".join(["TECHNIQUE CARDS (measured on other problems; patterns, not answers):", ALWAYS] + [CARDS[c] for c in picked])
