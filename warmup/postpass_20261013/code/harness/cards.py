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


# 2026-10-13 ($0 steps): a heartbeat-first card from techniques measured on our own records.
# OFF by default (house rule: a new card is switched on only after it wins an A/B); shown only under --heartbeat-first (cards_for below).
HEARTBEAT_FIRST = ("HEARTBEAT-FIRST RULES (measured on our records; patterns, not answers): (1) restrict every automation call to a named list: "
                   "`simp` -> `simp only [..]` (median -222 hb over 39 pairs), `grind` -> `grind only [..]` (-275), `simp_all only [..]` or "
                   "`simp_all [-lemma]`; take the list from the `simp?`/`grind?` certificate. (2) Never pay for failing attempts: route each goal to the "
                   "one closer that works (`case'` tags, main-goal order, `with_reducible apply` inside `first`); a failing branch costs its whole "
                   "elaboration. (3) Hidden retries: `rw` = `rewrite` + `try (with_reducible rfl)`, `exists` = `refine` + `try trivial`, Mathlib `use` "
                   "runs a discharger on leftover goals: write `rewrite` / `refine ⟨.., ?_⟩` when those retries do not close the goal. (4) Lemma choice "
                   "drives instance search: prefer the specialized lemma (`AlgHom.map_smul_of_tower` over `map_smul`: -834 hb at 0 tokens; semilinear "
                   "variants over IsScalarTower / SMulCommClass searches); compile both. (5) Definitional steps: `dsimp only` or `rfl`, not `simp only` "
                   "(86-100% cheaper when definitional). (6) Follow the recursion: `fun_induction f` over `induction x <;> simp [f] <;> split` (median "
                   "-2,028 hb); `induction h` over `cases h` when the indices are variables. (7) Trade by the exchange rate in `axis`: when heartbeat "
                   "points left exceed length points, accept tokens for heartbeats (explicit constructor terms instead of one `grind` per case: "
                   "59,830 -> 1,800 hb on an inductive-typing proof). On heartbeat-heavy proofs do not default to automation or term mode: measure.")

# 2026-10-13 --heartbeat-first (agent.py, agent_claude_code.py --prompt v2; OFF by default, every default prompt byte-identical): the guidance that
# contradicts HEARTBEAT_FIRST, as (old, new) pairs applied by heartbeat_aware(). System prompts are static per run, so their new wording is itself
# axis-conditional (R1, R2: applied whenever the flag is on); the user-prompt pieces (cards, scout / structural / heartbeat briefs, repo cards) are
# rewritten only where heartbeat_first_on() passes. Every `old` must occur in a live prompt (harness/test_heartbeat_first.py), so a reworded source
# fails the test instead of silently keeping the contradiction; no `new` contains an `old` (idempotent). A/B UNIT (review 2026-10-13): the
# flag, not the gate: the system-prompt rewrites reach every row of a flag-on run, so a flag-on row with runs[].heartbeat_first False is not a
# control. Gate threshold: H >= L as specified; v2's own heartbeat-first threshold is H >= cc_levers.H_FIRST (2 points), so on v2 the card can be
# off on rows whose `axis.work_on` already says heartbeats (a design decision; the system wording below follows `work_on` in both drivers).
HB_REWRITES = (
    # R1 agent.py SYSTEM: AUTOMATION FIRST (solve_by_elim / aesop / bare grind as the robust default closers)
    ("CLOSERS: AUTOMATION FIRST (`grind` with lemma hints, forward hints `grind [→ lemma]` for lemmas concluding ∃ or a constructor, `simp`, "
     "`omega`, `aesop`, `solve_by_elim`, `linear_combination`): it is robust, while hand-written terms are the most common failure (wrong "
     "hypothesis, argument order). Once the proof compiles, replace an automation call by an explicit term only where the `axis` in lean_check "
     "says the heartbeats saved are worth more than the tokens added, and keep the swap only if it compiles and scores higher; on small proofs "
     "one `grind` costs ~200 heartbeats, so count calls.",
     # review 2026-10-13 (finding 5): the length branch keeps the old closer list and swap rule word for word, so a flag-on row whose lean_check
     # says `work_on` tokens reads the same closers as before; only the heartbeat branch is new
     "CLOSERS BY THE AXIS: read `axis` in lean_check. While its `work_on` is tokens, automation comes first (`grind` with lemma hints, forward "
     "hints `grind [→ lemma]` for lemmas concluding ∃ or a constructor, `simp`, `omega`, `aesop`, `solve_by_elim`, `linear_combination`): it is "
     "robust, while hand-written terms are the most common failure (wrong hypothesis, argument order); once the proof compiles, replace an "
     "automation call by an explicit term only where `axis` says the heartbeats saved are worth more than the tokens added, and keep the swap "
     "only if it compiles and scores higher. When `work_on` is heartbeats (or no axis is known yet), heartbeats come first: restrict every "
     "automation call to a named list (`simp only [..]`, `grind only [..]` from the `simp?` / `grind?` certificate), route each goal to the one "
     "closer that works, and write explicit terms, `exact` or `rfl` where they compile cheaper; a failing branch costs its whole elaboration and "
     "one `grind` costs ~200 heartbeats on small proofs, so count calls. On heartbeat-heavy proofs neither automation nor term mode is a "
     "default: compile both and keep the higher score."),
    # R2 TOKEN_RULES (agent.py SYSTEM with --length-tools / --token-rules, prompt_v2 SYSTEM_V2): one blanket closer per block. Review 2026-10-13
    # (finding 6): keyed to `axis.work_on`, so each driver's own threshold applies (agent.py: H > L; v2: H >= cc_levers.H_FIRST, as HEARTBEAT_CC
    # and LENGTH_CC say) instead of a second threshold in the same system prompt
    ("The big wins are still whole blocks replaced by one closer (`grind [lemmas]`, `simp_all`, `omega`, `fun_prop`, `aesop`) — 75-95% of a block.",
     "On the length axis the big wins are whole blocks replaced by one closer (`grind [lemmas]`, `simp_all`, `omega`, `fun_prop`, `aesop`) — 75-95% "
     "of a block; when `axis.work_on` is heartbeats, pin that closer to a named list (`simp only [..]`, `grind only [..]`) and compile it against "
     "the explicit steps."),
    # R3 agent.py SCOUT_BRIEFS['automation'] (--brief automation)
    ("SCOUT A — AUTOMATION FIRST. Aim for the shortest proof by delegating to decision procedures: `simp_all`, `simp only [...] at *`, `grind`, "
     "`omega`, `decide`, `aesop`, `norm_num`, `positivity`, `linarith`/`nlinarith`, `fun_prop`, `ext <;> simp`. Try `by grind` / `by simp_all` / "
     "`by omega` on the whole goal first, then on each case after ONE `cases`/`induction` with `<;>` or `all_goals`. Batch the closers with "
     "lean_check_variants. `simp only` beats `simp` on heartbeats when both compile.",
     "SCOUT A — AUTOMATION, PINNED (heartbeat-first). Find which blocks one decision procedure closes (`simp_all`, `simp only [...] at *`, `grind`, "
     "`omega`, `decide`, `norm_num`, `positivity`, `linarith`/`nlinarith`, `fun_prop`), then pin every call to a named list from its `?` "
     "certificate (`simp?` -> `simp only [..]`, `grind?` -> `grind only [..]`, `simp_all only [..]`): a bare `simp_all` / `grind` / `aesop` costs "
     "hundreds to thousands of heartbeats per call. After ONE `cases`/`induction`, route each case to the one closer that works (`case'` tags) "
     "instead of `<;> first | ..` retries. Batch the closers with lean_check_variants and keep the variant with the higher score (`axis`), not "
     "the shorter one."),
    # R4 agent.py SCOUT_BRIEFS['direct'] (--brief direct): term mode as the default shape
    ("Avoid tactic blocks except a single closer.",
     "Compile each term against the tactic block it replaces and keep the higher score (`axis`): a term is not cheaper by default (elaboration "
     "and instance search hide in it)."),
    # R5 agent.py cycle-22 HEARTBEAT FIRST brief: term mode ranked first
    ("Prefer, in order: a more direct proof shape (term-mode `exact`/anonymous constructors over tactic blocks), lower search burden (`simp only "
     "[...]`/`rw` over `simp`/`omega`/`grind`/`aesop` where both compile, `exact lemma args` over `apply`+goals), then clarity, then brevity.",
     "Prefer, in order: lower search burden (named lists from the `?` certificate: `simp only [...]` / `grind only [...]` over bare `simp`/`grind`/"
     "`aesop`; one routed closer per goal over `first | ..` retries; `exact lemma args` over `apply`+goals), a more direct proof shape where it "
     "measures cheaper (an explicit term or anonymous constructor is a candidate to compile, not a default), then clarity, then brevity."),
    # R6 agent.py STRUCTURAL PASS item (3): one blanket grind per case over hand-written terms
    ("(3) one shared AUTOMATION closer for alike cases (`induction x <;> grind [hints]`, `all_goals simp only [...]`, `case'` + `first | …`) "
     "instead of a hand-written term per case; ",
     "(3) one shared closer for alike cases where it is cheap (`all_goals simp only [...]`, `case'` sending each case to the one closer that "
     "works); a blanket `<;> grind` per case can cost far more heartbeats than explicit constructor terms, so compile both; "),
    # R7 CARDS['inductive'] item (4): solve_by_elim first
    ("(4) For constructor goals use `solve_by_elim [C.c1, C.c2]` or `⟨_, by solve_by_elim [...]⟩` instead of hand-built terms (most failures "
     "are misbound IHs / argument order).",
     "(4) For constructor goals, explicit constructor terms (`C.c1 h₁ h₂`, `⟨_, C.c2 ..⟩`) are the cheapest closers once the induction "
     "hypotheses are bound right (check them with lean_goals); `solve_by_elim [C.c1, C.c2]` finds the term but pays for its search: use it to "
     "discover the term, then write the term."),
    # R8 SCOUT_BRIEFS['restructure'] (agent.py --brief restructure, prompt_v2 from-reference): tokens first
    ("Batch 2-4 architectures with lean_check_variants and keep the one with the fewest tokens, then cut heartbeats.",
     "Batch 2-4 architectures with lean_check_variants and keep the one with the highest score (`axis` says which axis holds the points), not "
     "the fewest tokens."),
    # R9 REPO_BRIEFS['cslib'] (agent.py --length-tools, prompt_v2 --repo-cards): a bare grind per case
    ("`all_goals grind [...]` after induction/cases.",
     "`all_goals grind [...]` after induction/cases; on heartbeat-heavy rows pin it to `grind only [...]` from the `grind?` certificate."),
    # ---- review 2026-10-13 (findings 2-4): the rest of the flag-on prompt that still contradicted the card ----
    # R10 agent.py SYSTEM (--length-tools): length first after every skeleton (v2 made the same paragraph axis-conditional: LENGTH_CC)
    ("LENGTH IS THE MISSING AXIS: on most problems the proof is still ~40% of the reference length and the target is ~20%. After any new "
     "compiling skeleton, call lean_mine once: it finds which blocks a single automation call closes. Then rewrite the remaining long blocks.",
     "LENGTH (while `axis.work_on` in lean_check is tokens; when it is heartbeats, CLOSERS BY THE AXIS comes first): after any new compiling "
     "skeleton, call lean_mine once: it finds which blocks a single automation call closes and banks the result only if it scores higher. Then "
     "rewrite the remaining long blocks."),
    # R11 agent.py lean_mine tool description (applied to TOOLS in main()): bare closers after every skeleton
    ("Takes 1-3 minutes. Use it after every new compiling skeleton, then golf what it returns.",
     "Takes 1-3 minutes. Use it after a new compiling skeleton while `axis.work_on` is tokens, then golf what it returns; its closers are bare "
     "automation, so on heartbeat-heavy proofs pin what it finds to `only` lists (`simp?` / `grind?`)."),
    # R12 CARDS['inductive'] item (2): `case'` into a `first | ..` retry chain (HEARTBEAT_FIRST (2): never pay for failing attempts)
    ("or `case'` to send sub-goals to `first | apply lemma <;> assumption | …`)",
     "or `case'` sending each sub-goal to the one closer that works, not into a `first | …` retry chain)"),
    # R13 CLOSED_LESSONS habit 2 (agent.py --closed-lessons user prompt, prompt_v2 SYSTEM_V2): `any_goals A` pays for A failing on every goal
    ("`<;> first | A | B` is shorter as `any_goals A` then `all_goals B` (2 tokens fewer).",
     "On the length axis, `any_goals A` then `all_goals B` is 2 tokens shorter than `<;> first | A | B`; on heartbeats both pay for A "
     "failing on every goal B closes: route each goal to the one closer that works."),
    # R14 LEVER_REVIEW checklist (agent.py --lever-review, prompt_v2 on a resume): the same lever
    ("`<;> first | A | B` (as `any_goals A` then `all_goals B`)",
     "`<;> first | A | B` (on the length axis `any_goals A` then `all_goals B`; on heartbeats one routed closer per goal)"),
    # R15 REPO_BRIEFS['arklib'] (agent.py --length-tools, prompt_v2 --repo-cards): unpinned simp_all / aesop
    ("structural goals → `simp_all`/`aesop`.",
     "structural goals → `simp_all`/`aesop` to find the closer, then pin it from its certificate (`simp?` -> `simp only [..]`, `aesop?` -> "
     "the script it prints) where that compiles cheaper."),
    # R16 REPO_BRIEFS['physlib']: unpinned simp_all (HEARTBEAT_CC: ~1.4k hb per call on the closed lines)
    ("prefer `simp_all`/`simp only [...]` over long rw chains.",
     "prefer `simp only [...]` (from the `simp?` certificate) over long rw chains; a bare `simp_all` costs ~1.4k heartbeats per call."),
)


def heartbeat_aware(text: str) -> str:
    """`text` with every HB_REWRITES pair applied (a no-op on text that holds none of them)."""
    for old, new in HB_REWRITES:
        text = text.replace(old, new)
    return text


def heartbeat_first_on(ax: dict | None) -> bool:
    """The --heartbeat-first gate: True when no axis is known (no measured best yet) or the stored best has at least as many heartbeat points
    left (against the profile floor once one was measured) as length points left (cc_levers.axis / agent.py's lean_check `axis`)."""
    if not ax:
        return True
    return float(ax.get("points_left_heartbeats") or 0) >= float(ax.get("points_left_length") or 0)


def best_axis(name: str, row: dict, state: dict, ref_hb=None) -> dict | None:
    """cc_levers.axis of the stored best (tokens, heartbeats, state.json hb_floor) against the scorer's local reference heartbeats (else
    `ref_hb`, the official ones); None when the best has no measured heartbeats (the reference start)."""
    from harness import cc_levers as LV
    from scorer.score import local_reference_heartbeats
    b = state.get("best") or {}
    return LV.axis(row.get("proof_length"), local_reference_heartbeats(name) or ref_hb, b.get("tokens"), b.get("heartbeats"), state.get("hb_floor"))


# 2026-10-13 review (finding 7): harness/agent_codex.py --heartbeat-first. Its task (agent_claude_code v1 SYSTEM / task_prompt) has no card
# slot and its lean_check.py returns no `axis` (that is v2's _lra_v2.py), so the card is appended to the task with rule (7) priced from the
# reference numbers the task message states.
HEARTBEAT_FIRST_V1 = HEARTBEAT_FIRST.replace(
    "Trade by the exchange rate in `axis`: when heartbeat points left exceed length points,",
    "Trade by the exchange rate (one token = reference heartbeats / reference tokens heartbeats, both in the task message): when "
    "heartbeats hold more of the score left than tokens,")


def gate(name: str, row: dict, state: dict, ref_hb=None, log=lambda *a: None) -> bool:
    """heartbeat_first_on(best_axis(..)) with one log line (an axis error counts as no axis: on); shared by the drivers."""
    try:
        ax = best_axis(name, row, state, ref_hb)
    except Exception as e:  # noqa: BLE001
        ax = None; log(f"heartbeat-first axis failed: {e}")
    on = heartbeat_first_on(ax)
    log(f"heartbeat-first {'ON' if on else 'off'} (" + (f"H {ax['points_left_heartbeats']} vs L {ax['points_left_length']} points left"
        if ax else "no axis yet") + ")")
    return on


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


def cards_for(statement: str, proof: str, context: str = "", heartbeat_first: bool = False) -> str:
    """The card block. heartbeat_first (--heartbeat-first, the caller's axis gate passed): HEARTBEAT_FIRST right after ALWAYS and the pattern
    cards rewritten by heartbeat_aware(); False returns the pre-2026-10-13 block byte for byte."""
    picked = select(statement, proof, context)
    if heartbeat_first:
        return "\n\n".join(["TECHNIQUE CARDS (measured on other problems; patterns, not answers):", ALWAYS, HEARTBEAT_FIRST]
                           + [heartbeat_aware(CARDS[c]) for c in picked])
    return "\n\n".join(["TECHNIQUE CARDS (measured on other problems; patterns, not answers):", ALWAYS] + [CARDS[c] for c in picked])
