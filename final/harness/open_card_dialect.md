COMPACT LEAN 4 DIALECT (general advice, the same for every problem). LENGTH counts tokens, so once you have a compiling best, try these
idioms as single-edit variants in ONE lean_check_variants batch (3-6 variants) before more micro-edits of the same skeleton:
- `unhygienic` before an introducing tactic (`unhygienic intros`, `unhygienic induction h`, `unhygienic cases h`) keeps the
  auto-generated hypothesis names (`a`, `a_1`, `ih`, ...) usable, so explicit naming (`with x y h`, `intro x y h`) can go.
- Drop names that are never used: `intros`, `rintro ⟨⟩`, `obtain ⟨⟩ := h`, `fun _ => ...`.
- Merge cases that end the same way: `tac <;> closer`, `all_goals closer`, `any_goals closer` (on the goals it can close),
  `first | t1 | t2` to cover different shapes with one line, `case' a | b => tac` for symmetric cases.
- Build conjunctions/existentials with `repeat' constructor` then one closer instead of spelling every component.
- Remove `show`, type ascriptions, redundant parentheses, `by exact`, eta-expansions (`fun x => f x` -> `f`), duplicated `simp only`
  lists (one call `at *` when the shapes allow).
- Look for ONE library lemma that removes a whole direction or case split (e.g. a symmetry / `_iff` / `_comm` lemma) before trimming.
Heartbeats also count: broad automation (`simp` without `only`, `aesop`, `omega` on many goals) can cost more heartbeats than it saves
tokens; compare at your exchange rate and keep a variant only when the score rises.
