SHORTER PROOFS BY AUTOMATION:
Length counts as much as heartbeats, and the usual gap is a long explicit proof where one automation call closes the same goal.
- Before polishing a step-by-step block, try to replace the whole block (or the whole proof) with one closer: `grind [lemmas the
  proof already uses]` (write `→ name` for a lemma that concludes an existential or a constructor), `simp_all [names]`, `omega`,
  `decide`, `aesop`.
- After `induction` / `cases` / `split`, close all the cases at once with `<;> closer` or `all_goals closer`; keep a separate case only
  where that fails.
- Inline a `have` that one closer proves.
- Keep the automated version only when the score is higher: if the heartbeats rise more than the length falls, keep the explicit one.
