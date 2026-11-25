-- F10: a theorem by well-founded recursion whose `decreasing_by` proof is a synthetic sorry: OWN (measured on cslib v4.31.0, the
-- sorry stays in D's own value, under `WellFounded.Nat.fix`; Lean names it in its sorry message, as for any `sorryAx` it sees).
-- expect: {"own_prefix": "LRAFix.mainT", "sorryAx": true, "sorry_message": true}
@HEADER@

namespace LRAFix

-- proof
theorem mainT : ∀ n : Nat, n + 0 = n
  | 0 => rfl
  | n + 1 => by
    have _h := mainT (n / 2)
    rfl
termination_by n => n
decreasing_by exact sorryAx _ true
