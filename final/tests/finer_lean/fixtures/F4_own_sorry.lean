-- F4: the proof's own value holds an explicit sorry (Lean's sorry message on it).
-- expect: {"sources": ["LRAFix.mainT"], "own": ["LRAFix.mainT"], "sorryAx": true, "sorry_message": true}
@HEADER@

namespace LRAFix

theorem libSorry : (1 : Nat) = 1 := sorry

-- proof
theorem mainT : (1 : Nat) = 1 ∧ True := ⟨sorry, trivial⟩
