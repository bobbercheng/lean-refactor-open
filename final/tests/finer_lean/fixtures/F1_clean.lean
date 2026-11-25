-- F1: a clean proof: no sorry source.
-- expect: {"sources": [], "own": [], "sorryAx": false, "sorry_message": false}
@HEADER@

namespace LRAFix

-- proof
theorem mainT : (2 : Nat) + 2 = 4 ∧ True := ⟨rfl, trivial⟩
