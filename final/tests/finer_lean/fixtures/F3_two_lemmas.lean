-- F3: the proof uses two lemmas of the same file proved by sorry.
-- expect: {"sources": ["LRAFix.libSorry", "LRAFix.libSorry2"], "own": [], "sorryAx": true, "sorry_message": false}
@HEADER@

namespace LRAFix

theorem libSorry : (1 : Nat) = 1 := sorry

theorem libSorry2 : (2 : Nat) = 2 := sorry

-- proof
theorem mainT : (1 : Nat) = 1 ∧ (2 : Nat) = 2 := ⟨libSorry, libSorry2⟩
