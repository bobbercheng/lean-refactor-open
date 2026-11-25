-- F2: the proof uses a lemma of the same file proved by sorry (as a library file's prefix would hold it).
-- expect: {"sources": ["LRAFix.libSorry"], "own": [], "sorryAx": true, "sorry_message": false}
@HEADER@

namespace LRAFix

theorem libSorry : (1 : Nat) = 1 := sorry

-- proof
theorem mainT : (1 : Nat) = 1 ∧ True := ⟨libSorry, trivial⟩
