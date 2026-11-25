-- F7: the declaration is a private theorem (as held-out row 42's is); it uses the file's lemma proved by sorry.
-- expect: {"decl": "LRAFix.mainT (private)", "sources": ["LRAFix.libSorry"], "own": [], "sorryAx": true, "sorry_message": false}
@HEADER@

namespace LRAFix

theorem libSorry : (1 : Nat) = 1 := sorry

-- proof
private theorem mainT : (1 : Nat) = 1 ∧ True := ⟨libSorry, trivial⟩
