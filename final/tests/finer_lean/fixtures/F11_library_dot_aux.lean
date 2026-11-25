-- F11: the library file's prefix holds a lemma named `mainT.aux` (D is a name prefix of it) proved by sorry; the proof uses it. It
-- is a source of the library, not OWN: its declaration range is before the proof text (review 2026-11-24, compat finding 2: program
-- v1 marked it OWN by name prefix, so a reference proof that used it failed its own finer check). Against itself: OK.
-- expect: {"sources": ["LRAFix.mainT.aux"], "own": [], "sorryAx": true, "sorry_message": false}
@HEADER@

namespace LRAFix

theorem mainT.aux : (1 : Nat) = 1 := sorry

-- proof
theorem mainT : (1 : Nat) = 1 ∧ True := ⟨mainT.aux, trivial⟩
