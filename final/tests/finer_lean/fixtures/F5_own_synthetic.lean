-- F5: the proof's own value holds a synthetic sorry, as Lean's error recovery leaves it, and NO Lean message names it (held-out
-- row 42's fault). A bare `sorryAx _ true` still draws "declaration uses `sorry`" on these toolchains (measured, cslib v4.31.0),
-- so the message is turned off here by `set_option warn.sorry false in`: the program must name D as OWN without any message.
-- (The guard's own text check flags that option by itself; this fixture tests the program, not the text check.)
-- The file also has a lemma proved by sorry, as the reference's library file would: the proof does not use it.
-- expect: {"sources": ["LRAFix.mainT"], "own": ["LRAFix.mainT"], "sorryAx": true, "sorry_message": false}
@HEADER@

namespace LRAFix

theorem libSorry : (1 : Nat) = 1 := sorry

-- proof
set_option warn.sorry false in
theorem mainT : (1 : Nat) = 1 ∧ True := ⟨sorryAx _ true, trivial⟩
