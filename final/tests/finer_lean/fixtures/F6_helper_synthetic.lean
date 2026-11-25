-- F6: a helper lemma written in the proof text (after the `-- proof` line), proved by a synthetic sorry, used by the proof: OWN (the
-- proof text declared it; program v2). D's own lines draw no sorry message
-- (Lean names the helper; the guard's message check covers the whole proof text, this fixture tests the program's naming).
-- expect: {"sources": ["LRAFix.auxHelper"], "own": ["LRAFix.auxHelper"], "sorryAx": true, "sorry_message": false}
@HEADER@

namespace LRAFix

theorem libSorry : (1 : Nat) = 1 := sorry

-- proof
theorem auxHelper : (1 : Nat) = 1 := sorryAx _ true

theorem mainT : (1 : Nat) = 1 ∧ True := ⟨auxHelper, trivial⟩
