-- F14: the proof text lowers `maxHeartbeats` for the rest of the file (1000, below what elaborating the program needs, measured
-- 3000-10000): the program runs with `set_option maxHeartbeats 0 in`, so it reads as F2 (review 2026-11-24, compat finding 3).
-- expect: {"sources": ["LRAFix.libSorry"], "own": [], "sorryAx": true, "sorry_message": false}
@HEADER@

namespace LRAFix

theorem libSorry : (1 : Nat) = 1 := sorry

-- proof
set_option maxHeartbeats 1000

theorem mainT : (1 : Nat) = 1 ∧ True := ⟨libSorry, trivial⟩
