-- F13: the file opens a namespace that declares names the program uses (`Json`, `Name`, `Std`, `collectAxioms`): the program
-- opens nothing and names every identifier from the root, so it reads as F2 (review 2026-11-24, compat finding 1: program v1
-- stopped with "Ambiguous term Json"; soundness finding 2: its `open Lean Elab Command in` could resolve a printed name to a
-- `Lean.*` constant that `#print axioms` does not see).
-- expect: {"sources": ["LRAFix.libSorry"], "own": [], "sorryAx": true, "sorry_message": false}
@HEADER@

namespace Other

def Json : Nat := 1

def Name : Nat := 2

def collectAxioms (n : Nat) : Nat := n

end Other

open Other

namespace LRAFix

theorem libSorry : (1 : Nat) = 1 := sorry

-- proof
theorem mainT : (1 : Nat) = 1 ∧ True := ⟨libSorry, trivial⟩
