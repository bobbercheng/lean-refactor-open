-- F12: the file declares, in D's namespace, names the program uses (`Name`, `String`, `toString`, `Json`): the program names every
-- identifier from the root, so it still runs and reads as F2 (review 2026-11-24, compat finding 1: program v1 stopped with
-- "Application type mismatch ... Name" and the check failed closed on every proof of the row).
-- expect: {"sources": ["LRAFix.libSorry"], "own": [], "sorryAx": true, "sorry_message": false}
@HEADER@

namespace LRAFix

structure Name where
  x : Nat

def String : Nat := 3

def toString (n : Nat) : Nat := n

def Json : Nat := 4

theorem libSorry : (1 : Nat) = 1 := sorry

-- proof
theorem mainT : (1 : Nat) = 1 ∧ True := ⟨libSorry, trivial⟩
