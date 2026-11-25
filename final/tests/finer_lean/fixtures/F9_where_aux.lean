-- F9: the sorry sits in an auxiliary declaration of D (`mainT.go`, from a `where` clause), not in D's own value: still OWN (D is a
-- name prefix of it). (Measured on cslib v4.31.0: a definition's nested proof with a sorry is not abstracted into `mainT.proof_1`,
-- and a `decreasing_by` sorry stays in D's own value, F10; a `match` auxiliary holds no proof.)
-- (In a `module` file the `where` auxiliary is private: the program names it `LRAFix.mainT.go (private)`.)
-- expect: {"sources": ["LRAFix.mainT.go"], "own": ["LRAFix.mainT.go"], "private_in_module": ["LRAFix.mainT.go"], "sorryAx": true}
@HEADER@

namespace LRAFix

theorem libSorry : (1 : Nat) = 1 := sorry

-- proof
theorem mainT : (1 : Nat) = 1 ∧ True := ⟨go, trivial⟩
where go : (1 : Nat) = 1 := sorryAx _ true
