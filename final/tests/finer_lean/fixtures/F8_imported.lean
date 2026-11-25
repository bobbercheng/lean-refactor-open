-- F8: the proof uses an IMPORTED constant of the library that rests on sorry (named per environment): the source is that
-- constant itself (the frontier), found by its axioms, not by walking into it.
-- expect: {"sources": ["@IMPORTED@"], "own": [], "local": [], "sorryAx": true, "sorry_message": false}
@HEADER@

namespace LRAFix

-- proof
theorem mainT : True := by
  have := @@IMPORTED@
  trivial
