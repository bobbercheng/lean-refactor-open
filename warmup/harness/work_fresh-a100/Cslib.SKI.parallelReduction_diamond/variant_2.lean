theorem parallelReduction_diamond : Diamond ParallelReduction := by
  intro a a₁ a₂ h₁ h₂
  have : Std.Refl _ := ⟨ParallelReduction.refl⟩
  induction h₁ generalizing a₂
  · use a₂, h₂, .refl _
  · cases h₂
    · exact ⟨_, .refl _, .red_I ..⟩
    · exact Std.Refl.refl _
    · rename_i hc ha
      cases hc
      exact ⟨_, ha, .red_I ..⟩
  · cases h₂
    · exact ⟨_, .refl _, .red_K ..⟩
    · exact Std.Refl.refl _
    · obtain ⟨a₁', h, rfl⟩ := Ka_irreducible _ _ ‹_›
      use a₁', h, .red_K ..
  · cases h₂
    · exact ⟨_, .refl _, .red_S ..⟩
    · exact Std.Refl.refl _
    · obtain ⟨a', b', h1, h2, rfl⟩ := Sab_irreducible _ _ _ ‹_›
      refine ⟨_, .par (.par h1 ?_) (.par h2 ?_), .red_S ..⟩
      <;> assumption
  · rename_i ha' hb' iha ihb
    cases h₂
    · exact ⟨_, .refl _, .par ha' hb'⟩
    · cases ha'
      exact ⟨_, .red_I .., hb'⟩
    · obtain ⟨a₂', h, rfl⟩ := Ka_irreducible _ _ ha'
      use a₂', .red_K .., h
    · obtain ⟨a'', c', h1, h2, rfl⟩ := Sab_irreducible _ _ _ ha'
      refine ⟨_, .red_S .., .par (.par h1 ?_) (.par h2 ?_)⟩
      <;> assumption
    · rename_i ha'' hb''
      have J := iha ha''
      exact ⟨_, .par J.choose_spec.1 (ihb hb'').choose_spec.1,
        .par J.choose_spec.2 (ihb hb'').choose_spec.2⟩
