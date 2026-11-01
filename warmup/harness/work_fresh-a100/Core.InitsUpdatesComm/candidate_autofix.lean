theorem InitsUpdatesComm
  {P : PureExpr} {σ σ' σ'' : SemanticStore P}
  {ks ks' : List P.Ident} {vs vs' : List P.Expr} :
  UpdateStates σ ks vs σ' →
  InitStates σ' ks' vs' σ'' →
  ∃ σ₁,
    σ₁ = (updatedStates σ ks' vs') ∧
    InitStates σ ks' vs' σ₁ ∧
    UpdateStates σ₁ ks vs σ'' := by
  intro Hup Hinit
  induction Hup
  · exact ⟨_, InitStatesUpdated Hinit, Hinit, .update_none⟩
  next σ x v σ₀ xs vs σ₁ Hup Hups ih =>
    obtain ⟨Hxval⟩ := id Hup
    obtain ⟨_, rfl, H1', Hup₂⟩ := ih Hinit
    have H1 := updatedStatesInit (InitStatesLength Hinit)
      (UpdateStateNotDefMonotone' (InitStatesNotDefined H1') Hup)
      (InitStatesNodup Hinit)
    refine ⟨_, rfl, H1, .update_some ?_ Hup₂⟩
    simp only [UpdateStateUpdated Hup, updatedStates, ← updatedStateComm' (by
      rw [List.unzip_zip (InitStatesLength Hinit)]
      intro Hin
      cases Hxval.symm.trans (InitStatesNotDefined H1 x Hin))]
    exact updatedStateUpdate (InitStatesSomeMonotone Hxval H1)
