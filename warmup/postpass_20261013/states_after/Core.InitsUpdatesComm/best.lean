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
  refine ⟨_, rfl, updatedStatesInit (InitStatesLength Hinit)
    (UpdateStatesNotDefMonotone' (InitStatesNotDefined Hinit) Hup)
    (InitStatesNodup Hinit), ?_⟩
  simp only [InitStatesUpdated Hinit, UpdateStatesUpdated Hup, updatedStates,
    updatedStatesComm (kvs := ks.zip vs) (kvs' := ks'.zip vs') $ by
      simp [List.unzip_zip, UpdateStatesLength Hup, InitStatesLength Hinit]
      exact λa Ha Hb =>
        Bool.noConfusion $ InitStatesNotDefined Hinit a Hb ▸
          UpdateStatesDefined Hup a Ha]
  exact updatedStatesUpdate (UpdateStatesLength Hup)
    (updatedStatesDefMonotone $ UpdateStatesDefined' Hup)
