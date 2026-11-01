lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  generalize eq : [] = Γ at der
  have der' := der
  induction der <;> subst eq
  case app l r ih_l ih_r =>
    right
    rcases ih_l rfl l with val_l | red_l
    · rcases ih_r rfl r with val_r | red_r
      · obtain ⟨_, _, rfl⟩ := l.canonical_form_abs val_l
        exact ⟨_, Red.abs val_l.lc val_r⟩
      · exact ⟨_, Red.appᵣ val_l red_r.choose_spec⟩
    · exact ⟨_, Red.appₗ r.wf.2.1 red_l.choose_spec⟩
  case tapp der sub ih =>
    right
    rcases ih rfl der with val | red
    · obtain ⟨_, _, rfl⟩ := der.canonical_form_tabs val
      exact ⟨_, Red.tabs val.lc sub.wf.2.1.lc⟩
    · exact ⟨_, Red.tapp sub.wf.2.1.lc red.choose_spec⟩
  case let' der _ ih _ =>
    right
    have hb := (body_let.mp der'.wf.2.1).2
    rcases ih rfl der with val | red
    · exact ⟨_, Red.let_body val hb⟩
    · exact ⟨_, Red.let_bind red.choose_spec hb⟩
  case inl der _ ih =>
    exact (ih rfl der).imp Value.inl fun r => ⟨_, Red.inl r.choose_spec⟩
  case inr der _ ih =>
    exact (ih rfl der).imp Value.inr fun r => ⟨_, Red.inr r.choose_spec⟩
  case case der _ _ ih _ _ =>
    right
    have hb := body_case.mp der'.wf.2.1
    rcases ih rfl der with val | red
    · obtain ⟨u, rfl | rfl⟩ := der.canonical_form_sum val
      · cases val with | inl v => exact ⟨_, Red.case_inl v hb.2.1 hb.2.2⟩
      · cases val with | inr v => exact ⟨_, Red.case_inr v hb.2.1 hb.2.2⟩
    · exact ⟨_, Red.case red.choose_spec hb.2.1 hb.2.2⟩
  case abs tabs => left; constructor; all_goals grind [→ wf]
  all_goals grind
