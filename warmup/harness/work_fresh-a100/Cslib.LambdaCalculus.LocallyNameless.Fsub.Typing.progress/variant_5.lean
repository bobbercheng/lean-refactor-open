lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  generalize eq : [] = Γ at der
  have der' := der
  induction der <;> subst eq
  case app l r ih_l ih_r =>
    obtain val_l | ⟨_, h⟩ := ih_l rfl l
    · obtain val_r | ⟨_, h₂⟩ := ih_r rfl r
      · grind only [→ canonical_form_abs, → Red.abs, val_l.lc]
      · grind [→ Red.appᵣ]
    · grind [→ Red.appₗ]
  case tapp => grind [→ Red.tabs, → canonical_form_tabs]
  case let' => grind only [→ Red.let_bind, → Red.let_body, body_let.mp der'.wf.2.1]
  case case der _ _ ih _ _ =>
    right
    have hb := body_case.mp der'.wf.2.1
    obtain val | ⟨_, h⟩ := ih rfl der
    · grind only [→ canonical_form_sum, → Red.case_inl, → Red.case_inr]
    · exact ⟨_, Red.case h hb.2.1 hb.2.2⟩
  all_goals grind [→ Red.inl, → Red.inr, → wf]
