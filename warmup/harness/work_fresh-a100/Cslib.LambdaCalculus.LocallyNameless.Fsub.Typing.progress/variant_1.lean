lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  generalize eq : [] = Γ at der
  have der' := der
  induction der <;> subst eq
  case app l r ih_l ih_r =>
    obtain val_l | ⟨_, h⟩ := ih_l rfl l
    · grind only [→ canonical_form_abs, → Red.abs, → Red.appᵣ]
    · grind [→ Red.appₗ]
  case let' => grind only [→ Red.let_bind, → Red.let_body, body_let.mp der'.wf.2.1]
  case case der _ _ ih _ _ =>
    obtain val | ⟨_, h⟩ := ih rfl der
    · grind only [→ canonical_form_sum, → Red.case_inl, → Red.case_inr, body_case.mp der'.wf.2.1]
    · grind [→ Red.case, body_case.mp der'.wf.2.1]
  case var | sub => grind
  all_goals grind only [→ wf, cases Value, → Red.inl, → Red.inr, → Red.tabs, → Red.tapp, → canonical_form_tabs]
