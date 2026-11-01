lemma Typing.progress (der : Typing [] t τ) : t.Value ∨ ∃ t', t ⭢βᵛ t' := by
  generalize eq : [] = Γ at der
  have der' := der
  induction der <;> subst eq
  case app => grind [→ canonical_form_abs, → Red.abs, → Red.appᵣ, → Red.appₗ]
  case let' => grind only [→ Red.let_bind, → Red.let_body, body_let.mp der'.wf.2.1]
  case case der _ _ ih _ _ =>
    have hb := body_case.mp der'.wf.2.1
    obtain val | ⟨_, h⟩ := ih rfl der
    grind [→ canonical_form_sum, → Red.case_inl, → Red.case_inr, → Red.case]
  all_goals grind [→ Red.inl, → Red.inr, → Red.tabs, → Red.tapp, → canonical_form_tabs]
