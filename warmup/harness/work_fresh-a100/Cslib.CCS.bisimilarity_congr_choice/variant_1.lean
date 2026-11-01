theorem bisimilarity_congr_choice :
    (p ~[lts (defs := defs)] q) → (choice p r) ~[lts (defs := defs)] (choice q r) :=
  fun hpq => ⟨ChoiceBisim, .choice hpq, by
    rintro s1 s2 (h | h) μ
    · constructor <;> intro s htr <;>
        cases htr with
        | choiceL htr => first | exact h.follow_fst htr |>.imp fun a => And.imp Tr.choiceL ChoiceBisim.bisim | exact h.follow_snd htr |>.imp fun a => And.imp Tr.choiceL ChoiceBisim.bisim
        | choiceR htr => exact ⟨s, .choiceR htr, .bisim .refl⟩
    · constructor <;> intro _ htr
      · exact h.follow_fst htr |>.imp fun a => And.imp_right ChoiceBisim.bisim
      · exact h.follow_snd htr |>.imp fun a => And.imp_right ChoiceBisim.bisim⟩
