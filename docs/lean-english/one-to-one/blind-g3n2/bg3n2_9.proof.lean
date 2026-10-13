open ControlStack
open ControlStack.AuthInstances

theorem claim : Claim := by
  refine ⟨Iff.rfl, (fun _ _ => Iff.rfl), ?_⟩
  intro E US UL s ops hUS hUL
  constructor
  · rintro ⟨hgood, hap, hprop⟩
    refine ⟨hgood, ?_, ?_⟩
    · intro a ha
      obtain ⟨hi, hr, _⟩ := hap a ha
      refine ⟨a.reviewer, SC17.Op.approve a.reviewer a.id, hi, ?_, rfl, rfl, hr⟩
      exact fun hu => hUL a.reviewer hu hr
    · intro p hp
      rcases hprop p hp with hi | hi
      · exact ⟨p.author, SC17.Op.propose p.author p.id p.diff, hi, rfl, Or.inl rfl⟩
      · exact ⟨p.author, SC17.Op.amend p.author p.id p.diff, hi, rfl, Or.inr rfl⟩
  · rintro ⟨hgood, hap, hprop⟩
    refine ⟨hgood, ?_, ?_⟩
    · intro a ha
      obtain ⟨c, o, hi, _, ho, hc, hr⟩ := hap a ha
      subst c
      subst o
      exact ⟨hi, hr, fun hu => hUS a.reviewer hu hr⟩
    · intro p hp
      obtain ⟨c, o, hi, hc, ho⟩ := hprop p hp
      subst c
      rcases ho with ho | ho
      · exact Or.inl (ho ▸ hi)
      · exact Or.inr (ho ▸ hi)

theorem witness : Witness := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    simp only [List.mem_singleton] at hc
    subst c
    decide
  · intro c hc
    change c ∈ ([1] : List ℕ) at hc
    simp only [List.mem_singleton] at hc
    subst c
    decide
  · decide
