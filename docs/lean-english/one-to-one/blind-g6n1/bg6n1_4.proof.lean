open ControlStack.SC25Content ControlStack.SC25

theorem row_iff (R : Roles) (g : List ARec) (e : Exec) : BackRow R g e ↔ OrigRow R g e := by
  constructor
  · rintro ⟨a, ha, hx⟩
    exact ⟨(e.id, e.content, true, a), hx, rfl, rfl, rfl, ha⟩
  · rintro ⟨⟨i, c, p, a⟩, hx, hi, hc, hp, ha⟩
    dsimp at hi hc hp ha
    subst i; subst c; subst p
    exact ⟨a, ha, hx⟩

theorem claim : Claim := by
  refine ⟨rfl, row_iff, ?_⟩
  intro R h cls ops hinj
  unfold Back Orig
  rw [grun_fst]
  exact forall_congr' fun e => forall_congr' fun _ => row_iff R _ e

theorem witness : Witness := by
  unfold Witness
  refine ⟨fun _ _ _ _ he => he, ?_, ?_⟩ <;> decide
