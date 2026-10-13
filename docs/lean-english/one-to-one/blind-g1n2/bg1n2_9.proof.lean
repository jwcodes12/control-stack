theorem componentwise : ComponentwiseClaim := by
  unfold ComponentwiseClaim
  intros
  constructor
  · simp only [BackHyp, OrigHyp, IsDist, forall_and]
    tauto
  · simp only [BackConclusion, OrigConclusion, mul_ite, mul_zero]

lemma back_shape : FrozenBack ↔ BackSchema := by
  constructor
  · intro hf
    intro P _ S q pr plans w c
    rintro ⟨hq, hpr0, hpr1, hc0, hc1, hw⟩
    exact hf P S q pr plans w c hq hpr0 hpr1 hc0 hc1 hw
  · intro hf
    intro P _ S q pr plans w c hq hpr0 hpr1 hc0 hc1 hw
    exact hf P S q pr plans w c ⟨hq, hpr0, hpr1, hc0, hc1, hw⟩

lemma original_shape : Original ↔ OrigSchema := by
  classical
  constructor
  · intro hf
    intro P _ S q pr plans w c
    rintro ⟨hq, hpr0, hpr1, hc, hw0, hw1⟩
    exact hf S q hq c pr hc hpr0 hpr1 w hw0 hw1 plans
  · intro hf
    intro P _ S q hq c pr hc hpr0 hpr1 w hw0 hw1 plans
    exact hf P S q pr plans w c ⟨hq, hpr0, hpr1, hc, hw0, hw1⟩

theorem pointwise : PointwiseClaim := by
  refine ⟨componentwise, ?_⟩
  intro P _ S q pr plans w c
  obtain ⟨hh, hc⟩ := componentwise P S q pr plans w c
  exact ⟨fun hb ho => hc.mp (hb (hh.mpr ho)), fun ho hb => hc.mpr (ho (hh.mp hb))⟩

theorem claim : Claim := ⟨back_shape, original_shape, pointwise⟩
