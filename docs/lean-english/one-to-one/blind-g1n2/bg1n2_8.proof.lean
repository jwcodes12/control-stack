theorem componentwise : ComponentwiseClaim := by
  unfold ComponentwiseClaim
  intros; exact ⟨Iff.rfl, Iff.rfl⟩

lemma back_shape : FrozenBack ↔ BackSchema := by
  constructor
  · intro hf
    intro S q b
    rintro ⟨hq, hb, hS⟩
    exact hf S q b hq hb hS
  · intro hf
    intro S q b hq hb hS
    exact hf S q b ⟨hq, hb, hS⟩

lemma original_shape : Original ↔ OrigSchema := by
  classical
  constructor
  · intro hf
    intro S q b
    rintro ⟨hq, hb, hS⟩
    exact hf S q hq b hb hS
  · intro hf
    intro S q hq b hb hS
    exact hf S q b ⟨hq, hb, hS⟩

theorem pointwise : PointwiseClaim := by
  refine ⟨componentwise, ?_⟩
  intro S q b
  obtain ⟨hh, hc⟩ := componentwise S q b
  exact ⟨fun hb ho => hc.mp (hb (hh.mpr ho)), fun ho hb => hc.mpr (ho (hh.mp hb))⟩

theorem claim : Claim := ⟨back_shape, original_shape, pointwise⟩
