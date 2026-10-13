theorem componentwise : ComponentwiseClaim := by
  unfold ComponentwiseClaim
  intros; exact ⟨Iff.rfl, Iff.rfl⟩

lemma back_shape : FrozenBack ↔ BackSchema := by
  constructor
  · intro hf
    intro E Ω M V _ _ _ _ rho enc dec
    rintro ⟨hr, he, hd⟩
    exact hf E Ω M V rho enc dec hr he hd
  · intro hf
    intro E Ω M V _ _ _ _ rho enc dec hr he hd
    exact hf E Ω M V rho enc dec ⟨hr, he, hd⟩

lemma original_shape : Original ↔ OrigSchema := by
  classical
  constructor
  · intro hf
    intro E Ω M V _ _ _ _ rho enc dec
    rintro ⟨hr, he, hd⟩
    exact hf V rho enc dec hr he hd
  · intro hf
    intro Ω M _ _ _ E V _ _ rho enc dec hr he hd
    exact hf E Ω M V rho enc dec ⟨hr, he, hd⟩

theorem pointwise : PointwiseClaim := by
  refine ⟨componentwise, ?_⟩
  intro E Ω M V _ _ _ _ rho enc dec
  obtain ⟨hh, hc⟩ := componentwise E Ω M V rho enc dec
  exact ⟨fun hb ho => hc.mp (hb (hh.mpr ho)), fun ho hb => hc.mpr (ho (hh.mp hb))⟩

theorem claim : Claim := ⟨back_shape, original_shape, pointwise⟩
