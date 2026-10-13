theorem componentwise : ComponentwiseClaim := by
  unfold ComponentwiseClaim
  intros
  constructor
  · simp only [BackHyp, OrigHyp, Fintype.sum_prod_type]
  · exact Iff.rfl

lemma back_shape : FrozenBack ↔ BackSchema := by
  constructor
  · intro hf
    intro Kt Q f m Ω M Y _ _ _ _ rho K dec
    rintro ⟨hr, hd, hk0, hk1⟩
    exact hf Kt Q f m Ω M Y rho K dec hr hd hk0 hk1
  · intro hf
    intro Kt Q f m Ω M Y _ _ _ _ rho K dec hr hd hk0 hk1
    exact hf Kt Q f m Ω M Y rho K dec ⟨hr, hd, hk0, hk1⟩

lemma original_shape : Original ↔ OrigSchema := by
  classical
  constructor
  · intro hf
    intro Kt Q f m Ω M Y _ _ _ _ rho K dec
    rintro ⟨hr, hd, hk0, hk1⟩
    exact hf Kt f Q m rho K dec hr hk0 hk1 hd
  · intro hf
    intro Ω M Y _ _ _ _ Kt f Q m rho K dec hr hk0 hk1 hd
    exact hf Kt Q f m Ω M Y rho K dec ⟨hr, hd, hk0, hk1⟩

theorem pointwise : PointwiseClaim := by
  refine ⟨componentwise, ?_⟩
  intro Kt Q f m Ω M Y _ _ _ _ rho K dec
  obtain ⟨hh, hc⟩ := componentwise Kt Q f m Ω M Y rho K dec
  exact ⟨fun hb ho => hc.mp (hb (hh.mpr ho)), fun ho hb => hc.mpr (ho (hh.mp hb))⟩

theorem claim : Claim := ⟨back_shape, original_shape, pointwise⟩
