theorem componentwise : ComponentwiseClaim := by
  unfold ComponentwiseClaim
  intros
  constructor
  · simp only [BackHyp, OrigHyp, not_and_or, not_le, not_lt, and_imp]
  · exact Iff.rfl

lemma back_shape : FrozenBack ↔ BackSchema := by
  constructor
  · intro hf
    intro n a E Ω M Y O _ _ _ _ _ rho K dec c L
    rintro ⟨hE, hr, hd, hk, hc, hL, hdom, hin, hout⟩
    exact hf n a E Ω M Y O rho K dec c L hE hr hd hk hc hL hdom hin hout
  · intro hf
    intro n a E Ω M Y O _ _ _ _ _ rho K dec c L hE hr hd hk hc hL hdom hin hout
    exact hf n a E Ω M Y O rho K dec c L ⟨hE, hr, hd, hk, hc, hL, hdom, hin, hout⟩

lemma original_shape : Original ↔ OrigSchema := by
  classical
  constructor
  · intro hf
    intro n a E Ω M Y O _ _ _ _ _ rho K dec c L
    rintro ⟨hE, hr, hd, hk, hc, hL, hdom, hin, hout⟩
    exact hf n a E hE L hL rho K c dec hr hk hdom hc hin hout hd
  · intro hf
    intro Ω Y O _ _ _ M _ _ n a E hE L hL rho K c dec hr hk hdom hc hin hout hd
    exact hf n a E Ω M Y O rho K dec c L ⟨hE, hr, hd, hk, hc, hL, hdom, hin, hout⟩

theorem pointwise : PointwiseClaim := by
  refine ⟨componentwise, ?_⟩
  intro n a E Ω M Y O _ _ _ _ _ rho K dec c L
  obtain ⟨hh, hc⟩ := componentwise n a E Ω M Y O rho K dec c L
  exact ⟨fun hb ho => hc.mp (hb (hh.mpr ho)), fun ho hb => hc.mpr (ho (hh.mp hb))⟩

theorem claim : Claim := ⟨back_shape, original_shape, pointwise⟩
