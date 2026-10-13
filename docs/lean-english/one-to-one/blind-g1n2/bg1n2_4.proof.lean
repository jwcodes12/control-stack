theorem componentwise : ComponentwiseClaim := by
  unfold ComponentwiseClaim
  intro k E Ω Y O _ _ _ rho K dec c L
  refine ⟨Iff.rfl, ?_⟩
  simp only [BackConclusion, OrigConclusion, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  rw [Fin.prod_univ_eq_prod_range]

lemma back_shape : FrozenBack ↔ BackSchema := by
  constructor
  · intro hf
    intro k E Ω Y O _ _ _ rho K dec c L
    rintro ⟨hr, hd, hk, hc, hL, hdom, hmass⟩
    exact hf k E Ω Y O rho K dec c L hr hd hk hc hL hdom hmass
  · intro hf
    intro k E Ω Y O _ _ _ rho K dec c L hr hd hk hc hL hdom hmass
    exact hf k E Ω Y O rho K dec c L ⟨hr, hd, hk, hc, hL, hdom, hmass⟩

lemma original_shape : Original ↔ OrigSchema := by
  classical
  constructor
  · intro hf
    intro k E Ω Y O _ _ _ rho K dec c L
    rintro ⟨hr, hd, hk, hc, hL, hdom, hmass⟩
    exact hf k E rho K c L dec hr hk hdom hc hL hmass hd
  · intro hf
    intro Ω Y O _ _ _ k E rho K c L dec hr hk hdom hc hL hmass hd
    exact hf k E Ω Y O rho K dec c L ⟨hr, hd, hk, hc, hL, hdom, hmass⟩

theorem pointwise : PointwiseClaim := by
  refine ⟨componentwise, ?_⟩
  intro k E Ω Y O _ _ _ rho K dec c L
  obtain ⟨hh, hc⟩ := componentwise k E Ω Y O rho K dec c L
  exact ⟨fun hb ho => hc.mp (hb (hh.mpr ho)), fun ho hb => hc.mpr (ho (hh.mp hb))⟩

theorem claim : Claim := ⟨back_shape, original_shape, pointwise⟩
