theorem pointwise : PointwiseClaim := by
  unfold PointwiseClaim
  intro N B S q r Y _ sigma K
  have hd : OrigHyp N B S q r Y sigma K → BackHyp N B S q r Y sigma K := by
    rintro ⟨hB, hr0, hr1, hs, hk0, hk1, hrec⟩
    refine ⟨hB, hr0, hr1, fun g a => (hs g).1 a, fun g => (hs g).2.le, hk0, ?_, hrec⟩
    simpa only [Fintype.sum_prod_type] using hk1
  refine ⟨hd, ?_, Iff.rfl⟩
  intro hb ho
  exact hb (hd ho)

lemma back_shape : FrozenBack ↔ BackSchema := by
  constructor
  · intro hf
    intro N B S q r Y _ sigma K
    rintro ⟨hB, hr0, hr1, hs0, hs1, hk0, hk1, hrec⟩
    exact hf N B S q r Y sigma K hB hr0 hr1 hs0 hs1 hk0 hk1 hrec
  · intro hf
    intro N B S q r Y _ sigma K hB hr0 hr1 hs0 hs1 hk0 hk1 hrec
    exact hf N B S q r Y sigma K ⟨hB, hr0, hr1, hs0, hs1, hk0, hk1, hrec⟩

lemma original_shape : Original ↔ OrigSchema := by
  classical
  constructor
  · intro hf
    intro N B S q r Y _ sigma K
    rintro ⟨hB, hr0, hr1, hs, hk0, hk1, hrec⟩
    exact hf S q B hB r hr0 hr1 K sigma hs hk0 hk1 hrec
  · intro hf
    intro N Y _ S q B hB r hr0 hr1 K sigma hs hk0 hk1 hrec
    exact hf N B S q r Y sigma K ⟨hB, hr0, hr1, hs, hk0, hk1, hrec⟩

theorem back_to_original : FrozenBack → Original := by
  intro hb
  apply original_shape.mpr
  intro N B S q r Y _ sigma K
  exact (pointwise N B S q r Y sigma K).2.1 ((back_shape.mp hb) N B S q r Y sigma K)

theorem claim : Claim := ⟨back_shape, original_shape, pointwise, back_to_original⟩
