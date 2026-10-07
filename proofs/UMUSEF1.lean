open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMSTRATF1

/-! ## (a) false halt -/

theorem usef_split {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ) (φ : Z → ℝ)
    (hM : IsKernel M) (hμ : IsDist μ) (A B : ℝ) :
    ∑ x, μ x * ∑ z, M x z * (φ z * A + (1 - φ z) * B) =
      (1 - flagRate M μ φ) * A + flagRate M μ φ * B := by
  have e : ∀ x, μ x * ∑ z, M x z * (φ z * A + (1 - φ z) * B) =
      A * μ x - (A - B) * (μ x * ∑ z, M x z * (1 - φ z)) := by
    intro x
    have h1 : ∑ z, M x z * (φ z * A + (1 - φ z) * B) =
        A * ∑ z, M x z - (A - B) * ∑ z, M x z * (1 - φ z) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro z _
      ring
    rw [h1, (hM x).2]
    ring
  rw [Finset.sum_congr rfl (fun x _ => e x), Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, hμ.2]
  unfold flagRate
  ring

theorem usef_flag01 {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (μ : X → ℝ)
    (φ : Z → ℝ) (hM : IsKernel M) (hφ : IsRule φ) (hμ : IsDist μ) :
    0 ≤ flagRate M μ φ ∧ flagRate M μ φ ≤ 1 := by
  unfold flagRate
  constructor
  · apply PLDep_UMPROTF1.wsum_nonneg _ _ hμ.1
    intro x
    exact PLDep_UMPROTF1.wsum_nonneg _ _ (hM x).1 (fun z => sub_nonneg.mpr (hφ z).2)
  · apply PLDep_UMPROTF1.wsum_le _ _ _ hμ
    intro x
    exact PLDep_UMPROTF1.wsum_le _ _ _ (hM x) (fun z => sub_le_self 1 (hφ z).1)

theorem usef_halt {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (μ : X → ℝ) (b : ℕ)
    (hM : IsKernel M) (hμ : IsDist μ) (hsupp : ∀ x, μ x ≠ 0 → ¬ Bad x) :
    ∀ n u h, 1 - haltP Bad M φ (fun _ => μ) b n u h =
      survH (flagRate M μ φ) (hardKill b) n u := by
  intro n
  induction n with
  | zero => intro u h; simp [haltP, survH]
  | succ n ih =>
    intro u h
    have ih' : ∀ u h, haltP Bad M φ (fun _ => μ) b n u h =
        1 - survH (flagRate M μ φ) (hardKill b) n u := by
      intro u h
      have := ih u h
      linarith
    have key : haltP Bad M φ (fun _ => μ) b (n + 1) u h =
        ∑ x, μ x * ∑ z, M x z * (φ z * (1 - survH (flagRate M μ φ) (hardKill b) n u) +
          (1 - φ z) * (if u < b then 1 - survH (flagRate M μ φ) (hardKill b) n (u + 1)
            else 1)) := by
      rw [haltP]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : μ x = 0
      · simp [hx]
      · have hb := hsupp x hx
        simp only [hb, if_false, ih']
    rw [key, usef_split M μ φ hM hμ, survH]
    by_cases hu : u < b
    · have hk : hardKill b u = 0 := by unfold hardKill; rw [if_neg (by omega)]
      simp only [hu, if_true, hk]
      ring
    · have hk : hardKill b u = 1 := by unfold hardKill; rw [if_pos (by omega)]
      simp only [hu, if_false, hk]
      ring

/-! ## (b) honest completion -/

theorem usef_bin01 (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    0 ≤ binCDF n s a ∧ binCDF n s a ≤ 1 := by
  have := PLDep_UMSURVF1.survH_prob a (hardKill s) h0 h1 (PLDep_UMPROTF1.hardKill_prob s) n 0
  rw [PLDep_UMSURVF1.claim.2.1 a n s] at this
  exact this

theorem usef_hc {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh b N : ℕ) (φ₀ : Z → ℝ) (μ : X → ℝ)
    (hM : IsKernel M) (hP : IsDist PH) (hμ : IsDist μ) (hsupp : ∀ x, μ x ≠ 0 → ¬ Bad x) :
    honestCompletion Bad M PH κ nh b N φ₀ μ =
      survH (missRate M PH φ₀) κ nh 0 * binCDF N b (flagRate M μ φ₀) := by
  unfold honestCompletion
  rw [usef_halt Bad M φ₀ μ b hM hμ hsupp N 0 [], PLDep_UMPROTF1.surv_eq M PH φ₀ κ nh hM hP,
    PLDep_UMSURVF1.claim.2.1 (flagRate M μ φ₀) N b]
  rfl

/-! ## (c') view-blind pair -/

theorem usef_vb {X Z : Type} [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop)
    [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r h : ℝ)
    (b N : ℕ) (x : X) (hM : IsKernel M) (hP : IsDist PH) (hx : Bad x) (hN : 1 ≤ N) :
    viewBlindRisk Bad M PH κ nh r b N h x =
      survH h κ nh 0 * (h + (if 0 < b then (1 - r) * (1 - h) else 0)) := by
  have hs1 : surv (push M PH) (fun _ => h) κ nh 0 = survH h κ nh 0 := by
    rw [PLDep_UMSURVF1.claim.1 Z (push M PH) (fun _ => h) κ nh 0
      (PLDep_UMPROTF1.push_dist M PH hM hP).2]
    congr 1
    rw [← Finset.sum_mul, (PLDep_UMPROTF1.push_dist M PH hM hP).2, one_mul]
  unfold viewBlindRisk protocolCat
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [Fintype.sum_unique, cat]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, hx, ↓reduceIte]
  rw [hs1]
  congr 1
  by_cases hb : 0 < b
  · simp only [hb, ↓reduceIte]
    rw [← Finset.sum_mul, (hM x).2]
    ring
  · simp only [hb, ↓reduceIte]
    rw [← Finset.sum_mul, (hM x).2]
    ring

/-! ## (d) binomial moments and Cantelli -/

def usefB (n : ℕ) (a : ℝ) (j : ℕ) : ℝ := (n.choose j : ℝ) * a ^ j * (1 - a) ^ (n - j)

theorem usefB_nonneg (n : ℕ) (a : ℝ) (j : ℕ) (h0 : 0 ≤ a) (h1 : a ≤ 1) : 0 ≤ usefB n a j :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 _)) (pow_nonneg (by linarith) _)

theorem usefB_step (n : ℕ) (a : ℝ) (g : ℕ → ℝ) :
    ∑ j ∈ range (n + 1 + 1), usefB (n + 1) a j * g j =
      (1 - a) * ∑ j ∈ range (n + 1), usefB n a j * g j +
        a * ∑ j ∈ range (n + 1), usefB n a j * g (j + 1) := by
  have e : ∀ k, usefB (n + 1) a (k + 1) = a * usefB n a k + (1 - a) * usefB n a (k + 1) := by
    intro k
    unfold usefB
    exact PLDep_UMSURVF1.binTerm_pascal n k a
  have e0 : usefB (n + 1) a 0 = (1 - a) * usefB n a 0 := by
    unfold usefB
    simp only [Nat.choose_zero_right, pow_zero, Nat.sub_zero, Nat.cast_one, one_mul]
    ring
  have hz : usefB n a (n + 1) = 0 := by
    unfold usefB
    simp [Nat.choose_succ_self]
  have e1 : ∑ k ∈ range (n + 1), usefB n a (k + 1) * g (k + 1) =
      ∑ j ∈ range (n + 1), usefB n a j * g j - usefB n a 0 * g 0 := by
    have h1 := Finset.sum_range_succ' (fun j => usefB n a j * g j) (n + 1)
    have h2 := Finset.sum_range_succ (fun j => usefB n a j * g j) (n + 1)
    rw [hz, zero_mul, add_zero] at h2
    linarith
  have e2 : ∑ k ∈ range (n + 1), (a * usefB n a k + (1 - a) * usefB n a (k + 1)) * g (k + 1) =
      a * ∑ k ∈ range (n + 1), usefB n a k * g (k + 1) +
        (1 - a) * ∑ k ∈ range (n + 1), usefB n a (k + 1) * g (k + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [Finset.sum_range_succ', Finset.sum_congr rfl (fun k _ => by rw [e k]), e2, e1, e0]
  ring

theorem usefB_m0 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j = 1 := by
  intro n
  induction n with
  | zero => simp [usefB]
  | succ n ih =>
    have hs := usefB_step n a (fun _ => 1)
    simp only [mul_one] at hs
    rw [hs, ih]
    ring

theorem usefB_m1 (a : ℝ) : ∀ n : ℕ, ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) = n * a := by
  intro n
  induction n with
  | zero => simp [usefB]
  | succ n ih =>
    have hs := usefB_step n a (fun j => (j : ℝ))
    have e : ∑ j ∈ range (n + 1), usefB n a j * ((j + 1 : ℕ) : ℝ) =
        ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) + ∑ j ∈ range (n + 1), usefB n a j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hs, e, ih, usefB_m0]
    push_cast
    ring

theorem usefB_m2 (a : ℝ) : ∀ n : ℕ,
    ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) ^ 2 = n * a * (1 - a) + (n * a) ^ 2 := by
  intro n
  induction n with
  | zero => simp [usefB]
  | succ n ih =>
    have hs := usefB_step n a (fun j => (j : ℝ) ^ 2)
    have e : ∑ j ∈ range (n + 1), usefB n a j * ((j + 1 : ℕ) : ℝ) ^ 2 =
        ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) ^ 2 +
          2 * ∑ j ∈ range (n + 1), usefB n a j * (j : ℝ) + ∑ j ∈ range (n + 1), usefB n a j := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      push_cast
      ring
    rw [hs, e, ih, usefB_m1, usefB_m0]
    push_cast
    ring

theorem usefB_var (a c : ℝ) (n : ℕ) :
    ∑ j ∈ range (n + 1), usefB n a j * ((j : ℝ) - c) ^ 2 = n * a * (1 - a) + (n * a - c) ^ 2 := by
  have e : ∀ j ∈ range (n + 1), usefB n a j * ((j : ℝ) - c) ^ 2 =
      usefB n a j * (j : ℝ) ^ 2 - 2 * c * (usefB n a j * (j : ℝ)) + c ^ 2 * usefB n a j := by
    intro j _
    ring
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, usefB_m2, usefB_m1, usefB_m0]
  ring

theorem usefB_ext (n K : ℕ) (a : ℝ) (g : ℕ → ℝ) (hK : n + 1 ≤ K) :
    ∑ j ∈ range K, usefB n a j * g j = ∑ j ∈ range (n + 1), usefB n a j * g j := by
  symm
  apply Finset.sum_subset (Finset.range_subset_range.mpr hK)
  intro j _ hj
  have hj' : n < j := by
    simp only [Finset.mem_range] at hj
    omega
  simp [usefB, Nat.choose_eq_zero_of_lt hj']

theorem usef_cant_alg (d σ W : ℝ) (hd : 0 < d) (hσ : 0 ≤ σ) (hW : 0 ≤ W)
    (h : ∀ t, 0 ≤ t → (d + t) ^ 2 * W ≤ σ + t ^ 2) : d ^ 2 * W ≤ σ * (1 - W) := by
  have ht : 0 ≤ σ / d := div_nonneg hσ hd.le
  have key := h (σ / d) ht
  have hdt : d * (σ / d) = σ := by field_simp
  have k2 : (d * (d + σ / d)) ^ 2 * W ≤ d ^ 2 * (σ + (σ / d) ^ 2) := by
    have := mul_le_mul_of_nonneg_left key (sq_nonneg d)
    calc (d * (d + σ / d)) ^ 2 * W = d ^ 2 * ((d + σ / d) ^ 2 * W) := by ring
      _ ≤ _ := this
  have e1 : d * (d + σ / d) = d ^ 2 + σ := by rw [mul_add, hdt]; ring
  have e2 : d ^ 2 * (σ + (σ / d) ^ 2) = σ * (d ^ 2 + σ) := by
    have h3 : d ^ 2 * (σ / d) ^ 2 = σ ^ 2 := by rw [← mul_pow, hdt]
    linear_combination h3
  rw [e1, e2] at k2
  have hpos : 0 < d ^ 2 + σ := by positivity
  have k3 : (d ^ 2 + σ) * W ≤ σ := by
    have h4 : (d ^ 2 + σ) * ((d ^ 2 + σ) * W) ≤ (d ^ 2 + σ) * σ := by
      calc (d ^ 2 + σ) * ((d ^ 2 + σ) * W) = (d ^ 2 + σ) ^ 2 * W := by ring
        _ ≤ σ * (d ^ 2 + σ) := k2
        _ = (d ^ 2 + σ) * σ := by ring
    exact le_of_mul_le_mul_left h4 hpos
  have e3 : (d ^ 2 + σ) * W = d ^ 2 * W + σ * W := by ring
  have e4 : σ * (1 - W) = σ - σ * W := by ring
  rw [e4]
  linarith

theorem usef_lower (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    (max 0 ((n : ℝ) * a - s)) ^ 2 * binCDF n s a ≤ n * a * (1 - a) * (1 - binCDF n s a) := by
  obtain ⟨F0, F1⟩ := usef_bin01 n s a h0 h1
  have hσ : 0 ≤ (n : ℝ) * a * (1 - a) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) h0) (by linarith)
  by_cases hd : (n : ℝ) * a - s ≤ 0
  · rw [max_eq_left hd]
    have := mul_nonneg hσ (sub_nonneg.mpr F1)
    simpa using this
  · push_neg at hd
    rw [max_eq_right hd.le]
    apply usef_cant_alg _ _ _ hd hσ F0
    intro t ht
    have hF : binCDF n s a = ∑ j ∈ range (s + 1), usefB n a j := rfl
    rw [hF, Finset.mul_sum]
    calc ∑ j ∈ range (s + 1), ((n : ℝ) * a - s + t) ^ 2 * usefB n a j
        ≤ ∑ j ∈ range (s + 1), usefB n a j * ((j : ℝ) - (n * a + t)) ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hjs : (j : ℝ) ≤ s := by
            have := Finset.mem_range.mp hj
            exact_mod_cast (by omega : j ≤ s)
          have hB := usefB_nonneg n a j h0 h1
          have hA : 0 ≤ (n : ℝ) * a - s + t := by linarith
          have hAB : (n : ℝ) * a - s + t ≤ n * a + t - j := by linarith
          have hp := pow_le_pow_left₀ hA hAB 2
          have e : ((j : ℝ) - (n * a + t)) ^ 2 = ((n : ℝ) * a + t - j) ^ 2 := by ring
          rw [e, mul_comm]
          exact mul_le_mul_of_nonneg_left hp hB
      _ ≤ ∑ j ∈ range (n + s + 1), usefB n a j * ((j : ℝ) - (n * a + t)) ^ 2 := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_subset_range.mpr (by omega))
          intro j _ _
          exact mul_nonneg (usefB_nonneg n a j h0 h1) (sq_nonneg _)
      _ = ∑ j ∈ range (n + 1), usefB n a j * ((j : ℝ) - (n * a + t)) ^ 2 :=
          usefB_ext n (n + s + 1) a _ (by omega)
      _ = n * a * (1 - a) + t ^ 2 := by rw [usefB_var]; ring

theorem usef_upper (n s : ℕ) (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    (max 0 ((s : ℝ) + 1 - n * a)) ^ 2 * (1 - binCDF n s a) ≤ n * a * (1 - a) * binCDF n s a := by
  obtain ⟨F0, F1⟩ := usef_bin01 n s a h0 h1
  have hσ : 0 ≤ (n : ℝ) * a * (1 - a) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg n) h0) (by linarith)
  by_cases hd : (s : ℝ) + 1 - n * a ≤ 0
  · rw [max_eq_left hd]
    have := mul_nonneg hσ F0
    simpa using this
  · push_neg at hd
    rw [max_eq_right hd.le]
    have hres := usef_cant_alg _ _ (1 - binCDF n s a) hd hσ (sub_nonneg.mpr F1) ?_
    · have e : 1 - (1 - binCDF n s a) = binCDF n s a := by ring
      rw [e] at hres
      exact hres
    intro t ht
    have hK : s + 1 ≤ n + s + 2 := by omega
    have hsplit := Finset.sum_range_add_sum_Ico (fun j => usefB n a j) hK
    have htot : ∑ j ∈ range (n + s + 2), usefB n a j = 1 := by
      have := usefB_ext n (n + s + 2) a (fun _ => 1) (by omega)
      simp only [mul_one] at this
      rw [this, usefB_m0]
    have hF : binCDF n s a = ∑ j ∈ range (s + 1), usefB n a j := rfl
    have h1F : 1 - binCDF n s a = ∑ j ∈ Ico (s + 1) (n + s + 2), usefB n a j := by
      rw [hF]
      linarith
    rw [h1F, Finset.mul_sum]
    set c : ℝ := n * a - t with hc
    have hsplit2 := Finset.sum_range_add_sum_Ico
      (fun j => usefB n a j * ((j : ℝ) - c) ^ 2) hK
    have hlow : 0 ≤ ∑ j ∈ range (s + 1), usefB n a j * ((j : ℝ) - c) ^ 2 :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (usefB_nonneg n a j h0 h1) (sq_nonneg _))
    have htot2 : ∑ j ∈ range (n + s + 2), usefB n a j * ((j : ℝ) - c) ^ 2 =
        n * a * (1 - a) + t ^ 2 := by
      rw [usefB_ext n (n + s + 2) a _ (by omega), usefB_var, hc]
      ring
    calc ∑ j ∈ Ico (s + 1) (n + s + 2), ((s : ℝ) + 1 - n * a + t) ^ 2 * usefB n a j
        ≤ ∑ j ∈ Ico (s + 1) (n + s + 2), usefB n a j * ((j : ℝ) - c) ^ 2 := by
          apply Finset.sum_le_sum
          intro j hj
          have hjs : (s : ℝ) + 1 ≤ j := by
            have := (Finset.mem_Ico.mp hj).1
            exact_mod_cast this
          have hB := usefB_nonneg n a j h0 h1
          have hA : 0 ≤ (s : ℝ) + 1 - n * a + t := by linarith
          have hAB : (s : ℝ) + 1 - n * a + t ≤ j - c := by rw [hc]; linarith
          have hp := pow_le_pow_left₀ hA hAB 2
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_left hp hB
      _ ≤ n * a * (1 - a) + t ^ 2 := by linarith

/-! ## (g) zero audit budget -/

theorem usef_cat_r {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r r' : ℝ) :
    ∀ n u h, cat Bad M φ π r 0 n u h = cat Bad M φ π r' 0 n u h := by
  intro n
  induction n with
  | zero => intro u h; simp [cat]
  | succ n ih =>
    intro u h
    simp only [cat, Nat.not_lt_zero, if_false, ih]

/-! ## main theorem -/

theorem claim : PL_UMUSEF1.Claim := by
  unfold PL_UMUSEF1.Claim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- (a)
  · intro X Z _ _ Bad _ M φ₀ μ b hM hφ hμ hsupp
    refine ⟨usef_flag01 M μ φ₀ hM hφ hμ, usef_halt Bad M φ₀ μ b hM hμ hsupp, ?_⟩
    intro N
    have := usef_halt Bad M φ₀ μ b hM hμ hsupp N 0 []
    rw [PLDep_UMSURVF1.claim.2.1] at this
    linarith
  -- (b)
  · intro X Z _ _ Bad _ M PH κ nh ns b N φ₀ μ hM hP hφ hμ hsupp hκ
    have a01 : 0 ≤ missRate M PH φ₀ ∧ missRate M PH φ₀ ≤ 1 :=
      PLDep_UMPROTF1.rate_facts M PH φ₀ hM hP hφ
    have f01 := usef_flag01 M μ φ₀ hM hφ hμ
    have hS := PLDep_UMSURVF1.survH_prob _ κ a01.1 a01.2 hκ nh 0
    have hD := usef_bin01 N b _ f01.1 f01.2
    refine ⟨a01, usef_hc Bad M PH κ nh b N φ₀ μ hM hP hμ hsupp, ?_, ?_⟩
    · rw [usef_hc Bad M PH κ nh b N φ₀ μ hM hP hμ hsupp]
      refine ⟨mul_nonneg hS.1 hD.1, ?_⟩
      have := mul_le_mul_of_nonneg_right hS.2 hD.1
      linarith [hD.2]
    · rw [usef_hc Bad M PH (hardKill ns) nh b N φ₀ μ hM hP hμ hsupp, PLDep_UMSURVF1.claim.2.1]
  -- (b')
  · intro X Z C _ _ Bad _ K c Es m sc b N φ₀ μ hK hφ hμ hsupp
    have hM : IsKernel (fun x => K (c x)) := fun x => hK (c x)
    rw [usef_halt Bad (fun x => K (c x)) φ₀ μ b hM hμ hsupp N 0 [], PLDep_UMSURVF1.claim.2.1]
    congr 1
    unfold stratSurv
    apply Finset.prod_congr rfl
    intro e _
    exact PLDep_UMSTRATF1.surv_eq_bin (K e) φ₀ (hK e).2 m sc
  -- (c')
  · intro X Z _ _ _ Bad _ M PH κ nh r h b N x hM hP hx hN
    exact usef_vb Bad M PH κ nh r h b N x hM hP hx hN
  -- (P)
  · intro X Z _ _ _ Bad _ M PH κ nh r b N φ₀ μ x Xc u hM hP hφ hμ hsupp hκ hr0 hr1 hx hN
    have hvb := usef_vb Bad M PH κ nh r (missRate M PH φ₀) b N x hM hP hx hN
    have hhc := usef_hc Bad M PH κ nh b N φ₀ μ hM hP hμ hsupp
    have a01 : 0 ≤ missRate M PH φ₀ ∧ missRate M PH φ₀ ≤ 1 :=
      PLDep_UMPROTF1.rate_facts M PH φ₀ hM hP hφ
    have hS := PLDep_UMSURVF1.survH_prob _ κ a01.1 a01.2 hκ nh 0
    have f01 := usef_flag01 M μ φ₀ hM hφ hμ
    have hD := usef_bin01 N b _ f01.1 f01.2
    have hq0 : missRate M PH φ₀ ≤
        missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0) := by
      split_ifs
      · have : 0 ≤ (1 - r) * (1 - missRate M PH φ₀) :=
          mul_nonneg (by linarith) (by linarith [a01.2])
        linarith
      · linarith
    have hqn : 0 ≤
        missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0) := by
      linarith [a01.1]
    have hid : binCDF N b (flagRate M μ φ₀) *
        viewBlindRisk Bad M PH κ nh r b N (missRate M PH φ₀) x =
        (missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0)) *
          honestCompletion Bad M PH κ nh b N φ₀ μ := by
      rw [hvb, hhc]
      ring
    refine ⟨hid, ?_⟩
    intro hcap hu
    have hR : viewBlindRisk Bad M PH κ nh r b N (missRate M PH φ₀) x ≤ Xc :=
      hcap Unit (fun _ => 1) (fun _ _ => missRate M PH φ₀)
        (fun _ _ x' => if x' = x then 1 else 0) ⟨fun _ => zero_le_one, by simp⟩
        (fun _ _ => a01) (fun _ _ => ⟨fun x' => by by_cases hh : x' = x <;> simp [hh], by simp⟩)
    have hR0 : 0 ≤ viewBlindRisk Bad M PH κ nh r b N (missRate M PH φ₀) x := by
      rw [hvb]
      exact mul_nonneg hS.1 hqn
    have hX0 : 0 ≤ Xc := le_trans hR0 hR
    have part1 : (missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0)) * u
        ≤ binCDF N b (flagRate M μ φ₀) * Xc := by
      calc (missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0)) * u
          ≤ (missRate M PH φ₀ + (if 0 < b then (1 - r) * (1 - missRate M PH φ₀) else 0)) *
              honestCompletion Bad M PH κ nh b N φ₀ μ := mul_le_mul_of_nonneg_left hu hqn
        _ = binCDF N b (flagRate M μ φ₀) *
              viewBlindRisk Bad M PH κ nh r b N (missRate M PH φ₀) x := hid.symm
        _ ≤ binCDF N b (flagRate M μ φ₀) * Xc := mul_le_mul_of_nonneg_left hR hD.1
    refine ⟨part1, ?_⟩
    by_cases hu0 : u ≤ 0
    · have : missRate M PH φ₀ * u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos a01.1 hu0
      linarith
    · push_neg at hu0
      have h1 := mul_le_mul_of_nonneg_right hq0 hu0.le
      have h2 : binCDF N b (flagRate M μ φ₀) * Xc ≤ Xc := by
        have := mul_le_mul_of_nonneg_right hD.2 hX0
        linarith
      linarith
  -- (d)
  · intro n s α h0 h1
    exact usef_lower n s α h0 h1
  -- (d) ε-form
  · intro n s α ε h0 h1 hε
    have hl := usef_lower n s α h0 h1
    obtain ⟨F0, F1⟩ := usef_bin01 n s α h0 h1
    have hσ : 0 ≤ (n : ℝ) * α * (1 - α) :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) h0) (by linarith)
    have hDn : 0 ≤ (max 0 ((n : ℝ) * α - s)) ^ 2 := sq_nonneg _
    have k1 := mul_le_mul_of_nonneg_left hε hDn
    have k2 : n * α * (1 - α) * (1 - binCDF n s α) ≤ n * α * (1 - α) * ε :=
      mul_le_mul_of_nonneg_left (by linarith) hσ
    linarith
  -- (d')
  · intro n s α h0 h1
    exact usef_upper n s α h0 h1
  -- (f)
  · intro X Z _ _ M PH μ φ₀ η hM hP hμ hφ
    have t := PLDep_UMHSF1.t2 Z η (push M μ) (push M PH) φ₀ hφ
    have e : E (push M μ) φ₀ = 1 - flagRate M μ φ₀ := by
      have h3 := usef_split M μ φ₀ hM hμ 1 0
      simp only [mul_one, mul_zero, add_zero] at h3
      rw [← h3]
      unfold E push
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      ring
    rw [← e]
    exact t
  -- (g)
  · intro X Z Ω _ _ _ Bad _ M PH nh ns N r L ρ φ π hM hP hρ hφ hπ hL hdom
    have e : protocolCat Bad M PH (hardKill ns) nh r 0 N ρ φ π =
        protocolCat Bad M PH (hardKill ns) nh 1 0 N ρ φ π := by
      unfold protocolCat
      apply Finset.sum_congr rfl
      intro ω _
      rw [usef_cat_r Bad M (φ ω) (π ω) r 1 N 0 []]
    rw [e]
    have := PLDep_UMPROTF1.claim.2.2.1 X Z Ω Bad M PH nh ns 0 N 1 L ρ φ π hM hP hρ hφ hπ
      zero_le_one le_rfl hL hdom
    linarith

/-! ## witness -/

theorem wM_k : IsKernel wM := by
  intro x
  constructor
  · intro z
    unfold wM
    split_ifs <;> norm_num
  · cases x <;> simp [wM, Fintype.sum_bool] <;> norm_num

theorem wPH_d : IsDist wPH := by
  constructor
  · intro x
    unfold wPH
    split_ifs <;> norm_num
  · simp [wPH, Fintype.sum_bool]

theorem wμ_d : IsDist wμ := by
  constructor
  · intro x
    unfold wμ
    split_ifs <;> norm_num
  · simp [wμ, Fintype.sum_bool]

theorem wφ_r : IsRule wφ := by
  intro z
  unfold wφ
  split_ifs <;> norm_num

theorem wφI_r : IsRule wφI := by
  intro z
  unfold wφI
  split_ifs <;> norm_num

theorem w_supp : ∀ x, wμ x ≠ 0 → ¬ x = true := by
  intro x hx
  cases x
  · simp
  · simp [wμ] at hx

theorem w_miss : missRate wM wPH wφ = 9 / 40 := by
  simp [missRate, push, wM, wPH, wφ, Fintype.sum_bool]
  norm_num

theorem w_flag : flagRate wM wμ wφ = 13 / 40 := by
  simp [flagRate, wM, wμ, wφ, Fintype.sum_bool]
  norm_num

theorem w_hs : hs 0 (push wM wμ) (push wM wPH) = 1 / 2 := by
  simp [hs, push, wM, wμ, wPH, Fintype.sum_bool]
  norm_num

theorem witness : PL_UMUSEF1.Witness := by
  unfold PL_UMUSEF1.Witness
  have hhalt := usef_halt (fun x => x = true) wM wφ wμ 1 wM_k wμ_d w_supp 2 0 []
  rw [PLDep_UMSURVF1.claim.2.1, w_flag] at hhalt
  have hhc := usef_hc (fun x => x = true) wM wPH (hardKill 0) 2 1 2 wφ wμ wM_k wPH_d wμ_d w_supp
  rw [PLDep_UMSURVF1.claim.2.1, w_flag, w_miss] at hhc
  have hvb1 := usef_vb (fun x => x = true) wM wPH (hardKill 0) 2 (1 / 2) (9 / 40) 1 2 true
    wM_k wPH_d rfl (by norm_num)
  rw [PLDep_UMSURVF1.claim.2.1] at hvb1
  have hvb0 := usef_vb (fun x => x = true) wM wPH (hardKill 0) 2 (1 / 2) (9 / 40) 0 2 true
    wM_k wPH_d rfl (by norm_num)
  rw [PLDep_UMSURVF1.claim.2.1] at hvb0
  refine ⟨wM_k, wPH_d, wμ_d, wφ_r, wφI_r, w_supp, ?_, w_miss, w_flag, ?_, ?_, ?_, by norm_num,
    w_hs, ?_, ?_, by norm_num, ?_, ?_⟩
  · intro x hx z
    subst hx
    cases z <;> simp [push, wM, wPH, Fintype.sum_bool]
  · have hb : binCDF 2 1 (13 / 40 : ℝ) = 1431 / 1600 := by
      simp [binCDF, Finset.sum_range_succ]
      norm_num
    rw [hb] at hhalt
    linarith
  · rw [hhc]
    simp [binCDF, Finset.sum_range_succ]
    norm_num
  · rw [hvb1]
    simp [binCDF, Finset.sum_range_succ]
    norm_num
  · rw [w_hs]
    simp [flagRate, missRate, push, wM, wμ, wPH, wφI, Fintype.sum_bool]
    norm_num
  · rw [hvb0]
    simp [binCDF, Finset.sum_range_succ]
    norm_num
  · simp [binCDF, Finset.sum_range_succ, Nat.choose]
    norm_num
  · simp [binCDF, Finset.sum_range_succ, Nat.choose]
    norm_num
