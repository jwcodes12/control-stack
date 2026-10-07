open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 Filter Topology

/-! ## Generic helpers -/

theorem mul_le_mul_of_pos_imp {p x y : ℝ} (hp : 0 ≤ p) (h : 0 < p → x ≤ y) :
    p * x ≤ p * y := by
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul, zero_mul]
  · exact mul_le_mul_of_nonneg_left (h hpos) hp

theorem conv01 {p v w : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) : 0 ≤ p * v + (1 - p) * w ∧ p * v + (1 - p) * w ≤ 1 := by
  have hq : 0 ≤ 1 - p := by linarith
  constructor
  · nlinarith [mul_nonneg hp0 hv0, mul_nonneg hq hw0]
  · nlinarith [mul_le_mul_of_nonneg_left hv1 hp0, mul_le_mul_of_nonneg_left hw1 hq]

theorem wsum01 {Y : Type} [Fintype Y] (w f : Y → ℝ) (hw : IsDist w)
    (hf : ∀ y, 0 ≤ f y ∧ f y ≤ 1) : 0 ≤ ∑ y, w y * f y ∧ ∑ y, w y * f y ≤ 1 :=
  ⟨PLDep_UMPROTF1.wsum_nonneg w f hw.1 (fun y => (hf y).1),
   PLDep_UMPROTF1.wsum_le w f 1 hw (fun y => (hf y).2)⟩

theorem prod3_nonneg {p q c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0 ≤ c) : 0 ≤ p * q * c :=
  mul_nonneg (mul_nonneg hp hq) hc

theorem prod3_le_one {p q c : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : p * q * c ≤ 1 := by
  have h1 : p * q ≤ 1 := mul_le_one₀ hp1 hq0 hq1
  exact mul_le_one₀ h1 hc0 hc1

theorem theta_bounds {η α : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    0 ≤ theta η α ∧ theta η α ≤ 1 := by
  unfold theta
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hη1) hα0]
  · nlinarith [mul_le_mul_of_nonneg_left hα1 (sub_nonneg.2 hη1)]

theorem one_sub_theta (η α : ℝ) : 1 - theta η α = (1 - η) * (1 - α) := by
  unfold theta; ring

/-! ## retry -/

theorem retry_zero (A θ : ℝ) : retry A θ 0 = 0 := rfl

theorem retry_succ (A θ : ℝ) (n : ℕ) :
    retry A θ (n + 1) = A + (1 - A) * (1 - θ) * retry A θ n := rfl

theorem retry_bounds {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ∀ n, 0 ≤ retry A θ n ∧ retry A θ n ≤ 1 := by
  intro n
  induction n with
  | zero => rw [retry_zero]; exact ⟨le_rfl, zero_le_one⟩
  | succ n ih =>
    rw [retry_succ]
    have hc0 : 0 ≤ (1 - A) * (1 - θ) := mul_nonneg (by linarith) (by linarith)
    have hc1 : (1 - A) * (1 - θ) ≤ 1 - A := by nlinarith
    constructor
    · nlinarith [mul_nonneg hc0 ih.1]
    · nlinarith [mul_le_mul_of_nonneg_left ih.2 hc0]

theorem retry_le_succ {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ1 : θ ≤ 1) :
    ∀ n, retry A θ n ≤ retry A θ (n + 1) := by
  intro n
  induction n with
  | zero => rw [retry_succ, retry_zero]; linarith
  | succ n ih =>
    have e1 := retry_succ A θ n
    have e2 := retry_succ A θ (n + 1)
    have hc0 : 0 ≤ (1 - A) * (1 - θ) := mul_nonneg (by linarith) (by linarith)
    have := mul_le_mul_of_nonneg_left ih hc0
    linarith

theorem retry_mono {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ1 : θ ≤ 1) {m n : ℕ}
    (hmn : m ≤ n) : retry A θ m ≤ retry A θ n :=
  monotone_nat_of_le_succ (retry_le_succ hA0 hA1 hθ1) hmn

theorem retry_closed (A θ : ℝ) :
    ∀ n, (θ + A * (1 - θ)) * retry A θ n = A * (1 - ((1 - A) * (1 - θ)) ^ n) := by
  intro n
  induction n with
  | zero => simp [retry]
  | succ n ih =>
    rw [retry_succ, pow_succ]
    linear_combination ((1 - A) * (1 - θ)) * ih

theorem retry_le_ratio (A θ : ℝ) (n : ℕ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hD : 0 < θ + A * (1 - θ)) : retry A θ n ≤ A / (θ + A * (1 - θ)) := by
  rw [le_div_iff₀ hD]
  have h := retry_closed A θ n
  have hc : 0 ≤ ((1 - A) * (1 - θ)) ^ n := pow_nonneg (mul_nonneg (by linarith) (by linarith)) n
  nlinarith [mul_nonneg hA0 hc]

theorem retry_limit (A θ : ℝ) (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hD : 0 < θ + A * (1 - θ)) :
    Tendsto (fun n : ℕ => retry A θ n) atTop (𝓝 (A / (θ + A * (1 - θ)))) := by
  have hc0 : 0 ≤ (1 - A) * (1 - θ) := mul_nonneg (by linarith) (by linarith)
  have hc1 : (1 - A) * (1 - θ) < 1 := by nlinarith
  have e : ∀ n : ℕ, retry A θ n =
      A / (θ + A * (1 - θ)) - A / (θ + A * (1 - θ)) * ((1 - A) * (1 - θ)) ^ n := by
    intro n
    have h := retry_closed A θ n
    rw [div_mul_eq_mul_div, div_sub_div_same, eq_div_iff hD.ne']
    linear_combination h
  have ht := tendsto_pow_atTop_nhds_zero_of_lt_one hc0 hc1
  have hl : Tendsto (fun n : ℕ => A / (θ + A * (1 - θ)) -
      A / (θ + A * (1 - θ)) * ((1 - A) * (1 - θ)) ^ n) atTop
      (𝓝 (A / (θ + A * (1 - θ)) - A / (θ + A * (1 - θ)) * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul ht)
  rw [mul_zero, sub_zero] at hl
  exact hl.congr (fun n => (e n).symm)

theorem theta_retry_le {A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (n : ℕ) : θ * retry A θ n ≤ A := by
  have h := retry_closed A θ n
  have hR := (retry_bounds hA0 hA1 hθ0 hθ1 n).1
  have hc : 0 ≤ ((1 - A) * (1 - θ)) ^ n := pow_nonneg (mul_nonneg (by linarith) (by linarith)) n
  nlinarith [mul_nonneg (mul_nonneg hA0 (sub_nonneg.2 hθ1)) hR, mul_nonneg hA0 hc]

/-! ## finiteCap -/

theorem fc_zero (r A θ : ℝ) (b u : ℕ) : finiteCap r A θ b 0 u = 0 := by
  simp [finiteCap]

theorem fc_ge (r A θ : ℝ) {b u : ℕ} (n : ℕ) (hbu : b ≤ u) :
    finiteCap r A θ b n u = retry A θ n := by
  unfold finiteCap
  split_ifs with h0 h1
  · subst h0; rfl
  · omega
  · rfl

theorem fc_lt (r A θ : ℝ) {b u : ℕ} (n : ℕ) (hu : u < b) :
    finiteCap r A θ b (n + 1) u = max (1 - r + r * A) (retry A θ (n + 1 - (b - u))) := by
  unfold finiteCap
  rw [if_neg (Nat.succ_ne_zero n), if_pos hu]

theorem fc_le_succ {r A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (b n u : ℕ) : finiteCap r A θ b n u ≤ finiteCap r A θ b (n + 1) u := by
  by_cases hu : u < b
  · rw [fc_lt r A θ n hu]
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0
      rw [fc_zero]
      exact le_trans (retry_bounds hA0 hA1 hθ0 hθ1 _).1 (le_max_right _ _)
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [fc_lt r A θ m hu]
      exact max_le_max le_rfl (retry_mono hA0 hA1 hθ1 (by omega))
  · rw [fc_ge r A θ n (by omega), fc_ge r A θ (n + 1) (by omega)]
    exact retry_le_succ hA0 hA1 hθ1 n

theorem fc_step {r A θ : ℝ} (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {b u : ℕ} (n : ℕ) (hu : u < b) :
    finiteCap r A θ b n (u + 1) ≤ finiteCap r A θ b (n + 1) u := by
  rw [fc_lt r A θ n hu]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    rw [fc_zero]
    exact le_trans (retry_bounds hA0 hA1 hθ0 hθ1 _).1 (le_max_right _ _)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    by_cases hu1 : u + 1 < b
    · rw [fc_lt r A θ m hu1]
      have e : m + 1 - (b - (u + 1)) = m + 1 + 1 - (b - u) := by omega
      rw [e]
    · rw [fc_ge r A θ (m + 1) (by omega)]
      have e : m + 1 + 1 - (b - u) = m + 1 := by omega
      rw [e]
      exact le_max_right _ _

section General
variable {X Z : Type} [Fintype X] [Fintype Z]

/-! ## (a) -/

theorem catV_eta_one (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ)
    (π : Hist X Z → X → ℝ) (r : ℝ) (a : Service X Z) (b : ℕ) :
    ∀ n u h, catV Bad M φ π r 1 a b n u h = cat Bad M φ π r b n u h := by
  intro n
  induction n with
  | zero => intro u h; simp [catV, cat]
  | succ n ih =>
    intro u h
    rw [catV, cat]
    simp only [ih, sub_self, zero_mul]

theorem catV_bounds (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ)
    (π : Hist X Z → X → ℝ) (r η : ℝ) (a : Service X Z) (b : ℕ)
    (hc : Core M φ π r η) (ha : IsService a) :
    ∀ n u h, 0 ≤ catV Bad M φ π r η a b n u h ∧ catV Bad M φ π r η a b n u h ≤ 1 := by
  obtain ⟨hM, hφ, hπ, hr0, hr1, hη0, hη1⟩ := hc
  intro n
  induction n with
  | zero => intro u h; simp [catV]
  | succ n ih =>
    intro u h
    rw [catV]
    apply wsum01 _ _ (hπ h)
    intro x
    apply wsum01 _ _ (hM x)
    intro z
    have ha0 := (ha h x z).1
    have ha1 := (ha h x z).2
    apply conv01 (hφ z).1 (hφ z).2
    · split_ifs
      · exact zero_le_one
      · exact (ih _ _).1
    · split_ifs
      · exact le_rfl
      · exact (ih _ _).2
    · split_ifs <;> first
        | linarith
        | exact (ih _ _).1
        | exact prod3_nonneg (by linarith) (by linarith) (ih _ _).1
    · split_ifs <;> first
        | linarith
        | exact (ih _ _).2
        | exact prod3_le_one (by linarith) (by linarith) (by linarith) (by linarith)
            (ih _ _).1 (ih _ _).2

/-! ## (b) finite cap -/

theorem catD_cap (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ)
    (π : Hist X Z → X → ℝ) (r η α A : ℝ) (b : ℕ) (hc : Core M φ π r η)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hbad : ∀ x, Bad x → E (M x) φ ≤ A) :
    ∀ n u h, catD Bad M φ π r η α b n u h ≤ finiteCap r A (theta η α) b n u := by
  obtain ⟨hM, hφ, hπ, hr0, hr1, hη0, hη1⟩ := hc
  obtain ⟨hθ0, hθ1⟩ := theta_bounds hη0 hη1 hα0 hα1
  have h1θ := one_sub_theta η α
  intro n
  induction n with
  | zero => intro u h; simp [catD, catV, finiteCap]
  | succ n ih =>
    intro u h
    unfold catD at ih ⊢
    rw [catV]
    by_cases hu : u < b
    · have hW := fc_lt r A (theta η α) n hu
      rw [hW]
      have hK : 1 - r + r * A ≤
          max (1 - r + r * A) (retry A (theta η α) (n + 1 - (b - u))) := le_max_left _ _
      apply PLDep_UMPROTF1.wsum_le _ _ _ (hπ h)
      intro x
      by_cases hx : Bad x
      · simp only [hx, hu, ↓reduceIte]
        have ha := hbad x hx
        unfold E at ha
        have e : ∀ z, M x z * (φ z * 1 + (1 - φ z) * (1 - r)) =
            (1 - r) * M x z + r * (M x z * φ z) := by intro z; ring
        rw [Finset.sum_congr rfl (fun z _ => e z), Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, (hM x).2]
        nlinarith [mul_le_mul_of_nonneg_left ha hr0]
      · simp only [hx, hu, ↓reduceIte]
        apply PLDep_UMPROTF1.wsum_le _ _ _ (hM x)
        intro z
        have c1 := le_trans (ih u (h ++ [(x, z, true)])) (fc_le_succ hA0 hA1 hθ0 hθ1 b n u)
        have c2 := le_trans (ih (u + 1) (h ++ [(x, z, false)])) (fc_step hA0 hA1 hθ0 hθ1 n hu)
        rw [hW] at c1 c2
        have p1 := (hφ z).1
        have p2 : 0 ≤ 1 - φ z := by linarith [(hφ z).2]
        nlinarith [mul_le_mul_of_nonneg_left c1 p1, mul_le_mul_of_nonneg_left c2 p2]
    · have hbu : b ≤ u := not_lt.mp hu
      rw [fc_ge r A _ (n + 1) hbu]
      have ihR : ∀ h', catV Bad M φ π r η (fun _ _ _ => α) b n u h' ≤ retry A (theta η α) n :=
        fun h' => (ih u h').trans (fc_ge r A _ n hbu).le
      have hR := retry_bounds hA0 hA1 hθ0 hθ1 n
      have hRs := retry_le_succ hA0 hA1 hθ1 n
      have hc0 : 0 ≤ 1 - theta η α := by linarith
      apply PLDep_UMPROTF1.wsum_le _ _ _ (hπ h)
      intro x
      by_cases hx : Bad x
      · simp only [hx, hu, ↓reduceIte]
        rw [← h1θ]
        have ha := hbad x hx
        unfold E at ha
        have hcR1 : (1 - theta η α) * retry A (theta η α) n ≤ 1 := by
          nlinarith [mul_le_mul_of_nonneg_left hR.2 hc0]
        calc _ ≤ ∑ z, ((M x z * φ z) * (1 - (1 - theta η α) * retry A (theta η α) n) +
              (1 - theta η α) * retry A (theta η α) n * M x z) := by
              apply Finset.sum_le_sum
              intro z _
              have hz := ihR (h ++ [(x, z, false)])
              have := mul_le_mul_of_nonneg_left hz
                (mul_nonneg ((hM x).1 z) (mul_nonneg (sub_nonneg.2 (hφ z).2) hc0))
              nlinarith
          _ = (∑ z, M x z * φ z) * (1 - (1 - theta η α) * retry A (theta η α) n) +
              (1 - theta η α) * retry A (theta η α) n := by
              rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, (hM x).2, mul_one]
          _ ≤ A * (1 - (1 - theta η α) * retry A (theta η α) n) +
              (1 - theta η α) * retry A (theta η α) n := by
              have : 0 ≤ 1 - (1 - theta η α) * retry A (theta η α) n := by linarith
              nlinarith [mul_le_mul_of_nonneg_right ha this]
          _ = retry A (theta η α) (n + 1) := by rw [retry_succ]; ring
      · simp only [hx, hu, ↓reduceIte, mul_one]
        apply PLDep_UMPROTF1.wsum_le _ _ _ (hM x)
        intro z
        have c1 := ihR (h ++ [(x, z, true)])
        have c2 := ihR (h ++ [(x, z, false)])
        have p1 := (hφ z).1
        have p2 : 0 ≤ 1 - φ z := by linarith [(hφ z).2]
        have q2 := mul_le_mul_of_nonneg_left c2 (mul_nonneg p2 (sub_nonneg.2 hη1))
        have q1 := mul_le_mul_of_nonneg_left c1 p1
        nlinarith [mul_nonneg (mul_nonneg p2 hη0) hR.1]

/-! ## floor bridge -/

theorem bridge (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ)
    (π : Hist X Z → X → ℝ) (r η α : ℝ) (a : Service X Z) (b n0 u0 : ℕ) (h0 : Hist X Z)
    (hc : Core M φ π r η) (ha : IsService a) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hfl : UniformFloor Bad M φ π η a b n0 u0 h0 α) :
    ∀ n u h, Reach Bad M φ π η a b n0 u0 h0 n u h →
      catV Bad M φ π r η a b n u h ≤ catD Bad M φ π r η α b n u h := by
  have hDnn : ∀ n u h, 0 ≤ catD Bad M φ π r η α b n u h := fun n u h =>
    (catV_bounds Bad M φ π r η (fun _ _ _ => α) b hc (fun _ _ _ => ⟨hα0, hα1⟩) n u h).1
  obtain ⟨hM, hφ, hπ, hr0, hr1, hη0, hη1⟩ := hc
  intro n
  induction n with
  | zero => intro u h _; simp [catD, catV]
  | succ n ih =>
    intro u h hR
    have hD : ∀ u' h', 0 ≤ catD Bad M φ π r η α b n u' h' := fun u' h' => hDnn n u' h'
    unfold catD at ih hD ⊢
    rw [catV, catV]
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_pos_imp ((hπ h).1 x)
    intro hπx
    apply Finset.sum_le_sum
    intro z _
    apply mul_le_mul_of_pos_imp ((hM x).1 z)
    intro hMz
    have hφ1 : 0 ≤ 1 - φ z := by linarith [(hφ z).2]
    have hη' : 0 ≤ 1 - η := by linarith
    apply add_le_add
    · apply mul_le_mul_of_pos_imp (hφ z).1
      intro hφz
      by_cases hx : Bad x
      · simp only [hx, ↓reduceIte, le_refl]
      · simp only [hx, ↓reduceIte]
        exact ih u _ (Reach.pass hR hπx hMz hx hφz)
    · apply mul_le_mul_of_pos_imp hφ1
      intro h1φ
      by_cases hu : u < b
      · by_cases hx : Bad x
        · simp only [hx, hu, ↓reduceIte, le_refl]
        · simp only [hx, hu, ↓reduceIte]
          exact ih (u + 1) _ (Reach.audit hR hπx hMz hx h1φ hu)
      · have hbu : b ≤ u := not_lt.mp hu
        have hDz := hD u (h ++ [(x, z, false)])
        by_cases hpos : 0 < (1 - η) * (if Bad x then 1 - a h x z else 1)
        · have hR' := Reach.defer hR hπx hMz h1φ hbu hpos
          have ihz := ih u _ hR'
          by_cases hx : Bad x
          · simp only [hx, hu, ↓reduceIte] at hpos ⊢
            have h1η : 0 < 1 - η := by
              rcases hη'.eq_or_lt with he | he
              · rw [← he, zero_mul] at hpos; exact absurd hpos (lt_irrefl 0)
              · exact he
            have hfa := hfl n u h x z hR hbu hx hπx hMz h1φ h1η
            have hq : 0 ≤ (1 - η) * (1 - a h x z) :=
              mul_nonneg hη' (by linarith [(ha h x z).2])
            have s1 := mul_le_mul_of_nonneg_left ihz hq
            have s2 : (1 - η) * (1 - a h x z) ≤ (1 - η) * (1 - α) :=
              mul_le_mul_of_nonneg_left (by linarith) hη'
            have s3 := mul_le_mul_of_nonneg_right s2 hDz
            exact le_trans s1 s3
          · simp only [hx, hu, ↓reduceIte, mul_one] at hpos ⊢
            exact mul_le_mul_of_nonneg_left ihz hη'
        · have hz0 : (1 - η) * (if Bad x then 1 - a h x z else 1) = 0 := by
            apply le_antisymm (not_lt.mp hpos)
            split_ifs
            · exact mul_nonneg hη' (by linarith [(ha h x z).2])
            · linarith
          simp only [hu, ↓reduceIte]
          rw [hz0, zero_mul]
          apply mul_nonneg _ hDz
          split_ifs
          · exact mul_nonneg hη' (by linarith)
          · linarith

/-! ## (c) attainment -/

theorem attain [DecidableEq X] (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ)
    (r η α A : ℝ) (b u : ℕ) (x : X) (hM : IsKernel M) (hx : Bad x) (hbu : b ≤ u) :
    ∀ n (h : Hist X Z), catD Bad M (fun _ => A) (fun _ x' => if x' = x then 1 else 0)
        r η α b n u h = retry A (theta η α) n := by
  have hu : ¬ u < b := not_lt.mpr hbu
  intro n
  induction n with
  | zero => intro h; simp [catD, catV, retry]
  | succ n ih =>
    intro h
    unfold catD at ih ⊢
    rw [catV]
    simp only [ih, hu, ↓reduceIte, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, hx, mul_one]
    rw [← Finset.sum_mul, (hM x).2, one_mul, retry_succ, theta]
    ring

end General

/-! ## (d) certificate -/

theorem seed_bound {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η α L : ℝ) (a : Service X Z)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (hPH : IsDist PH) (hc : Core M φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (ha : IsService a) (hfl : UniformFloor Bad M φ π η a b N 0 [] α)
    (hdom : ∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      surv (push M PH) φ (hardKill ns) nh 0 * catV Bad M φ π r η a b N 0 [] ≤
        survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) (theta η α) b N 0 := by
  have hcore := hc
  obtain ⟨hM, hφ, hπ, hr0, hr1, hη0, hη1⟩ := hc
  obtain ⟨h0, h1⟩ := PLDep_UMPROTF1.rate_facts M PH φ hM hPH hφ
  refine ⟨∑ z, push M PH z * φ z, h0, h1, ?_⟩
  rw [PLDep_UMPROTF1.surv_eq M PH φ (hardKill ns) nh hM hPH]
  have hsp := PLDep_UMSURVF1.survH_prob _ (hardKill ns) h0 h1
    (PLDep_UMPROTF1.hardKill_prob ns) nh 0
  have hA0 : 0 ≤ min 1 (L * ∑ z, push M PH z * φ z) := le_min zero_le_one (mul_nonneg hL h0)
  have hA1 : min 1 (L * ∑ z, push M PH z * φ z) ≤ 1 := min_le_left _ _
  have hbad : ∀ x, Bad x → E (M x) φ ≤ min 1 (L * ∑ z, push M PH z * φ z) := fun x hx =>
    le_min (PLDep_UMPROTF1.E_le_one M φ hM hφ x) (PLDep_UMPROTF1.E_dom M PH φ hφ L x (hdom x hx))
  have hbr := bridge Bad M φ π r η α a b N 0 [] hcore ha hα0 hα1 hfl N 0 [] Reach.start
  have hcap := catD_cap Bad M φ π r η α _ b hcore hα0 hα1 hA0 hA1 hbad N 0 []
  exact mul_le_mul_of_nonneg_left (hbr.trans hcap) hsp.1

theorem cert {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop)
    [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (nh ns b N : ℕ) (r η α L U : ℝ)
    (a : Ω → Service X Z) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ)
    (hpc : PairCore M PH ρ φ π r η) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hL : 0 ≤ L)
    (hfl : ProtocolFloor Bad M φ π η a b N α)
    (hdom : ∀ x, Bad x → ∀ z, M x z ≤ L * push M PH z)
    (hU : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) (theta η α) b N 0 ≤ U) :
    protocolCatV Bad M PH (hardKill ns) nh r η a b N ρ φ π ≤ U := by
  obtain ⟨hPH, hρ, hcore⟩ := hpc
  unfold protocolCatV
  simp_rw [mul_assoc]
  apply PLDep_UMPROTF1.wsum_le _ _ _ hρ
  intro ω
  obtain ⟨t, ht0, ht1, hle⟩ := seed_bound Bad M PH nh ns b N r η α L (a ω) (φ ω) (π ω) hPH
    (hcore ω) hα0 hα1 hL (hfl ω).1 (hfl ω).2 hdom
  exact hle.trans (hU t ht0 ht1)

theorem coarse_bound (r θ L t : ℝ) (b N nh ns : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hL : 0 ≤ L)
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    survH t (hardKill ns) nh 0 * finiteCap r (min 1 (L * t)) θ b N 0 ≤
      max (if 0 < b then (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) else 0)
        (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) / θ) := by
  have hB0 : 0 ≤ ((ns : ℝ) + 1) / ((nh : ℝ) + 1) := by positivity
  have hsp := PLDep_UMSURVF1.survH_prob t (hardKill ns) ht0 ht1
    (PLDep_UMPROTF1.hardKill_prob ns) nh 0
  have hfm : t * survH t (hardKill ns) nh 0 ≤ ((ns : ℝ) + 1) / ((nh : ℝ) + 1) := by
    rw [PLDep_UMSURVF1.survH_hard t ns nh 0 (Nat.zero_le _), Nat.sub_zero]
    exact PLDep_UMSURVF1.first_moment' nh ns t ht0 ht1
  have hA0 : 0 ≤ min 1 (L * t) := le_min zero_le_one (mul_nonneg hL ht0)
  have hA1 : min 1 (L * t) ≤ 1 := min_le_left _ _
  have hAL : min 1 (L * t) ≤ L * t := min_le_right _ _
  have hH0 : 0 ≤ L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) / θ :=
    div_nonneg (mul_nonneg hL hB0) hθ0.le
  have hRet : ∀ m, survH t (hardKill ns) nh 0 * retry (min 1 (L * t)) θ m ≤
      L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) / θ := by
    intro m
    rw [le_div_iff₀ hθ0]
    have h1 := theta_retry_le hA0 hA1 hθ0.le hθ1 m
    have h2 := mul_le_mul_of_nonneg_left h1 hsp.1
    have h3 := mul_le_mul_of_nonneg_left hAL hsp.1
    have h4 := mul_le_mul_of_nonneg_left hfm hL
    nlinarith
  have hK := PLDep_UMPROTF1.final_dom (survH t (hardKill ns) nh 0) t L r (min 1 (L * t))
    (((ns : ℝ) + 1) / ((nh : ℝ) + 1)) hsp.1 hsp.2 hr0 hr1 hL hAL (by linarith [hfm])
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    rw [fc_zero, mul_zero]
    exact le_trans hH0 (le_max_right _ _)
  · by_cases hb : 0 < b
    · obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
      rw [fc_lt r _ θ m hb, mul_max_of_nonneg _ _ hsp.1]
      simp only [hb, ↓reduceIte]
      exact max_le_max hK (hRet _)
    · rw [fc_ge r _ θ N (by omega)]
      exact le_trans (hRet N) (le_max_right _ _)

/-! ## (e) no-go -/

theorem cnt_append (h : Hist Bool Bool) (x z c : Bool) :
    ((h ++ [(x, z, c)]).filter (fun e => e.2.2 = false)).length =
      (h.filter (fun e => e.2.2 = false)).length + (if c = false then 1 else 0) := by
  cases c <;> simp [List.filter_append]

theorem attack_phase (r t : ℝ) (b : ℕ) :
    ∀ n (u : ℕ) (h : Hist Bool Bool), b ≤ u → b ≤ (h.filter (fun e => e.2.2 = false)).length →
      catV (X := Bool) (Z := Bool) (fun x => x = true) (fun x z => if z = x then 1 else 0)
        (fun z => if z = true then t else 0) (burnThenAttack b) r 0 (fun _ _ _ => 0) b n u h
        = 1 - (1 - t) ^ n := by
  intro n
  induction n with
  | zero => intro u h _ _; simp [catV]
  | succ n ih =>
    intro u h hbu hc
    have hu : ¬ u < b := not_lt.mpr hbu
    have hlt : ¬ (h.filter (fun e => e.2.2 = false)).length < b := not_lt.mpr hc
    have hc' : b ≤ ((h ++ [(true, true, false)]).filter (fun e => e.2.2 = false)).length := by
      rw [cnt_append, if_pos rfl]; omega
    have key := ih u (h ++ [(true, true, false)]) hbu hc'
    have hlt2 : ¬ (List.filter (fun e => !e.2.2) h).length < b := by simpa using hlt
    rw [catV]
    simp [burnThenAttack, hlt2, hu, key]
    ring

theorem burn_phase (r t : ℝ) (b : ℕ) :
    ∀ n k (u : ℕ) (h : Hist Bool Bool), u = (h.filter (fun e => e.2.2 = false)).length →
      u + k = b →
      catV (X := Bool) (Z := Bool) (fun x => x = true) (fun x z => if z = x then 1 else 0)
        (fun z => if z = true then t else 0) (burnThenAttack b) r 0 (fun _ _ _ => 0) b n u h
        = 1 - (1 - t) ^ (n - k) := by
  intro n
  induction n with
  | zero => intro k u h _ _; simp [catV]
  | succ n ih =>
    intro k u h hu hk
    rcases k with _ | k
    · rw [attack_phase r t b (n + 1) u h (by omega) (by omega), Nat.sub_zero]
    · have hlt : u < b := by omega
      have hlt' : (h.filter (fun e => e.2.2 = false)).length < b := by omega
      have hc' : u + 1 = ((h ++ [(false, false, false)]).filter (fun e => e.2.2 = false)).length := by
        rw [cnt_append]; simp [hu]
      have key := ih k (u + 1) (h ++ [(false, false, false)]) hc' (by omega)
      have hlt2 : (List.filter (fun e => !e.2.2) h).length < b := by simpa using hlt'
      rw [catV]
      simp [burnThenAttack, hlt, hlt2, key]

theorem nogo_eq (PH : Bool → ℝ) (nh ns b N : ℕ) (r t : ℝ) (hPH : IsDist PH) :
    protocolCatD (X := Bool) (Z := Bool) (Ω := Unit)
        (fun x => x = true) (fun x z => if z = x then 1 else 0)
        PH (hardKill ns) nh r 0 0 b N (fun _ => 1)
        (fun _ z => if z = true then t else 0) (fun _ => burnThenAttack b) =
      binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b)) := by
  unfold protocolCatD protocolCatV
  rw [Fintype.sum_unique]
  dsimp only
  rw [one_mul, PLDep_UMPROTF1.surv_eq _ PH _ _ nh PLDep_UMHSF1.idKernel hPH]
  have hrate : ∑ z, push (fun x z : Bool => if z = x then (1 : ℝ) else 0) PH z *
      (if z = true then t else 0) = PH true * t := by
    simp [push]
  rw [hrate, PLDep_UMSURVF1.survH_hard _ ns nh 0 (Nat.zero_le _), Nat.sub_zero,
    burn_phase r t b N b 0 [] (by simp) (by simp)]

theorem nogo_lb (PH : Bool → ℝ) (nh ns b N : ℕ) (t : ℝ) (hPH : IsDist PH) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    (1 - t) ^ nh * (1 - (1 - t) ^ (N - b)) ≤
      binCDF nh ns (PH true * t) * (1 - (1 - t) ^ (N - b)) := by
  have hP1 : PH true ≤ 1 := by
    have := hPH.2
    rw [Fintype.sum_bool] at this
    linarith [hPH.1 false]
  have hP0 := hPH.1 true
  have hs0 : 0 ≤ PH true * t := mul_nonneg hP0 ht0
  have hs1 : PH true * t ≤ t := by nlinarith
  have hfac : 0 ≤ 1 - (1 - t) ^ (N - b) := by
    have := pow_le_one₀ (n := N - b) (by linarith : (0 : ℝ) ≤ 1 - t) (by linarith : 1 - t ≤ 1)
    linarith
  apply mul_le_mul_of_nonneg_right _ hfac
  calc (1 - t) ^ nh ≤ (1 - PH true * t) ^ nh := pow_le_pow_left₀ (by linarith) (by linarith) nh
    _ = (fun j => (nh.choose j : ℝ) * (PH true * t) ^ j * (1 - PH true * t) ^ (nh - j)) 0 := by
        simp
    _ ≤ binCDF nh ns (PH true * t) := by
        unfold binCDF
        apply Finset.single_le_sum
          (f := fun j => (nh.choose j : ℝ) * (PH true * t) ^ j * (1 - PH true * t) ^ (nh - j))
        · intro j _
          exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs0 _))
            (pow_nonneg (by linarith) _)
        · simp

theorem limit_e' (nh : ℕ) : Tendsto
    (fun K : ℕ => (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ nh *
      (1 - (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ K)) atTop (𝓝 1) := by
  have hsq : Tendsto (fun K : ℕ => Real.sqrt ((K : ℝ) + 1)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun K : ℕ => 1 / Real.sqrt ((K : ℝ) + 1)) atTop (𝓝 0) := by
    exact (tendsto_inv_atTop_zero.comp hsq).congr
      (fun K => by simp only [Function.comp_apply, one_div])
  have h1 : Tendsto (fun K : ℕ => (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ nh) atTop (𝓝 1) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hs).pow nh
  have hKs : Tendsto (fun K : ℕ => (K : ℝ) * (1 / Real.sqrt ((K : ℝ) + 1))) atTop atTop := by
    have e : ∀ K : ℕ, (K : ℝ) * (1 / Real.sqrt ((K : ℝ) + 1)) =
        Real.sqrt ((K : ℝ) + 1) + (-(1 / Real.sqrt ((K : ℝ) + 1))) := by
      intro K
      have hpos : 0 < Real.sqrt ((K : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
      have hss : Real.sqrt ((K : ℝ) + 1) * Real.sqrt ((K : ℝ) + 1) = (K : ℝ) + 1 :=
        Real.mul_self_sqrt (by positivity)
      field_simp
      linarith
    have := hsq.atTop_add hs.neg
    exact this.congr (fun K => (e K).symm)
  have h2 : Tendsto (fun K : ℕ => (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ K) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hKs)
    · intro K
      have hge : 1 ≤ Real.sqrt ((K : ℝ) + 1) := Real.one_le_sqrt.2 (by
        have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        linarith)
      have hle : 1 / Real.sqrt ((K : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]; exact hge
      exact pow_nonneg (by linarith) K
    · intro K
      have hge : 1 ≤ Real.sqrt ((K : ℝ) + 1) := Real.one_le_sqrt.2 (by
        have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
        linarith)
      have hle : 1 / Real.sqrt ((K : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by linarith)]; exact hge
      have hb := Real.add_one_le_exp (-(1 / Real.sqrt ((K : ℝ) + 1)))
      simp only [Function.comp]
      calc (1 - 1 / Real.sqrt ((K : ℝ) + 1)) ^ K
          ≤ (Real.exp (-(1 / Real.sqrt ((K : ℝ) + 1)))) ^ K :=
            pow_le_pow_left₀ (by linarith) (by linarith) K
        _ = Real.exp (-((K : ℝ) * (1 / Real.sqrt ((K : ℝ) + 1)))) := by
            rw [← Real.exp_nat_mul]; ring_nf
  have := h1.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub h2)
  simpa using this

/-! ## Claim -/

theorem claim : PL_UMDEFERF1.Claim := by
  unfold PL_UMDEFERF1.Claim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X Z _ _ Bad _ M φ π r a b n u h
    exact catV_eta_one Bad M φ π r a b n u h
  · intro X Z Ω _ _ _ Bad _ M PH κ nh r a b N ρ φ π
    unfold protocolCatV protocolCat
    simp only [catV_eta_one]
  · intro X Z _ _ Bad _ M φ π r η a b hc ha
    exact catV_bounds Bad M φ π r η a b hc ha
  · intro X Z _ _ Bad _ M φ π r η α A b hc hα0 hα1 hA0 hA1 hbad
    exact catD_cap Bad M φ π r η α A b hc hα0 hα1 hA0 hA1 hbad
  · intro X Z _ _ Bad _ M φ π r η α a b n u h hc ha hα0 hα1 hfl
    exact bridge Bad M φ π r η α a b n u h hc ha hα0 hα1 hfl n u h Reach.start
  · intro X Z _ _ _ Bad _ M r η α A b n u h x hM hx hbu
    exact attain Bad M r η α A b u x hM hx hbu n h
  · exact retry_closed
  · intro A θ n hA0 hA1 hθ0 hθ1 hD
    exact retry_le_ratio A θ n hA0 hA1 hθ0 hθ1 hD
  · intro A θ hA0 hA1 hθ0 hθ1 hD
    exact retry_limit A θ hA0 hA1 hθ0 hθ1 hD
  · intro X Z Ω _ _ _ Bad _ M PH nh ns b N r η α L U a ρ φ π hpc hα0 hα1 hL hfl hdom hU
    exact cert Bad M PH nh ns b N r η α L U a ρ φ π hpc hα0 hα1 hL hfl hdom hU
  · intro X Z Ω _ _ _ Bad _ M PH nh ns b N r η α L a ρ φ π hpc hα0 hα1 hL hfl hθ hdom
    obtain ⟨hPH, hρ, hcore⟩ := hpc
    unfold protocolCatV
    simp_rw [mul_assoc]
    apply PLDep_UMPROTF1.wsum_le _ _ _ hρ
    intro ω
    obtain ⟨_, _, _, hr0, hr1, hη0, hη1⟩ := hcore ω
    obtain ⟨t, ht0, ht1, hle⟩ := seed_bound Bad M PH nh ns b N r η α L (a ω) (φ ω) (π ω) hPH
      (hcore ω) hα0 hα1 hL (hfl ω).1 (hfl ω).2 hdom
    exact hle.trans (coarse_bound r (theta η α) L t b N nh ns hr0 hr1 hL hθ
      (theta_bounds hη0 hη1 hα0 hα1).2 ht0 ht1)
  · intro PH nh ns b N r t hPH ht0 ht1
    exact ⟨nogo_eq PH nh ns b N r t hPH, nogo_lb PH nh ns b N t hPH ht0 ht1⟩
  · exact limit_e'

/-! ## Witness -/

theorem witness : PL_UMDEFERF1.Witness := by
  unfold PL_UMDEFERF1.Witness
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, by norm_num, by norm_num, by norm_num, by norm_num⟩
    · intro x
      exact ⟨fun z => by simp [witnessM], by simp [witnessM]⟩
    · intro z
      simp only [witnessPhi]
      norm_num
    · intro h
      exact ⟨fun x => by simp [witnessPi], by simp [witnessPi]⟩
  · exact ⟨fun _ => zero_le_one, by simp⟩
  · intro h x z
    unfold witnessService
    split_ifs <;> norm_num
  · intro k v g x z _ _ _ _ _ _ _
    unfold witnessService
    split_ifs <;> norm_num
  · simp [E, witnessM, witnessPhi]
  · intro z
    simp [push, witnessM]
  · simp [catV, witnessM, witnessPhi, witnessPi, witnessService]
    norm_num
  · simp [catD, catV, witnessM, witnessPhi, witnessPi]
    norm_num
  · simp [catD, catV, witnessM, witnessPhi, witnessPi]
    norm_num
  · simp [finiteCap, retry]
    norm_num
  · simp [catD, catV, witnessM, witnessPhi, witnessPi]
  · intro t ht0 ht1
    have hmin : min 1 (1 * t) = t := by rw [one_mul]; exact min_eq_right ht1
    rw [hmin, PLDep_UMSURVF1.survH_hard t 0 3 0 le_rfl, Nat.sub_self,
      PLDep_UMSURVF1.binCDF_n_zero, fc_ge 1 t _ 2 le_rfl, retry_succ, retry_succ, retry_zero,
      theta]
    have hs0 : 0 ≤ 1 - t := by linarith
    have h1 : (1 - t) ^ 3 ≤ 1 - t := by
      have : (1 - t) ^ 2 ≤ 1 := pow_le_one₀ hs0 (by linarith)
      nlinarith
    have h2 : 0 ≤ t + (1 - t) * (1 / 2) * t := by nlinarith
    have h3 : t + (1 - t) * (1 / 2) * t ≤ 3 / 2 * t := by nlinarith
    nlinarith [mul_le_mul h1 h3 h2 hs0, sq_nonneg (1 - 2 * t)]
  · simp [protocolCatV, surv, push, hardKill, catV, witnessM, witnessPhi, witnessPi,
      witnessService]
    norm_num
  · have hPH : IsDist (fun x : Bool => if x = true then (1 : ℝ) else 0) :=
      ⟨fun x => by cases x <;> simp, by simp⟩
    rw [nogo_eq _ 2 0 1 3 1 (1 / 2) hPH]
    simp [binCDF]
    norm_num
