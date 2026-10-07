open PL_TMCERTF1

/-! Generic helpers: unfolding `risk`, `honestER`, `Vstar` over Boolean actions -/

theorem risk_zero' {S A Θ : Type} [Fintype S] [Fintype A] (G : Θ → Game S A)
    (θ : ℕ → RHist S A → S → A → Θ) (σ : RHist S A → S → A → ℝ) (s : S) (h : RHist S A) :
    risk G θ σ 0 s h = 0 := by
  simp [risk]

theorem risk_succ_bool {S : Type} [Fintype S] (G : Game S Bool) (σ : RHist S Bool → S → Bool → ℝ)
    (n : ℕ) (s : S) (h : RHist S Bool) :
    risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ (n + 1) s h =
      σ h s true * (G.cat n s true + ∑ s', G.K n s true s' *
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, true)])) +
      σ h s false * (G.cat n s false + ∑ s', G.K n s false s' *
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, false)])) := by
  rw [risk, Fintype.sum_bool]

theorem risk_hist {S A : Type} [Fintype S] [Fintype A] (G : Game S A) (σ : RHist S A → S → A → ℝ)
    (hσ : ∀ h s a, σ h s a = σ [] s a) :
    ∀ n s h, risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s h =
      risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s [] := by
  intro n
  induction n with
  | zero => intro s h; simp [risk]
  | succ n ih =>
    intro s h
    rw [risk, risk]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [hσ h s a]
    congr 2
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    rw [ih s' (h ++ _), ih s' ([] ++ _)]

theorem risk_succ_hf {S : Type} [Fintype S] (G : Game S Bool) (σ : RHist S Bool → S → Bool → ℝ)
    (hσ : ∀ h s a, σ h s a = σ [] s a) (n : ℕ) (s : S) (h : RHist S Bool) :
    risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ (n + 1) s h =
      σ [] s true * (G.cat n s true + ∑ s', G.K n s true s' *
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' []) +
      σ [] s false * (G.cat n s false + ∑ s', G.K n s false s' *
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' []) := by
  rw [risk_succ_bool, hσ h s true, hσ h s false]
  have e : ∀ a, ∑ s', G.K n s a s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, a)]) =
      ∑ s', G.K n s a s' * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' [] :=
    fun a => Finset.sum_congr rfl (fun s' _ => by rw [risk_hist G σ hσ n s' (h ++ [(s, a)])])
  rw [e true, e false]

theorem honestER_hist {S A : Type} [Fintype S] (G : Game S A) (a₀ : A) (rew : Unit → ℕ → S → ℝ) :
    ∀ n s h, honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s h =
      honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s [] := by
  intro n
  induction n with
  | zero => intro s h; simp [honestER]
  | succ n ih =>
    intro s h
    rw [honestER, honestER]
    congr 1
    refine Finset.sum_congr rfl (fun s' _ => ?_)
    rw [ih s' (h ++ _), ih s' ([] ++ _)]

theorem honestER_succ_hf {S A : Type} [Fintype S] (G : Game S A) (a₀ : A) (rew : Unit → ℕ → S → ℝ)
    (n : ℕ) (s : S) (h : RHist S A) :
    honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) (n + 1) s h =
      rew () n s + ∑ s', G.K n s a₀ s' * honestER (fun _ : Unit => G) a₀ rew (fun _ _ _ => ()) n s' [] := by
  rw [honestER]
  congr 1
  exact Finset.sum_congr rfl (fun s' _ => by rw [honestER_hist G a₀ rew n s' (h ++ _)])

theorem sup'_bool (g : Bool → ℝ) :
    (Finset.univ : Finset Bool).sup' Finset.univ_nonempty g = max (g true) (g false) := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro a _
    cases a
    · exact le_max_right _ _
    · exact le_max_left _ _
  · exact max_le (Finset.le_sup' g (Finset.mem_univ true)) (Finset.le_sup' g (Finset.mem_univ false))

theorem Vstar_succ_bool {S : Type} [Fintype S] (G : Game S Bool) (n : ℕ) (s : S) :
    Vstar G (n + 1) s = max (G.cat n s true + ∑ s', G.K n s true s' * Vstar G n s')
      (G.cat n s false + ∑ s', G.K n s false s' * Vstar G n s') := by
  rw [Vstar, sup'_bool]

theorem constRed_t {S : Type} (β : ℝ) (h : RHist S Bool) (s : S) : constRed β h s true = β := rfl
theorem constRed_f {S : Type} (β : ℝ) (h : RHist S Bool) (s : S) : constRed β h s false = 1 - β := rfl

/-! Rows of `gac` -/

theorem gac_cat_true (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) :
    (gac C TA TD FA).cat n c true =
      (if 0 < c.val then 1 - TD n c.val else 1 - TD n c.val + TA n c.val) := rfl

theorem gac_cat_false (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) :
    (gac C TA TD FA).cat n c false = 0 := rfl

theorem gac_sum_true (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) (F : Fin (C + 1) → ℝ) :
    ∑ c', (gac C TA TD FA).K n c true c' * F c' = (TD n c.val - TA n c.val) * F c := by
  simp [gac, ite_mul, Finset.sum_ite_eq']

theorem gac_sum_false_zero (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n : ℕ) (c : Fin (C + 1)) (hc : c.val = 0)
    (F : Fin (C + 1) → ℝ) :
    ∑ c', (gac C TA TD FA).K n c false c' * F c' = F c := by
  have e : ∀ c', (gac C TA TD FA).K n c false c' * F c' = if c' = c then F c' else 0 := by
    intro c'
    simp only [gac, Bool.false_eq_true, ite_false, hc, lt_self_iff_false]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun c' _ => e c'), Finset.sum_ite_eq']
  simp

theorem gac_sum_false_succ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ) (n k : ℕ) (hk : k + 1 < C + 1)
    (F : Fin (C + 1) → ℝ) :
    ∑ c', (gac C TA TD FA).K n ⟨k + 1, hk⟩ false c' * F c' =
      FA n (k + 1) * F ⟨k, by omega⟩ + (1 - FA n (k + 1)) * F ⟨k + 1, hk⟩ := by
  have e : ∀ c' : Fin (C + 1), (gac C TA TD FA).K n ⟨k + 1, hk⟩ false c' * F c' =
      (if c'.val + 1 = k + 1 then FA n (k + 1) * F c' else 0) +
        (if c' = ⟨k + 1, hk⟩ then (1 - FA n (k + 1)) * F c' else 0) := by
    intro c'
    simp only [gac, Bool.false_eq_true, ite_false, Nat.zero_lt_succ, ite_true]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun c' _ => e c'), Finset.sum_add_distrib, Finset.sum_ite_eq']
  rw [Finset.sum_eq_single_of_mem (⟨k, by omega⟩ : Fin (C + 1)) (Finset.mem_univ _)]
  · simp
  · intro b _ hb
    rw [ite_eq_right_iff]
    intro h
    exact absurd (Fin.ext (show b.val = k by omega)) hb

/-! (L) and (LQ) -/

theorem conjL : ∀ (C : ℕ) (TA TD FA : ℕ → ℕ → ℝ),
      (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) →
      Lawful (gac C TA TD FA) := by
  intro C TA TD FA hT N n _ c a
  obtain ⟨h1, h2, h3, h4, h5⟩ := hT n c.val
  have hs : ∀ a, ∑ c', (gac C TA TD FA).K n c a c' = ∑ c', (gac C TA TD FA).K n c a c' * (fun _ => (1 : ℝ)) c' :=
    fun a => by simp
  cases a
  · refine ⟨le_of_eq (gac_cat_false C TA TD FA n c).symm, ?_, ?_⟩
    · intro c'
      simp only [gac, Bool.false_eq_true, ite_false]
      split_ifs <;> linarith
    · rw [hs, gac_cat_false]
      rcases Nat.eq_zero_or_pos c.val with hc | hc
      · rw [gac_sum_false_zero C TA TD FA n c hc]; norm_num
      · obtain ⟨k, hk⟩ := c
        cases k with
        | zero => simp at hc
        | succ k =>
          rw [gac_sum_false_succ]
          linarith
  · refine ⟨?_, ?_, ?_⟩
    · rw [gac_cat_true]; split_ifs <;> linarith
    · intro c'
      simp only [gac, ite_true]
      split_ifs <;> linarith
    · rw [hs, gac_cat_true, gac_sum_true]
      split_ifs <;> linarith

theorem conjLQ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ),
      (∀ m c, 0 ≤ qa m c ∧ qa m c ≤ qd m c ∧ qd m c ≤ 1 ∧ 0 ≤ f (qa m c) ∧ f (qa m c) ≤ f (qd m c) ∧
        f (qd m c) ≤ 1) →
      Lawful (gacQ C f qa qd) := by
  intro C f qa qd hq
  apply conjL
  intro n c
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq (n + 1) c
  exact ⟨h4, h5, h6, h1, le_trans h2 h3⟩

/-! (Z) and (UZ) -/

theorem conjZ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (β : ℝ),
      f 0 = 0 → (∀ m, qa m 0 = 0) →
      ∀ (m : ℕ) (c : Fin (C + 1)),
        1 - risk (fun _ : Unit => gacQ C f qa qd) (fun _ _ _ _ => ()) (constRed β) m c [] =
          zGAC f qa qd β m c.val := by
  intro C f qa qd β hf hq m
  simp only [gacQ]
  induction m with
  | zero => intro c; simp [risk, zGAC]
  | succ m ih =>
    intro c
    rw [risk_succ_hf _ _ (fun _ _ _ => rfl), constRed_t, constRed_f, gac_cat_true, gac_cat_false,
      gac_sum_true]
    obtain ⟨k, hk⟩ := c
    cases k with
    | zero =>
      rw [gac_sum_false_zero _ _ _ _ _ _ rfl]
      have e0 := ih ⟨0, hk⟩
      dsimp only at e0 ⊢
      simp only [lt_self_iff_false, ite_false, hq, hf, zGAC]
      linear_combination (1 - β + β * f (qd (m + 1) 0)) * e0
    | succ k =>
      rw [gac_sum_false_succ]
      have e1 := ih ⟨k + 1, hk⟩
      have e2 := ih ⟨k, by omega⟩
      dsimp only at e1 e2 ⊢
      simp only [Nat.zero_lt_succ, ite_true, zGAC]
      linear_combination (β * (f (qd (m + 1) (k + 1)) - f (qa (m + 1) (k + 1))) +
        (1 - β) * (1 - qa (m + 1) (k + 1))) * e1 + (1 - β) * qa (m + 1) (k + 1) * e2

theorem conjUZ : ∀ (C : ℕ) (f : ℝ → ℝ) (qa qd : ℕ → ℕ → ℝ) (m : ℕ) (c : Fin (C + 1)),
      honestER (fun _ : Unit => gacQ C f qa qd) false (fun _ n c => usedReward qa qd n c.val)
          (fun _ _ _ => ()) m c [] = uGAC qa qd m c.val := by
  intro C f qa qd m
  simp only [gacQ]
  induction m with
  | zero => intro c; simp [honestER, uGAC]
  | succ m ih =>
    intro c
    rw [honestER_succ_hf]
    obtain ⟨k, hk⟩ := c
    cases k with
    | zero =>
      rw [gac_sum_false_zero _ _ _ _ _ _ rfl, ih]
      dsimp only
      simp only [usedReward, uGAC, lt_self_iff_false, ite_false]
      ring
    | succ k =>
      rw [gac_sum_false_succ, ih, ih]
      dsimp only
      simp only [usedReward, uGAC, Nat.zero_lt_succ, ite_true]
      ring

/-! (M) -/

theorem conjM : ∀ (S Ω : Type) [Fintype S] [Fintype Ω] (G : Game S Bool) (ρ : Ω → ℝ) (β : Ω → ℝ) (N : ℕ)
      (s₀ : S) (U : ℝ),
      (∀ ω, 0 ≤ ρ ω) → ∑ ω, ρ ω = 1 → (∀ ω, 0 ≤ β ω ∧ β ω ≤ 1) →
      (∀ b : ℝ, 0 ≤ b → b ≤ 1 → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U) →
      ∑ ω, ρ ω * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed (β ω)) N s₀ [] ≤ U := by
  intro S Ω _ _ G ρ β N s₀ U hρ hρ1 hβ hU
  calc ∑ ω, ρ ω * risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed (β ω)) N s₀ []
      ≤ ∑ ω, ρ ω * U :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hU _ (hβ ω).1 (hβ ω).2) (hρ ω))
    _ = U := by rw [← Finset.sum_mul, hρ1, one_mul]

/-! (Lip) and (Grid) -/

theorem rowval_bounds {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (n : ℕ) (s : S) (a : Bool)
    (F : S → ℝ) (hF : ∀ s, 0 ≤ F s ∧ F s ≤ 1) :
    0 ≤ G.cat n s a + ∑ s', G.K n s a s' * F s' ∧ G.cat n s a + ∑ s', G.K n s a s' * F s' ≤ 1 := by
  obtain ⟨h1, h2, h3⟩ := hG (n + 1) n (Nat.lt_succ_self n) s a
  constructor
  · have : 0 ≤ ∑ s', G.K n s a s' * F s' :=
      Finset.sum_nonneg (fun s' _ => mul_nonneg (h2 s') (hF s').1)
    linarith
  · have : ∑ s', G.K n s a s' * F s' ≤ ∑ s', G.K n s a s' :=
      Finset.sum_le_sum (fun s' _ => mul_le_of_le_one_right (h2 s') (hF s').2)
    linarith

theorem risk_const_bounds {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (b : ℝ) (hb0 : 0 ≤ b)
    (hb1 : b ≤ 1) : ∀ n s, 0 ≤ risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) n s [] ∧
      risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) n s [] ≤ 1 := by
  intro n
  induction n with
  | zero => intro s; simp [risk]
  | succ n ih =>
    intro s
    rw [risk_succ_hf G (constRed b) (fun _ _ _ => rfl), constRed_t, constRed_f]
    obtain ⟨x0, x1⟩ := rowval_bounds G hG n s true _ ih
    obtain ⟨y0, y1⟩ := rowval_bounds G hG n s false _ ih
    have hb2 : 0 ≤ 1 - b := by linarith
    constructor
    · exact add_nonneg (mul_nonneg hb0 x0) (mul_nonneg hb2 y0)
    · nlinarith [mul_le_mul_of_nonneg_left x1 hb0, mul_le_mul_of_nonneg_left y1 hb2]

theorem rowval_diff {S : Type} [Fintype S] (G : Game S Bool) (hG : Lawful G) (n : ℕ) (s : S) (a : Bool)
    (F1 F2 : S → ℝ) (e : ℝ) (he : 0 ≤ e) (hF : ∀ s, |F1 s - F2 s| ≤ e) :
    |(G.cat n s a + ∑ s', G.K n s a s' * F1 s') - (G.cat n s a + ∑ s', G.K n s a s' * F2 s')| ≤ e := by
  obtain ⟨h1, h2, h3⟩ := hG (n + 1) n (Nat.lt_succ_self n) s a
  have hd : (G.cat n s a + ∑ s', G.K n s a s' * F1 s') - (G.cat n s a + ∑ s', G.K n s a s' * F2 s') =
      ∑ s', G.K n s a s' * (F1 s' - F2 s') := by
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [hd]
  calc |∑ s', G.K n s a s' * (F1 s' - F2 s')| ≤ ∑ s', |G.K n s a s' * (F1 s' - F2 s')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s', G.K n s a s' * |F1 s' - F2 s'| :=
        Finset.sum_congr rfl (fun s' _ => by rw [abs_mul, abs_of_nonneg (h2 s')])
    _ ≤ ∑ s', G.K n s a s' * e :=
        Finset.sum_le_sum (fun s' _ => mul_le_mul_of_nonneg_left (hF s') (h2 s'))
    _ = (∑ s', G.K n s a s') * e := by rw [Finset.sum_mul]
    _ ≤ 1 * e := mul_le_mul_of_nonneg_right (by linarith) he
    _ = e := one_mul e

theorem lip_comb (b b' X Y X' Y' e : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hX0 : 0 ≤ X') (hX1 : X' ≤ 1) (hY0 : 0 ≤ Y') (hY1 : Y' ≤ 1)
    (hXX : |X - X'| ≤ e) (hYY : |Y - Y'| ≤ e) :
    |b * X + (1 - b) * Y - (b' * X' + (1 - b') * Y')| ≤ e + |b - b'| := by
  have hb2 : 0 ≤ 1 - b := by linarith
  have h1 : b * X + (1 - b) * Y - (b' * X' + (1 - b') * Y') =
      b * (X - X') + (1 - b) * (Y - Y') + (b - b') * (X' - Y') := by ring
  have h2 : |X' - Y'| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [h1]
  calc |b * (X - X') + (1 - b) * (Y - Y') + (b - b') * (X' - Y')|
      ≤ |b * (X - X')| + |(1 - b) * (Y - Y')| + |(b - b') * (X' - Y')| := abs_add_three _ _ _
    _ = b * |X - X'| + (1 - b) * |Y - Y'| + |b - b'| * |X' - Y'| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg hb2]
    _ ≤ b * e + (1 - b) * e + |b - b'| * 1 := by
        gcongr
    _ = e + |b - b'| := by ring

theorem conjLip : ∀ (S : Type) [Fintype S] (G : Game S Bool) (N : ℕ) (s₀ : S) (b b' : ℝ),
      Lawful G → 0 ≤ b → b ≤ 1 → 0 ≤ b' → b' ≤ 1 →
      |risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] -
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b') N s₀ []| ≤ N * |b - b'| := by
  intro S _ G N s₀ b b' hG hb0 hb1 hb'0 hb'1
  revert s₀
  induction N with
  | zero => intro s; simp [risk]
  | succ n ih =>
    intro s
    rw [risk_succ_hf G (constRed b) (fun _ _ _ => rfl), risk_succ_hf G (constRed b') (fun _ _ _ => rfl),
      constRed_t, constRed_f, constRed_t, constRed_f]
    have hB := risk_const_bounds G hG b' hb'0 hb'1 n
    obtain ⟨x0, x1⟩ := rowval_bounds G hG n s true _ hB
    obtain ⟨y0, y1⟩ := rowval_bounds G hG n s false _ hB
    have he : 0 ≤ (n : ℝ) * |b - b'| := mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _)
    have hX := rowval_diff G hG n s true
      (fun s' => risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) n s' [])
      (fun s' => risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b') n s' []) _ he ih
    have hY := rowval_diff G hG n s false
      (fun s' => risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) n s' [])
      (fun s' => risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b') n s' []) _ he ih
    have := lip_comb b b' _ _ _ _ _ hb0 hb1 x0 x1 y0 y1 hX hY
    calc _ ≤ (n : ℝ) * |b - b'| + |b - b'| := this
      _ = ((n + 1 : ℕ) : ℝ) * |b - b'| := by push_cast; ring

theorem conjGrid : ∀ (S : Type) [Fintype S] (G : Game S Bool) (N J : ℕ) (s₀ : S) (U : ℝ),
      Lawful G → 0 < J →
      (∀ j : ℕ, j ≤ J → risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed ((j : ℝ) / J)) N s₀ [] ≤ U) →
      ∀ b : ℝ, 0 ≤ b → b ≤ 1 →
        risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤ U + N / (2 * J) := by
  intro S _ G N J s₀ U hG hJ hU b hb0 hb1
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hfl1 : ((⌊b * J + 1/2⌋₊ : ℕ) : ℝ) ≤ b * J + 1/2 := Nat.floor_le (by positivity)
  have hfl2 : b * J + 1/2 < ((⌊b * J + 1/2⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  generalize ⌊b * J + 1/2⌋₊ = j at hfl1 hfl2
  have hjJ : j ≤ J := by
    have h1 : (j : ℝ) < J + 1 := by nlinarith
    have h2 : j < J + 1 := by exact_mod_cast h1
    omega
  have hjr0 : (0 : ℝ) ≤ j / J := by positivity
  have hjr1 : (j : ℝ) / J ≤ 1 := by
    rw [div_le_one hJr]; exact_mod_cast hjJ
  have hdist : |b - j / J| ≤ 1 / (2 * J) := by
    have e1 : b - j / J = (b * J - j) / J := by field_simp
    have h3 : |b * J - j| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [e1, abs_div, abs_of_pos hJr, div_le_div_iff₀ hJr (by positivity)]
    nlinarith
  have hl := conjLip S G N s₀ b (j / J) hG hb0 hb1 hjr0 hjr1
  have hu := hU j hjJ
  have h4 : risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] ≤
      risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed ((j : ℝ) / J)) N s₀ [] + N * |b - j / J| := by
    linarith [le_abs_self (risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed b) N s₀ [] -
      risk (fun _ : Unit => G) (fun _ _ _ _ => ()) (constRed ((j : ℝ) / J)) N s₀ [])]
  have h5 : (N : ℝ) * |b - j / J| ≤ N / (2 * J) := by
    calc (N : ℝ) * |b - j / J| ≤ N * (1 / (2 * J)) := mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg N)
      _ = N / (2 * J) := by ring
  linarith

/-! (W) -/

theorem Vstar_zero' {S A : Type} [Fintype S] [Fintype A] [Nonempty A] (G : Game S A) (s : S) :
    Vstar G 0 s = 0 := by
  simp [Vstar]

theorem conjW : ∀ (TA TD FA : ℕ → ℕ → ℝ),
      (∀ n c, 0 ≤ TA n c ∧ TA n c ≤ TD n c ∧ TD n c ≤ 1 ∧ 0 ≤ FA n c ∧ FA n c ≤ 1) →
      ∀ (N : ℕ) (c : Fin 1),
        risk (fun _ : Unit => gac 0 TA TD FA) (fun _ _ _ _ => ()) (constRed 1) N c [] =
          Vstar (gac 0 TA TD FA) N c := by
  intro TA TD FA hT N
  have key : ∀ c : Fin 1, risk (fun _ : Unit => gac 0 TA TD FA) (fun _ _ _ _ => ()) (constRed 1) N c [] =
      Vstar (gac 0 TA TD FA) N c ∧ Vstar (gac 0 TA TD FA) N c ≤ 1 := by
    induction N with
    | zero => intro c; simp [risk, Vstar]
    | succ n ih =>
      intro c
      have hc : c.val = 0 := by have := c.isLt; omega
      obtain ⟨e, hle⟩ := ih c
      obtain ⟨h1, h2, h3, h4, h5⟩ := hT n 0
      rw [risk_succ_hf _ _ (fun _ _ _ => rfl), Vstar_succ_bool, constRed_t, constRed_f]
      simp only [gac_sum_true, gac_sum_false_zero _ _ _ _ _ _ hc, gac_cat_true, gac_cat_false, hc,
        lt_self_iff_false, ite_false]
      rw [e]
      have hge : 0 + Vstar (gac 0 TA TD FA) n c ≤
          1 - TD n 0 + TA n 0 + (TD n 0 - TA n 0) * Vstar (gac 0 TA TD FA) n c := by
        nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - (TD n 0 - TA n 0) by linarith)
          (show (0 : ℝ) ≤ 1 - Vstar (gac 0 TA TD FA) n c by linarith)]
      rw [max_eq_left hge]
      constructor
      · ring
      · nlinarith [mul_le_mul_of_nonneg_left hle (show (0 : ℝ) ≤ TD n 0 - TA n 0 by linarith)]
  exact fun c => (key c).1

/-! (T5) -/

theorem ex_row0t (n : ℕ) (F : Fin 2 → ℝ) :
    exG3.cat n 0 true + ∑ s', exG3.K n 0 true s' * F s' = 1/4 + 3/4 * F 0 := by
  simp [exG3, gac, exTA3, exTD3, exFA3]
  norm_num

theorem ex_row0f (n : ℕ) (F : Fin 2 → ℝ) :
    exG3.cat n 0 false + ∑ s', exG3.K n 0 false s' * F s' = F 0 := by
  simp [exG3, gac, exTA3, exTD3, exFA3]

theorem ex_row1t (n : ℕ) (F : Fin 2 → ℝ) :
    exG3.cat n 1 true + ∑ s', exG3.K n 1 true s' * F s' = 1/4 := by
  simp [exG3, gac, exTA3, exTD3, exFA3]
  norm_num

theorem ex_row1f (n : ℕ) (F : Fin 2 → ℝ) :
    exG3.cat n 1 false + ∑ s', exG3.K n 1 false s' * F s' = 1/2 * F 0 + 1/2 * F 1 := by
  simp [exG3, gac, Fin.sum_univ_two, exTA3, exTD3, exFA3]
  norm_num

theorem ex_step0 (σ : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ) (n : ℕ) (h : RHist (Fin 2) Bool) :
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ (n + 1) 0 h =
      σ h 0 true * (1/4 + 3/4 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(0, true)])) +
      σ h 0 false * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(0, false)]) := by
  rw [risk_succ_bool, ex_row0t, ex_row0f]

theorem ex_step1 (σ : RHist (Fin 2) Bool → Fin 2 → Bool → ℝ) (n : ℕ) (h : RHist (Fin 2) Bool) :
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ (n + 1) 1 h =
      σ h 1 true * (1/4) +
      σ h 1 false * (1/2 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 0 (h ++ [(1, false)]) +
        1/2 * risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) σ n 1 (h ++ [(1, false)])) := by
  rw [risk_succ_bool, ex_row1t, ex_row1f]

theorem ex_V0 (n : ℕ) : Vstar exG3 (n + 1) 0 = max (1/4 + 3/4 * Vstar exG3 n 0) (Vstar exG3 n 0) := by
  rw [Vstar_succ_bool, ex_row0t, ex_row0f]

theorem ex_V1 (n : ℕ) :
    Vstar exG3 (n + 1) 1 = max (1/4) (1/2 * Vstar exG3 n 0 + 1/2 * Vstar exG3 n 1) := by
  rw [Vstar_succ_bool, ex_row1t, ex_row1f]

theorem ex_poly (b : ℝ) :
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed b) 3 1 [] =
      3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 := by
  simp only [ex_step0, ex_step1, risk_zero', constRed_t, constRed_f]
  ring

theorem ex_clocked : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32 := by
  simp [ex_step0, ex_step1, risk_zero', clocked3]
  norm_num

theorem ex_coin : risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) coinRed 3 1 [] = 9/32 := by
  simp [ex_step0, ex_step1, risk_zero', coinRed]
  norm_num

theorem ex_Vstar : Vstar exG3 3 1 = 11/32 := by
  have v10 : Vstar exG3 1 0 = 1/4 := by
    rw [ex_V0, Vstar_zero', max_eq_left (by norm_num)]; norm_num
  have v11 : Vstar exG3 1 1 = 1/4 := by
    rw [ex_V1, Vstar_zero', Vstar_zero', max_eq_left (by norm_num)]
  have v20 : Vstar exG3 2 0 = 7/16 := by
    rw [ex_V0, v10, max_eq_left (by norm_num)]; norm_num
  have v21 : Vstar exG3 2 1 = 1/4 := by
    rw [ex_V1, v10, v11, max_eq_left (by norm_num)]
  rw [ex_V1, v20, v21, max_eq_right (by norm_num)]; norm_num

theorem conjT5 :
    (∀ b : ℝ, 0 ≤ b → b ≤ 1 →
      risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed b) 3 1 [] =
        3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ∧
      3/4 * b - 21/32 * b ^ 2 + 5/32 * b ^ 3 ≤ 13/50) ∧
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) (constRed (4/5)) 3 1 [] = 13/50 ∧
    IsPolicy clocked3 ∧ IsPolicy coinRed ∧
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) coinRed 3 1 [] = 9/32 ∧ (13/50 : ℝ) < 9/32 ∧
    risk (fun _ : Unit => exG3) (fun _ _ _ _ => ()) clocked3 3 1 [] = 11/32 ∧
    Vstar exG3 3 1 = 11/32 ∧
    (13/50 : ℝ) < 11/32 := by
  refine ⟨fun b hb0 hb1 => ⟨ex_poly b, ?_⟩, ?_, ?_, ?_, ex_coin, by norm_num, ex_clocked, ex_Vstar,
    by norm_num⟩
  · nlinarith [mul_nonneg (sq_nonneg (5 * b - 4)) (show (0 : ℝ) ≤ 13 - 5 * b by linarith)]
  · rw [ex_poly]; norm_num
  · intro h s
    by_cases h1 : 1 ≤ h.length
    · refine ⟨fun a => ?_, ?_⟩
      · cases a <;> simp [clocked3, h1]
      · simp [clocked3, h1]
    · refine ⟨fun a => ?_, ?_⟩
      · cases a <;> simp [clocked3, h1]
      · simp [clocked3, h1]
  · intro h s
    by_cases h1 : s.val = 0
    · refine ⟨fun a => ?_, ?_⟩
      · cases a <;> simp [coinRed, h1]
      · simp [coinRed, h1]
    · refine ⟨fun a => ?_, ?_⟩
      · cases a <;> simp [coinRed, h1]
      · simp [coinRed, h1]

/-! Soundness of a certificate (single model), proved locally -/

theorem sound_unit {S A : Type} [Fintype S] [Fintype A] (G : Game S A) (N : ℕ) (V : ℕ → S → ℝ)
    (σ : RHist S A → S → A → ℝ) (hK : ∀ n, n < N → ∀ s a s', 0 ≤ G.K n s a s')
    (hV : RiskCertUpTo N (fun _ : Unit => G) (fun _ _ _ _ => True) V) (hσ : IsPolicy σ) :
    ∀ n, n ≤ N → ∀ s h, risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s h ≤ V n s := by
  intro n
  induction n with
  | zero => intro _ s h; rw [risk_zero']; exact hV.1 s
  | succ n ih =>
    intro hn s h
    rw [risk]
    calc ∑ a, σ h s a * (G.cat n s a + ∑ s', G.K n s a s' *
          risk (fun _ : Unit => G) (fun _ _ _ _ => ()) σ n s' (h ++ [(s, a)]))
        ≤ ∑ a, σ h s a * V (n + 1) s := by
          refine Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left ?_ ((hσ h s).1 a))
          refine le_trans ?_ (hV.2 n (by omega) s a () trivial)
          exact add_le_add (le_refl _) (Finset.sum_le_sum (fun s' _ =>
            mul_le_mul_of_nonneg_left (ih (by omega) s' _) (hK n (by omega) s a s')))
      _ = V (n + 1) s := by rw [← Finset.sum_mul, (hσ h s).2, one_mul]

theorem claim : PL_TMGACF1.Claim :=
  ⟨conjL, conjLQ, conjZ, conjUZ, conjM, conjLip, conjGrid, conjW, conjT5⟩

theorem witness : PL_TMGACF1.Witness := by
  have hlaw : Lawful exG3 := conjL 1 exTA3 exTD3 exFA3 (by
    intro n c
    simp only [exTA3, exTD3, exFA3]
    split_ifs <;> norm_num)
  have hcert : RiskCertUpTo 3 (fun _ : Unit => exG3) (fun _ _ _ _ => True) exV3 := by
    refine ⟨fun s => by simp [exV3], ?_⟩
    intro n hn s a _ _
    have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
    show exG3.cat n s a + ∑ s', exG3.K n s a s' * exV3 n s' ≤ exV3 (n + 1) s
    interval_cases n <;> rcases hs with rfl | rfl <;> cases a <;>
      simp only [ex_row0t, ex_row0f, ex_row1t, ex_row1f] <;> norm_num [exV3]
  refine ⟨?_, hlaw, hcert, ?_, ex_clocked, ?_, ?_, ?_, ?_, ?_⟩
  · unfold exG3 gacQ
    congr 1
    · funext n c
      rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc; simp [exTA3]
      · simp [exTA3, hc, hc.ne']; norm_num [min_def]
    · funext n c; simp [exTD3]; norm_num [min_def]
    · funext n c
      rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc; simp [exFA3]
      · simp [exFA3, hc, hc.ne']
  · intro σ hσ
    have := sound_unit exG3 3 exV3 σ (fun n hn s a s' => ((hlaw 3) n hn s a).2.1 s') hcert hσ 3 le_rfl 1 []
    calc _ ≤ exV3 3 1 := this
      _ = 11/32 := by norm_num [exV3]
  · norm_num [uGAC]
  · norm_num [zGAC, min_def]
  · have hz := conjZ 1 (fun q => min 1 (3 * q)) (fun _ c => if c = 0 then 0 else 1/4)
      (fun _ c => if c = 0 then 1/4 else 1/2) (1/2) (by norm_num [min_def]) (fun m => by simp) 2 1
    rw [hz]
    norm_num [zGAC, min_def]
  · norm_num [uGAC]
  · norm_num [uGAC]
