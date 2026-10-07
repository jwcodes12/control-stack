open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMLOWERF1

-- Generic facts about `adSurv`

theorem adSurv_zero' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ)
    (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (h : Hist X Z) :
    adSurv T M φ keep 0 h = keep h := by
  simp only [adSurv]

theorem adSurv_succ' {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ)
    (M : X → Z → ℝ) (φ : Z → ℝ) (keep : Hist X Z → ℝ) (n : ℕ) (h : Hist X Z) :
    adSurv T M φ keep (n + 1) h = ∑ x, T h x * ∑ z, M x z *
      (φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) +
       (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)])) := by
  simp only [adSurv]

/-- (s) -/
theorem s_aux {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h))
    (hk : ∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) :
    ∀ (n : ℕ) (h : Hist X Z), (∀ e ∈ h, e.2.2 = false) →
      adSurv T M (fun _ => 0) keep n h = 1 := by
  have hM1 : ∀ x, ∑ z, M x z = 1 := fun x => (hM x).2
  intro n
  induction n with
  | zero => intro h hh; rw [adSurv_zero']; exact hk h hh
  | succ n ih =>
    intro h hh
    rw [adSurv_succ']
    have e : ∀ x z, adSurv T M (fun _ => 0) keep n (h ++ [(x, z, false)]) = 1 := by
      intro x z; apply ih; intro e he
      rw [List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact hh e he
      · rw [he]
    simp only [e, zero_mul, sub_zero, one_mul, zero_add, mul_one, hM1]
    exact (hT h).2

theorem part_s : ∀ (X Z : Type) [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
      (keep : Hist X Z → ℝ) (n : ℕ),
      IsKernel M → (∀ h, IsDist (T h)) → (∀ h : Hist X Z, (∀ e ∈ h, e.2.2 = false) → keep h = 1) →
      AcceptsAllFlag T M keep n := by
  intro X Z _ _ T M keep n hM hT hk
  exact s_aux T M keep hM hT hk n [] (by simp)

-- (a): identical until bad

theorem surv_bounds {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (φ : Z → ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h))
    (hφ : IsRule φ) (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) :
    ∀ (n : ℕ) (h : Hist X Z), 0 ≤ adSurv T M φ keep n h ∧ adSurv T M φ keep n h ≤ 1 := by
  intro n
  induction n with
  | zero => intro h; rw [adSurv_zero']; exact hk h
  | succ n ih =>
    intro h
    rw [adSurv_succ']
    have hin : ∀ x z, 0 ≤ φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) +
        (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)]) ∧
        φ z * adSurv T M φ keep n (h ++ [(x, z, true)]) +
        (1 - φ z) * adSurv T M φ keep n (h ++ [(x, z, false)]) ≤ 1 := by
      intro x z
      obtain ⟨a0, a1⟩ := ih (h ++ [(x, z, true)])
      obtain ⟨b0, b1⟩ := ih (h ++ [(x, z, false)])
      obtain ⟨p0, p1⟩ := hφ z
      have q1 := mul_nonneg p0 a0
      have q2 := mul_nonneg (sub_nonneg.2 p1) b0
      have q3 := mul_nonneg p0 (sub_nonneg.2 a1)
      have q4 := mul_nonneg (sub_nonneg.2 p1) (sub_nonneg.2 b1)
      constructor <;> nlinarith
    constructor
    · apply PLDep_UMPROTF1.wsum_nonneg _ _ (hT h).1; intro x
      apply PLDep_UMPROTF1.wsum_nonneg _ _ (hM x).1; intro z; exact (hin x z).1
    · apply PLDep_UMPROTF1.wsum_le _ _ _ (hT h); intro x
      apply PLDep_UMPROTF1.wsum_le _ _ _ (hM x); intro z; exact (hin x z).2

/-- expected weighted number of queries in the all-FLAG reference continuation -/
noncomputable def Qf {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ)
    (M : X → Z → ℝ) (w : Z → ℝ) : ℕ → Hist X Z → ℝ
  | 0, _ => 0
  | n + 1, h => ∑ x, T h x * ∑ z, M x z * (w z + Qf T M w n (h ++ [(x, z, false)]))

theorem Qf_zero {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ)
    (M : X → Z → ℝ) (w : Z → ℝ) (h : Hist X Z) : Qf T M w 0 h = 0 := by
  simp only [Qf]

theorem Qf_succ {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ)
    (M : X → Z → ℝ) (w : Z → ℝ) (n : ℕ) (h : Hist X Z) :
    Qf T M w (n + 1) h = ∑ x, T h x * ∑ z, M x z * (w z + Qf T M w n (h ++ [(x, z, false)])) := by
  simp only [Qf]

theorem Qf_nonneg {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ)
    (M : X → Z → ℝ) (w : Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h))
    (hw : ∀ z, 0 ≤ w z) : ∀ (n : ℕ) (h : Hist X Z), 0 ≤ Qf T M w n h := by
  intro n
  induction n with
  | zero => intro h; rw [Qf_zero]
  | succ n ih =>
    intro h
    rw [Qf_succ]
    apply PLDep_UMPROTF1.wsum_nonneg _ _ (hT h).1; intro x
    apply PLDep_UMPROTF1.wsum_nonneg _ _ (hM x).1; intro z
    exact add_nonneg (hw z) (ih _)

theorem sum2_add {X Z : Type} [Fintype X] [Fintype Z] (a : X → ℝ) (m : X → Z → ℝ)
    (f g : X → Z → ℝ) (t : ℝ) :
    ∑ x, a x * ∑ z, m x z * f x z + t * ∑ x, a x * ∑ z, m x z * g x z =
      ∑ x, a x * ∑ z, m x z * (f x z + t * g x z) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro x _
  simp only [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro z _
  ring

theorem ref_lb {X Z : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (φ w : Z → ℝ) (t : ℝ) (keep : Hist X Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h))
    (hk : ∀ h, 0 ≤ keep h ∧ keep h ≤ 1) (hφ : IsRule φ) (hw : ∀ z, 0 ≤ w z) (ht : 0 ≤ t)
    (hφw : ∀ z, φ z ≤ t * w z) :
    ∀ (n : ℕ) (h : Hist X Z),
      adSurv T M (fun _ => 0) keep n h - t * Qf T M w n h ≤ adSurv T M φ keep n h := by
  have h0rule : IsRule (fun _ : Z => (0 : ℝ)) := fun _ => ⟨le_refl _, zero_le_one⟩
  intro n
  induction n with
  | zero => intro h; rw [adSurv_zero', adSurv_zero', Qf_zero]; linarith
  | succ n ih =>
    intro h
    rw [sub_le_iff_le_add, adSurv_succ', adSurv_succ', Qf_succ, sum2_add]
    apply Finset.sum_le_sum; intro x _
    apply mul_le_mul_of_nonneg_left _ ((hT h).1 x)
    apply Finset.sum_le_sum; intro z _
    apply mul_le_mul_of_nonneg_left _ ((hM x).1 z)
    obtain ⟨A1, -⟩ := surv_bounds T M φ keep hM hT hφ hk n (h ++ [(x, z, true)])
    obtain ⟨B0, B1⟩ := surv_bounds T M (fun _ => 0) keep hM hT h0rule hk n (h ++ [(x, z, false)])
    have IH := ih (h ++ [(x, z, false)])
    have Q0 := Qf_nonneg T M w hM hT hw n (h ++ [(x, z, false)])
    obtain ⟨p0, p1⟩ := hφ z
    have q1 := mul_nonneg p0 A1
    have q2 := mul_le_mul_of_nonneg_left IH (sub_nonneg.2 p1)
    have q3 := mul_nonneg p0 (sub_nonneg.2 B1)
    have q4 := mul_nonneg (mul_nonneg p0 ht) Q0
    have q5 := hφw z
    simp only [zero_mul, sub_zero, one_mul, zero_add]
    nlinarith

theorem Q_sum_le {X Z Ω : Type} [Fintype X] [Fintype Z] (T : Hist X Z → X → ℝ)
    (M : X → Z → ℝ) (hM : IsKernel M) (hT : ∀ h, IsDist (T h)) (S : Finset Ω)
    (w : Ω → Z → ℝ) (hw1 : ∀ z, ∑ ω ∈ S, w ω z ≤ 1) :
    ∀ (n : ℕ) (h : Hist X Z), ∑ ω ∈ S, Qf T M (w ω) n h ≤ n := by
  intro n
  induction n with
  | zero => intro h; simp only [Qf_zero, Finset.sum_const_zero, Nat.cast_zero, le_refl]
  | succ n ih =>
    intro h
    have e : ∑ ω ∈ S, Qf T M (w ω) (n + 1) h = ∑ x, T h x * ∑ z, M x z *
        (∑ ω ∈ S, w ω z + ∑ ω ∈ S, Qf T M (w ω) n (h ++ [(x, z, false)])) := by
      simp only [Qf_succ]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl; intro z _
      rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [e]
    push_cast
    apply PLDep_UMPROTF1.wsum_le _ _ _ (hT h); intro x
    apply PLDep_UMPROTF1.wsum_le _ _ _ (hM x); intro z
    have := ih (h ++ [(x, z, false)])
    have := hw1 z
    linarith

theorem ind_sum_le {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (S : Finset X)
    (hinj : Set.InjOn c (S : Set X)) (z : Z) :
    ∑ ω ∈ S, (if g z = c ω then (1 : ℝ) else 0) ≤ 1 := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hcard : (S.filter (fun ω => g z = c ω)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact hinj (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1) (ha.2.symm.trans hb.2)
  exact_mod_cast hcard

theorem classRule_rule {X Z C : Type} [DecidableEq C] (c : X → C) (g : Z → C) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : X) : IsRule (classRule c g t ω) := by
  intro z; unfold classRule; split_ifs <;> constructor <;> linarith

theorem conv_a {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X)
    (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X))
    (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x)
    (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ) (hTk : AdTester T keep)
    (hacc : AcceptsAllFlag T M keep n) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) :
    t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤
      adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z := Z)) := by
  obtain ⟨hT, hk⟩ := hTk
  have hkpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS
  have hrule : ∀ ω, IsRule (classRule c g t ω) := classRule_rule c g t ht0 ht1
  have hsv0 : ∀ ω, 0 ≤ adSurv T M (classRule c g t ω) keep n [] :=
    fun ω => (surv_bounds T M _ keep hM hT (hrule ω) hk n []).1
  have hπ : ∀ (ω : X) (h : Hist X Z), IsDist (seedPolicy (Z := Z) ω h) := by
    intro ω h; constructor
    · intro x; unfold seedPolicy; split_ifs <;> norm_num
    · simp [seedPolicy]
  have hct0 : ∀ ω, 0 ≤ cat Bad M (classRule c g t ω) (seedPolicy ω) r b N 0 [] :=
    fun ω => (PLDep_UMPROTF1.t3a Bad M _ _ r 1 b hM (hrule ω) (hπ ω) hr0 hr1 zero_le_one le_rfl
      (fun x _ => PLDep_UMPROTF1.E_le_one M _ hM (hrule ω) x) N 0 []).1
  have hctS : ∀ ω ∈ S, t ≤ cat Bad M (classRule c g t ω) (seedPolicy ω) r b N 0 [] := by
    intro ω hω
    have h1 := PLDep_UMLOWERF1.cat_ge Bad M (classRule c g t ω) r b N ω hM (hrule ω) hr1 hN
      (hbad ω hω)
    have hpe := PLDep_UMLOWERF1.pass_eq M c g hM hg t ω ω
    rw [if_pos rfl] at hpe
    have hpe' : ∑ z, M ω z * classRule c g t ω z = t := hpe
    rw [hpe'] at h1
    exact h1
  have hsum : (S.card : ℝ) - t * n ≤ ∑ ω ∈ S, adSurv T M (classRule c g t ω) keep n [] := by
    have hlb : ∀ ω ∈ S, 1 - t * Qf T M (fun z => if g z = c ω then (1:ℝ) else 0) n [] ≤
        adSurv T M (classRule c g t ω) keep n [] := by
      intro ω _
      have h1 := ref_lb T M (classRule c g t ω) (fun z => if g z = c ω then (1:ℝ) else 0) t keep
        hM hT hk (hrule ω) (fun z => by split_ifs <;> norm_num) ht0
        (fun z => by unfold classRule; split_ifs <;> simp) n []
      unfold AcceptsAllFlag at hacc
      rw [hacc] at h1
      exact h1
    have hQ := Q_sum_le T M hM hT S (fun ω z => if g z = c ω then (1:ℝ) else 0)
      (fun z => ind_sum_le c g S hinj z) n []
    calc (S.card : ℝ) - t * n
        ≤ ∑ ω ∈ S, (1 - t * Qf T M (fun z => if g z = c ω then (1:ℝ) else 0) n []) := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
          have := mul_le_mul_of_nonneg_left hQ ht0
          linarith
      _ ≤ _ := Finset.sum_le_sum hlb
  have hrisk : (t / (S.card : ℝ)) * ∑ ω ∈ S, adSurv T M (classRule c g t ω) keep n [] ≤
      adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z := Z)) := by
    unfold adProtocolCat
    have hterm : ∀ ω, (if ω ∈ S then t / (S.card : ℝ) * adSurv T M (classRule c g t ω) keep n []
        else 0) ≤ seedLaw S ω * adSurv T M (classRule c g t ω) keep n [] *
          cat Bad M (classRule c g t ω) (seedPolicy ω) r b N 0 [] := by
      intro ω
      unfold seedLaw
      split_ifs with h
      · calc t / (S.card : ℝ) * adSurv T M (classRule c g t ω) keep n []
            = 1 / (S.card : ℝ) * adSurv T M (classRule c g t ω) keep n [] * t := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (hctS ω h)
              (mul_nonneg (by positivity) (hsv0 ω))
      · simp
    calc (t / (S.card : ℝ)) * ∑ ω ∈ S, adSurv T M (classRule c g t ω) keep n []
        = ∑ ω, (if ω ∈ S then t / (S.card : ℝ) * adSurv T M (classRule c g t ω) keep n []
            else 0) := by
          rw [Finset.sum_ite_mem_eq, Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun ω _ => hterm ω)
  have hrisk0 : 0 ≤
      adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z := Z)) := by
    unfold adProtocolCat
    apply Finset.sum_nonneg; intro ω _
    apply mul_nonneg (mul_nonneg _ (hsv0 ω)) (hct0 ω)
    unfold seedLaw; split_ifs <;> positivity
  rcases le_total (1 - t * n / (S.card : ℝ)) 0 with hneg | hpos
  · rw [max_eq_left hneg, mul_zero]; exact hrisk0
  · rw [max_eq_right hpos]
    refine le_trans ?_ hrisk
    have e : t * (1 - t * n / (S.card : ℝ)) = t / (S.card : ℝ) * ((S.card : ℝ) - t * n) := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem opt_arith (k n : ℝ) (hk : 0 < k) (hn : 1 ≤ n) :
    min (1 / 2) (k / (4 * n)) ≤
      min 1 (k / (2 * n)) * max 0 (1 - min 1 (k / (2 * n)) * n / k) := by
  have hn0 : 0 < n := by linarith
  rcases le_total (2 * n) k with h | h
  · have h1 : 1 ≤ k / (2 * n) := by rw [le_div_iff₀ (by positivity)]; linarith
    rw [min_eq_left h1, one_mul, one_mul]
    have h2 : n / k ≤ 1 / 2 := by rw [div_le_iff₀ hk]; linarith
    have h3 : 1 / 2 ≤ max 0 (1 - n / k) := le_trans (by linarith) (le_max_right _ _)
    exact le_trans (min_le_left _ _) h3
  · have h1 : k / (2 * n) ≤ 1 := by rw [div_le_iff₀ (by positivity)]; linarith
    rw [min_eq_right h1]
    have e : k / (2 * n) * n / k = 1 / 2 := by field_simp
    rw [e]
    have e2 : k / (2 * n) * max 0 (1 - 1 / 2) = k / (4 * n) := by
      rw [max_eq_right (by norm_num)]; field_simp; ring
    rw [e2]
    exact min_le_right _ _

theorem part_a : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C]
      (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X),
      Setup Bad M c S →
      ∃ g : Z → C, (∀ x z, M x z ≠ 0 → g z = c x) ∧
        (∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ),
          AdTester T keep → AcceptsAllFlag T M keep n →
          ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
            t * max 0 (1 - t * (n : ℝ) / (S.card : ℝ)) ≤
              adProtocolCat Bad M T keep n r b N (seedLaw S) (classRule c g t) (seedPolicy (Z := Z))) ∧
        (∀ (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ), 1 ≤ n →
          AdTester T keep → AcceptsAllFlag T M keep n →
          ∀ (r : ℝ) (b N : ℕ), 0 ≤ r → r ≤ 1 → 1 ≤ N →
            min (1 / 2) ((S.card : ℝ) / (4 * n)) ≤
              adProtocolCat Bad M T keep n r b N (seedLaw S)
                (classRule c g (min 1 ((S.card : ℝ) / (2 * n)))) (seedPolicy (Z := Z))) := by
  intro X Z C _ _ _ _ Bad _ M c S hset
  obtain ⟨hM, hcp, hbad, hinj, hS⟩ := hset
  obtain ⟨g, hg⟩ := hcp
  have hkpos : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS
  refine ⟨g, hg, ?_, ?_⟩
  · intro n T keep hTk hacc t ht0 ht1 r b N hr0 hr1 hN
    exact conv_a Bad M c S hM hbad hinj hS g hg n T keep hTk hacc t ht0 ht1 r b N hr0 hr1 hN
  · intro n T keep hn hTk hacc r b N hr0 hr1 hN
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have ht0 : 0 ≤ min 1 ((S.card : ℝ) / (2 * n)) := le_min zero_le_one (by positivity)
    have ht1 : min 1 ((S.card : ℝ) / (2 * n)) ≤ 1 := min_le_left _ _
    refine le_trans (opt_arith (S.card : ℝ) (n : ℝ) hkpos hn') ?_
    exact conv_a Bad M c S hM hbad hinj hS g hg n T keep hTk hacc _ ht0 ht1 r b N hr0 hr1 hN

-- Concrete testers: deterministic queries, identity mediator

theorem adSurv_det {X : Type} [Fintype X] [DecidableEq X] (T : Hist X X → X → ℝ)
    (M : X → X → ℝ) (q : Hist X X → X) (hT : ∀ h x, T h x = if x = q h then 1 else 0)
    (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (keep : Hist X X → ℝ) (n : ℕ)
    (h : Hist X X) :
    adSurv T M φ keep (n + 1) h = φ (q h) * adSurv T M φ keep n (h ++ [(q h, q h, true)]) +
      (1 - φ (q h)) * adSurv T M φ keep n (h ++ [(q h, q h, false)]) := by
  rw [adSurv_succ']
  simp only [hT, hM, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem cat_id1 {X : Type} [Fintype X] [DecidableEq X] (M : X → X → ℝ)
    (hM : ∀ x z, M x z = if z = x then 1 else 0) (φ : X → ℝ) (ω : X) :
    cat (fun _ : X => True) M φ (seedPolicy (Z := X) ω) 1 1 1 0 [] = φ ω := by
  simp [cat, hM, seedPolicy]

theorem det_dist {X : Type} [Fintype X] [DecidableEq X] (y : X) :
    IsDist (fun x : X => if x = y then (1 : ℝ) else 0) := by
  constructor
  · intro x; dsimp only; split_ifs <;> norm_num
  · simp

theorem keep01 (P : Prop) [Decidable P] : 0 ≤ (if P then (1 : ℝ) else 0) ∧
    (if P then (1 : ℝ) else 0) ≤ 1 := by
  split_ifs <;> norm_num

theorem setup_id {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (M : X → X → ℝ)
    (hM : ∀ x z, M x z = if z = x then 1 else 0) :
    Setup (fun _ : X => True) M id (univ : Finset X) := by
  refine ⟨?_, ⟨id, ?_⟩, fun _ _ => trivial, ?_, ?_⟩
  · intro x
    have e : M x = fun z => if z = x then (1 : ℝ) else 0 := funext (fun z => hM x z)
    rw [e]; exact det_dist x
  · intro x z h
    by_contra hne
    exact h (by rw [hM, if_neg (show ¬ z = x from hne)])
  · intro a _ b _ hab; exact hab
  · exact Finset.card_pos.mpr Finset.univ_nonempty

theorem misses_allflag {X Z : Type} (h : Hist X Z) (hh : ∀ e ∈ h, e.2.2 = false) :
    misses h = 0 := by
  unfold misses
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro e he
  simp [hh e he]

theorem c1_surv (t : ℝ) (ω : Bool) :
    adSurv ctrT idM (classRule id id t ω) ctrKeep 3 [] =
      if ω then 1 - t ^ 2 else (1 - t) + t * (1 - t) ^ 2 := by
  have hs := adSurv_det ctrT idM ctrQuery (fun _ _ => rfl) (fun _ _ => rfl)
  cases ω <;> simp [hs, adSurv_zero', ctrQuery, ctrKeep, misses, classRule] <;> ring

theorem c1_risk (t : ℝ) :
    adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool))
      (classRule id id t) (seedPolicy (Z := Bool)) =
      t / 2 * ((1 - t ^ 2) + ((1 - t) + t * (1 - t) ^ 2)) := by
  unfold adProtocolCat
  rw [Fintype.sum_bool]
  simp only [c1_surv, cat_id1 idM (fun _ _ => rfl), seedLaw, Finset.mem_univ, if_true,
    Finset.card_univ, Fintype.card_bool, classRule, id]
  norm_num
  ring

theorem c2_surv (t : ℝ) (ω : Fin 3) :
    adSurv stT idM3 (classRule id id t ω) stKeep 3 [] =
      if ω = 0 then (1 - t) + t * (1 - t) ^ 2 else if ω = 1 then 1 - t ^ 2 else 1 := by
  have hs := adSurv_det stT idM3 stQuery (fun _ _ => rfl) (fun _ _ => rfl)
  fin_cases ω <;> simp [hs, adSurv_zero', stQuery, List.find?, stKeep, misses, classRule] <;> ring

theorem c2_risk (t : ℝ) :
    adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1
      (seedLaw (univ : Finset (Fin 3))) (classRule id id t) (seedPolicy (Z := Fin 3)) =
      t - t ^ 3 + t ^ 4 / 3 := by
  unfold adProtocolCat
  rw [Fin.sum_univ_three]
  simp only [c2_surv, cat_id1 idM3 (fun _ _ => rfl), seedLaw, Finset.mem_univ, if_true,
    Finset.card_univ, Fintype.card_fin, classRule, id]
  norm_num
  ring

theorem c2_bound (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t - t ^ 3 + t ^ 4 / 3 < 1 / 2 := by
  nlinarith [mul_nonneg (sq_nonneg (t - 7/10)) (by linarith : (0:ℝ) ≤ t + 7/5),
    mul_nonneg (pow_nonneg ht0 3) (sub_nonneg.2 ht1)]

theorem w_surv (t : ℝ) (ω : Bool) :
    adSurv wT idM (classRule id id t ω) wKeep 1 [] = if ω then 1 else 1 - t := by
  have hs := adSurv_det wT idM (fun _ => false) (fun _ _ => rfl) (fun _ _ => rfl)
  cases ω <;> simp [hs, adSurv_zero', wKeep, misses, classRule]

theorem wbad_surv (t : ℝ) (ω : Bool) :
    adSurv wT idM (classRule id id t ω) wKeepBad 1 [] = if ω then 0 else t := by
  have hs := adSurv_det wT idM (fun _ => false) (fun _ _ => rfl) (fun _ _ => rfl)
  cases ω <;> simp [hs, adSurv_zero', wKeepBad, misses, classRule]

theorem part_c1 : (Setup (fun _ : Bool => True) idM id (univ : Finset Bool) ∧
    AdTester ctrT ctrKeep ∧ AcceptsAllFlag ctrT idM ctrKeep 3 ∧
    (∀ h : Hist Bool Bool, misses h ≤ 1 → ctrKeep h = 1) ∧
    adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool))
        (classRule id id (3/4)) (seedPolicy (Z := Bool)) = 141/512 ∧
    (141/512 : ℝ) < 3/4 * (1 - 3/4 * (3 : ℝ) / ((2 : ℝ) * ((1 : ℝ) + 1))) ∧
    adProtocolCat (fun _ : Bool => True) idM ctrT ctrKeep 3 1 1 1 (seedLaw (univ : Finset Bool))
        (classRule id id (2/3)) (seedPolicy (Z := Bool)) = 26/81 ∧
    (26/81 : ℝ) < 2/3 * (1 - 2/3 * (3 : ℝ) / ((2 : ℝ) * ((1 : ℝ) + 1))) ∧
    min 1 ((2 : ℝ) * ((1 : ℝ) + 1) / (2 * 3)) = 2/3 ∧
    min (1/2) ((2 : ℝ) * ((1 : ℝ) + 1) / (4 * 3)) = 1/3) := by
  have hacc : ∀ h : Hist Bool Bool, (∀ e ∈ h, e.2.2 = false) → ctrKeep h = 1 := by
    intro h hh; unfold ctrKeep; rw [misses_allflag h hh]; simp
  have hT : ∀ h, IsDist (ctrT h) := fun h => det_dist (ctrQuery h)
  have hM : IsKernel idM := (setup_id idM (fun _ _ => rfl)).1
  refine ⟨setup_id idM (fun _ _ => rfl), ⟨hT, fun h => keep01 _⟩,
    part_s Bool Bool ctrT idM ctrKeep 3 hM hT hacc, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h hh; unfold ctrKeep; rw [if_pos hh]
  · rw [c1_risk]; norm_num
  · norm_num
  · rw [c1_risk]; norm_num
  · norm_num
  · norm_num
  · norm_num

theorem part_c2 : (Setup (fun _ : Fin 3 => True) idM3 id (univ : Finset (Fin 3)) ∧
    AdTester stT stKeep ∧ AcceptsAllFlag stT idM3 stKeep 3 ∧
    (∀ h : Hist (Fin 3) (Fin 3), misses h ≤ 1 → stKeep h = 1) ∧
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      adProtocolCat (fun _ : Fin 3 => True) idM3 stT stKeep 3 1 1 1 (seedLaw (univ : Finset (Fin 3)))
          (classRule id id t) (seedPolicy (Z := Fin 3)) = t - t ^ 3 + t ^ 4 / 3 ∧
      t - t ^ 3 + t ^ 4 / 3 < 1 / 2) ∧
    min (1/2) ((3 : ℝ) * ((1 : ℝ) + 1) / (4 * 3)) = 1/2 ∧
    (1 : ℝ) * (1 - 1 * (3 : ℝ) / ((3 : ℝ) * ((1 : ℝ) + 1))) = 1/2) := by
  have hacc : ∀ h : Hist (Fin 3) (Fin 3), (∀ e ∈ h, e.2.2 = false) → stKeep h = 1 := by
    intro h hh; unfold stKeep; rw [misses_allflag h hh]; simp
  have hT : ∀ h, IsDist (stT h) := fun h => det_dist (stQuery h)
  have hM : IsKernel idM3 := (setup_id idM3 (fun _ _ => rfl)).1
  refine ⟨setup_id idM3 (fun _ _ => rfl), ⟨hT, fun h => keep01 _⟩,
    part_s (Fin 3) (Fin 3) stT idM3 stKeep 3 hM hT hacc, ?_, ?_, ?_, ?_⟩
  · intro h hh; unfold stKeep; rw [if_pos hh]
  · intro t ht0 ht1
    exact ⟨c2_risk t, c2_bound t ht0 ht1⟩
  · norm_num
  · norm_num

theorem claim : PL_UMADAPTF1.Claim :=
  ⟨part_s, part_a, part_c1, part_c2⟩

theorem witness : PL_UMADAPTF1.Witness := by
  have hT : ∀ h, IsDist (wT h) := fun _ => det_dist false
  have hM : IsKernel idM := (setup_id idM (fun _ _ => rfl)).1
  have hacc : ∀ h : Hist Bool Bool, (∀ e ∈ h, e.2.2 = false) → wKeep h = 1 := by
    intro h hh; unfold wKeep; rw [misses_allflag h hh]; simp
  refine ⟨setup_id idM (fun _ _ => rfl), ⟨hT, fun h => keep01 _⟩,
    part_s Bool Bool wT idM wKeep 1 hM hT hacc, ?_, ?_, ⟨hT, fun h => ?_⟩, ?_, ?_⟩
  · norm_num
  · unfold adProtocolCat
    rw [Fintype.sum_bool]
    simp only [w_surv, cat_id1 idM (fun _ _ => rfl), seedLaw, Finset.mem_univ, if_true,
      Finset.card_univ, Fintype.card_bool, classRule, id]
    norm_num
  · unfold wKeepBad; split_ifs <;> norm_num
  · unfold AcceptsAllFlag
    have hs := adSurv_det wT idM (fun _ => false) (fun _ _ => rfl) (fun _ _ => rfl)
    simp [hs, adSurv_zero', wKeepBad, misses]
  · unfold adProtocolCat
    rw [Fintype.sum_bool]
    simp only [wbad_surv, cat_id1 idM (fun _ _ => rfl), seedLaw, Finset.mem_univ, if_true,
      Finset.card_univ, Fintype.card_bool, classRule, id]
    norm_num
