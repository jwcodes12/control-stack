open PL_UMADAPTF1
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
    adSurv ctrT idM (PL_UMLOWERF1.classRule id id t ω) ctrKeep 3 [] =
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
    adSurv stT idM3 (PL_UMLOWERF1.classRule id id t ω) stKeep 3 [] =
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
    adSurv wT idM (PL_UMLOWERF1.classRule id id t ω) wKeep 1 [] = if ω then 1 else 1 - t := by
  have hs := adSurv_det wT idM (fun _ => false) (fun _ _ => rfl) (fun _ _ => rfl)
  cases ω <;> simp [hs, adSurv_zero', wKeep, misses, classRule]

theorem wbad_surv (t : ℝ) (ω : Bool) :
    adSurv wT idM (PL_UMLOWERF1.classRule id id t ω) wKeepBad 1 [] = if ω then 0 else t := by
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

theorem claim1 : PL_UMADAPTF1.Claim :=
  ⟨part_s, part_a, part_c1, part_c2⟩

theorem witness1 : PL_UMADAPTF1.Witness := by
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


/-! Combinatorial core of the sharp balanced adaptive converse. -/

namespace SharpBalance

private def slope (b : ℝ) (n : ℕ) : ℝ := b ^ (n + 1) - b ^ n

private lemma slope_mono (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ {n k : ℕ}, n ≤ k → slope b n ≤ slope b k := by
  intro n k hnk
  have hp : b ^ k ≤ b ^ n := pow_le_pow_of_le_one hb0 hb1 hnk
  have hn : 0 ≤ b ^ n := pow_nonneg hb0 _
  have hc : b - 1 ≤ 0 := by linarith
  unfold slope
  rw [show n + 1 = Nat.succ n by omega, pow_succ,
      show k + 1 = Nat.succ k by omega, pow_succ]
  have hmul := mul_le_mul_of_nonpos_right hp hc
  nlinarith [hmul]

private lemma tangent_step (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (m q : ℕ) (hmq : m ≤ q) :
    b ^ (q + 1) + ((m : ℝ) - ((q + 1 : ℕ) : ℝ)) * slope b (q + 1) ≤
      b ^ q + ((m : ℝ) - (q : ℝ)) * slope b q := by
  have hmono := slope_mono b hb0 hb1 (n := q) (k := q + 1) (Nat.le_succ q)
  have hmq' : (m : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast (show m ≤ q + 1 by omega)
  have hc : 0 ≤ ((q + 1 : ℕ) : ℝ) - (m : ℝ) := by linarith
  have hprod := mul_le_mul_of_nonneg_left hmono hc
  have hp : b ^ (q + 1) = b ^ q + slope b q := by
    unfold slope
    ring
  have hcast : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by norm_num
  rw [hcast] at hprod ⊢
  rw [hp]
  nlinarith [hprod]

theorem balanced_bound (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m q : ℕ) :
    b ^ m ≥ b ^ q + ((m : ℝ) - (q : ℝ)) * (b ^ (q + 1) - b ^ q) := by
  by_cases hmq : m ≤ q
  · have h : ∀ q', m ≤ q' → b ^ m ≥ b ^ q' + ((m : ℝ) - (q' : ℝ)) * slope b q' := by
      intro q' hmq'
      exact Nat.le_induction
        (by simp [slope])
        (fun n hmn ih => (tangent_step b hb0 hb1 m n hmn).trans ih)
        q' hmq'
    have h' := h q hmq
    simpa [slope] using h'
  · have hqm : q ≤ m := Nat.le_of_not_ge hmq
    have h : ∀ m', q ≤ m' → b ^ m' ≥ b ^ q + ((m' : ℝ) - (q : ℝ)) * slope b q := by
      intro m' hqm'
      exact Nat.le_induction
        (by simp [slope])
        (fun n _ ih => by
          have hmono := slope_mono b hb0 hb1 (n := q) (k := n) (by omega)
          have hp : b ^ (n + 1) = b ^ n + slope b n := by
            unfold slope
            ring
          rw [hp]
          push_cast
          nlinarith [ih, hmono])
        m' hqm'
    have h' := h m hqm
    simpa [slope] using h'

theorem aggregate_balanced_budget (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (k q a : ℕ) (_hk : 0 < k) (ha : a < k)
    (counts : Fin k → ℕ)
    (hcounts : ∑ i : Fin k, counts i ≤ k * q + a) :
    ∑ i : Fin k, b ^ (counts i) ≥
      ((k - a : ℕ) : ℝ) * b ^ q + (a : ℝ) * b ^ (q + 1) := by
  let d : ℝ := b ^ (q + 1) - b ^ q
  have hd : d ≤ 0 := by
    dsimp [d]
    have hp : b ^ (q + 1) ≤ b ^ q := pow_le_pow_of_le_one hb0 hb1 (Nat.le_succ q)
    linarith
  have hpoint (i : Fin k) := balanced_bound b hb0 hb1 (counts i) q
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hsum' : (∑ i : Fin k, (b ^ q + ((counts i : ℝ) - (q : ℝ)) * d)) ≤
      ∑ i : Fin k, b ^ (counts i) := by
    simpa [d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  have hcastsum : (∑ i : Fin k, (counts i : ℝ)) = ((∑ i : Fin k, counts i : ℕ) : ℝ) := by
    simp
  have hsumformula : (∑ i : Fin k, (b ^ q + ((counts i : ℝ) - (q : ℝ)) * d)) =
      (k : ℝ) * b ^ q + (((∑ i : Fin k, counts i : ℕ) : ℝ) - (k : ℝ) * (q : ℝ)) * d := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hcastsum]
    simp
  have hupper : ((∑ i : Fin k, counts i : ℕ) : ℝ) ≤ (k : ℝ) * (q : ℝ) + (a : ℝ) := by
    exact_mod_cast hcounts
  have hcoef : (((∑ i : Fin k, counts i : ℕ) : ℝ) - (k : ℝ) * (q : ℝ)) ≤ (a : ℝ) := by
    have hmul : (k : ℝ) * (q : ℝ) = ((k * q : ℕ) : ℝ) := by norm_num
    rw [hmul]
    have hnat : ∑ i : Fin k, counts i ≤ k * q + a := hcounts
    have hcast : ((∑ i : Fin k, counts i : ℕ) : ℝ) ≤ ((k * q + a : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    linarith
  have hcoefmul := mul_le_mul_of_nonpos_right hcoef hd
  rw [hsumformula] at hsum'
  have haCast : ((k - a : ℕ) : ℝ) = (k : ℝ) - (a : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt ha)]
  rw [haCast]
  dsimp [d] at hcoefmul ⊢
  nlinarith [hsum', hcoefmul]

/-- With exactly `n` queries allocated among `k` classes, a balanced allocation
minimizes the sum of miss probabilities. -/
theorem aggregate_balanced_exact (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (k n : ℕ) (hk : 0 < k) (counts : Fin k → ℕ)
    (hcounts : ∑ i : Fin k, counts i = n) :
    ∑ i : Fin k, b ^ (counts i) ≥
      ((k - n % k : ℕ) : ℝ) * b ^ (n / k) + ((n % k : ℕ) : ℝ) * b ^ (n / k + 1) := by
  have ha : n % k < k := Nat.mod_lt _ hk
  have hn : (∑ i : Fin k, counts i) ≤ k * (n / k) + n % k := by
    have heq : n = n % k + k * (n / k) := (Nat.mod_add_div n k).symm
    calc
      ∑ i : Fin k, counts i = n := hcounts
      _ = n % k + k * (n / k) := heq
      _ = k * (n / k) + n % k := Nat.add_comm _ _
      _ ≤ k * (n / k) + n % k := le_rfl
  exact aggregate_balanced_budget b hb0 hb1 k (n / k) (n % k) hk ha counts hn

end SharpBalance


/-! Direct recursive proof layer for the sharp adaptive converse. It avoids an
explicit dependent `Path` type: all-FLAG prefixes are the histories already
used by `adSurv`, with decoder-class query counts tracked as a potential. -/

namespace SharpGeneric

open SharpBalance

abbrev SharpHist (X : Type) (Z : Type) := List (X × Z × Bool)

def passProb {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (t : ℝ)
    (ω : Fin k) (z : Z) : ℝ := if g z = some ω then t else 0

def classCount {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (h : SharpHist X Z) (ω : Fin k) : ℕ :=
  (h.filter (fun e => g e.2.1 = some ω)).length

theorem classCount_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) :
    classCount g (h ++ [(x, z, false)]) ω =
      classCount g h ω + (if g z = some ω then 1 else 0) := by
  by_cases hmatch : g z = some ω <;> simp [classCount, List.filter_append, List.filter_cons, hmatch]

theorem flagFactor {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (b : ℝ) (ω : Fin k) (z : Z) :
    1 - passProb g (1-b) ω z = if g z = some ω then b else 1 := by
  by_cases h : g z = some ω <;> simp [passProb, h]

noncomputable def fullSurv {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (t : ℝ) (keep : SharpHist X Z → ℝ) (ω : Fin k) :
    ℕ → SharpHist X Z → ℝ
  | 0, h => keep h
  | n + 1, h => ∑ x, T h x * ∑ z, M x z *
      (passProb g t ω z * fullSurv T M g t keep ω n (h ++ [(x,z,true)]) +
       (1 - passProb g t ω z) * fullSurv T M g t keep ω n (h ++ [(x,z,false)]))

theorem passProb_bounds {k : ℕ} {Z : Type} (g : Z → Option (Fin k)) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (ω : Fin k) (z : Z) :
    0 ≤ passProb g t ω z ∧ passProb g t ω z ≤ 1 := by
  by_cases h : g z = some ω
  · simp [passProb, h, ht0, ht1]
  · simp [passProb, h]

theorem fullSurv_nonneg {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) :
    ∀ n h ω, 0 ≤ fullSurv T M g t keep ω n h := by
  intro n
  induction n with
  | zero => intro h ω; simp [fullSurv, hk]
  | succ n ih =>
      intro h ω
      rw [fullSurv]
      apply Finset.sum_nonneg
      intro x _
      apply mul_nonneg (hT h x)
      apply Finset.sum_nonneg
      intro z _
      apply mul_nonneg (hM x z)
      obtain ⟨hp0, hp1⟩ := passProb_bounds g t ht0 ht1 ω z
      have htrue := ih (h ++ [(x,z,true)]) ω
      have hfalse := ih (h ++ [(x,z,false)]) ω
      exact add_nonneg (mul_nonneg hp0 htrue) (mul_nonneg (sub_nonneg.mpr hp1) hfalse)

noncomputable def flagOnly {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (t : ℝ) (keep : SharpHist X Z → ℝ) (ω : Fin k) :
    ℕ → SharpHist X Z → ℝ
  | 0, h => keep h
  | n + 1, h => ∑ x, T h x * ∑ z, M x z *
      (1 - passProb g t ω z) * flagOnly T M g t keep ω n (h ++ [(x,z,false)])

theorem fullSurv_ge_flagOnly {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z) :
    ∀ n h ω, flagOnly T M g t keep ω n h ≤ fullSurv T M g t keep ω n h := by
  intro n
  induction n with
  | zero => intro h ω; rfl
  | succ n ih =>
      intro h ω
      rw [flagOnly, fullSurv]
      apply Finset.sum_le_sum
      intro x _
      apply mul_le_mul_of_nonneg_left _ (hT h x)
      apply Finset.sum_le_sum
      intro z _
      obtain ⟨hp0, hp1⟩ := passProb_bounds g t ht0 ht1 ω z
      have hfalse := ih (h ++ [(x,z,false)]) ω
      have htrue := fullSurv_nonneg T M g t ht0 ht1 keep hk hT hM n
        (h ++ [(x,z,true)]) ω
      have hprod := mul_le_mul_of_nonneg_left hfalse (sub_nonneg.mpr hp1)
      have hnonneg := mul_nonneg hp0 htrue
      have hbracket :
          (1 - passProb g t ω z) * flagOnly T M g t keep ω n (h ++ [(x,z,false)]) ≤
          passProb g t ω z * fullSurv T M g t keep ω n (h ++ [(x,z,true)]) +
            (1 - passProb g t ω z) * fullSurv T M g t keep ω n (h ++ [(x,z,false)]) := by
        nlinarith
      calc
        M x z * (1 - passProb g t ω z) *
            flagOnly T M g t keep ω n (h ++ [(x,z,false)]) =
          M x z * ((1 - passProb g t ω z) *
            flagOnly T M g t keep ω n (h ++ [(x,z,false)])) := by ring
        _ ≤ M x z * (passProb g t ω z *
              fullSurv T M g t keep ω n (h ++ [(x,z,true)]) +
            (1 - passProb g t ω z) *
              fullSurv T M g t keep ω n (h ++ [(x,z,false)])) :=
          mul_le_mul_of_nonneg_left hbracket (hM x z)

noncomputable def refSurv {X : Type} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (keep : SharpHist X Z → ℝ) : ℕ → SharpHist X Z → ℝ
  | 0, h => keep h
  | n + 1, h => ∑ x, T h x * ∑ z, M x z *
      refSurv T M keep n (h ++ [(x,z,false)])

theorem refSurv_eq_fullSurv_zero {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (keep : SharpHist X Z → ℝ) :
    ∀ n h ω, refSurv T M keep n h = fullSurv T M g 0 keep ω n h := by
  intro n
  induction n with
  | zero => intro h ω; rfl
  | succ n ih =>
      intro h ω
      rw [refSurv, fullSurv]
      apply Finset.sum_congr rfl
      intro x _
      apply congrArg (T h x * ·)
      apply Finset.sum_congr rfl
      intro z _
      have hz : passProb g 0 ω z = 0 := by simp [passProb]
      rw [hz, ih]
      ring

noncomputable def weightedFlag {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (b : ℝ) (keep : SharpHist X Z → ℝ) :
    ℕ → SharpHist X Z → ℝ
  | n, h => ∑ ω : Fin k,
      b ^ (classCount g h ω) * flagOnly T M g (1-b) keep ω n h

theorem classPower_append_flag {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (b : ℝ) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) :
    b ^ classCount g h ω * (if g z = some ω then b else 1) =
      b ^ classCount g (h ++ [(x,z,false)]) ω := by
  rw [classCount_append_flag]
  by_cases hmatch : g z = some ω <;> simp [hmatch, pow_succ]

private theorem weightedFactor_append {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (b : ℝ) (h : SharpHist X Z) (x : X) (z : Z) (ω : Fin k) (f : ℝ) :
    b ^ classCount g (h ++ [(x,z,false)]) ω * f =
      b ^ classCount g h ω * ((1 - passProb g (1-b) ω z) * f) := by
  rw [flagFactor]
  by_cases hm : g z = some ω
  · have hc := classCount_append_flag g h x z ω
    rw [hc, if_pos hm]
    simp only [if_pos hm]
    rw [pow_succ]
    ring
  · have hc := classCount_append_flag g h x z ω
    rw [hc, if_neg hm]
    simp only [if_neg hm]
    simp

theorem weighted_double_sum {α β : Type} [Fintype α] [Fintype β]
    (a : α → ℝ) (c : β → ℝ) (f : α → β → ℝ) :
    (∑ i, a i * ∑ j, c j * f i j) =
      ∑ j, c j * ∑ i, a i * f i j := by
  calc
    (∑ i, a i * ∑ j, c j * f i j) =
        ∑ i, ∑ j, a i * (c j * f i j) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
    _ = ∑ j, ∑ i, a i * (c j * f i j) := by
          rw [Finset.sum_comm]
    _ = ∑ j, c j * ∑ i, a i * f i j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

theorem weightedFlag_succ {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (b : ℝ) (keep : SharpHist X Z → ℝ)
    (n : ℕ) (h : SharpHist X Z) :
    weightedFlag T M g b keep (n+1) h =
      ∑ x, T h x * ∑ z, M x z *
        weightedFlag T M g b keep n (h ++ [(x,z,false)]) := by
  simp only [weightedFlag, flagOnly, mul_assoc]
  calc
    (∑ ω : Fin k, b ^ classCount g h ω *
      ∑ x : X, T h x * ∑ z : Z, M x z *
        ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
          (h ++ [(x,z,false)])))
      = ∑ ω : Fin k, ∑ x : X,
          b ^ classCount g h ω * T h x * ∑ z : Z, M x z *
            ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
              (h ++ [(x,z,false)])) := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ∑ x : X, ∑ ω : Fin k,
          b ^ classCount g h ω * T h x * ∑ z : Z, M x z *
            ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
              (h ++ [(x,z,false)])) := by
          let F : Fin k → X → ℝ := fun ω x =>
            b ^ classCount g h ω * T h x * ∑ z : Z, M x z *
              ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                (h ++ [(x,z,false)]))
          simpa [F] using
            (Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := F))
    _ = ∑ x : X, T h x * ∑ z : Z, M x z *
          ∑ ω : Fin k, b ^ classCount g h ω *
            ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
              (h ++ [(x,z,false)])) := by
          apply Finset.sum_congr rfl
          intro x _
          calc
            (∑ ω : Fin k, b ^ classCount g h ω * T h x *
              ∑ z : Z, M x z *
                ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                  (h ++ [(x,z,false)])))
              = T h x * ∑ ω : Fin k, b ^ classCount g h ω *
                  ∑ z : Z, M x z *
                    ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                      (h ++ [(x,z,false)])) := by
                    calc
                      _ = ∑ ω : Fin k,
                          (b ^ classCount g h ω *
                            ∑ z : Z, M x z *
                              ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                                (h ++ [(x,z,false)]))) * T h x := by
                              apply Finset.sum_congr rfl
                              intro ω _
                              ring
                      _ = (∑ ω : Fin k, b ^ classCount g h ω *
                            ∑ z : Z, M x z *
                              ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                                (h ++ [(x,z,false)]))) * T h x := by rw [Finset.sum_mul]
                      _ = T h x * ∑ ω : Fin k, b ^ classCount g h ω *
                            ∑ z : Z, M x z *
                              ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                                (h ++ [(x,z,false)])) := by ring
            _ = T h x * ∑ z : Z, M x z * ∑ ω : Fin k,
                  b ^ classCount g h ω *
                    ((1 - passProb g (1-b) ω z) * flagOnly T M g (1-b) keep ω n
                      (h ++ [(x,z,false)])) := by
                    exact congrArg (T h x * ·)
                      (weighted_double_sum (fun ω => b ^ classCount g h ω)
                        (fun z => M x z)
                        (fun ω z => (1 - passProb g (1-b) ω z) *
                          flagOnly T M g (1-b) keep ω n (h ++ [(x,z,false)])))
    _ = ∑ x : X, T h x * ∑ z : Z, M x z *
          weightedFlag T M g b keep n (h ++ [(x,z,false)]) := by
          apply Finset.sum_congr rfl
          intro x _
          apply congrArg (T h x * ·)
          apply Finset.sum_congr rfl
          intro z _
          apply congrArg (M x z * ·)
          rw [weightedFlag]
          apply Finset.sum_congr rfl
          intro ω _
          rw [flagFactor, ← mul_assoc, classPower_append_flag]

theorem count_sum_le {X : Type} {k : ℕ} {Z : Type} (g : Z → Option (Fin k))
    (h : SharpHist X Z) :
    (∑ ω : Fin k, classCount g h ω) ≤ h.length := by
  induction h with
  | nil => simp [classCount]
  | cons e h ih =>
      have hrec : ∀ ω, classCount g (e :: h) ω =
          (if g e.2.1 = some ω then 1 else 0) + classCount g h ω := by
        intro ω
        by_cases heq : g e.2.1 = some ω
        · simp [classCount, heq]
          omega
        · simp [classCount, heq]
      rw [Finset.sum_congr rfl (fun ω _ => hrec ω)]
      rw [Finset.sum_add_distrib]
      have hdelta : (∑ ω : Fin k, if g e.2.1 = some ω then 1 else 0) ≤ 1 := by
        classical
        by_cases hex : ∃ i, g e.2.1 = some i
        · obtain ⟨i, hi⟩ := hex
          have hone : (∑ ω : Fin k, if g e.2.1 = some ω then 1 else 0) = 1 := by
            rw [Finset.sum_eq_single i]
            · simp [hi]
            · intro ω _ hω
              have hne : g e.2.1 ≠ some ω := by
                intro heq
                apply hω
                exact (Option.some.inj (hi.symm.trans heq)).symm
              simp [hne]
            · simp
          rw [hone]
        · have hnone : ∀ i, g e.2.1 ≠ some i := by
            intro i hi
            exact hex ⟨i, hi⟩
          simp [hnone]
      have hsumle := Nat.add_le_add hdelta ih
      simpa [List.length_cons, Nat.add_comm] using hsumle

noncomputable def balancedTarget (k n : ℕ) (b : ℝ) : ℝ :=
    ((k - n % k : ℕ) : ℝ) * b ^ (n / k) +
      ((n % k : ℕ) : ℝ) * b ^ (n / k + 1)

/-- All-FLAG reference histories retain the sharp balanced mass. -/
theorem weightedFlag_lower {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (g : Z → Option (Fin k)) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (N : ℕ) :
    ∀ n h, h.length + n = N →
      balancedTarget k N b * refSurv T M keep n h ≤ weightedFlag T M g b keep n h := by
  intro n
  induction n with
  | zero =>
      intro h hlen
      have hsum := count_sum_le g h
      have hcounts : ∑ ω : Fin k, classCount g h ω ≤ N := by omega
      let counts : Fin k → ℕ := fun ω => classCount g h ω
      have hb := aggregate_balanced_budget
        b hb0 hb1 k (N / k) (N % k) hkpos (Nat.mod_lt N hkpos) counts
        (by
          calc
            ∑ ω : Fin k, counts ω ≤ N := by simpa [counts] using hcounts
            _ = N % k + k * (N / k) := (Nat.mod_add_div N k).symm
            _ = k * (N / k) + N % k := Nat.add_comm _ _)
      simp [weightedFlag, flagOnly, refSurv]
      dsimp [balancedTarget]
      have hk' := hk h
      have hsumPow : ∑ ω : Fin k, b ^ classCount g h ω = ∑ ω : Fin k, b ^ counts ω := by
        simp [counts]
      rw [← Finset.sum_mul, hsumPow]
      exact mul_le_mul_of_nonneg_right hb hk'
  | succ n ih =>
      intro h hlen
      rw [weightedFlag_succ, refSurv]
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x _
      calc
        balancedTarget k N b *
            (T h x * ∑ z, M x z * refSurv T M keep n (h ++ [(x,z,false)]))
          = T h x * ∑ z, M x z *
              (balancedTarget k N b * refSurv T M keep n (h ++ [(x,z,false)])) := by
                calc
                  _ = T h x * (balancedTarget k N b *
                      ∑ z, M x z * refSurv T M keep n (h ++ [(x,z,false)])) := by ring
                  _ = T h x * ∑ z, balancedTarget k N b *
                      (M x z * refSurv T M keep n (h ++ [(x,z,false)])) := by
                        rw [Finset.mul_sum]
                  _ = T h x * ∑ z, M x z *
                      (balancedTarget k N b * refSurv T M keep n (h ++ [(x,z,false)])) := by
                        congr 1
                        apply Finset.sum_congr rfl
                        intro z _
                        ring
        _ ≤ T h x * ∑ z, M x z *
              weightedFlag T M g b keep n (h ++ [(x,z,false)]) := by
                apply mul_le_mul_of_nonneg_left _ (hT h x)
                apply Finset.sum_le_sum
                intro z _
                apply mul_le_mul_of_nonneg_left _ (hM x z)
                apply ih
                simp [List.length_append] at hlen ⊢
                omega

/-- Sharp aggregate survival under an all-FLAG acceptance contract. The decoder
may return `none` on views outside the seed classes. -/
theorem sharp_survival {X : Type} {k : ℕ} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (g : Z → Option (Fin k))
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (n : ℕ)
    (hacc : refSurv T M keep n [] = 1) :
    balancedTarget k n (1-t) ≤
      ∑ ω : Fin k, fullSurv T M g t keep ω n [] := by
  have hb0 : 0 ≤ 1-t := by linarith
  have hb1 : 1-t ≤ 1 := by linarith
  have hcore := weightedFlag_lower T M g (1-t) hb0 hb1 keep hk hT hM hkpos n
    n [] (by simp)
  rw [hacc] at hcore
  have hroot : weightedFlag T M g (1-t) keep n [] =
      ∑ ω : Fin k, flagOnly T M g t keep ω n [] := by
    simp [weightedFlag, classCount]
  have hflag := calc
      balancedTarget k n (1-t) ≤ weightedFlag T M g (1-t) keep n [] := by
        simpa using hcore
      _ = ∑ ω : Fin k, flagOnly T M g t keep ω n [] := hroot
  have hfull : (∑ ω : Fin k, flagOnly T M g t keep ω n []) ≤
      ∑ ω : Fin k, fullSurv T M g t keep ω n [] := by
    apply Finset.sum_le_sum
    intro ω _
    exact fullSurv_ge_flagOnly T M g t ht0 ht1 keep hk hT hM n [] ω
  exact hflag.trans hfull

/-- Uniform seed averaging turns the sharp survival sum into a risk bound,
assuming each seed has deployment catastrophe probability at least `t`. -/
theorem sharp_uniform_cat {k : ℕ} (hkpos : 0 < k) (t : ℝ) (ht0 : 0 ≤ t)
    (n : ℕ) (surv cat : Fin k → ℝ)
    (hsurv : ∀ i, 0 ≤ surv i)
    (hcat : ∀ i, t ≤ cat i)
    (hsum : balancedTarget k n (1-t) ≤ ∑ i : Fin k, surv i) :
    (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
      (1 / (k : ℝ)) * ∑ i : Fin k, surv i * cat i := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hkpos
  have hrec : ∀ i : Fin k, t * surv i ≤ surv i * cat i := by
    intro i
    calc
      t * surv i ≤ cat i * surv i := mul_le_mul_of_nonneg_right (hcat i) (hsurv i)
      _ = surv i * cat i := by ring
  have hsumcat : t * ∑ i : Fin k, surv i ≤ ∑ i : Fin k, surv i * cat i := by
    calc
      t * ∑ i : Fin k, surv i = ∑ i : Fin k, t * surv i := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin k, surv i * cat i := Finset.sum_le_sum (fun i _ => hrec i)
  have hscale := mul_le_mul_of_nonneg_left hsumcat (by positivity : 0 ≤ (1 / (k : ℝ)))
  have htarg : (t / (k : ℝ)) * balancedTarget k n (1-t) =
      (1 / (k : ℝ)) * (t * balancedTarget k n (1-t)) := by ring
  have hsrhs : (1 / (k : ℝ)) * (t * ∑ i : Fin k, surv i) ≤
      (1 / (k : ℝ)) * ∑ i : Fin k, surv i * cat i := hscale
  calc
    (t / (k : ℝ)) * balancedTarget k n (1-t) =
        (1 / (k : ℝ)) * (t * balancedTarget k n (1-t)) := htarg
    _ ≤ (1 / (k : ℝ)) * (t * ∑ i : Fin k, surv i) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (1 / (k : ℝ)))
      exact mul_le_mul_of_nonneg_left hsum ht0
    _ ≤ (1 / (k : ℝ)) * ∑ i : Fin k, surv i * cat i := hsrhs

/-- Index the unique seed class matched by a decoder output; unmatched outputs map to None. -/
noncomputable def seedDecoder {X C Z : Type} [DecidableEq C] {k : ℕ}
    (seed : Fin k → X) (c : X → C) (g : Z → C) (z : Z) : Option (Fin k) := by
  classical
  exact if h : ∃ i, g z = c (seed i) then some (Classical.choose h) else none

theorem seedDecoder_eq_some_iff {X C Z : Type} [DecidableEq C] {k : ℕ}
    (seed : Fin k → X) (c : X → C) (g : Z → C)
    (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (z : Z) (i : Fin k) :
    seedDecoder seed c g z = some i ↔ g z = c (seed i) := by
  classical
  by_cases hex : ∃ j, g z = c (seed j)
  · let j := Classical.choose hex
    have hj := Classical.choose_spec hex
    unfold seedDecoder
    rw [dif_pos hex]
    constructor
    · intro hs
      have hji : Classical.choose hex = i := Option.some.inj hs
      subst i
      exact hj
    · intro hi
      congr 1
      apply hinj
      exact hj.symm.trans hi
  · unfold seedDecoder
    rw [dif_neg hex]
    constructor
    · intro h; cases h
    · intro hi
      exact False.elim (hex ⟨i, hi⟩)

def classPass {X C Z : Type} [DecidableEq C]
    (c : X → C) (g : Z → C) (t : ℝ) (x : X) (z : Z) : ℝ :=
  if g z = c x then t else 0

theorem seedDecoder_pass_eq {X C Z : Type} [DecidableEq C] {k : ℕ}
    (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ)
    (hinj : ∀ i j, c (seed i) = c (seed j) → i = j) (i : Fin k) (z : Z) :
    passProb (seedDecoder seed c g) t i z = classPass c g t (seed i) z := by
  by_cases h : g z = c (seed i)
  · have hd := (seedDecoder_eq_some_iff seed c g hinj z i).2 h
    simp [passProb, classPass, hd, h]
  · have hd : seedDecoder seed c g z ≠ some i := by
      intro hd
      exact h ((seedDecoder_eq_some_iff seed c g hinj z i).1 hd)
    simp [passProb, classPass, hd, h]


noncomputable def passSurv {X : Type} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ)
    (keep : SharpHist X Z → ℝ) : ℕ → SharpHist X Z → ℝ
  | 0, h => keep h
  | n + 1, h => ∑ x, T h x * ∑ z, M x z *
      (φ z * passSurv T M φ keep n (h ++ [(x,z,true)]) +
       (1-φ z) * passSurv T M φ keep n (h ++ [(x,z,false)]))

theorem refSurv_eq_passSurv_zero {X : Type} {Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) :
    ∀ n h, refSurv T M keep n h = passSurv T M (fun _ => 0) keep n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      rw [refSurv, passSurv]
      apply Finset.sum_congr rfl
      intro x _
      apply congrArg (T h x * ·)
      apply Finset.sum_congr rfl
      intro z _
      rw [ih (h ++ [(x,z,false)])]
      ring

theorem fullSurv_eq_passSurv_seed {X C Z : Type} [DecidableEq C]
    [Fintype X] [Fintype Z] {k : ℕ}
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (seed : Fin k → X) (c : X → C) (g : Z → C) (t : ℝ)
    (hinj : ∀ i j, c (seed i) = c (seed j) → i = j)
    (keep : SharpHist X Z → ℝ) (i : Fin k) :
    ∀ n h, fullSurv T M (seedDecoder seed c g) t keep i n h =
      passSurv T M (classPass c g t (seed i)) keep n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      rw [fullSurv, passSurv]
      apply Finset.sum_congr rfl
      intro x _
      apply congrArg (T h x * ·)
      apply Finset.sum_congr rfl
      intro z _
      rw [seedDecoder_pass_eq seed c g t hinj i z]
      rw [ih (h ++ [(x,z,true)]), ih (h ++ [(x,z,false)])]

theorem sharp_seedset_survival {X C Z : Type} [DecidableEq C]
    [Fintype X] [Fintype Z] {k : ℕ}
    (S : Finset X) (e : Fin k ≃ {x // x ∈ S})
    (c : X → C) (g : Z → C)
    (hinjS : Set.InjOn c (S : Set X))
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (n : ℕ)
    (hacc : refSurv T M keep n [] = 1) :
    balancedTarget k n (1-t) ≤
      ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n [] := by
  have hclass : ∀ i j, c ((e i).val) = c ((e j).val) → i = j := by
    intro i j hij
    have hx : (e i).val = (e j).val :=
      hinjS (e i).property (e j).property hij
    apply e.injective
    exact Subtype.ext hx
  let dec : Z → Option (Fin k) := seedDecoder (fun i => (e i).val) c g
  have hsurv := sharp_survival T M dec t ht0 ht1 keep hk hT hM hkpos n hacc
  calc
    balancedTarget k n (1-t) ≤
        ∑ i : Fin k, fullSurv T M dec t keep i n [] := hsurv
    _ = ∑ i : Fin k, passSurv T M (classPass c g t ((e i).val)) keep n [] := by
        apply Finset.sum_congr rfl
        intro i _
        exact fullSurv_eq_passSurv_seed T M (fun i => (e i).val) c g t hclass keep i n []

theorem sharp_seedset_catRisk {X C Z : Type} [DecidableEq C]
    [Fintype X] [Fintype Z] {k : ℕ}
    (S : Finset X) (e : Fin k ≃ {x // x ∈ S})
    (c : X → C) (g : Z → C)
    (hinjS : Set.InjOn c (S : Set X))
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (n : ℕ)
    (hacc : refSurv T M keep n [] = 1)
    (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) :
    (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
      (1 / (k : ℝ)) * ∑ i : Fin k,
        passSurv T M (classPass c g t ((e i).val)) keep n [] * cat i := by
  let surv : Fin k → ℝ := fun i => passSurv T M (classPass c g t ((e i).val)) keep n []
  have hsum : balancedTarget k n (1-t) ≤ ∑ i : Fin k, surv i := by
    simpa [surv] using sharp_seedset_survival S e c g hinjS T M t ht0 ht1 keep hk hT hM hkpos n hacc
  have hnonneg : ∀ i, 0 ≤ surv i := by
    intro i
    have hclass : ∀ i j, c ((e i).val) = c ((e j).val) → i = j := by
      intro i j hij
      have hx : (e i).val = (e j).val :=
        hinjS (e i).property (e j).property hij
      apply e.injective
      exact Subtype.ext hx
    let dec : Z → Option (Fin k) := seedDecoder (fun i => (e i).val) c g
    have hfull := fullSurv_nonneg T M dec t ht0 ht1 keep hk hT hM n [] i
    have heq := fullSurv_eq_passSurv_seed T M (fun i => (e i).val) c g t hclass keep i n []
    simpa [surv] using heq ▸ hfull
  exact sharp_uniform_cat hkpos t ht0 n surv cat hnonneg hcat hsum

noncomputable def seedEquiv {X : Type} (S : Finset X) (k : ℕ)
    (hcard : S.card = k) : Fin k ≃ {x // x ∈ S} :=
  (S.equivFinOfCardEq hcard).symm


end SharpGeneric


/-! Integration interface for the adaptive collusion theorem. The definitions
below have the same recursions as PL_UMADAPTF1.adSurv and classRule; this module
keeps the sharp combinatorial argument independently importable in this Lake project. -/

namespace SharpUM

open SharpGeneric

noncomputable def adSurv {X Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (φ : Z → ℝ)
    (keep : SharpHist X Z → ℝ) : ℕ → SharpHist X Z → ℝ :=
  passSurv T M φ keep

def classRule {X C Z : Type} [DecidableEq C]
    (c : X → C) (g : Z → C) (t : ℝ) (x : X) (z : Z) : ℝ :=
  classPass c g t x z

theorem adSurv_reference_eq {X Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) :
    ∀ n h, refSurv T M keep n h = adSurv T M (fun _ => 0) keep n h := by
  intro n h
  exact refSurv_eq_passSurv_zero T M keep n h

theorem accepts_all_flag_reference {X Z : Type} [Fintype X] [Fintype Z]
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ) (keep : SharpHist X Z → ℝ) (n : ℕ)
    (hacc : adSurv T M (fun _ => 0) keep n [] = 1) :
    refSurv T M keep n [] = 1 := by
  rw [adSurv_reference_eq]
  exact hacc

/-- Uniform-seed sharp converse with the contract written in the same
all-FLAG survival form as AcceptsAllFlag. `cat i ≥ t` is the deployment lower
bound supplied by the protocol/colluder lemma. -/
theorem sharp_uniform_seed_risk {X C Z : Type} [DecidableEq C]
    [Fintype X] [Fintype Z] {k : ℕ}
    (S : Finset X) (e : Fin k ≃ {x // x ∈ S})
    (c : X → C) (g : Z → C)
    (hinjS : Set.InjOn c (S : Set X))
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (n : ℕ)
    (hacc : adSurv T M (fun _ => 0) keep n [] = 1)
    (cat : Fin k → ℝ) (hcat : ∀ i, t ≤ cat i) :
    (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
      (1 / (k : ℝ)) * ∑ i : Fin k,
        adSurv T M (classRule c g t ((e i).val)) keep n [] * cat i := by
  have href : refSurv T M keep n [] = 1 :=
    accepts_all_flag_reference T M keep n hacc
  have h := sharp_seedset_catRisk S e c g hinjS T M t ht0 ht1 keep hk hT hM
    hkpos n href cat hcat
  change (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
    (1 / (k : ℝ)) * ∑ i : Fin k,
      passSurv T M (classPass c g t ((e i).val)) keep n [] * cat i
  exact h

noncomputable def seedLawModel {X : Type} [DecidableEq X]
    (S : Finset X) (x : X) : ℝ := if x ∈ S then 1 / (S.card : ℝ) else 0

noncomputable def protocolCatModel {X : Type} [Fintype X] [DecidableEq X]
    (S : Finset X) (surv cat : X → ℝ) : ℝ :=
  ∑ x, seedLawModel S x * surv x * cat x

theorem protocolCatModel_eq {X : Type} [Fintype X] [DecidableEq X]
    (S : Finset X) (surv cat : X → ℝ) :
    protocolCatModel S surv cat =
      (1 / (S.card : ℝ)) * ∑ x : {x // x ∈ S}, surv x.val * cat x.val := by
  classical
  unfold protocolCatModel seedLawModel
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_mem_eq]
  calc
    (∑ x ∈ S, 1 / (S.card : ℝ) * surv x * cat x) =
        ∑ x ∈ S, (1 / (S.card : ℝ)) * (surv x * cat x) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ = (1 / (S.card : ℝ)) * ∑ x ∈ S, surv x * cat x := by rw [Finset.mul_sum]
    _ = (1 / (S.card : ℝ)) * ∑ x : {x // x ∈ S}, surv x.val * cat x.val := by
      congr 1
      exact Finset.sum_subtype (s := S) (h := fun _ => Iff.rfl)
        (f := fun x => surv x * cat x)

theorem sum_finEquiv_eq_sum_seed {X : Type} {k : ℕ} (S : Finset X)
    (e : Fin k ≃ {x // x ∈ S}) (f : {x // x ∈ S} → ℝ) :
    (∑ i : Fin k, f (e i)) = ∑ x : {x // x ∈ S}, f x := e.sum_comp f

theorem sharp_uniform_adProtocolCatModel {X C Z : Type} [DecidableEq C]
    [Fintype X] [Fintype Z] [DecidableEq X] {k : ℕ}
    (S : Finset X) (e : Fin k ≃ {x // x ∈ S})
    (c : X → C) (g : Z → C)
    (hinjS : Set.InjOn c (S : Set X))
    (T : SharpHist X Z → X → ℝ) (M : X → Z → ℝ)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (keep : SharpHist X Z → ℝ) (hk : ∀ h, 0 ≤ keep h)
    (hT : ∀ h x, 0 ≤ T h x) (hM : ∀ x z, 0 ≤ M x z)
    (hkpos : 0 < k) (n : ℕ)
    (hacc : adSurv T M (fun _ => 0) keep n [] = 1)
    (cat : X → ℝ) (hcat : ∀ x ∈ S, t ≤ cat x) :
    (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
      protocolCatModel S
        (fun x => adSurv T M (classRule c g t x) keep n []) cat := by
  let catI : Fin k → ℝ := fun i => cat (e i).val
  have hcatI : ∀ i, t ≤ catI i := fun i => hcat (e i).val (e i).property
  have hbound := sharp_uniform_seed_risk S e c g hinjS T M t ht0 ht1 keep hk hT hM
    hkpos n hacc catI hcatI
  have hreindex : (∑ i : Fin k,
      passSurv T M (classPass c g t ((e i).val)) keep n [] * catI i) =
      ∑ x : {x // x ∈ S},
        passSurv T M (classPass c g t x.val) keep n [] * cat x.val := by
    exact e.sum_comp (fun x : {x // x ∈ S} =>
      passSurv T M (classPass c g t x.val) keep n [] * cat x.val)
  have hmodel := protocolCatModel_eq S
    (fun x => passSurv T M (classPass c g t x) keep n []) cat
  have hkcard : S.card = k := by
    have hc := Fintype.card_congr e
    simpa using hc.symm
  have hkcast : (S.card : ℝ) = (k : ℝ) := by exact_mod_cast hkcard
  rw [hkcast] at hmodel
  change (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
    (1 / (k : ℝ)) * ∑ i : Fin k,
      passSurv T M (classPass c g t ((e i).val)) keep n [] * catI i at hbound
  rw [hreindex] at hbound
  change (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
    protocolCatModel S
      (fun x => passSurv T M (classPass c g t x) keep n []) cat
  calc
    (t / (k : ℝ)) * balancedTarget k n (1-t) ≤
        (1 / (k : ℝ)) * ∑ x : {x // x ∈ S},
          passSurv T M (classPass c g t x.val) keep n [] * cat x.val := hbound
    _ = protocolCatModel S
        (fun x => passSurv T M (classPass c g t x) keep n []) cat := hmodel.symm

end SharpUM



open SharpUM SharpGeneric SharpBalance

theorem sharp_surv_eq_campaign {X Z : Type} [Fintype X] [Fintype Z]
    (T : _root_.PL_UMPROTF1.Hist X Z → X → ℝ) (M : X → Z → ℝ)
    (φ : Z → ℝ) (keep : _root_.PL_UMPROTF1.Hist X Z → ℝ) :
    ∀ n h, SharpUM.adSurv T M φ keep n h =
      _root_.PL_UMADAPTF1.adSurv T M φ keep n h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
      intro h
      simp only [SharpGeneric.passSurv, _root_.PL_UMADAPTF1.adSurv]
      have ih' : ∀ h : SharpHist X Z,
          SharpGeneric.passSurv T M φ keep n h = _root_.PL_UMADAPTF1.adSurv T M φ keep n h := by
        intro h
        simpa [SharpUM.adSurv] using ih h
      apply Finset.sum_congr rfl
      intro x _
      apply congrArg (T h x * ·)
      apply Finset.sum_congr rfl
      intro z _
      rw [ih' (h ++ [(x,z,true)]), ih' (h ++ [(x,z,false)])]

 theorem conv_a_sharp {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq X] [DecidableEq C]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (S : Finset X)
    (hM : IsKernel M) (hbad : ∀ x ∈ S, Bad x) (hinj : Set.InjOn c (S : Set X))
    (hS : 0 < S.card) (g : Z → C) (hg : ∀ x z, M x z ≠ 0 → g z = c x)
    (n : ℕ) (T : Hist X Z → X → ℝ) (keep : Hist X Z → ℝ)
    (hTk : AdTester T keep) (hacc : AcceptsAllFlag T M keep n)
    (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (r : ℝ) (b N : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hN : 1 ≤ N) :
    (t / (S.card : ℝ)) *
      balancedTarget S.card n (1-t) ≤
      adProtocolCat Bad M T keep n r b N (seedLaw S) (_root_.PL_UMLOWERF1.classRule c g t)
        (seedPolicy (Z := Z)) := by
  rcases hTk with ⟨hT, hk⟩
  have hT0 : ∀ h x, 0 ≤ T h x := fun h x => (hT h).1 x
  have hkeep0 : ∀ h, 0 ≤ keep h := fun h => (hk h).1
  have hM0 : ∀ x z, 0 ≤ M x z := fun x z => (hM x).1 z
  have hkpos : 0 < S.card := hS
  let e : Fin S.card ≃ {x // x ∈ S} := SharpGeneric.seedEquiv S S.card rfl
  have hacc' : SharpUM.adSurv T M (fun _ => 0) keep n [] = 1 := by
    unfold AcceptsAllFlag at hacc
    rw [sharp_surv_eq_campaign T M (fun _ => 0) keep n []]
    exact hacc
  have hrule : ∀ x, IsRule (_root_.PL_UMLOWERF1.classRule c g t x) :=
    classRule_rule c g t ht0 ht1
  have hcat : ∀ x ∈ S,
      t ≤ _root_.PL_UMPROTF1.cat Bad M (SharpUM.classRule c g t x)
        (seedPolicy (Z := Z) x) r b N 0 [] := by
    intro x hx
    have hcat0 := _root_.PLDep_UMLOWERF1.cat_ge Bad M (_root_.PL_UMLOWERF1.classRule c g t x) r b N x
      hM (hrule x) hr1 hN (hbad x hx)
    have hpass := _root_.PLDep_UMLOWERF1.pass_eq M c g hM hg t x x
    have hpass' : ∑ z, M x z * _root_.PL_UMLOWERF1.classRule c g t x z = t := by
      simpa [_root_.PL_UMLOWERF1.classRule] using hpass
    rw [hpass'] at hcat0
    exact hcat0
  let cat : X → ℝ := fun x =>
    _root_.PL_UMPROTF1.cat Bad M (SharpUM.classRule c g t x) (seedPolicy (Z := Z) x) r b N 0 []
  have hcat' : ∀ x ∈ S, t ≤ cat x := hcat
  have hmain := SharpUM.sharp_uniform_adProtocolCatModel S e c g hinj T M t ht0 ht1
    keep hkeep0 hT0 hM0 hkpos n hacc' cat hcat'
  have hclass : ∀ x, SharpUM.classRule c g t x = _root_.PL_UMLOWERF1.classRule c g t x := by
    intro x
    rfl
  have hmodel :
      SharpUM.protocolCatModel S
        (fun x => SharpUM.adSurv T M (SharpUM.classRule c g t x) keep n []) cat =
      adProtocolCat Bad M T keep n r b N (seedLaw S) (_root_.PL_UMLOWERF1.classRule c g t)
        (seedPolicy (Z := Z)) := by
    classical
    unfold SharpUM.protocolCatModel SharpUM.seedLawModel
    unfold _root_.PL_UMADAPTF1.adProtocolCat _root_.PL_UMLOWERF1.seedLaw
    apply Finset.sum_congr rfl
    intro x _
    simp only [hclass x, cat]
    rw [sharp_surv_eq_campaign T M (_root_.PL_UMLOWERF1.classRule c g t x) keep n []]
  rw [hmodel] at hmain
  simpa [cat, SharpUM.classRule, SharpGeneric.classPass, _root_.PL_UMLOWERF1.classRule] using hmain



theorem sharpTarget_eq (k n : ℕ) (b : ℝ) :
    PL_UMADAPTF2.sharpTarget k n b = balancedTarget k n b := rfl

theorem claim : PL_UMADAPTF2.Claim := by
  intro X Z C _ _ _ _ Bad _ M c S hset
  obtain ⟨hM, hcp, hbad, hinj, hS⟩ := hset
  obtain ⟨g, hg⟩ := hcp
  refine ⟨g, hg, ?_⟩
  intro n T keep hTk hacc t ht0 ht1 r b N hr0 hr1 hN
  rw [sharpTarget_eq]
  exact conv_a_sharp Bad M c S hM hbad hinj hS g hg n T keep hTk hacc t ht0 ht1 r b N hr0 hr1 hN

theorem rr_surv (t : ℝ) (ω : Bool) :
    PL_UMADAPTF1.adSurv rrT idM (PL_UMLOWERF1.classRule id id t ω) rrKeep 3 [] = if ω then 1 - t else (1 - t) ^ 2 := by
  have hs := adSurv_det rrT idM rrQuery (fun _ _ => rfl) (fun _ _ => rfl)
  cases ω <;> simp [hs, adSurv_zero', rrQuery, rrKeep, misses, PL_UMLOWERF1.classRule] <;> ring

theorem witness : PL_UMADAPTF2.Witness := by
  have hT : ∀ h, IsDist (rrT h) := fun h => det_dist (rrQuery h)
  have hM : IsKernel idM := (setup_id idM (fun _ _ => rfl)).1
  have hacc : ∀ h : Hist Bool Bool, (∀ e ∈ h, e.2.2 = false) → rrKeep h = 1 := by
    intro h hh; unfold rrKeep; rw [misses_allflag h hh]; simp
  refine ⟨setup_id idM (fun _ _ => rfl), ⟨hT, fun h => keep01 _⟩,
    part_s Bool Bool rrT idM rrKeep 3 hM hT hacc, ?_, ?_, ?_⟩
  · unfold PL_UMADAPTF2.sharpTarget; norm_num
  · norm_num
  · unfold adProtocolCat
    rw [Fintype.sum_bool]
    simp only [rr_surv, cat_id1 idM (fun _ _ => rfl), seedLaw, Finset.mem_univ, if_true,
      Finset.card_univ, Fintype.card_bool, PL_UMLOWERF1.classRule, id]
    norm_num
