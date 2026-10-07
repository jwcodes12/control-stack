open Finset PL_UMHSF1 PL_UMSURVF1

theorem wsum_le {Y : Type} [Fintype Y] (w f : Y → ℝ) (c : ℝ) (hw : IsDist w)
    (hf : ∀ y, f y ≤ c) : ∑ y, w y * f y ≤ c := by
  calc ∑ y, w y * f y ≤ ∑ y, w y * c :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hf y) (hw.1 y))
    _ = c := by rw [← Finset.sum_mul, hw.2, one_mul]

theorem wsum_nonneg {Y : Type} [Fintype Y] (w f : Y → ℝ) (hw : ∀ y, 0 ≤ w y)
    (hf : ∀ y, 0 ≤ f y) : 0 ≤ ∑ y, w y * f y :=
  Finset.sum_nonneg (fun y _ => mul_nonneg (hw y) (hf y))

theorem t3a {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ)
    (hM : IsKernel M) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) :
    ∀ n u h, 0 ≤ cat Bad M φ π r b n u h ∧
        cat Bad M φ π r b n u h ≤ (if u < b then 1 - r + r * A else A) := by
  have hAB : A ≤ 1 - r + r * A := by nlinarith
  have hB0 : ∀ u : ℕ, 0 ≤ (if u < b then 1 - r + r * A else A) := by
    intro u; split_ifs <;> linarith
  have hBmono : ∀ u : ℕ, (if u + 1 < b then 1 - r + r * A else A) ≤
      (if u < b then 1 - r + r * A else A) := by
    intro u; split_ifs <;> linarith
  intro n
  induction n with
  | zero => intro u h; simp only [cat]; exact ⟨le_refl _, hB0 u⟩
  | succ n ih =>
    intro u h
    rw [cat]
    have hB0u := hB0 u
    have hBm := hBmono u
    constructor
    · apply wsum_nonneg _ _ (hπ h).1
      intro x
      apply wsum_nonneg _ _ (hM x).1
      intro z
      have p1 := (hφ z).1
      have p2 : 0 ≤ 1 - φ z := by linarith [(hφ z).2]
      by_cases hx : Bad x <;> by_cases hu : u < b <;>
        simp only [hx, hu, ↓reduceIte]
      · exact add_nonneg (by linarith) (mul_nonneg p2 (by linarith))
      · simp
        exact p1
      · exact add_nonneg (mul_nonneg p1 (ih u _).1) (mul_nonneg p2 (ih (u + 1) _).1)
      · simp
        exact mul_nonneg p1 (ih u _).1
    · apply wsum_le _ _ _ (hπ h)
      intro x
      by_cases hx : Bad x
      · have ha := hbad x hx
        unfold E at ha
        by_cases hu : u < b
        · simp only [hx, hu, ↓reduceIte]
          have e : ∀ z, M x z * (φ z * 1 + (1 - φ z) * (1 - r)) =
              (1 - r) * M x z + r * (M x z * φ z) := by intro z; ring
          simp_rw [e]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hM x).2]
          nlinarith
        · simp only [hx, hu, ↓reduceIte]
          simp only [mul_one, mul_zero, add_zero]
          exact ha
      · by_cases hu : u < b
        · simp only [hx, hu, ↓reduceIte]
          apply wsum_le _ _ _ (hM x)
          intro z
          have p1 := (hφ z).1
          have p2 : 0 ≤ 1 - φ z := by linarith [(hφ z).2]
          have c1 := (ih u (h ++ [(x, z, true)])).2
          have c2 := (ih (u + 1) (h ++ [(x, z, false)])).2
          have q1 := mul_le_mul_of_nonneg_left c1 p1
          have q2 := mul_le_mul_of_nonneg_left (le_trans c2 hBm) p2
          simp only [hu, ↓reduceIte] at q1 ⊢
          simp only [hu, ↓reduceIte] at hBm hB0u
          nlinarith
        · simp only [hx, hu, ↓reduceIte]
          apply wsum_le _ _ _ (hM x)
          intro z
          have p1 := (hφ z).1
          have p1' := (hφ z).2
          have c1 := (ih u (h ++ [(x, z, true)])).2
          have q1 := mul_le_mul_of_nonneg_left c1 p1
          simp only [hu, ↓reduceIte] at q1 hB0u ⊢
          nlinarith

theorem cat_le {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ)
    (hM : IsKernel M) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h)) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hA0 : 0 ≤ A) (hA1 : A ≤ 1) (hbad : ∀ x, Bad x → E (M x) φ ≤ A) (n u : ℕ) (h : Hist X Z) :
    0 ≤ cat Bad M φ π r b n u h ∧ cat Bad M φ π r b n u h ≤ 1 - r + r * A := by
  have hAB : A ≤ 1 - r + r * A := by nlinarith
  have := t3a Bad M φ π r A b hM hφ hπ hr0 hr1 hA0 hA1 hbad n u h
  refine ⟨this.1, le_trans this.2 ?_⟩
  split_ifs <;> linarith

theorem push_dist {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ)
    (hM : IsKernel M) (hP : IsDist PH) : IsDist (push M PH) := by
  constructor
  · intro z
    unfold push
    exact wsum_nonneg _ _ hP.1 (fun x => (hM x).1 z)
  · unfold push
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    simp only [(hM _).2, mul_one]
    exact hP.2

theorem prot_bound {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop)
    [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ)
    (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ) (C : ℝ)
    (hM : IsKernel M) (hρ : IsDist ρ) (hφ : ∀ ω, IsRule (φ ω)) (hπ : ∀ ω h, IsDist (π ω h))
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hω : ∀ ω, ∃ A, 0 ≤ A ∧ A ≤ 1 ∧ (∀ x, Bad x → E (M x) (φ ω) ≤ A) ∧
        0 ≤ surv (push M PH) (φ ω) κ nh 0 ∧
        surv (push M PH) (φ ω) κ nh 0 * (1 - r + r * A) ≤ C) :
    protocolCat Bad M PH κ nh r b N ρ φ π ≤ C := by
  unfold protocolCat
  simp_rw [mul_assoc]
  apply wsum_le _ _ _ hρ
  intro ω
  obtain ⟨A, hA0, hA1, hbad, hs0, hsC⟩ := hω ω
  have hc := cat_le Bad M (φ ω) (π ω) r A b hM (hφ ω) (hπ ω) hr0 hr1 hA0 hA1 hbad N 0 []
  calc surv (push M PH) (φ ω) κ nh 0 * cat Bad M (φ ω) (π ω) r b N 0 []
      ≤ surv (push M PH) (φ ω) κ nh 0 * (1 - r + r * A) := mul_le_mul_of_nonneg_left hc.2 hs0
    _ ≤ C := hsC

theorem rate_facts {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ)
    (φ : Z → ℝ) (hM : IsKernel M) (hP : IsDist PH) (hφ : IsRule φ) :
    0 ≤ ∑ z, push M PH z * φ z ∧ ∑ z, push M PH z * φ z ≤ 1 :=
  ⟨wsum_nonneg _ _ (push_dist M PH hM hP).1 (fun z => (hφ z).1),
   wsum_le _ _ _ (push_dist M PH hM hP) (fun z => (hφ z).2)⟩

theorem E_le_one {X Z : Type} [Fintype Z] (M : X → Z → ℝ) (φ : Z → ℝ) (hM : IsKernel M)
    (hφ : IsRule φ) (x : X) : E (M x) φ ≤ 1 :=
  wsum_le _ _ _ (hM x) (fun z => (hφ z).2)

theorem surv_eq {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ)
    (φ : Z → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (hM : IsKernel M) (hP : IsDist PH) :
    surv (push M PH) φ κ nh 0 = survH (∑ z, push M PH z * φ z) κ nh 0 :=
  PLDep_UMSURVF1.claim.1 Z (push M PH) φ κ nh 0 (push_dist M PH hM hP).2

theorem final_dom (S h L r A B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hL : 0 ≤ L) (hA : A ≤ L * h) (hB : h * S ≤ B) :
    S * (1 - r + r * A) ≤ (1 - r) + r * (L * B) := by
  have e1 : S * (1 - r) ≤ 1 - r := by nlinarith
  have e2 : S * A ≤ L * B :=
    calc S * A ≤ S * (L * h) := mul_le_mul_of_nonneg_left hA hS0
      _ = L * (h * S) := by ring
      _ ≤ L * B := mul_le_mul_of_nonneg_left hB hL
  have e3 := mul_le_mul_of_nonneg_left e2 hr0
  have e4 : S * (1 - r + r * A) = S * (1 - r) + r * (S * A) := by ring
  rw [e4]
  linarith

theorem final_hs (S h r A δ c B : ℝ) (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hδ : 0 ≤ δ) (hc : 0 ≤ c) (hA : A ≤ c * h + δ) (hB : h * S ≤ B) :
    S * (1 - r + r * A) ≤ (1 - r) + r * (δ + c * B) := by
  have e1 : S * (1 - r) ≤ 1 - r := by nlinarith
  have e2 : S * A ≤ δ + c * B :=
    calc S * A ≤ S * (c * h + δ) := mul_le_mul_of_nonneg_left hA hS0
      _ = c * (h * S) + δ * S := by ring
      _ ≤ c * B + δ * 1 := add_le_add (mul_le_mul_of_nonneg_left hB hc)
          (mul_le_mul_of_nonneg_left hS1 hδ)
      _ = δ + c * B := by ring
  have e3 := mul_le_mul_of_nonneg_left e2 hr0
  have e4 : S * (1 - r + r * A) = S * (1 - r) + r * (S * A) := by ring
  rw [e4]
  linarith

theorem hardKill_prob (ns : ℕ) : ∀ i, 0 ≤ hardKill ns i ∧ hardKill ns i ≤ 1 := by
  intro i; unfold hardKill; split_ifs <;> norm_num

theorem E_dom {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ)
    (φ : Z → ℝ) (hφ : IsRule φ) (L : ℝ) (x : X) (hd : ∀ z, M x z ≤ L * push M PH z) :
    E (M x) φ ≤ L * ∑ z, push M PH z * φ z := by
  unfold E
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  calc M x z * φ z ≤ (L * push M PH z) * φ z := mul_le_mul_of_nonneg_right (hd z) (hφ z).1
    _ = L * (push M PH z * φ z) := by ring

theorem claim : PL_UMPROTF1.Claim := by
  unfold PL_UMPROTF1.Claim
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X Z _ _ Bad _ M φ π r A b hM hφ hπ hr0 hr1 hA0 hA1 hbad
    exact t3a Bad M φ π r A b hM hφ hπ hr0 hr1 hA0 hA1 hbad
  · intro X Z _ _ Bad _ _ M PH κ nh r b N φ x hM hx hN hb
    unfold protocolCat
    obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
    have hb' : 0 < b := hb
    rw [Fintype.sum_unique, cat]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, hx, hb',
      ↓reduceIte]
    congr 1
    unfold E
    have e : ∀ z, M x z * (φ z * 1 + (1 - φ z) * (1 - r)) =
        (1 - r) * M x z + r * (M x z * φ z) := by intro z; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hM x).2]
    ring
  · intro X Z Ω _ _ _ Bad _ M PH nh ns b N r L ρ φ π hM hP hρ hφ hπ hr0 hr1 hL hdom
    apply prot_bound Bad M PH _ nh r b N ρ φ π _ hM hρ hφ hπ hr0 hr1
    intro ω
    obtain ⟨h0, h1⟩ := rate_facts M PH (φ ω) hM hP (hφ ω)
    have hsp := (PLDep_UMSURVF1.survH_prob (∑ z, push M PH z * φ ω z) (hardKill ns) h0 h1
      (hardKill_prob ns) nh 0)
    rw [PLDep_UMSURVF1.survH_hard _ ns nh 0 (Nat.zero_le _), Nat.sub_zero] at hsp
    refine ⟨min 1 (L * ∑ z, push M PH z * φ ω z), le_min zero_le_one (mul_nonneg hL h0),
      min_le_left _ _, ?_, ?_, ?_⟩
    · intro x hx
      exact le_min (E_le_one M (φ ω) hM (hφ ω) x) (E_dom M PH (φ ω) (hφ ω) L x (hdom x hx))
    · rw [surv_eq M PH (φ ω) _ nh hM hP, PLDep_UMSURVF1.survH_hard _ ns nh 0 (Nat.zero_le _),
        Nat.sub_zero]
      exact hsp.1
    · rw [surv_eq M PH (φ ω) _ nh hM hP, PLDep_UMSURVF1.survH_hard _ ns nh 0 (Nat.zero_le _),
        Nat.sub_zero]
      exact final_dom _ _ _ _ _ _ hsp.1 hsp.2 hr0 hr1 hL (min_le_right _ _)
        (PLDep_UMSURVF1.first_moment' nh ns _ h0 h1)
  · intro X Z Ω _ _ _ Bad _ M PH nh ns b N r η δ ρ φ π hM hP hρ hφ hπ hr0 hr1 hδ hhs
    apply prot_bound Bad M PH _ nh r b N ρ φ π _ hM hρ hφ hπ hr0 hr1
    intro ω
    obtain ⟨h0, h1⟩ := rate_facts M PH (φ ω) hM hP (hφ ω)
    have hsp := (PLDep_UMSURVF1.survH_prob (∑ z, push M PH z * φ ω z) (hardKill ns) h0 h1
      (hardKill_prob ns) nh 0)
    rw [PLDep_UMSURVF1.survH_hard _ ns nh 0 (Nat.zero_le _), Nat.sub_zero] at hsp
    refine ⟨min 1 (Real.exp η * (∑ z, push M PH z * φ ω z) + δ),
      le_min zero_le_one (add_nonneg (mul_nonneg (Real.exp_pos η).le h0) hδ),
      min_le_left _ _, ?_, ?_, ?_⟩
    · intro x hx
      refine le_min (E_le_one M (φ ω) hM (hφ ω) x) ?_
      have t := PLDep_UMHSF1.t2 Z η (M x) (push M PH) (φ ω) (hφ ω)
      have := hhs x hx
      unfold E at t ⊢
      linarith
    · rw [surv_eq M PH (φ ω) _ nh hM hP, PLDep_UMSURVF1.survH_hard _ ns nh 0 (Nat.zero_le _),
        Nat.sub_zero]
      exact hsp.1
    · rw [surv_eq M PH (φ ω) _ nh hM hP, PLDep_UMSURVF1.survH_hard _ ns nh 0 (Nat.zero_le _),
        Nat.sub_zero]
      exact final_hs _ _ _ _ _ _ _ hsp.1 hsp.2 hr0 hr1 hδ (Real.exp_pos η).le (min_le_right _ _)
        (PLDep_UMSURVF1.first_moment' nh ns _ h0 h1)
  · intro X Z Ω _ _ _ Bad _ M PH nh ns b N r L ρ φ π hM hP hρ hφ hπ hr0 hr1 hL hns hdom
    apply prot_bound Bad M PH _ nh r b N ρ φ π _ hM hρ hφ hπ hr0 hr1
    intro ω
    obtain ⟨h0, h1⟩ := rate_facts M PH (φ ω) hM hP (hφ ω)
    have hns' : (1 : ℝ) ≤ (ns : ℝ) := by exact_mod_cast hns
    have hk0 : (0 : ℝ) < 1 / (ns : ℝ) := by positivity
    have hk1 : 1 / (ns : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hns'
    have hsp := (PLDep_UMSURVF1.survH_prob (∑ z, push M PH z * φ ω z) (softKill ns) h0 h1
      (fun _ => ⟨hk0.le, hk1⟩) nh 0)
    have hsc : survH (∑ z, push M PH z * φ ω z) (softKill ns) nh 0 =
        (1 - 1 / (ns : ℝ) * ∑ z, push M PH z * φ ω z) ^ nh :=
      PLDep_UMSURVF1.survH_const _ _ nh 0
    rw [hsc] at hsp
    have hfm := PLDep_UMSURVF1.claim.2.2.2.2.1 nh _ (1 / (ns : ℝ)) h0 h1 hk0 hk1
    have hq : 1 / (1 / (ns : ℝ) * ((nh : ℝ) + 1)) = (ns : ℝ) / ((nh : ℝ) + 1) := by
      field_simp
    rw [hq] at hfm
    refine ⟨min 1 (L * ∑ z, push M PH z * φ ω z), le_min zero_le_one (mul_nonneg hL h0),
      min_le_left _ _, ?_, ?_, ?_⟩
    · intro x hx
      exact le_min (E_le_one M (φ ω) hM (hφ ω) x) (E_dom M PH (φ ω) (hφ ω) L x (hdom x hx))
    · rw [surv_eq M PH (φ ω) _ nh hM hP, hsc]
      exact hsp.1
    · rw [surv_eq M PH (φ ω) _ nh hM hP, hsc]
      exact final_dom _ _ _ _ _ _ hsp.1 hsp.2 hr0 hr1 hL (min_le_right _ _) hfm

theorem witness : PL_UMPROTF1.Witness := by
  unfold PL_UMPROTF1.Witness protocolCat
  refine ⟨?_, ?_, ?_⟩
  · simp [cat, surv, push, hardKill]
    norm_num
  · intro z
    cases z <;> simp [push]
  · norm_num
