import ControlStack.Refinement
open OracleComp
namespace ControlStack.Refine
open ControlStack.Bridge (honeypotPasses binCDF)

theorem probOutput_true_add_false_one (c : ProbComp Bool) :
    Pr[= true | c] + Pr[= false | c] = 1 := by
  have h := sum_probOutput_eq_sub c
  rw [Fintype.sum_bool] at h
  rw [h]
  simp

theorem probOutput_false_toReal (c : ProbComp Bool) :
    (Pr[= false | c]).toReal = 1 - (Pr[= true | c]).toReal := by
  have h2 := congrArg ENNReal.toReal (probOutput_true_add_false_one c)
  rw [ENNReal.toReal_add probOutput_ne_top probOutput_ne_top] at h2
  simp at h2
  linarith

theorem probOutput_not_true (c : ProbComp Bool) :
    Pr[= true | (fun caught => !caught) <$> c] = Pr[= false | c] :=
  probOutput_map_injective c (fun a b h => by cases a <;> cases b <;> simp_all) false

theorem deploy_step {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) :
    Pr[= true | deploy Bad π M D A b (n+1) u h] = ∑ x, Pr[= x | π h] * ∑ z, Pr[= z | M x] *
      (Pr[= true | D z] * Pr[= true | (if Bad x then pure true else deploy Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Bool)] +
       Pr[= false | D z] * Pr[= true | (if u < b then
        (if Bad x then (fun caught => !caught) <$> A h x z
         else deploy Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure false : ProbComp Bool)]) := by
  rw [deploy]
  simp only [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
  simp

theorem deploy_step_real {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (π : Hist X Z → ProbComp X) (M : X → ProbComp Z) (D : Z → ProbComp Bool)
    (A : Hist X Z → X → Z → ProbComp Bool) (b n u : ℕ) (h : Hist X Z) :
    (Pr[= true | deploy Bad π M D A b (n+1) u h]).toReal = ∑ x, (Pr[= x | π h]).toReal * ∑ z, (Pr[= z | M x]).toReal *
      ((Pr[= true | D z]).toReal * (Pr[= true | (if Bad x then pure true else deploy Bad π M D A b n u (h ++ [(x, z, true)]) : ProbComp Bool)]).toReal +
       (1 - (Pr[= true | D z]).toReal) * (Pr[= true | (if u < b then
        (if Bad x then (fun caught => !caught) <$> A h x z
         else deploy Bad π M D A b n (u + 1) (h ++ [(x, z, false)])) else pure false : ProbComp Bool)]).toReal) := by
  rw [deploy_step, ENNReal.toReal_sum (fun x _ => ENNReal.mul_ne_top probOutput_ne_top
    (ENNReal.sum_ne_top.2 fun z _ => ENNReal.mul_ne_top probOutput_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top,
        ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top⟩)))]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_sum (fun z _ => ENNReal.mul_ne_top probOutput_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top,
        ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top⟩))]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)
    (ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top), ENNReal.toReal_mul, ENNReal.toReal_mul,
    probOutput_false_toReal]

theorem toReal_probOutput_le_one {α : Type} (c : ProbComp α) (x : α) : (Pr[= x | c]).toReal ≤ 1 := by
  have := (ENNReal.toReal_le_toReal probOutput_ne_top ENNReal.one_ne_top).2 (probOutput_le_one (mx := c) (x := x))
  simpa using this

theorem toReal_probEvent_le_one {α : Type} (c : ProbComp α) (p : α → Prop) : (Pr[p | c]).toReal ≤ 1 := by
  have := (ENNReal.toReal_le_toReal probEvent_ne_top ENNReal.one_ne_top).2 (probEvent_le_one (mx := c) (p := p))
  simpa using this

theorem sum_toReal_probOutput {α : Type} [Fintype α] (c : ProbComp α) :
    ∑ x, (Pr[= x | c]).toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun x _ => probOutput_ne_top)]
  rw [sum_probOutput_eq_sub]
  simp

theorem catG_const {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) :
    ∀ n u h, catG Bad M φ π (fun _ _ _ => r) b n u h = cat Bad M φ π r b n u h := by
  intro n
  induction n with
  | zero => intro u h; simp [catG, cat]
  | succ n ih => intro u h; simp only [catG, cat, ih]

theorem catG_congr {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R R' : Hist X Z → X → Z → ℝ) (b : ℕ)
    (hR : ∀ h x z, Bad x → R h x z = R' h x z) :
    ∀ n u h, catG Bad M φ π R b n u h = catG Bad M φ π R' b n u h := by
  intro n
  induction n with
  | zero => intro u h; simp [catG]
  | succ n ih =>
    intro u h
    simp only [catG, ih]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : Bad x
    · have hz : ∀ z, R h x z = R' h x z := fun z => hR h x z hx
      simp only [hz]
    · simp only [hx, if_false]

theorem catG_le_cat {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (R : Hist X Z → X → Z → ℝ) (r : ℝ) (b : ℕ)
    (hπ : ∀ h x, 0 ≤ π h x) (hM : ∀ x z, 0 ≤ M x z) (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1)
    (hR : ∀ h x z, Bad x → r ≤ R h x z) :
    ∀ n u h, catG Bad M φ π R b n u h ≤ cat Bad M φ π r b n u h := by
  intro n
  induction n with
  | zero => intro u h; simp [catG, cat]
  | succ n ih =>
    intro u h
    rw [catG, cat]
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hπ h x)
    apply Finset.sum_le_sum
    intro z _
    apply mul_le_mul_of_nonneg_left _ (hM x z)
    have p1 := hφ0 z
    have p2 : 0 ≤ 1 - φ z := by linarith [hφ1 z]
    by_cases hx : Bad x <;> by_cases hu : u < b <;> simp only [hx, hu, if_true, if_false]
    · have := hR h x z hx
      nlinarith
    · exact le_rfl
    · exact add_le_add (mul_le_mul_of_nonneg_left (ih _ _) p1) (mul_le_mul_of_nonneg_left (ih _ _) p2)
    · exact add_le_add (mul_le_mul_of_nonneg_left (ih _ _) p1) le_rfl

theorem wsum_le {Y : Type} [Fintype Y] (w f : Y → ℝ) (c : ℝ) (hw0 : ∀ y, 0 ≤ w y)
    (hw1 : ∑ y, w y = 1) (hf : ∀ y, f y ≤ c) : ∑ y, w y * f y ≤ c := by
  calc ∑ y, w y * f y ≤ ∑ y, w y * c :=
        Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hf y) (hw0 y))
    _ = c := by rw [← Finset.sum_mul, hw1, one_mul]

theorem t3a {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r A : ℝ) (b : ℕ)
    (hM0 : ∀ x z, 0 ≤ M x z) (hM1 : ∀ x, ∑ z, M x z = 1)
    (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z, φ z ≤ 1)
    (hπ0 : ∀ h x, 0 ≤ π h x) (hπ1 : ∀ h, ∑ x, π h x = 1)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hA0 : 0 ≤ A) (hA1 : A ≤ 1)
    (hbad : ∀ x, Bad x → ∑ z, M x z * φ z ≤ A) :
    ∀ n u h, cat Bad M φ π r b n u h ≤ (if u < b then 1 - r + r * A else A) := by
  have hB0 : ∀ u : ℕ, 0 ≤ (if u < b then 1 - r + r * A else A) := by
    intro u; split_ifs <;> nlinarith
  have hBmono : ∀ u : ℕ, (if u + 1 < b then 1 - r + r * A else A) ≤
      (if u < b then 1 - r + r * A else A) := by
    intro u; split_ifs <;> first | linarith | nlinarith
  intro n
  induction n with
  | zero => intro u h; simp only [cat]; exact hB0 u
  | succ n ih =>
    intro u h
    rw [cat]
    have hB0u := hB0 u
    have hBm := hBmono u
    apply wsum_le _ _ _ (hπ0 h) (hπ1 h)
    intro x
    by_cases hx : Bad x
    · have ha := hbad x hx
      by_cases hu : u < b
      · simp only [hx, hu, if_true]
        have e : ∀ z, M x z * (φ z * 1 + (1 - φ z) * (1 - r)) =
            (1 - r) * M x z + r * (M x z * φ z) := by intro z; ring
        simp_rw [e]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hM1 x]
        nlinarith
      · simp only [hx, hu, if_true, if_false]
        simp only [mul_one, mul_zero, add_zero]
        exact ha
    · by_cases hu : u < b
      · simp only [hx, hu, if_true, if_false]
        apply wsum_le _ _ _ (hM0 x) (hM1 x)
        intro z
        have p1 := hφ0 z
        have p2 : 0 ≤ 1 - φ z := by linarith [hφ1 z]
        have c1 := ih u (h ++ [(x, z, true)])
        have c2 := ih (u + 1) (h ++ [(x, z, false)])
        have q1 := mul_le_mul_of_nonneg_left c1 p1
        have q2 := mul_le_mul_of_nonneg_left (le_trans c2 hBm) p2
        simp only [hu, if_true] at q1 q2 hBm hB0u ⊢
        nlinarith
      · simp only [hx, hu, if_false]
        apply wsum_le _ _ _ (hM0 x) (hM1 x)
        intro z
        have p1 := hφ0 z
        have p1' := hφ1 z
        have c1 := ih u (h ++ [(x, z, true)])
        have q1 := mul_le_mul_of_nonneg_left c1 p1
        simp only [hu, if_false] at q1 hB0u ⊢
        nlinarith

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

theorem first_moment (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hB : binCDF (n + 1) (s + 1) h ≤ 1) :
    ((n : ℝ) + 1) * (h * binCDF n s h) ≤ (s : ℝ) + 1 := by
  have hp : 0 ≤ 1 - h := by linarith
  have key : ((n : ℝ) + 1) * (h * binCDF n s h) =
      ∑ j ∈ Finset.range (s + 1), ((j : ℝ) + 1) *
        (((n + 1).choose (j + 1) : ℝ) * h ^ (j + 1) * (1 - h) ^ (n + 1 - (j + 1))) := by
    unfold binCDF
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hc := Nat.add_one_mul_choose_eq n j
    have hc' : ((n : ℝ) + 1) * (n.choose j : ℝ) = ((n + 1).choose (j + 1) : ℝ) * ((j : ℝ) + 1) := by
      exact_mod_cast hc
    have e : n + 1 - (j + 1) = n - j := by omega
    rw [e, pow_succ]
    linear_combination (h ^ j * h * (1 - h) ^ (n - j)) * hc'
  rw [key]
  have hle : ∑ j ∈ Finset.range (s + 1), ((j : ℝ) + 1) *
        (((n + 1).choose (j + 1) : ℝ) * h ^ (j + 1) * (1 - h) ^ (n + 1 - (j + 1))) ≤
      ∑ j ∈ Finset.range (s + 1), ((s : ℝ) + 1) *
        (((n + 1).choose (j + 1) : ℝ) * h ^ (j + 1) * (1 - h) ^ (n + 1 - (j + 1))) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjs : (j : ℝ) ≤ s := by
      have := Finset.mem_range.mp hj
      exact_mod_cast (by omega : j ≤ s)
    apply mul_le_mul_of_nonneg_right (by linarith)
    positivity
  refine le_trans hle ?_
  rw [← Finset.mul_sum]
  unfold binCDF at hB
  rw [Finset.sum_range_succ'] at hB
  have h0 : 0 ≤ ((n + 1).choose 0 : ℝ) * h ^ 0 * (1 - h) ^ (n + 1 - 0) := by positivity
  have hS : ∑ j ∈ Finset.range (s + 1),
      ((n + 1).choose (j + 1) : ℝ) * h ^ (j + 1) * (1 - h) ^ (n + 1 - (j + 1)) ≤ 1 := by
    linarith
  have hs0 : (0 : ℝ) ≤ (s : ℝ) + 1 := by positivity
  nlinarith

theorem first_moment' (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hB : binCDF (n + 1) (s + 1) h ≤ 1) :
    h * binCDF n s h ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1) := by
  rw [le_div_iff₀ (by positivity)]
  have := first_moment n s h hh0 hh1 hB
  linarith

theorem deployG : DeployGClaim := by
  intro X Z _ _ Bad _ π M D A b n
  induction n with
  | zero => intro u h; simp [deploy, catG]
  | succ n ih =>
    intro u h
    rw [deploy_step_real, catG]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun z _ => ?_
    congr 1
    by_cases hx : Bad x <;> by_cases hu : u < b <;> simp [hx, hu, ih, probOutput_not_true, probOutput_false_toReal]

theorem deploy_le : DeployClaim := by
  intro X Z _ _ Bad _ π M D A r b hr n u h
  rw [deployG X Z Bad π M D A b n u h]
  exact catG_le_cat Bad _ _ _ _ r b (fun _ _ => ENNReal.toReal_nonneg) (fun _ _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg) (fun z => toReal_probOutput_le_one _ _) hr n u h

theorem deploy_exact : DeployExactClaim := by
  intro X Z _ _ Bad _ π M D A r b hr n u h
  rw [deployG X Z Bad π M D A b n u h, ← catG_const]
  exact catG_congr Bad _ _ _ _ _ b hr n u h

theorem protocol : ProtocolClaim := by
  intro X Z Ω _ Bad _ ρ H M D π A nh ns b N
  have key : ∀ ω, Pr[= true | honeypotPasses H M (D ω) nh >>= fun k =>
      if k ≤ ns then deploy Bad (π ω) M (D ω) A b N 0 [] else pure false] =
      Pr[fun k => k ≤ ns | honeypotPasses H M (D ω) nh] *
        Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []] := by
    intro ω
    rw [probOutput_bind_eq_tsum, probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun k => ?_
    by_cases hk : k ≤ ns <;> simp [hk]
  unfold protocolGame
  rw [probOutput_bind_eq_tsum, tsum_fintype]
  simp only [key]
  rw [ENNReal.toReal_sum (fun ω _ => by finiteness)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, Bridge.bridge, mul_assoc]

theorem endToEnd : EndToEndClaim := by
  intro X Z Ω _ _ _ Bad _ ρ H M D π A nh ns b N r L hr0 hr1 hL hrec hdom
  rw [protocol X Z Ω Bad ρ H M D π A nh ns b N]
  set C : ℝ := (1 - r) + r * (L * (((ns : ℝ) + 1) / ((nh : ℝ) + 1))) with hC
  have hρ : ∑ ω, (Pr[= ω | ρ]).toReal = 1 := sum_toReal_probOutput ρ
  calc ∑ ω, (Pr[= ω | ρ]).toReal * binCDF nh ns (Pr[= true | H >>= M >>= D ω]).toReal *
        (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
      ≤ ∑ ω, (Pr[= ω | ρ]).toReal * C := by
        apply Finset.sum_le_sum
        intro ω _
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
        set hω := (Pr[= true | H >>= M >>= D ω]).toReal with hhω
        have hS := Bridge.bridge X Z H M (D ω) nh ns
        have hS' := Bridge.bridge X Z H M (D ω) (nh + 1) (ns + 1)
        rw [← hhω] at hS hS'
        have hS0 : 0 ≤ binCDF nh ns hω := hS ▸ ENNReal.toReal_nonneg
        have hS1 : binCDF nh ns hω ≤ 1 := hS ▸ toReal_probEvent_le_one _ _
        have hS1' : binCDF (nh + 1) (ns + 1) hω ≤ 1 := hS' ▸ toReal_probEvent_le_one _ _
        have hh0 : 0 ≤ hω := ENNReal.toReal_nonneg
        have hh1 : hω ≤ 1 := toReal_probOutput_le_one _ _
        -- hω as a sum over views
        have hsum : hω = ∑ z, (Pr[= z | H >>= M]).toReal * (Pr[= true | D ω z]).toReal := by
          rw [hhω, probOutput_bind_eq_tsum, tsum_fintype,
            ENNReal.toReal_sum (fun z _ => by finiteness)]
          simp only [ENNReal.toReal_mul]
        set Aω := min 1 (L * hω) with hAω
        have hA0 : 0 ≤ Aω := le_min zero_le_one (mul_nonneg hL hh0)
        have hA1 : Aω ≤ 1 := min_le_left _ _
        have hbad : ∀ x, Bad x → ∑ z, (Pr[= z | M x]).toReal * (Pr[= true | D ω z]).toReal ≤ Aω := by
          intro x hx
          apply le_min
          · apply wsum_le _ _ _ (fun _ => ENNReal.toReal_nonneg) (sum_toReal_probOutput _)
            intro z; exact toReal_probOutput_le_one _ _
          · rw [hsum, Finset.mul_sum]
            apply Finset.sum_le_sum
            intro z _
            calc (Pr[= z | M x]).toReal * (Pr[= true | D ω z]).toReal
                ≤ (L * (Pr[= z | H >>= M]).toReal) * (Pr[= true | D ω z]).toReal :=
                  mul_le_mul_of_nonneg_right (hdom x hx z) ENNReal.toReal_nonneg
              _ = L * ((Pr[= z | H >>= M]).toReal * (Pr[= true | D ω z]).toReal) := by ring
        have hdep := deploy_le X Z Bad (π ω) M (D ω) A r b hrec N 0 []
        have hcat := t3a Bad (fun x z => (Pr[= z | M x]).toReal) (fun z => (Pr[= true | D ω z]).toReal)
          (fun h x => (Pr[= x | π ω h]).toReal) r Aω b (fun _ _ => ENNReal.toReal_nonneg)
          (fun x => sum_toReal_probOutput _) (fun _ => ENNReal.toReal_nonneg)
          (fun _ => toReal_probOutput_le_one _ _) (fun _ _ => ENNReal.toReal_nonneg)
          (fun h => sum_toReal_probOutput _) hr0 hr1 hA0 hA1 hbad N 0 []
        have hAB : Aω ≤ 1 - r + r * Aω := by nlinarith
        have hP : (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal ≤ 1 - r + r * Aω := by
          refine le_trans hdep (le_trans hcat ?_)
          split_ifs <;> linarith
        calc binCDF nh ns hω * (Pr[= true | deploy Bad (π ω) M (D ω) A b N 0 []]).toReal
            ≤ binCDF nh ns hω * (1 - r + r * Aω) := mul_le_mul_of_nonneg_left hP hS0
          _ ≤ C := final_dom _ _ _ _ _ _ hS0 hS1 hr0 hr1 hL (min_le_right _ _)
                (first_moment' nh ns hω hh0 hh1 hS1')
    _ = C := by rw [← Finset.sum_mul, hρ, one_mul]

theorem attain : AttainClaim := by
  intro X Z Ω _ Bad _ ρ H M D A nh ns b N r x hx hN hb hA
  rw [protocol X Z Ω Bad ρ H M D (fun _ _ => pure x) A nh ns b N]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hb' : 0 < b := hb
  have hZ : Nonempty Z := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have h1 := tsum_probOutput_eq_sub (M x)
    simp at h1
  obtain ⟨z0⟩ := hZ
  have hr1 : r ≤ 1 := hA z0 ▸ toReal_probOutput_le_one _ _
  have ha : ∀ z, Pr[= false | A [] x z] = ENNReal.ofReal (1 - r) := by
    intro z
    rw [← ENNReal.ofReal_toReal (probOutput_ne_top (mx := A [] x z) (x := false)),
      probOutput_false_toReal, hA z]
  have hstep : Pr[= true | deploy Bad (fun _ => pure x) M (D ω) A b (m + 1) 0 []] =
      Pr[= true | M x >>= D ω] + ENNReal.ofReal (1 - r) * Pr[= false | M x >>= D ω] := by
    rw [deploy]
    simp only [pure_bind, hx, hb', ↓reduceIte]
    rw [probOutput_bind_eq_tsum, probOutput_bind_eq_tsum, probOutput_bind_eq_tsum,
      ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    refine tsum_congr fun z => ?_
    rw [probOutput_bind_eq_tsum, tsum_fintype, Fintype.sum_bool]
    simp [probOutput_not_true, ha]
    ring
  rw [hstep, ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith), probOutput_false_toReal]
  ring

theorem witness : Witness := by
  have hq : Pr[= true | ((fun k : Fin 4 => decide (k = 0)) <$> $[0..3] : ProbComp Bool)] = 4⁻¹ := by
    rw [probOutput_map_eq_sum_fintype_ite]
    simp
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [protocol]
    simp [deploy, hq]
    rw [probOutput_bind_eq_tsum, tsum_fintype]
    simp [binCDF]
    have h4 : ((3 : ENNReal) + 1).toReal = 4 := by
      rw [ENNReal.toReal_add (by simp) (by simp)]
      norm_num
    rw [h4]
    norm_num
  · intro z
    simp
  · norm_num

end ControlStack.Refine
