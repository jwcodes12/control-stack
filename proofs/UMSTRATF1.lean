open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

theorem surv_eq_bin {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : ∑ z, q z = 1) (m sc : ℕ) :
    surv q φ (hardKill sc) m 0 = binCDF m sc (E q φ) := by
  show surv q φ (hardKill sc) m 0 = binCDF m sc (∑ z, q z * φ z)
  rw [PLDep_UMSURVF1.claim.1 Z q φ (hardKill sc) m 0 hq,
    PLDep_UMSURVF1.survH_hard _ sc m 0 (Nat.zero_le _), Nat.sub_zero]

theorem rate01 {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : IsDist q) (hφ : IsRule φ) :
    0 ≤ E q φ ∧ E q φ ≤ 1 :=
  ⟨PLDep_UMPROTF1.wsum_nonneg _ _ hq.1 (fun z => (hφ z).1),
   PLDep_UMPROTF1.wsum_le _ _ _ hq (fun z => (hφ z).2)⟩

theorem factor01 {Z : Type} [Fintype Z] (q φ : Z → ℝ) (hq : IsDist q) (hφ : IsRule φ)
    (m sc : ℕ) :
    0 ≤ surv q φ (hardKill sc) m 0 ∧ surv q φ (hardKill sc) m 0 ≤ 1 := by
  rw [surv_eq_bin q φ hq.2]
  obtain ⟨h0, h1⟩ := rate01 q φ hq hφ
  have := PLDep_UMSURVF1.survH_prob _ (hardKill sc) h0 h1 (PLDep_UMPROTF1.hardKill_prob sc) m 0
  rw [PLDep_UMSURVF1.survH_hard _ sc m 0 (Nat.zero_le _), Nat.sub_zero] at this
  exact this

theorem strat01 {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C) (φ : Z → ℝ)
    (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) :
    0 ≤ stratSurv K Es φ m sc ∧ stratSurv K Es φ m sc ≤ 1 := by
  unfold stratSurv
  exact ⟨Finset.prod_nonneg (fun e _ => (factor01 (K e) φ (hK e) hφ m sc).1),
    Finset.prod_le_one₀ (fun e _ => (factor01 (K e) φ (hK e) hφ m sc).1)
      (fun e _ => (factor01 (K e) φ (hK e) hφ m sc).2)⟩

theorem strat_le_factor {Z C : Type} [Fintype Z] (K : C → Z → ℝ) (Es : Finset C)
    (φ : Z → ℝ) (m sc : ℕ) (hK : IsKernel K) (hφ : IsRule φ) (e : C) (he : e ∈ Es) :
    stratSurv K Es φ m sc ≤ surv (K e) φ (hardKill sc) m 0 := by
  classical
  unfold stratSurv
  rw [← Finset.mul_prod_erase Es _ he]
  have h1 := factor01 (K e) φ (hK e) hφ m sc
  have h2 : ∏ e' ∈ Es.erase e, surv (K e') φ (hardKill sc) m 0 ≤ 1 :=
    Finset.prod_le_one₀ (fun e _ => (factor01 (K e) φ (hK e) hφ m sc).1)
      (fun e _ => (factor01 (K e) φ (hK e) hφ m sc).2)
  calc _ ≤ surv (K e) φ (hardKill sc) m 0 * 1 := mul_le_mul_of_nonneg_left h2 h1.1
    _ = _ := mul_one _

theorem exists_A {X Z C : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (φ : Z → ℝ) (m sc : ℕ)
    (hK : IsKernel K) (hφ : IsRule φ) (hEs : ∀ x, Bad x → c x ∈ Es) :
    ∃ A, 0 ≤ A ∧ A ≤ 1 ∧ (∀ x, Bad x → E (K (c x)) φ ≤ A) ∧
      A * stratSurv K Es φ m sc ≤ ((sc : ℝ) + 1) / ((m : ℝ) + 1) := by
  have hS := strat01 K Es φ m sc hK hφ
  by_cases hex : ∃ x, Bad x
  · have hne : (Finset.univ.filter Bad).Nonempty := by
      obtain ⟨x, hx⟩ := hex
      exact ⟨x, by simp [hx]⟩
    obtain ⟨x0, hx0, hmax⟩ :=
      Finset.exists_max_image (Finset.univ.filter Bad) (fun x => E (K (c x)) φ) hne
    have hbx0 : Bad x0 := (Finset.mem_filter.mp hx0).2
    obtain ⟨h0, h1⟩ := rate01 (K (c x0)) φ (hK (c x0)) hφ
    refine ⟨E (K (c x0)) φ, h0, h1, ?_, ?_⟩
    · intro x hx
      exact hmax x (by simp [hx])
    · have hle := strat_le_factor K Es φ m sc hK hφ (c x0) (hEs x0 hbx0)
      rw [surv_eq_bin (K (c x0)) φ (hK (c x0)).2] at hle
      calc E (K (c x0)) φ * stratSurv K Es φ m sc
          ≤ E (K (c x0)) φ * binCDF m sc (E (K (c x0)) φ) := mul_le_mul_of_nonneg_left hle h0
        _ ≤ _ := PLDep_UMSURVF1.first_moment' m sc _ h0 h1
  · refine ⟨0, le_refl _, zero_le_one, ?_, ?_⟩
    · intro x hx
      exact absurd ⟨x, hx⟩ hex
    · rw [zero_mul]
      positivity

theorem claim1 : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω]
      (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C)
      (m sc b N : ℕ) (r : ℝ) (ρ : Ω → ℝ)
      (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) →
      (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤
        (1 - r) + r * (((sc : ℝ) + 1) / ((m : ℝ) + 1)) := by
  intro X Z C Ω _ _ _ Bad _ K c Es m sc b N r ρ φ π hK hρ hφ hπ hr0 hr1 hEs
  unfold stratProtocolCat
  simp_rw [mul_assoc]
  apply PLDep_UMPROTF1.wsum_le _ _ _ hρ
  intro ω
  obtain ⟨A, hA0, hA1, hbad, hAS⟩ := exists_A Bad K c Es (φ ω) m sc hK (hφ ω) hEs
  have hS := strat01 K Es (φ ω) m sc hK (hφ ω)
  have hc := PLDep_UMPROTF1.cat_le Bad (fun x => K (c x)) (φ ω) (π ω) r A b
    (fun x => hK (c x)) (hφ ω) (hπ ω) hr0 hr1 hA0 hA1 hbad N 0 []
  calc stratSurv K Es (φ ω) m sc * cat Bad (fun x => K (c x)) (φ ω) (π ω) r b N 0 []
      ≤ stratSurv K Es (φ ω) m sc * (1 - r + r * A) := mul_le_mul_of_nonneg_left hc.2 hS.1
    _ ≤ (1 - r) + r * (1 * (((sc : ℝ) + 1) / ((m : ℝ) + 1))) :=
        PLDep_UMPROTF1.final_dom _ A 1 r A _ hS.1 hS.2 hr0 hr1 zero_le_one (by linarith)
          (by linarith)
    _ = _ := by rw [one_mul]

theorem binCDF_at_zero (m sc : ℕ) : binCDF m sc 0 = 1 := by
  unfold binCDF
  rw [Finset.sum_range_succ']
  simp

theorem E_dec {Z C : Type} [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (g : Z → C) (t : ℝ)
    (e0 e : C) (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) :
    E (K e) (fun z => if g z = e0 then t else 0) = if e = e0 then t else 0 := by
  unfold E
  by_cases he : e = e0
  · subst he
    rw [if_pos rfl]
    have : ∀ z, K e z * (if g z = e then t else 0) = t * K e z := by
      intro z
      by_cases hz : K e z = 0
      · simp [hz]
      · rw [if_pos (hdec e z hz)]
        ring
    simp_rw [this]
    rw [← Finset.mul_sum, (hK e).2, mul_one]
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro z _
    by_cases hz : K e z = 0
    · rw [hz, zero_mul]
    · have hg := hdec e z hz
      have hne : ¬ g z = e0 := by rw [hg]; exact he
      simp only [hne, if_false, mul_zero]

theorem strat_att {Z C : Type} [Fintype Z] [DecidableEq C] (K : C → Z → ℝ) (g : Z → C)
    (Es : Finset C) (t : ℝ) (e0 : C) (m sc : ℕ)
    (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) (he0 : e0 ∈ Es) :
    stratSurv K Es (fun z => if g z = e0 then t else 0) m sc = binCDF m sc t := by
  unfold stratSurv
  rw [Finset.prod_eq_single_of_mem e0 he0]
  · rw [surv_eq_bin _ _ (hK e0).2, E_dec K g t e0 e0 hK hdec, if_pos rfl]
  · intro e _ hne
    rw [surv_eq_bin _ _ (hK e).2, E_dec K g t e0 e hK hdec, if_neg hne]
    exact binCDF_at_zero m sc

theorem cat_point {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    [DecidableEq X] (M : X → Z → ℝ) (φ : Z → ℝ) (r : ℝ) (b N : ℕ) (x : X)
    (hM : IsKernel M) (hx : Bad x) (hN : 1 ≤ N) (hb : 1 ≤ b) :
    cat Bad M φ (fun _ x' => if x' = x then 1 else 0) r b N 0 [] = 1 - r + r * E (M x) φ := by
  have := PLDep_UMPROTF1.claim.2.1 X Z Bad M (fun _ => 0) (fun _ => 0) 0 r b N φ x hM hx hN hb
  unfold protocolCat at this
  simpa [surv] using this

theorem claim2 : ∀ (X Z C : Type) [Fintype X] [Fintype Z]
      [DecidableEq C] [DecidableEq X]
      (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C)
      (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) →
      Bad x → c x ∈ Es → 1 ≤ N → 1 ≤ b → 0 ≤ t → t ≤ 1 →
      stratProtocolCat Bad K c Es m sc r b N
          (fun _ : Unit => 1)
          (fun _ z => if g z = c x then t else 0)
          (fun _ _ x' => if x' = x then 1 else 0) =
        binCDF m sc t * (1 - r + r * t) := by
  intro X Z C _ _ _ _ Bad _ K c g Es m sc b N r t x hK hdec hx hcx hN hb ht0 ht1
  unfold stratProtocolCat
  rw [Fintype.sum_unique]
  rw [strat_att K g Es t (c x) m sc hK hdec hcx]
  rw [cat_point Bad (fun x => K (c x)) _ r b N x (fun x => hK (c x)) hx hN hb]
  rw [E_dec K g t (c x) (c x) hK hdec, if_pos rfl]
  ring

theorem claim : PL_UMSTRATF1.Claim := ⟨claim1, claim2⟩

theorem wK : IsKernel witnessK := by
  intro e
  constructor
  · intro z
    unfold witnessK
    split_ifs <;> norm_num
  · cases e <;> simp [witnessK]

theorem wdec : ∀ e z : Bool, witnessK e z ≠ 0 → id z = e := by
  intro e z h
  unfold witnessK at h
  split_ifs at h with hz
  · exact hz
  · exact absurd rfl h

theorem wval : stratProtocolCat (fun x : Bool => x = true)
      witnessK id (Finset.univ : Finset Bool) 12 1 1 1 1
      (fun _ : Unit => 1) witnessPhi witnessPi =
    binCDF 12 1 (1 / 6) * (1 - 1 + 1 * (1 / 6 : ℝ)) :=
  claim2 Bool Bool Bool (fun x : Bool => x = true) witnessK id id Finset.univ 12 1 1 1 1 (1 / 6)
    true wK wdec rfl (Finset.mem_univ _) le_rfl le_rfl (by norm_num) (by norm_num)

theorem wbin : binCDF 12 1 (1 / 6 : ℝ) = (5 / 6) ^ 12 + 12 * (1 / 6) * (5 / 6) ^ 11 := by
  simp [binCDF, Finset.sum_range_succ]
  norm_num

theorem witness : PL_UMSTRATF1.Witness := by
  unfold PL_UMSTRATF1.Witness
  refine ⟨wK, wdec, ?_, ?_, ?_, ?_, ⟨true, rfl⟩, rfl, Finset.mem_univ _, ?_, by norm_num,
    le_rfl, by norm_num, by norm_num, le_rfl, ?_, ?_, wval, by norm_num, ?_, ?_⟩
  · exact ⟨fun _ => zero_le_one, by simp⟩
  · intro ω z
    unfold witnessPhi
    split_ifs <;> norm_num
  · intro ω h
    constructor
    · intro x
      unfold witnessPi
      split_ifs <;> norm_num
    · simp [witnessPi]
  · intro x _
    exact Finset.mem_univ _
  · simp
  · intro z
    rfl
  · intro ω h x
    rfl
  · rw [wval, wbin]
    norm_num
  · rw [wval, wbin]
    norm_num
