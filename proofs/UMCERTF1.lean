open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMSTRATF1

-- capB facts

theorem capB_mono (r : ℝ) (b : ℕ) (hr : 0 ≤ r) {a a' : ℝ} (h : a ≤ a') :
    capB r b a ≤ capB r b a' := by
  unfold capB
  split_ifs
  · nlinarith
  · exact h

theorem capB_nonneg (r : ℝ) (b : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ capB r b a := by
  unfold capB
  split_ifs
  · nlinarith
  · exact ha

theorem capB_le (r : ℝ) (b : ℕ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {a : ℝ} (ha : a ≤ 1) :
    capB r b a ≤ 1 - r + r * a := by
  unfold capB
  split_ifs
  · exact le_rfl
  · nlinarith

theorem capB_one (r : ℝ) (b : ℕ) : capB r b 1 = 1 := by
  unfold capB
  split_ifs <;> ring

-- expectation facts

theorem E_const {Z : Type} [Fintype Z] (P : Z → ℝ) (hP : ∑ z, P z = 1) (t : ℝ) :
    E P (fun _ => t) = t := by
  unfold E
  rw [← Finset.sum_mul, hP, one_mul]

theorem E_push {X Z : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (P : X → ℝ) (ψ : Z → ℝ) :
    E (push M P) ψ = ∑ x, P x * E (M x) ψ := by
  unfold E push
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  ring

theorem unit_dist : IsDist (fun _ : Unit => (1 : ℝ)) := ⟨fun _ => zero_le_one, by simp⟩

theorem point_dist {X : Type} [Fintype X] [DecidableEq X] (x : X) :
    IsDist (fun x' : X => if x' = x then (1 : ℝ) else 0) := by
  constructor
  · intro x'
    show 0 ≤ (if x' = x then (1 : ℝ) else 0)
    split_ifs <;> norm_num
  · simp

-- the deployment recursion

theorem cat_empty {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (π : Hist X Z → X → ℝ) (r : ℝ) (b : ℕ) (hB : ∀ x, ¬ Bad x) :
    ∀ n u h, cat Bad M φ π r b n u h = 0 := by
  intro n
  induction n with
  | zero => intro u h; rw [cat]
  | succ n ih =>
    intro u h
    rw [cat]
    simp [hB, ih]

theorem cat_oneshot {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    [DecidableEq X] (M : X → Z → ℝ) (ψ : Z → ℝ) (r : ℝ) (b N : ℕ) (x : X)
    (hM : IsKernel M) (hx : Bad x) (hN : 1 ≤ N) :
    cat Bad M ψ (fun _ x' => if x' = x then 1 else 0) r b N 0 [] = capB r b (E (M x) ψ) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [cat]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, hx, ↓reduceIte]
  unfold capB E
  by_cases hb : 0 < b
  · simp only [hb, ↓reduceIte]
    have e : ∀ z, M x z * (ψ z * 1 + (1 - ψ z) * (1 - r)) =
        (1 - r) * M x z + r * (M x z * ψ z) := by intro z; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, (hM x).2]
    ring
  · simp only [hb, ↓reduceIte, mul_zero, add_zero, mul_one]

theorem exists_worst {X : Type} [Fintype X] (Bad : X → Prop) [DecidablePred Bad] (f : X → ℝ)
    (hex : ∃ x, Bad x) : ∃ x0, Bad x0 ∧ ∀ x, Bad x → f x ≤ f x0 := by
  have hne : (Finset.univ.filter Bad).Nonempty := by
    obtain ⟨x, hx⟩ := hex
    exact ⟨x, by simp [hx]⟩
  obtain ⟨x0, hx0, hmax⟩ := Finset.exists_max_image (Finset.univ.filter Bad) f hne
  exact ⟨x0, (Finset.mem_filter.mp hx0).2, fun x hx => hmax x (by simp [hx])⟩

theorem oneshot_value {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    [DecidableEq X] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ)
    (ψ : Z → ℝ) (x : X) (hM : IsKernel M) (hP : IsDist PH) (hx : Bad x) (hN : 1 ≤ N) :
    protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (fun _ => ψ)
        (fun _ _ x' => if x' = x then 1 else 0)
      = survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) := by
  unfold protocolCat
  rw [Fintype.sum_unique]
  simp only [one_mul]
  rw [PLDep_UMPROTF1.surv_eq M PH ψ κ nh hM hP, cat_oneshot Bad M ψ r b N x hM hx hN]
  all_goals rfl

theorem strat_oneshot_value {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] [DecidableEq X]
    (Bad : X → Prop) [DecidablePred Bad] (K : C → Z → ℝ) (c : X → C) (g : Z → C)
    (Es : Finset C) (m sc b N : ℕ) (r t : ℝ) (x : X)
    (hK : IsKernel K) (hdec : ∀ e z, K e z ≠ 0 → g z = e) (hx : Bad x) (hcx : c x ∈ Es)
    (hN : 1 ≤ N) :
    stratProtocolCat Bad K c Es m sc r b N (fun _ : Unit => 1)
        (fun _ z => if g z = c x then t else 0) (fun _ _ x' => if x' = x then 1 else 0)
      = binCDF m sc t * capB r b t := by
  unfold stratProtocolCat
  rw [Fintype.sum_unique]
  simp only [one_mul]
  rw [PLDep_UMSTRATF1.strat_att K g Es t (c x) m sc hK hdec hcx,
    cat_oneshot Bad (fun x => K (c x)) _ r b N x (fun x => hK (c x)) hx hN]
  have h2 : E ((fun x => K (c x)) x) (fun z => if g z = c x then t else 0) = t := by
    show E (K (c x)) (fun z => if g z = c x then t else 0) = t
    rw [PLDep_UMSTRATF1.E_dec K g t (c x) (c x) hK hdec, if_pos rfl]
  rw [h2]

/-- per-seed bound: the worst bad submission decides -/
theorem seed_le {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ)
    (φ : Z → ℝ) (π : Hist X Z → X → ℝ)
    (hM : IsKernel M) (hP : IsDist PH) (hφ : IsRule φ) (hπ : ∀ h, IsDist (π h))
    (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hU : 0 ≤ U)
    (hyp : ∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ →
      survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U) :
    surv (push M PH) φ κ nh 0 * cat Bad M φ π r b N 0 [] ≤ U := by
  rw [PLDep_UMPROTF1.surv_eq M PH φ κ nh hM hP]
  obtain ⟨t0, t1⟩ := PLDep_UMSTRATF1.rate01 (push M PH) φ (PLDep_UMPROTF1.push_dist M PH hM hP) hφ
  have hS := PLDep_UMSURVF1.survH_prob _ κ t0 t1 hκ nh 0
  by_cases hex : ∃ x, Bad x
  · obtain ⟨x0, hx0, hmax⟩ := exists_worst Bad (fun x => E (M x) φ) hex
    obtain ⟨a0, a1⟩ := PLDep_UMSTRATF1.rate01 (M x0) φ (hM x0) hφ
    have hc := PLDep_UMPROTF1.t3a Bad M φ π r (E (M x0) φ) b hM hφ hπ hr0 hr1 a0 a1 hmax N 0 []
    calc survH (∑ z, push M PH z * φ z) κ nh 0 * cat Bad M φ π r b N 0 []
        ≤ survH (∑ z, push M PH z * φ z) κ nh 0 * capB r b (E (M x0) φ) :=
          mul_le_mul_of_nonneg_left hc.2 hS.1
      _ ≤ U := hyp x0 hx0 φ hφ
  · push_neg at hex
    rw [cat_empty Bad M φ π r b hex N 0 [], mul_zero]
    exact hU

theorem reduce_le {X Z Ω : Type} [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop)
    [DecidablePred Bad] (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ)
    (U : ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ)
    (hM : IsKernel M) (hP : IsDist PH) (hρ : IsDist ρ) (hφ : ∀ ω, IsRule (φ ω))
    (hπ : ∀ ω h, IsDist (π ω h))
    (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hU : 0 ≤ U)
    (hyp : ∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ →
      survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U) :
    protocolCat Bad M PH κ nh r b N ρ φ π ≤ U := by
  unfold protocolCat
  simp_rw [mul_assoc]
  apply PLDep_UMPROTF1.wsum_le _ _ _ hρ
  intro ω
  exact seed_le Bad M PH κ nh r b N U (φ ω) (π ω) hM hP (hφ ω) (hπ ω) hκ hr0 hr1 hU hyp

-- survival is antitone in the pass rate

theorem survH_aux (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) (h : ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    ∀ n j, (1 - κ j) * survH h κ n (j + 1) ≤ survH h κ n j := by
  intro n
  induction n with
  | zero =>
    intro j
    simp only [survH]
    linarith [(hκ j).1]
  | succ n ih =>
    intro j
    simp only [survH]
    have d1 := ih j
    have d2 := ih (j + 1)
    have p1 : 0 ≤ 1 - h := by linarith
    have p2 : 0 ≤ h * (1 - κ j) := mul_nonneg h0 (by linarith [(hκ j).2])
    have q := add_nonneg (mul_nonneg p1 (sub_nonneg.2 d1)) (mul_nonneg p2 (sub_nonneg.2 d2))
    have key : ((1 - h) * survH h κ n j + h * (1 - κ j) * survH h κ n (j + 1)) -
        (1 - κ j) * ((1 - h) * survH h κ n (j + 1) + h * (1 - κ (j + 1)) * survH h κ n (j + 1 + 1))
        = (1 - h) * (survH h κ n j - (1 - κ j) * survH h κ n (j + 1)) +
          h * (1 - κ j) * (survH h κ n (j + 1) - (1 - κ (j + 1)) * survH h κ n (j + 1 + 1)) := by
      ring
    linarith

theorem survH_anti (κ : ℕ → ℝ) (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) :
    ∀ n j (s t : ℝ), 0 ≤ s → s ≤ t → t ≤ 1 → survH t κ n j ≤ survH s κ n j := by
  intro n
  induction n with
  | zero => intro j s t _ _ _; simp [survH]
  | succ n ih =>
    intro j s t hs hst ht
    simp only [survH]
    have a := ih j s t hs hst ht
    have b := ih (j + 1) s t hs hst ht
    have c := survH_aux κ hκ s hs (by linarith) n j
    have pk : 0 ≤ 1 - κ j := by linarith [(hκ j).2]
    have q1 : 0 ≤ (1 - t) * (survH s κ n j - survH t κ n j) :=
      mul_nonneg (by linarith) (by linarith)
    have q2 : 0 ≤ t * (1 - κ j) * (survH s κ n (j + 1) - survH t κ n (j + 1)) :=
      mul_nonneg (mul_nonneg (by linarith) pk) (by linarith)
    have q3 : 0 ≤ (t - s) * (survH s κ n j - (1 - κ j) * survH s κ n (j + 1)) :=
      mul_nonneg (by linarith) (by linarith)
    have key : ((1 - s) * survH s κ n j + s * (1 - κ j) * survH s κ n (j + 1)) -
        ((1 - t) * survH t κ n j + t * (1 - κ j) * survH t κ n (j + 1))
        = (1 - t) * (survH s κ n j - survH t κ n j) +
          t * (1 - κ j) * (survH s κ n (j + 1) - survH t κ n (j + 1)) +
          (t - s) * (survH s κ n j - (1 - κ j) * survH s κ n (j + 1)) := by
      ring
    linarith

-- grid certificates

theorem GridOK_cons2 (S F : ℝ → ℝ) (U s t : ℝ) (rest : List ℝ) :
    GridOK S F U (s :: t :: rest) ↔ s ≤ t ∧ S s * F t ≤ U ∧ GridOK S F U (t :: rest) := Iff.rfl

theorem GridOK_single (S F : ℝ → ℝ) (U a : ℝ) : GridOK S F U [a] ↔ True := Iff.rfl

theorem grid_aux (S F : ℝ → ℝ) (U : ℝ)
    (hS : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s)
    (hF : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t)
    (h0 : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) :
    ∀ (rest : List ℝ) (a b : ℝ), GridOK S F U (a :: b :: rest) →
      (a :: b :: rest).getLast? = some 1 → 0 ≤ a →
      a ≤ 1 ∧ ∀ t, a ≤ t → t ≤ 1 → S t * F t ≤ U := by
  intro rest
  induction rest with
  | nil =>
    intro a b hG hL ha
    obtain ⟨hab, hcell, -⟩ := (GridOK_cons2 S F U a b []).1 hG
    have hb : b = 1 := by simpa using hL
    subst hb
    refine ⟨hab, fun t hat ht1 => ?_⟩
    have h1 := hS a t ha hat ht1
    have h2 := hF t 1 (le_trans ha hat) ht1 le_rfl
    obtain ⟨sa, -⟩ := h0 a ha hab
    obtain ⟨-, ft⟩ := h0 t (le_trans ha hat) ht1
    calc S t * F t ≤ S a * F t := mul_le_mul_of_nonneg_right h1 ft
      _ ≤ S a * F 1 := mul_le_mul_of_nonneg_left h2 sa
      _ ≤ U := hcell
  | cons c rest' ih =>
    intro a b hG hL ha
    obtain ⟨hab, hcell, hrest⟩ := (GridOK_cons2 S F U a b (c :: rest')).1 hG
    have hL' : (b :: c :: rest').getLast? = some 1 := by
      rw [List.getLast?_cons_cons] at hL
      exact hL
    obtain ⟨hb1, hrestb⟩ := ih b c hrest hL' (le_trans ha hab)
    refine ⟨le_trans hab hb1, fun t hat ht1 => ?_⟩
    by_cases htb : t ≤ b
    · have h1 := hS a t ha hat ht1
      have h2 := hF t b (le_trans ha hat) htb hb1
      obtain ⟨sa, -⟩ := h0 a ha (le_trans hab hb1)
      obtain ⟨-, ft⟩ := h0 t (le_trans ha hat) ht1
      calc S t * F t ≤ S a * F t := mul_le_mul_of_nonneg_right h1 ft
        _ ≤ S a * F b := mul_le_mul_of_nonneg_left h2 sa
        _ ≤ U := hcell
    · exact hrestb t (not_le.mp htb).le ht1

theorem grid_cert (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ)
    (hS : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s)
    (hF : ∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t)
    (h0 : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t)
    (hG : GridCert S F U ts) : ∀ t, 0 ≤ t → t ≤ 1 → S t * F t ≤ U := by
  obtain ⟨hh, hl, hok⟩ := hG
  rcases ts with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp at hh
  · have e1 : a = 0 := by simpa using hh
    have e2 : a = 1 := by simpa using hl
    rw [e1] at e2
    norm_num at e2
  · have ha : a = 0 := by simpa using hh
    subst ha
    intro t ht0 ht1
    exact (grid_aux S F U hS hF h0 rest 0 b hok hl le_rfl).2 t ht0 ht1

-- binomial CDF facts

theorem bin_anti (m sc : ℕ) : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ 1 → binCDF m sc t ≤ binCDF m sc s := by
  intro s t hs hst ht
  rw [← PLDep_UMSURVF1.claim.2.1 t m sc, ← PLDep_UMSURVF1.claim.2.1 s m sc]
  exact survH_anti (hardKill sc) (PLDep_UMPROTF1.hardKill_prob sc) m 0 s t hs hst ht

theorem bin_nonneg (m sc : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ binCDF m sc t := by
  rw [← PLDep_UMSURVF1.claim.2.1 t m sc]
  exact (PLDep_UMSURVF1.survH_prob t _ h0 h1 (PLDep_UMPROTF1.hardKill_prob sc) m 0).1

-- domination from class coverage (no finiteness of the class type needed)

theorem dom_content {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C]
    (K : C → Z → ℝ) (c : X → C) (PH : X → ℝ) (p : ℝ) (hK : IsKernel K) (hP : IsDist PH)
    (hp : 0 < p) (x : X) (hcov : p ≤ contentLaw c PH (c x)) (z : Z) :
    (fun x => K (c x)) x z ≤ (1 / p) * push (fun x => K (c x)) PH z := by
  show K (c x) z ≤ (1 / p) * push (fun x => K (c x)) PH z
  have key : contentLaw c PH (c x) * K (c x) z ≤ push (fun x => K (c x)) PH z := by
    simp only [contentLaw, push, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro x' _
    unfold delta
    split_ifs with h
    · rw [h, mul_one]
    · rw [mul_zero, zero_mul]
      exact mul_nonneg (hP.1 x') ((hK _).1 z)
  have hK0 : 0 ≤ K (c x) z := (hK (c x)).1 z
  have h1 : p * K (c x) z ≤ push (fun x => K (c x)) PH z :=
    le_trans (mul_le_mul_of_nonneg_right hcov hK0) key
  calc K (c x) z = (1 / p) * (p * K (c x) z) := by field_simp
    _ ≤ (1 / p) * push (fun x => K (c x)) PH z := mul_le_mul_of_nonneg_left h1 (by positivity)

-- the conjuncts

theorem claim_R : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N → 0 ≤ U →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔
       (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ →
          survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ) ≤ U)) := by
  intro X Z _ _ Bad _ M PH κ nh r b N U hM hP hκ hr0 hr1 hN hU
  constructor
  · intro hall x hx ψ hψ
    haveI := Classical.decEq X
    have := hall Unit (fun _ => 1) (fun _ => ψ) (fun _ _ x' => if x' = x then 1 else 0)
      unit_dist (fun _ => hψ) (fun _ _ => point_dist x)
    rwa [oneshot_value Bad M PH κ nh r b N ψ x hM hP hx hN] at this
  · intro hyp Ω _ ρ φ π hρ hφ hπ
    exact reduce_le Bad M PH κ nh r b N U ρ φ π hM hP hρ hφ hπ hκ hr0 hr1 hU hyp

theorem claim_C : ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop)
      [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 0 ≤ U →
      (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 (env t)) ≤ U) →
      protocolCat Bad M PH κ nh r b N ρ φ π ≤ U := by
  intro X Z Ω _ _ _ Bad _ M PH κ nh r b N env U ρ φ π hM hP hρ hφ hπ hκ hr0 hr1 hU henv hcert
  apply reduce_le Bad M PH κ nh r b N U ρ φ π hM hP hρ hφ hπ hκ hr0 hr1 hU
  intro x hx ψ hψ
  obtain ⟨t0, t1⟩ :=
    PLDep_UMSTRATF1.rate01 (push M PH) ψ (PLDep_UMPROTF1.push_dist M PH hM hP) hψ
  obtain ⟨-, a1⟩ := PLDep_UMSTRATF1.rate01 (M x) ψ (hM x) hψ
  have hS := (PLDep_UMSURVF1.survH_prob _ κ t0 t1 hκ nh 0).1
  have hmin : E (M x) ψ ≤ min 1 (env (E (push M PH) ψ)) := le_min a1 (henv x hx ψ hψ)
  calc survH (E (push M PH) ψ) κ nh 0 * capB r b (E (M x) ψ)
      ≤ survH (E (push M PH) ψ) κ nh 0 * capB r b (min 1 (env (E (push M PH) ψ))) :=
        mul_le_mul_of_nonneg_left (capB_mono r b hr0 hmin) hS
    _ ≤ U := hcert _ t0 t1

theorem claim_E1 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (L : ℝ)
      (x : X), (∀ z, M x z ≤ L * push M PH z) →
      ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ L * E (push M PH) ψ := by
  intro X Z _ _ M PH L x hd ψ hψ
  exact PLDep_UMPROTF1.E_dom M PH ψ hψ L x hd

theorem claim_E2 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (PH : X → ℝ) (η δ : ℝ)
      (x : X), hs η (M x) (push M PH) ≤ δ →
      ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ Real.exp η * E (push M PH) ψ + δ := by
  intro X Z _ _ M PH η δ x hhs ψ hψ
  have := PLDep_UMHSF1.t2 Z η (M x) (push M PH) ψ hψ
  linarith

theorem claim_G0 : ∀ (κ : ℕ → ℝ) (n j : ℕ) (s t : ℝ), (∀ i, 0 ≤ κ i ∧ κ i ≤ 1) → 0 ≤ s → s ≤ t →
      t ≤ 1 → survH t κ n j ≤ survH s κ n j :=
  fun κ n j s t hκ hs hst ht => survH_anti κ hκ n j s t hs hst ht

theorem claim_G : ∀ (S F : ℝ → ℝ) (U : ℝ) (ts : List ℝ),
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → S t ≤ S s) →
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → F s ≤ F t) →
      (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ S t ∧ 0 ≤ F t) →
      GridCert S F U ts → ∀ t, 0 ≤ t → t ≤ 1 → S t * F t ≤ U :=
  fun S F U ts hS hF h0 hG => grid_cert S F U ts hS hF h0 hG

theorem claim_CG : ∀ (X Z Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop)
      [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (env : ℝ → ℝ) (U : ℝ)
      (ts : List ℝ) (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel M → IsDist PH → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → ∀ ψ : Z → ℝ, IsRule ψ → E (M x) ψ ≤ env (E (push M PH) ψ)) →
      (∀ s t, 0 ≤ s → s ≤ t → t ≤ 1 → env s ≤ env t) → (∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ env t) →
      GridCert (fun t => survH t κ nh 0) (fun t => capB r b (min 1 (env t))) U ts →
      protocolCat Bad M PH κ nh r b N ρ φ π ≤ U := by
  intro X Z Ω _ _ _ Bad _ M PH κ nh r b N env U ts ρ φ π hM hP hρ hφ hπ hκ hr0 hr1 henv hmono
    hnn hG
  have hcert := grid_cert (fun t => survH t κ nh 0) (fun t => capB r b (min 1 (env t))) U ts
    (fun s t hs hst ht => survH_anti κ hκ nh 0 s t hs hst ht)
    (fun s t hs hst ht => capB_mono r b hr0 (min_le_min_left 1 (hmono s t hs hst ht)))
    (fun t h0 h1 => ⟨(PLDep_UMSURVF1.survH_prob t κ h0 h1 hκ nh 0).1,
       capB_nonneg r b hr0 hr1 (le_min zero_le_one (hnn t h0 h1))⟩) hG
  have hU : 0 ≤ U := by
    have h0 := hcert 0 le_rfl zero_le_one
    have hpos : 0 ≤ survH 0 κ nh 0 * capB r b (min 1 (env 0)) :=
      mul_nonneg (PLDep_UMSURVF1.survH_prob 0 κ le_rfl zero_le_one hκ nh 0).1
        (capB_nonneg r b hr0 hr1 (le_min zero_le_one (hnn 0 le_rfl zero_le_one)))
    exact le_trans hpos h0
  exact claim_C X Z Ω Bad M PH κ nh r b N env U ρ φ π hM hP hρ hφ hπ hκ hr0 hr1 hU henv hcert

theorem claim_S1 : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop)
      [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U) →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U := by
  intro X Z C Ω _ _ _ Bad _ K c Es m sc b N r U ρ φ π hK hρ hφ hπ hr0 hr1 hEs hcert
  have hU : 0 ≤ U := by
    have h0 := hcert 0 le_rfl zero_le_one
    rw [PLDep_UMSTRATF1.binCDF_at_zero, one_mul] at h0
    exact le_trans (capB_nonneg r b hr0 hr1 le_rfl) h0
  unfold stratProtocolCat
  simp_rw [mul_assoc]
  apply PLDep_UMPROTF1.wsum_le _ _ _ hρ
  intro ω
  have hS := PLDep_UMSTRATF1.strat01 K Es (φ ω) m sc hK (hφ ω)
  by_cases hex : ∃ x, Bad x
  · obtain ⟨x0, hx0, hmax⟩ := exists_worst Bad (fun x => E (K (c x)) (φ ω)) hex
    obtain ⟨a0, a1⟩ := PLDep_UMSTRATF1.rate01 (K (c x0)) (φ ω) (hK (c x0)) (hφ ω)
    have hc := PLDep_UMPROTF1.t3a Bad (fun x => K (c x)) (φ ω) (π ω) r (E (K (c x0)) (φ ω)) b
      (fun x => hK (c x)) (hφ ω) (hπ ω) hr0 hr1 a0 a1 hmax N 0 []
    have hle := PLDep_UMSTRATF1.strat_le_factor K Es (φ ω) m sc hK (hφ ω) (c x0) (hEs x0 hx0)
    rw [PLDep_UMSTRATF1.surv_eq_bin (K (c x0)) (φ ω) (hK (c x0)).2] at hle
    have hcap0 : 0 ≤ capB r b (E (K (c x0)) (φ ω)) := capB_nonneg r b hr0 hr1 a0
    calc stratSurv K Es (φ ω) m sc * cat Bad (fun x => K (c x)) (φ ω) (π ω) r b N 0 []
        ≤ stratSurv K Es (φ ω) m sc * capB r b (E (K (c x0)) (φ ω)) :=
          mul_le_mul_of_nonneg_left hc.2 hS.1
      _ ≤ binCDF m sc (E (K (c x0)) (φ ω)) * capB r b (E (K (c x0)) (φ ω)) :=
          mul_le_mul_of_nonneg_right hle hcap0
      _ ≤ U := hcert _ a0 a1
  · push_neg at hex
    rw [cat_empty Bad _ (φ ω) (π ω) r b hex N 0 [], mul_zero]
    exact hU

theorem claim_SG : ∀ (X Z C Ω : Type) [Fintype X] [Fintype Z] [Fintype Ω] (Bad : X → Prop)
      [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ) (ts : List ℝ)
      (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
      IsKernel K → IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) → 0 ≤ r → r ≤ 1 →
      (∀ x, Bad x → c x ∈ Es) →
      GridCert (fun t => binCDF m sc t) (fun t => capB r b t) U ts →
      stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U := by
  intro X Z C Ω _ _ _ Bad _ K c Es m sc b N r U ts ρ φ π hK hρ hφ hπ hr0 hr1 hEs hG
  have hcert := grid_cert (fun t => binCDF m sc t) (fun t => capB r b t) U ts
    (fun s t hs hst ht => bin_anti m sc s t hs hst ht)
    (fun s t _ hst _ => capB_mono r b hr0 hst)
    (fun t h0 h1 => ⟨bin_nonneg m sc t h0 h1, capB_nonneg r b hr0 hr1 h0⟩) hG
  exact claim_S1 X Z C Ω Bad K c Es m sc b N r U ρ φ π hK hρ hφ hπ hr0 hr1 hEs hcert

theorem claim_D1 : ∀ (n s b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 0 ≤ t → t ≤ 1 →
      survH t (hardKill s) n 0 * capB r b (min 1 (L * t)) ≤
        (1 - r) + r * (L * (((s : ℝ) + 1) / ((n : ℝ) + 1))) := by
  intro n s b r L t hr0 hr1 hL ht0 ht1
  rw [PLDep_UMSURVF1.claim.2.1 t n s]
  have hS1 := PLDep_UMSURVF1.binCDF_le_one n s t ht0 ht1
  have hS0 := bin_nonneg n s t ht0 ht1
  have hfm := PLDep_UMSURVF1.first_moment' n s t ht0 ht1
  calc binCDF n s t * capB r b (min 1 (L * t))
      ≤ binCDF n s t * (1 - r + r * min 1 (L * t)) :=
        mul_le_mul_of_nonneg_left (capB_le r b hr0 hr1 (min_le_left _ _)) hS0
    _ ≤ _ := PLDep_UMPROTF1.final_dom _ t L r _ _ hS0 hS1 hr0 hr1 hL (min_le_right _ _) hfm

theorem claim_D2 : ∀ (n ns b : ℕ) (r L t : ℝ), 0 ≤ r → r ≤ 1 → 0 ≤ L → 1 ≤ ns → 0 ≤ t → t ≤ 1 →
      survH t (softKill ns) n 0 * capB r b (min 1 (L * t)) ≤
        (1 - r) + r * (L * ((ns : ℝ) / ((n : ℝ) + 1))) := by
  intro n ns b r L t hr0 hr1 hL hns ht0 ht1
  have hns' : (1 : ℝ) ≤ (ns : ℝ) := by exact_mod_cast hns
  have hk0 : (0 : ℝ) < 1 / (ns : ℝ) := by positivity
  have hk1 : 1 / (ns : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hns'
  have hsp := PLDep_UMSURVF1.survH_prob t (softKill ns) ht0 ht1 (fun _ => ⟨hk0.le, hk1⟩) n 0
  have hsc : survH t (softKill ns) n 0 = (1 - 1 / (ns : ℝ) * t) ^ n :=
    PLDep_UMSURVF1.survH_const _ _ n 0
  have hfm := PLDep_UMSURVF1.claim.2.2.2.2.1 n t (1 / (ns : ℝ)) ht0 ht1 hk0 hk1
  have hq : 1 / (1 / (ns : ℝ) * ((n : ℝ) + 1)) = (ns : ℝ) / ((n : ℝ) + 1) := by
    field_simp
  rw [hq, ← hsc] at hfm
  calc survH t (softKill ns) n 0 * capB r b (min 1 (L * t))
      ≤ survH t (softKill ns) n 0 * (1 - r + r * min 1 (L * t)) :=
        mul_le_mul_of_nonneg_left (capB_le r b hr0 hr1 (min_le_left _ _)) hsp.1
    _ ≤ _ := PLDep_UMPROTF1.final_dom _ t L r _ _ hsp.1 hsp.2 hr0 hr1 hL (min_le_right _ _) hfm

theorem claim_F : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → 1 ≤ N → (∃ x, Bad x) →
      (∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U := by
  intro X Z _ _ Bad _ M PH κ nh r b N U hM hP hN hex hall t ht0 ht1
  haveI := Classical.decEq X
  obtain ⟨x, hx⟩ := hex
  have hψ : IsRule (fun _ : Z => t) := fun _ => ⟨ht0, ht1⟩
  have := hall Unit (fun _ => 1) (fun _ => fun _ => t) (fun _ _ x' => if x' = x then 1 else 0)
    unit_dist (fun _ => hψ) (fun _ _ => point_dist x)
  rw [oneshot_value Bad M PH κ nh r b N _ x hM hP hx hN,
    E_const _ (PLDep_UMPROTF1.push_dist M PH hM hP).2, E_const _ (hM x).2] at this
  exact this

theorem claim_X : ∀ (X Z : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel M → IsDist PH → (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      (∃ x, Bad x) → (∀ x, Bad x → ∀ z, M x z ≤ push M PH z) →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad M PH κ nh r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b t ≤ U)) := by
  intro X Z _ _ Bad _ M PH κ nh r b N U hM hP hκ hr0 hr1 hN hex hdom
  constructor
  · exact claim_F X Z Bad M PH κ nh r b N U hM hP hN hex
  · intro hcert Ω _ ρ φ π hρ hφ hπ
    have hU : 0 ≤ U := by
      have h0 := hcert 0 le_rfl zero_le_one
      have hpos : 0 ≤ survH 0 κ nh 0 * capB r b 0 :=
        mul_nonneg (PLDep_UMSURVF1.survH_prob 0 κ le_rfl zero_le_one hκ nh 0).1
          (capB_nonneg r b hr0 hr1 le_rfl)
      exact le_trans hpos h0
    apply claim_C X Z Ω Bad M PH κ nh r b N (fun t => t) U ρ φ π hM hP hρ hφ hπ hκ hr0 hr1 hU
    · intro x hx ψ hψ
      have := PLDep_UMPROTF1.E_dom M PH ψ hψ 1 x (fun z => by rw [one_mul]; exact hdom x hx z)
      rw [one_mul] at this
      exact this
    · intro t ht0 ht1
      show survH t κ nh 0 * capB r b (min 1 t) ≤ U
      rw [min_eq_right ht1]
      exact hcert t ht0 ht1

theorem claim_Xp : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [DecidableEq C] (Bad : X → Prop)
      [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ) (p : ℝ)
      (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (U : ℝ),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → IsDist PH → 0 < p →
      (∀ x, Bad x → p ≤ contentLaw c PH (c x)) → (∃ x, Bad x ∧ contentLaw c PH (c x) = p) →
      (∀ j, 0 ≤ κ j ∧ κ j ≤ 1) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          protocolCat Bad (fun x => K (c x)) PH κ nh r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → survH t κ nh 0 * capB r b (min 1 ((1 / p) * t)) ≤ U)) := by
  intro X Z C _ _ _ Bad _ K c g PH p κ nh r b N U hK hdec hP hp hcov hatt hκ hr0 hr1 hN
  have hM : IsKernel (fun x => K (c x)) := fun x => hK (c x)
  constructor
  · intro hall
    haveI := Classical.decEq X
    obtain ⟨x0, hx0, hpx0⟩ := hatt
    have key : ∀ s, 0 ≤ s → s ≤ p → survH s κ nh 0 * capB r b (s / p) ≤ U := by
      intro s hs0 hsp
      have hsp1 : s / p ≤ 1 := (div_le_one hp).2 hsp
      have hsp0 : 0 ≤ s / p := div_nonneg hs0 hp.le
      have hψ : IsRule (fun z => if g z = c x0 then s / p else 0) := by
        intro z
        dsimp only
        split_ifs
        · exact ⟨hsp0, hsp1⟩
        · exact ⟨le_rfl, zero_le_one⟩
      have hEK : ∀ e, E (K e) (fun z => if g z = c x0 then s / p else 0) =
          if e = c x0 then s / p else 0 :=
        fun e => PLDep_UMSTRATF1.E_dec K g (s / p) (c x0) e hK hdec
      have hEpush : E (push (fun x => K (c x)) PH) (fun z => if g z = c x0 then s / p else 0)
          = s := by
        rw [E_push]
        simp only [hEK]
        have hsum : ∑ x, PH x * (if c x = c x0 then s / p else 0)
            = s / p * contentLaw c PH (c x0) := by
          simp only [contentLaw, push, delta]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          by_cases h : c x = c x0
          · rw [if_pos h, if_pos h.symm]
            ring
          · rw [if_neg h, if_neg (Ne.symm h)]
            ring
        rw [hsum, hpx0]
        field_simp
      have := hall Unit (fun _ => 1) (fun _ => fun z => if g z = c x0 then s / p else 0)
        (fun _ _ x' => if x' = x0 then 1 else 0) unit_dist (fun _ => hψ)
        (fun _ _ => point_dist x0)
      rw [oneshot_value Bad (fun x => K (c x)) PH κ nh r b N _ x0 hM hP hx0 hN, hEpush] at this
      have h2 : E ((fun x => K (c x)) x0) (fun z => if g z = c x0 then s / p else 0) = s / p := by
        show E (K (c x0)) (fun z => if g z = c x0 then s / p else 0) = s / p
        rw [hEK, if_pos rfl]
      rw [h2] at this
      exact this
    intro t ht0 ht1
    by_cases htp : t ≤ p
    · have e : min 1 ((1 / p) * t) = t / p := by
        rw [show (1 / p) * t = t / p by ring]
        exact min_eq_right ((div_le_one hp).2 htp)
      rw [e]
      exact key t ht0 htp
    · push_neg at htp
      have e : min 1 ((1 / p) * t) = 1 := by
        rw [show (1 / p) * t = t / p by ring]
        exact min_eq_left ((one_lt_div hp).2 htp).le
      rw [e]
      have hk := key p hp.le le_rfl
      rw [div_self hp.ne'] at hk
      calc survH t κ nh 0 * capB r b 1 ≤ survH p κ nh 0 * capB r b 1 :=
            mul_le_mul_of_nonneg_right (survH_anti κ hκ nh 0 p t hp.le htp.le ht1)
              (by rw [capB_one]; norm_num)
        _ ≤ U := hk
  · intro hcert Ω _ ρ φ π hρ hφ hπ
    have hU : 0 ≤ U := by
      have h0 := hcert 0 le_rfl zero_le_one
      have hpos : 0 ≤ survH 0 κ nh 0 * capB r b (min 1 ((1 / p) * 0)) :=
        mul_nonneg (PLDep_UMSURVF1.survH_prob 0 κ le_rfl zero_le_one hκ nh 0).1
          (capB_nonneg r b hr0 hr1 (le_min zero_le_one (by rw [mul_zero])))
      exact le_trans hpos h0
    apply claim_C X Z Ω Bad (fun x => K (c x)) PH κ nh r b N (fun t => (1 / p) * t) U ρ φ π
      hM hP hρ hφ hπ hκ hr0 hr1 hU
    · intro x hx ψ hψ
      exact PLDep_UMPROTF1.E_dom (fun x => K (c x)) PH ψ hψ (1 / p) x
        (dom_content K c PH p hK hP hp x (hcov x hx))
    · exact hcert

theorem claim_S2 : ∀ (X Z C : Type) [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
      (K : C → Z → ℝ) (c : X → C) (g : Z → C) (Es : Finset C) (m sc b N : ℕ) (r U : ℝ),
      IsKernel K → (∀ e z, K e z ≠ 0 → g z = e) → 0 ≤ r → r ≤ 1 → 1 ≤ N →
      (∃ x, Bad x) → (∀ x, Bad x → c x ∈ Es) →
      ((∀ (Ω : Type) [Fintype Ω] (ρ : Ω → ℝ) (φ : Ω → Z → ℝ) (π : Ω → Hist X Z → X → ℝ),
          IsDist ρ → (∀ ω, IsRule (φ ω)) → (∀ ω h, IsDist (π ω h)) →
          stratProtocolCat Bad K c Es m sc r b N ρ φ π ≤ U) ↔
       (∀ t : ℝ, 0 ≤ t → t ≤ 1 → binCDF m sc t * capB r b t ≤ U)) := by
  intro X Z C _ _ Bad _ K c g Es m sc b N r U hK hdec hr0 hr1 hN hex hEs
  constructor
  · intro hall t ht0 ht1
    haveI := Classical.decEq X
    haveI := Classical.decEq C
    obtain ⟨x, hx⟩ := hex
    have hψ : IsRule (fun z => if g z = c x then t else 0) := by
      intro z
      dsimp only
      split_ifs
      · exact ⟨ht0, ht1⟩
      · exact ⟨le_rfl, zero_le_one⟩
    have := hall Unit (fun _ => 1) (fun _ z => if g z = c x then t else 0)
      (fun _ _ x' => if x' = x then 1 else 0) unit_dist (fun _ => hψ) (fun _ _ => point_dist x)
    rwa [strat_oneshot_value Bad K c g Es m sc b N r t x hK hdec hx (hEs x hx) hN] at this
  · intro hcert Ω _ ρ φ π hρ hφ hπ
    exact claim_S1 X Z C Ω Bad K c Es m sc b N r U ρ φ π hK hρ hφ hπ hr0 hr1 hEs hcert

theorem claim : PL_UMCERTF1.Claim :=
  ⟨claim_R, claim_C, claim_E1, claim_E2, claim_G0, claim_G, claim_CG, claim_SG, claim_D1, claim_D2,
    claim_F, claim_X, claim_Xp, claim_S1, claim_S2⟩

-- the witness

theorem bin12 (s : ℝ) : binCDF 12 1 s = (1 - s) ^ 12 + 12 * s * (1 - s) ^ 11 := by
  simp [binCDF, Finset.sum_range_succ]

theorem bin30 (s : ℝ) : binCDF 30 1 s = (1 - s) ^ 30 + 30 * s * (1 - s) ^ 29 := by
  simp [binCDF, Finset.sum_range_succ]

theorem soft5 (t : ℝ) : survH t (softKill 5) 100 0 = (1 - 1 / 5 * t) ^ 100 := by
  have h : softKill 5 = fun _ => (1 / 5 : ℝ) := by
    funext j
    simp [softKill]
  rw [h]
  exact PLDep_UMSURVF1.survH_const t (1 / 5) 100 0

theorem hard1 (t : ℝ) : survH t (hardKill 1) 30 0 = binCDF 30 1 t :=
  PLDep_UMSURVF1.claim.2.1 t 30 1

theorem capB11 (a : ℝ) : capB 1 1 a = a := by
  unfold capB
  norm_num

theorem capBk (a : ℝ) : capB (9 / 10) 1 a = 1 / 10 + 9 / 10 * a := by
  unfold capB
  norm_num

theorem idK_kernel : IsKernel idK := by
  intro e
  constructor
  · intro z
    unfold idK
    split_ifs <;> norm_num
  · cases e <;> simp [idK]

theorem idK_dec : ∀ e z : Bool, idK e z ≠ 0 → id z = e := by
  intro e z h
  unfold idK at h
  split_ifs at h with hz
  · exact hz
  · exact absurd rfl h

theorem ptTrue_dist : IsDist ptTrue := by
  constructor
  · intro x
    unfold ptTrue
    split_ifs <;> norm_num
  · simp [ptTrue]

theorem w_main : GridCert (fun t => binCDF 12 1 t) (fun t => capB 1 1 t) (7/100) gridMain := by
  unfold GridCert gridMain
  refine ⟨rfl, rfl, ?_⟩
  simp only [GridOK_cons2, GridOK_single, and_true, bin12, capB11]
  norm_num

theorem w_soft : GridCert (fun t => survH t (softKill 5) 100 0)
    (fun t => capB 1 1 (min 1 (1 * t))) (19/1000) gridSoft := by
  unfold GridCert gridSoft
  refine ⟨rfl, rfl, ?_⟩
  simp only [GridOK_cons2, GridOK_single, and_true, soft5, capB11, one_mul]
  norm_num [min_def]

theorem w_kink : GridCert (fun t => survH t (hardKill 1) 30 0)
    (fun t => capB (9/10) 1 (min 1 (4 * t))) (17/100) gridKink := by
  unfold GridCert gridKink
  refine ⟨rfl, rfl, ?_⟩
  simp only [GridOK_cons2, GridOK_single, and_true, hard1, bin30, capBk]
  norm_num [min_def]

theorem w_strat : (6833/100000 : ℝ) ≤ stratProtocolCat (fun x : Bool => x = true) idK id
    Finset.univ 12 1 1 1 1 (fun _ : Unit => 1) (fun _ z => if z = true then 1/8 else 0)
    (fun _ _ x => if x = true then 1 else 0) := by
  have h := strat_oneshot_value (fun x : Bool => x = true) idK id id Finset.univ 12 1 1 1 1
    (1/8 : ℝ) true idK_kernel idK_dec rfl (Finset.mem_univ _) le_rfl
  refine le_trans ?_ (le_of_eq h.symm)
  rw [bin12, capB11]
  norm_num

theorem w_prot : (6833/100000 : ℝ) ≤ protocolCat (fun x : Bool => x = true) idK ptTrue
    (hardKill 1) 12 1 1 1 (fun _ : Unit => 1) (fun _ _ => 1/8)
    (fun _ _ x => if x = true then 1 else 0) := by
  have h := oneshot_value (fun x : Bool => x = true) idK ptTrue (hardKill 1) 12 1 1 1
    (fun _ => (1/8 : ℝ)) true idK_kernel ptTrue_dist rfl le_rfl
  rw [E_const _ (PLDep_UMPROTF1.push_dist idK ptTrue idK_kernel ptTrue_dist).2,
    E_const _ (idK_kernel true).2] at h
  refine le_trans ?_ (le_of_eq h.symm)
  rw [PLDep_UMSURVF1.claim.2.1, bin12, capB11]
  norm_num

theorem witness : PL_UMCERTF1.Witness := by
  unfold PL_UMCERTF1.Witness
  refine ⟨w_main, ?_, by norm_num, idK_kernel, idK_dec, ptTrue_dist, ?_, w_strat, w_prot,
    w_soft, ?_, by norm_num, w_kink, ?_, by norm_num⟩
  · rw [bin12, capB11]
    norm_num
  · intro x hx z
    subst hx
    cases z <;> simp [push, idK, ptTrue]
  · rw [soft5, capB11]
    norm_num [min_def]
  · rw [hard1, bin30, capBk]
    norm_num [min_def]
