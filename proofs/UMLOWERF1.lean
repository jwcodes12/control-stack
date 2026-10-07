open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1 PL_UMLOWERF1

theorem pat_sum_prod {n : ℕ} (f : Fin n → Bool → ℝ) :
    ∑ pat : Fin n → Bool, ∏ i, f i (pat i) = ∏ i, ∑ b, f i b :=
  (Fintype.prod_sum f).symm

theorem bern_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (pat : Fin n → Bool) :
    0 ≤ ∏ i, (if pat i then a i else 1 - a i) := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs
  · exact (ha i).1
  · linarith [(ha i).2]

theorem bern_sum {n : ℕ} (a : Fin n → ℝ) :
    ∑ pat : Fin n → Bool, ∏ i, (if pat i then a i else 1 - a i) = 1 := by
  rw [pat_sum_prod (fun i b => if b then a i else 1 - a i)]
  simp

theorem bern_mean {n : ℕ} (a : Fin n → ℝ) :
    ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) *
      ((univ.filter (fun i => pat i = true)).card : ℝ) = ∑ i, a i := by
  have h1 : ∀ pat : Fin n → Bool, ((univ.filter (fun i => pat i = true)).card : ℝ) =
      ∑ j, (if pat j = true then (1:ℝ) else 0) := by
    intro pat; rw [Finset.sum_boole]
  simp_rw [h1, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have h2 : ∀ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) *
      (if pat j = true then (1:ℝ) else 0) =
      ∏ i, ((if pat i then a i else 1 - a i) *
        (if i = j then (if pat i = true then (1:ℝ) else 0) else 1)) := by
    intro pat
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' univ j]
    simp
  simp_rw [h2]
  rw [pat_sum_prod (fun i b => (if b then a i else 1 - a i) *
    (if i = j then (if b = true then (1:ℝ) else 0) else 1))]
  have h3 : ∀ i, ∑ b : Bool, (if b then a i else 1 - a i) *
      (if i = j then (if b = true then (1:ℝ) else 0) else 1) = if i = j then a j else 1 := by
    intro i
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  simp_rw [h3]
  simp

theorem keep_lb (ns : ℕ) (k : ℝ) (m : ℕ) (hk0 : 0 ≤ k) (hk : m ≤ ns → k = 1) :
    1 - (m : ℝ) / ((ns : ℝ) + 1) ≤ k := by
  by_cases h : m ≤ ns
  · rw [hk h]
    have : 0 ≤ (m : ℝ) / ((ns : ℝ) + 1) := by positivity
    linarith
  · push_neg at h
    have h' : (ns : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast h
    have : 1 ≤ (m : ℝ) / ((ns : ℝ) + 1) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith

theorem inner_lb {n : ℕ} (ns : ℕ) (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (kp : (Fin n → Bool) → ℝ) (hk0 : ∀ pat, 0 ≤ kp pat)
    (hk1 : ∀ pat, (univ.filter (fun i => pat i = true)).card ≤ ns → kp pat = 1) :
    1 - (∑ i, a i) / ((ns : ℝ) + 1) ≤
      ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * kp pat := by
  calc 1 - (∑ i, a i) / ((ns : ℝ) + 1)
      = ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) *
          (1 - ((univ.filter (fun i => pat i = true)).card : ℝ) / ((ns : ℝ) + 1)) := by
        simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib, bern_sum, mul_div_assoc',
          ← Finset.sum_div, bern_mean]
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro pat _
        apply mul_le_mul_of_nonneg_left _ (bern_nonneg a ha pat)
        exact keep_lb ns (kp pat) _ (hk0 pat) (hk1 pat)

theorem inner_nonneg {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (kp : (Fin n → Bool) → ℝ) (hk0 : ∀ pat, 0 ≤ kp pat) :
    0 ≤ ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) * kp pat :=
  Finset.sum_nonneg (fun pat _ => mul_nonneg (bern_nonneg a ha pat) (hk0 pat))

theorem pass_eq {X Z C : Type} [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C)
    (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (t : ℝ) (x ω : X) :
    ∑ z, M x z * (if g z = c ω then t else 0) = if c x = c ω then t else 0 := by
  have h : ∀ z, M x z * (if g z = c ω then t else 0) = M x z * (if c x = c ω then t else 0) := by
    intro z
    by_cases hz : M x z = 0
    · rw [hz, zero_mul, zero_mul]
    · rw [hg x z hz]
  rw [Finset.sum_congr rfl (fun z _ => h z), ← Finset.sum_mul, (hM x).2, one_mul]

theorem class_sum_le {X C : Type} [DecidableEq C] (c : X → C) (S : Finset X)
    (hinj : Set.InjOn c (S : Set X)) (t : ℝ) (ht : 0 ≤ t) (x : X) :
    ∑ ω ∈ S, (if c x = c ω then t else 0) ≤ t := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard : (S.filter (fun ω => c x = c ω)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    simp only [Finset.mem_filter] at ha hb
    exact hinj (Finset.mem_coe.mpr ha.1) (Finset.mem_coe.mpr hb.1) (ha.2.symm.trans hb.2)
  have : ((S.filter (fun ω => c x = c ω)).card : ℝ) ≤ 1 := by exact_mod_cast hcard
  nlinarith

theorem cat_ge {X Z : Type} [Fintype X] [Fintype Z] [DecidableEq X] (Bad : X → Prop)
    [DecidablePred Bad] (M : X → Z → ℝ) (φ : Z → ℝ) (r : ℝ) (b N : ℕ) (ω : X)
    (hM : IsKernel M) (hφ : IsRule φ) (hr1 : r ≤ 1) (hN : 1 ≤ N) (hω : Bad ω) :
    ∑ z, M ω z * φ z ≤ cat Bad M φ (fun _ x => if x = ω then 1 else 0) r b N 0 [] := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [cat]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, hω, ↓reduceIte]
  apply Finset.sum_le_sum
  intro z _
  apply mul_le_mul_of_nonneg_left _ ((hM ω).1 z)
  have h1 : 0 ≤ 1 - φ z := by linarith [(hφ z).2]
  have h2 : 0 ≤ (if 0 < b then 1 - r else (0:ℝ)) := by split_ifs <;> linarith
  nlinarith [mul_nonneg h1 h2]

theorem surv_sum_lb {X Ω : Type} [Fintype X] (n ns : ℕ) (D : (Fin n → X) → ℝ) (hD : IsDist D)
    (keep : (Fin n → X) → (Fin n → Bool) → ℝ) (hkeep : ∀ xs pat, 0 ≤ keep xs pat)
    (hkeep1 : ∀ xs pat, (univ.filter (fun i => pat i = true)).card ≤ ns → keep xs pat = 1)
    (S : Finset Ω) (a : Ω → X → ℝ) (ha : ∀ ω x, 0 ≤ a ω x ∧ a ω x ≤ 1) (t : ℝ)
    (hsumA : ∀ x, ∑ ω ∈ S, a ω x ≤ t) :
    (S.card : ℝ) - n * t / ((ns : ℝ) + 1) ≤ ∑ ω ∈ S, ∑ xs, D xs * ∑ pat : Fin n → Bool,
      (∏ i, (if pat i then a ω (xs i) else 1 - a ω (xs i))) * keep xs pat := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hin : ∀ xs : Fin n → X, (S.card : ℝ) - n * t / ((ns : ℝ) + 1) ≤
      ∑ ω ∈ S, ∑ pat : Fin n → Bool,
        (∏ i, (if pat i then a ω (xs i) else 1 - a ω (xs i))) * keep xs pat := by
    intro xs
    have h1 : ∀ ω ∈ S, 1 - (∑ i, a ω (xs i)) / ((ns : ℝ) + 1) ≤ ∑ pat : Fin n → Bool,
        (∏ i, (if pat i then a ω (xs i) else 1 - a ω (xs i))) * keep xs pat :=
      fun ω _ => inner_lb ns (fun i => a ω (xs i)) (fun i => ha ω (xs i)) (keep xs)
        (hkeep xs) (hkeep1 xs)
    refine le_trans ?_ (Finset.sum_le_sum h1)
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.sum_div,
      Finset.sum_comm]
    have h2 : ∑ i, ∑ ω ∈ S, a ω (xs i) ≤ n * t := by
      calc ∑ i, ∑ ω ∈ S, a ω (xs i) ≤ ∑ _i : Fin n, t :=
            Finset.sum_le_sum (fun i _ => hsumA (xs i))
        _ = n * t := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have h3 : (∑ i, ∑ ω ∈ S, a ω (xs i)) / ((ns : ℝ) + 1) ≤ n * t / ((ns : ℝ) + 1) :=
      div_le_div_of_nonneg_right h2 (by positivity)
    linarith
  calc (S.card : ℝ) - n * t / ((ns : ℝ) + 1)
      = ∑ xs, D xs * ((S.card : ℝ) - n * t / ((ns : ℝ) + 1)) := by
        rw [← Finset.sum_mul, hD.2, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun xs _ => mul_le_mul_of_nonneg_left (hin xs) (hD.1 xs))

theorem combine {X : Type} [Fintype X] [DecidableEq X] (S : Finset X) (n ns : ℕ)
    (sv ct : X → ℝ) (t : ℝ) (hS : 0 < S.card) (ht : 0 ≤ t) (hsv0 : ∀ ω, 0 ≤ sv ω)
    (hct : ∀ ω ∈ S, t ≤ ct ω)
    (hsum : (S.card : ℝ) - n * t / ((ns : ℝ) + 1) ≤ ∑ ω ∈ S, sv ω) :
    t * (1 - t * (n : ℝ) / ((S.card : ℝ) * ((ns : ℝ) + 1))) ≤
      ∑ ω, (if ω ∈ S then 1 / (S.card : ℝ) else 0) * sv ω * ct ω := by
  have hk : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS
  have hρsv : ∀ ω, (if ω ∈ S then 1 / (S.card : ℝ) else 0) * sv ω * t ≤
      (if ω ∈ S then 1 / (S.card : ℝ) else 0) * sv ω * ct ω := by
    intro ω
    split_ifs with h
    · exact mul_le_mul_of_nonneg_left (hct ω h) (mul_nonneg (by positivity) (hsv0 ω))
    · simp
  refine le_trans ?_ (Finset.sum_le_sum (fun ω _ => hρsv ω))
  have e : ∑ ω, (if ω ∈ S then 1 / (S.card : ℝ) else 0) * sv ω * t =
      t / (S.card : ℝ) * ∑ ω ∈ S, sv ω := by
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem_eq, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro ω _; ring
  rw [e]
  calc t * (1 - t * (n : ℝ) / ((S.card : ℝ) * ((ns : ℝ) + 1)))
      = t / (S.card : ℝ) * ((S.card : ℝ) - n * t / ((ns : ℝ) + 1)) := by
        field_simp
    _ ≤ t / (S.card : ℝ) * ∑ ω ∈ S, sv ω := mul_le_mul_of_nonneg_left hsum (by positivity)

theorem claim : PL_UMLOWERF1.Claim := by
  intro X Z C _ _ _ _ Bad _ M c S hset
  obtain ⟨hM, hcp, hbad, hinj, hS⟩ := hset
  obtain ⟨g, hg⟩ := hcp
  refine ⟨g, hg, ?_⟩
  intro n ns D keep htest t ht0 ht1
  obtain ⟨hD, hkeep, hkeep1⟩ := htest
  have hk : (0 : ℝ) < (S.card : ℝ) := by exact_mod_cast hS
  have hpe := pass_eq M c g hM hg t
  have ha : ∀ ω x, 0 ≤ ∑ z, M x z * (if g z = c ω then t else 0) ∧
      ∑ z, M x z * (if g z = c ω then t else 0) ≤ 1 := by
    intro ω x
    rw [hpe x ω]
    split_ifs <;> constructor <;> linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro ω; unfold seedLaw; split_ifs <;> positivity
    · unfold seedLaw
      rw [Finset.sum_ite_mem_eq, Finset.sum_const, nsmul_eq_mul]
      field_simp
  · intro ω h
    by_contra hω
    exact h (by unfold seedLaw; exact if_neg hω)
  · intro ω z
    unfold classRule
    split_ifs <;> constructor <;> linarith
  · intro ω h
    constructor
    · intro x; unfold seedPolicy; split_ifs <;> norm_num
    · simp [seedPolicy]
  · intro r b N hr0 hr1 hN
    unfold designProtocolCat seedLaw classRule seedPolicy
    apply combine S n ns
      (fun ω => designSurv n D M (fun z => if g z = c ω then t else 0) keep)
      (fun ω => cat Bad M (fun z => if g z = c ω then t else 0)
        (fun _ x => if x = ω then 1 else 0) r b N 0 []) t hS ht0
    · intro ω
      unfold designSurv
      exact Finset.sum_nonneg (fun xs _ => mul_nonneg (hD.1 xs)
        (inner_nonneg (fun i => ∑ z, M (xs i) z * (if g z = c ω then t else 0))
          (fun i => ha ω (xs i)) (keep xs) (fun pat => (hkeep xs pat).1)))
    · intro ω hω
      have := cat_ge Bad M (fun z => if g z = c ω then t else 0) r b N ω hM
        (fun z => by dsimp only; split_ifs <;> constructor <;> linarith) hr1 hN (hbad ω hω)
      rw [hpe ω ω, if_pos rfl] at this
      exact this
    · unfold designSurv
      exact surv_sum_lb n ns D hD keep (fun xs pat => (hkeep xs pat).1) hkeep1 S
        (fun ω x => ∑ z, M x z * (if g z = c ω then t else 0)) ha t
        (fun x => by simp_rw [hpe x]; exact class_sum_le c S hinj t ht0 x)

theorem none_pass {n : ℕ} (a : Fin n → ℝ) :
    ∑ pat : Fin n → Bool, (∏ i, (if pat i then a i else 1 - a i)) *
      (if (univ.filter (fun i => pat i = true)).card ≤ 0 then (1 : ℝ) else 0) =
      ∏ i, (1 - a i) := by
  have h1 : ∀ pat : Fin n → Bool,
      (if (univ.filter (fun i => pat i = true)).card ≤ 0 then (1 : ℝ) else 0) =
      ∏ i, (if pat i = true then (0 : ℝ) else 1) := by
    intro pat
    have e : ∀ i, (if pat i = true then (0 : ℝ) else 1) = if pat i = false then 1 else 0 := by
      intro i; cases pat i <;> simp
    simp_rw [e]
    rw [Fintype.prod_boole]
    by_cases h : ∀ i, pat i = false
    · rw [if_pos h, if_pos]
      simp [h]
    · rw [if_neg h, if_neg]
      push_neg at h
      obtain ⟨i, hi⟩ := h
      have : i ∈ univ.filter (fun i => pat i = true) := by simp [hi]
      have := Finset.card_pos.mpr ⟨i, this⟩
      omega
  simp_rw [h1, ← Finset.prod_mul_distrib]
  rw [pat_sum_prod (fun i b => (if b then a i else 1 - a i) * (if b = true then (0 : ℝ) else 1))]
  simp

theorem witness : PL_UMLOWERF1.Witness := by
  unfold PL_UMLOWERF1.Witness
  have hMk : IsKernel witnessM := by
    intro x
    constructor
    · intro z; unfold witnessM; split_ifs <;> norm_num
    · simp [witnessM]
  refine ⟨⟨hMk, ⟨id, ?_⟩, fun _ _ => trivial, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x z h
    by_contra hne
    exact h (by unfold witnessM; exact if_neg hne)
  · intro a _ b _ h; exact h
  · simp
  · constructor
    · intro xs; unfold witnessD; split_ifs <;> norm_num
    · simp [witnessD]
  · intro xs pat; unfold witnessKeep; split_ifs <;> norm_num
  · intro xs pat h
    unfold witnessKeep
    rw [if_pos h]
  · intro x z h
    by_contra hne
    exact h (by unfold witnessM; exact if_neg hne)
  · constructor
    · intro ω; unfold seedLaw; split_ifs <;> norm_num
    · simp [seedLaw]
  · intro ω _; exact Finset.mem_univ ω
  · intro ω z; unfold classRule; split_ifs <;> norm_num
  · intro ω h
    constructor
    · intro x; unfold seedPolicy; split_ifs <;> norm_num
    · simp [seedPolicy]
  · norm_num
  · norm_num
  · unfold designProtocolCat
    have hs : ∀ ω : Fin 4,
        designSurv 4 witnessD witnessM (classRule id id (1/2) ω) witnessKeep = 1/2 := by
      intro ω
      unfold designSurv witnessD witnessM witnessKeep classRule
      simp only [id_eq, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte]
      rw [none_pass]
      fin_cases ω <;> simp [Fin.prod_univ_four] <;> norm_num
    have hc : ∀ ω : Fin 4, cat (fun _ : Fin 4 => True) witnessM (classRule id id (1/2) ω)
        (seedPolicy (Z := Fin 4) ω) 1 1 1 0 [] = 1/2 := by
      intro ω
      simp [cat, witnessM, classRule, seedPolicy]
    simp_rw [hs, hc]
    norm_num [seedLaw]
