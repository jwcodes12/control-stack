open Finset PL_UMHSF1 PL_UMSURVF1 PL_UMPROTF1

lemma submit_sum {X Z : Type} [Fintype X] (xs : X) (ω : Unit) (h : Hist X Z) (f : X → ℝ) :
    ∑ x, submit (Z := Z) xs ω h x * f x = f xs := by
  classical
  rw [Finset.sum_eq_single xs]
  · simp [submit]
  · intro x _ hx
    simp [submit, hx]
  · intro hn
    exact absurd (Finset.mem_univ xs) hn

lemma submit_dist {X Z : Type} [Fintype X] (xs : X) (ω : Unit) (h : Hist X Z) :
    IsDist (submit (Z := Z) xs ω h) := by
  constructor
  · intro x
    unfold submit
    split_ifs <;> norm_num
  · have := submit_sum (Z := Z) xs ω h (fun _ => 1)
    simpa using this

lemma classMonitor_rule {Z C : Type} [DecidableEq C] (g : Z → C) (e : C) (t : ℝ)
    (h0 : 0 ≤ t) (h1 : t ≤ 1) : ∀ ω, IsRule (classMonitor g e t ω) := by
  intro ω z
  unfold classMonitor
  split_ifs
  · exact ⟨h0, h1⟩
  · exact ⟨le_refl 0, zero_le_one⟩

lemma protocolCat_unit {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (PH : X → ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ)
    (φ : Unit → Z → ℝ) (π : Unit → Hist X Z → X → ℝ) :
    protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) φ π =
      surv (push M PH) (φ ()) κ nh 0 * cat Bad M (φ ()) (π ()) r b N 0 [] := by
  unfold protocolCat
  rw [Fintype.sum_unique]
  simp only [one_mul]

lemma cat_submit {X Z : Type} [Fintype X] [Fintype Z] (Bad : X → Prop) [DecidablePred Bad]
    (M : X → Z → ℝ) (φ : Z → ℝ) (xs : X) (hx : Bad xs) (r : ℝ) (b N : ℕ) (hN : 1 ≤ N) :
    cat Bad M φ (submit (Z := Z) xs ()) r b N 0 [] =
      ∑ z, M xs z * (φ z * 1 + (1 - φ z) * (if 0 < b then 1 - r else 0)) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  rw [cat, submit_sum]
  simp only [hx, ↓reduceIte]

lemma rate_eq {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C] (M : X → Z → ℝ)
    (c : X → C) (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x)
    (PH : X → ℝ) (e : C) (t : ℝ) :
    ∑ z, push M PH z * classMonitor g e t () z = t * contentLaw c PH e := by
  have key : ∀ x, ∑ z, M x z * classMonitor g e t () z = t * delta (c x) e := by
    intro x
    have h1 : ∀ z, M x z * classMonitor g e t () z = M x z * (t * delta (c x) e) := by
      intro z
      by_cases hz : M x z = 0
      · rw [hz]; ring
      · simp only [classMonitor, delta, hg x z hz]
        by_cases hce : c x = e
        · simp [hce]
        · simp [hce, Ne.symm hce]
    rw [Finset.sum_congr rfl (fun z _ => h1 z), ← Finset.sum_mul, (hM x).2, one_mul]
  simp only [push, contentLaw, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum, key x]
  ring

lemma pass_sum {X Z C : Type} [Fintype Z] [DecidableEq C] (M : X → Z → ℝ) (c : X → C)
    (g : Z → C) (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (xs : X) (t K : ℝ) :
    ∑ z, M xs z * (classMonitor g (c xs) t () z * 1 + (1 - classMonitor g (c xs) t () z) * K)
      = t + (1 - t) * K := by
  have h1 : ∀ z, M xs z * (classMonitor g (c xs) t () z * 1
      + (1 - classMonitor g (c xs) t () z) * K) = M xs z * (t + (1 - t) * K) := by
    intro z
    by_cases hz : M xs z = 0
    · rw [hz]; ring
    · simp [classMonitor, hg xs z hz]
  rw [Finset.sum_congr rfl (fun z _ => h1 z), ← Finset.sum_mul, (hM xs).2, one_mul]

lemma prot_formula {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C]
    (Bad : X → Prop) [DecidablePred Bad] (M : X → Z → ℝ) (c : X → C) (g : Z → C)
    (PH : X → ℝ) (xs : X)
    (hM : IsKernel M) (hg : ∀ x z, M x z ≠ 0 → g z = c x) (hPH : IsDist PH) (hx : Bad xs)
    (t : ℝ) (κ : ℕ → ℝ) (nh : ℕ) (r : ℝ) (b N : ℕ) (hN : 1 ≤ N) :
    protocolCat Bad M PH κ nh r b N (fun _ : Unit => 1) (classMonitor g (c xs) t)
        (submit (Z := Z) xs) =
      survH (t * contentLaw c PH (c xs)) κ nh 0 * (t + (1 - t) * (if 0 < b then 1 - r else 0)) := by
  rw [protocolCat_unit, PLDep_UMPROTF1.surv_eq M PH _ κ nh hM hPH, rate_eq M c g hM hg PH (c xs) t,
    cat_submit Bad M _ xs hx r b N hN, pass_sum M c g hM hg xs t]

lemma survH_ge (h : ℝ) (κ : ℕ → ℝ) (h0 : 0 ≤ h) (h1 : h ≤ 1) (hκ : ∀ j, 0 ≤ κ j ∧ κ j ≤ 1) :
    ∀ n j, (1 - h) ^ n ≤ survH h κ n j := by
  intro n
  induction n with
  | zero => intro j; simp [survH]
  | succ n ih =>
    intro j
    simp only [survH]
    have a := ih j
    have b := (PLDep_UMSURVF1.survH_prob h κ h0 h1 hκ n (j + 1)).1
    have k := hκ j
    have p : 0 ≤ h * (1 - κ j) * survH h κ n (j + 1) :=
      mul_nonneg (mul_nonneg h0 (by linarith)) b
    have q : (1 - h) * (1 - h) ^ n ≤ (1 - h) * survH h κ n j :=
      mul_le_mul_of_nonneg_left a (by linarith)
    have e : (1 - h) ^ (n + 1) = (1 - h) * (1 - h) ^ n := by ring
    rw [e]
    linarith

lemma contentLaw_nonneg {X C : Type} [Fintype X] [DecidableEq C] (c : X → C) (PH : X → ℝ)
    (hPH : IsDist PH) (e : C) : 0 ≤ contentLaw c PH e := by
  unfold contentLaw push
  apply Finset.sum_nonneg
  intro x _
  apply mul_nonneg (hPH.1 x)
  unfold delta
  dsimp only
  split_ifs <;> norm_num

lemma classes_sum_le {X C : Type} [Fintype X] [DecidableEq C] (c : X → C) (PH : X → ℝ)
    (hPH : IsDist PH) (S : Finset X) (hinj : Set.InjOn c (S : Set X)) :
    ∑ x ∈ S, contentLaw c PH (c x) ≤ 1 := by
  classical
  have inner : ∀ y, ∑ x ∈ S, delta (c y) (c x) ≤ 1 := by
    intro y
    simp only [delta]
    rw [Finset.sum_boole]
    have : (S.filter (fun x => c x = c y)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact hinj ha.1 hb.1 (ha.2.trans hb.2.symm)
    exact_mod_cast this
  unfold contentLaw push
  rw [Finset.sum_comm]
  calc ∑ y, ∑ x ∈ S, PH y * delta (c y) (c x) = ∑ y, PH y * ∑ x ∈ S, delta (c y) (c x) := by
        apply Finset.sum_congr rfl; intro y _; rw [Finset.mul_sum]
    _ ≤ ∑ y, PH y * 1 := by
        apply Finset.sum_le_sum; intro y _
        exact mul_le_mul_of_nonneg_left (inner y) (hPH.1 y)
    _ = 1 := by simp only [mul_one]; exact hPH.2

theorem claim : PL_UMNOGOF1.Claim := by
  unfold PL_UMNOGOF1.Claim
  refine ⟨?_, ?_⟩
  · intro X Z C _ _ _ _ Bad _ M c PH S hM hcp hPH hBad hinj hcard
    classical
    obtain ⟨g, hg⟩ := hcp
    have hk1 : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
    have hkpos : (0 : ℝ) < (S.card : ℝ) := by linarith
    have hsum : ∑ x ∈ S, contentLaw c PH (c x) ≤ ∑ x ∈ S, (1 / (S.card : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div_cancel hkpos.ne']
      exact classes_sum_le c PH hPH S hinj
    obtain ⟨xs, hxsS, hxs⟩ := Finset.exists_le_of_sum_le (Finset.card_pos.mp hcard) hsum
    refine ⟨classMonitor g (c xs) 1, submit xs, classMonitor_rule g (c xs) 1 zero_le_one le_rfl,
      fun ω h => submit_dist xs ω h, ?_, ⟨xs, hxsS, rfl⟩, ?_⟩
    · intro ω z
      unfold classMonitor
      split_ifs
      · right; rfl
      · left; rfl
    · intro nh κ r b N hκ hr0 hr1 hN
      rw [prot_formula Bad M c g PH xs hM hg hPH (hBad xs hxsS) 1 κ nh r b N hN]
      have hp0 := contentLaw_nonneg c PH hPH (c xs)
      have hinv : 1 / (S.card : ℝ) ≤ 1 := by rw [div_le_one hkpos]; exact hk1
      have hp1 : contentLaw c PH (c xs) ≤ 1 := le_trans hxs hinv
      have h0 : 0 ≤ 1 - 1 / (S.card : ℝ) := by linarith
      have hle : 1 - 1 / (S.card : ℝ) ≤ 1 - 1 * contentLaw c PH (c xs) := by linarith
      have s1 := pow_le_pow_left₀ h0 hle nh
      have s2 := survH_ge (1 * contentLaw c PH (c xs)) κ (by linarith) (by linarith) hκ nh 0
      simp only [sub_self, zero_mul, add_zero, mul_one, one_mul]
      simp only [one_mul] at s1 s2
      linarith
  · intro X Z C _ _ _ _ Bad _ M c PH xs t hM hcp hPH hx ht0 ht1
    obtain ⟨g, hg⟩ := hcp
    refine ⟨classMonitor g (c xs) t, submit xs, classMonitor_rule g (c xs) t ht0 ht1,
      fun ω h => submit_dist xs ω h, rfl, ?_⟩
    intro nh ns b N hN
    rw [prot_formula Bad M c g PH xs hM hg hPH hx t (hardKill ns) nh 1 b N hN,
      PLDep_UMSURVF1.survH_hard _ ns nh 0 (Nat.zero_le _), Nat.sub_zero]
    have hK : (if 0 < b then (1 : ℝ) - 1 else 0) = 0 := by split_ifs <;> norm_num
    rw [hK]
    ring

lemma witnessM_kernel : IsKernel witnessM := by
  intro x
  constructor
  · intro z
    unfold witnessM
    split_ifs <;> norm_num
  · simp [witnessM]

lemma witnessM_dec : ∀ x z, witnessM x z ≠ 0 → (id : Fin 4 → Fin 4) z = id x := by
  intro x z h
  unfold witnessM at h
  split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

lemma witnessPH_dist : IsDist witnessPH := by
  constructor
  · intro x
    unfold witnessPH
    norm_num
  · simp [witnessPH]

lemma witness_content : contentLaw (id : Fin 4 → Fin 4) witnessPH 2 = 1 / 4 := by
  simp [contentLaw, push, delta, witnessPH]

lemma witnessS_card : witnessS.card = 4 := by
  simp [witnessS]

theorem witness : PL_UMNOGOF1.Witness := by
  unfold PL_UMNOGOF1.Witness
  have hp := fun (t : ℝ) => prot_formula witnessBad witnessM (id : Fin 4 → Fin 4) id witnessPH
    (2 : Fin 4) witnessM_kernel witnessM_dec witnessPH_dist trivial t (hardKill 0) 2 1 1 1 le_rfl
  refine ⟨witnessM_kernel, ⟨id, witnessM_dec⟩, witnessPH_dist, fun _ _ => trivial,
    fun a _ b _ h => h, witnessS_card, by rw [witnessS_card]; norm_num, trivial,
    PLDep_UMPROTF1.hardKill_prob 0, by norm_num, by norm_num, le_rfl, by norm_num, by norm_num,
    witness_content, classMonitor_rule _ _ 1 zero_le_one le_rfl, ?_,
    classMonitor_rule _ _ (1 / 2) (by norm_num) (by norm_num),
    fun ω h => submit_dist (2 : Fin 4) ω h, ?_, ?_, ?_, ?_⟩
  · intro ω z
    unfold classMonitor
    split_ifs
    · right; rfl
    · left; rfl
  · rw [witnessS_card]; norm_num
  · refine (hp 1).trans ?_
    rw [PLDep_UMSURVF1.survH_hard _ 0 2 0 le_rfl, Nat.sub_zero,
      PLDep_UMSURVF1.binCDF_n_zero]
    simp only [id_eq]
    rw [witness_content]
    norm_num
  · refine (hp (1 / 2)).trans ?_
    rw [PLDep_UMSURVF1.survH_hard _ 0 2 0 le_rfl, Nat.sub_zero,
      PLDep_UMSURVF1.binCDF_n_zero]
    simp only [id_eq]
    rw [witness_content]
    norm_num
  · rw [witness_content, PLDep_UMSURVF1.binCDF_n_zero]
    norm_num
