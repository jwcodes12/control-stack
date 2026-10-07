
/-- binomial term -/
lemma binTerm_pascal (n k : ℕ) (h : ℝ) :
    ((n + 1).choose (k + 1) : ℝ) * h ^ (k + 1) * (1 - h) ^ (n + 1 - (k + 1)) =
      h * ((n.choose k : ℝ) * h ^ k * (1 - h) ^ (n - k)) +
      (1 - h) * ((n.choose (k + 1) : ℝ) * h ^ (k + 1) * (1 - h) ^ (n - (k + 1))) := by
  rw [Nat.choose_succ_succ', show n + 1 - (k + 1) = n - k by omega]
  push_cast
  rcases Nat.lt_or_ge k n with hk | hk
  · obtain ⟨m, rfl⟩ : ∃ m, n = k + 1 + m := ⟨n - (k + 1), by omega⟩
    have e2 : k + 1 + m - k = m + 1 := by omega
    have e3 : k + 1 + m - (k + 1) = m := by omega
    rw [e2, e3]
    ring
  · have hc : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have e2 : n - k = 0 := by omega
    rw [hc, e2]
    push_cast
    ring

lemma binCDF_zero_n (s : ℕ) (h : ℝ) : binCDF 0 s h = 1 := by
  unfold binCDF
  rw [Finset.sum_range_succ']
  have : ∀ i ∈ Finset.range s, ((Nat.choose 0 (i + 1) : ℕ) : ℝ) * h ^ (i + 1) * (1 - h) ^ (0 - (i + 1)) = 0 := by
    intro i _
    simp
  rw [Finset.sum_eq_zero this]
  simp

lemma binCDF_n_zero (n : ℕ) (h : ℝ) : binCDF n 0 h = (1 - h) ^ n := by
  unfold binCDF
  simp

lemma binCDF_pascal (n s : ℕ) (h : ℝ) :
    binCDF (n + 1) (s + 1) h = (1 - h) * binCDF n (s + 1) h + h * binCDF n s h := by
  unfold binCDF
  rw [Finset.sum_range_succ' _ (s + 1), Finset.sum_range_succ' _ (s + 1)]
  simp_rw [binTerm_pascal]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp
  ring

lemma survH_hard (h : ℝ) (ns : ℕ) :
    ∀ n j, j ≤ ns → survH h (hardKill ns) n j = binCDF n (ns - j) h := by
  intro n
  induction n with
  | zero =>
    intro j _
    simp [survH, binCDF_zero_n]
  | succ n ih =>
    intro j hj
    rcases Nat.lt_or_ge j ns with hlt | hge
    · have hk : hardKill ns j = 0 := by simp [hardKill]; omega
      simp only [survH, hk, sub_zero, mul_one]
      rw [ih j hj, ih (j + 1) hlt]
      obtain ⟨s, hs⟩ : ∃ s, ns - j = s + 1 := ⟨ns - j - 1, by omega⟩
      have hs' : ns - (j + 1) = s := by omega
      rw [hs, hs', binCDF_pascal]
    · have hje : j = ns := le_antisymm hj hge
      subst hje
      have hk : hardKill j j = 1 := by simp [hardKill]
      simp only [survH, hk, sub_self, mul_zero, zero_mul, add_zero]
      rw [ih j le_rfl, Nat.sub_self, binCDF_n_zero, binCDF_n_zero]
      ring

lemma survH_const (h k : ℝ) : ∀ (n j : ℕ), survH h (fun _ => k) n j = (1 - k * h) ^ n := by
  intro n
  induction n with
  | zero => intro j; simp [survH]
  | succ n ih =>
    intro j
    simp only [survH, ih]
    ring

lemma survH_prob (h : ℝ) (κ : ℕ → ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hκ : ∀ i, 0 ≤ κ i ∧ κ i ≤ 1) :
    ∀ n j, 0 ≤ survH h κ n j ∧ survH h κ n j ≤ 1 := by
  intro n
  induction n with
  | zero => intro j; simp [survH]
  | succ n ih =>
    intro j
    obtain ⟨a0, a1⟩ := ih j
    obtain ⟨b0, b1⟩ := ih (j + 1)
    obtain ⟨k0, k1⟩ := hκ j
    simp only [survH]
    have p1 : 0 ≤ 1 - h := by linarith
    have p2 : 0 ≤ 1 - κ j := by linarith
    have p3 : 0 ≤ h * (1 - κ j) := mul_nonneg hh0 p2
    have p4 : h * (1 - κ j) ≤ h := by nlinarith
    constructor
    · have := mul_nonneg p1 a0
      have := mul_nonneg p3 b0
      linarith
    · have q1 : (1 - h) * survH h κ n j ≤ (1 - h) := by nlinarith
      have q2 : h * (1 - κ j) * survH h κ n (j + 1) ≤ h * (1 - κ j) := by nlinarith
      linarith

lemma binCDF_le_one (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) : binCDF n s h ≤ 1 := by
  have := survH_hard h s n 0 (Nat.zero_le _)
  rw [Nat.sub_zero] at this
  rw [← this]
  exact (survH_prob h (hardKill s) hh0 hh1 (fun i => by
    unfold hardKill; split_ifs <;> norm_num) n 0).2

lemma first_moment (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
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
  have hB := binCDF_le_one (n + 1) (s + 1) h hh0 hh1
  unfold binCDF at hB
  rw [Finset.sum_range_succ'] at hB
  have h0 : 0 ≤ ((n + 1).choose 0 : ℝ) * h ^ 0 * (1 - h) ^ (n + 1 - 0) := by positivity
  have hS : ∑ j ∈ Finset.range (s + 1),
      ((n + 1).choose (j + 1) : ℝ) * h ^ (j + 1) * (1 - h) ^ (n + 1 - (j + 1)) ≤ 1 := by
    linarith
  have hs0 : (0 : ℝ) ≤ (s : ℝ) + 1 := by positivity
  nlinarith

lemma first_moment' (n s : ℕ) (h : ℝ) (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    h * binCDF n s h ≤ ((s : ℝ) + 1) / ((n : ℝ) + 1) := by
  rw [le_div_iff₀ (by positivity)]
  have := first_moment n s h hh0 hh1
  linarith

theorem claim : Claim := by
  unfold Claim
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z _ q φ κ n j hq
    induction n generalizing j with
    | zero => simp [surv, survH]
    | succ n ih =>
      simp only [surv, survH]
      rw [ih j, ih (j + 1)]
      have e : ∀ z, q z * ((1 - φ z) * survH (∑ z, q z * φ z) κ n j +
          φ z * (1 - κ j) * survH (∑ z, q z * φ z) κ n (j + 1)) =
          q z * survH (∑ z, q z * φ z) κ n j +
          (q z * φ z) * ((1 - κ j) * survH (∑ z, q z * φ z) κ n (j + 1) -
            survH (∑ z, q z * φ z) κ n j) := by
        intro z; ring
      simp_rw [e]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, hq]
      ring
  · intro h n ns
    rw [survH_hard h ns n 0 (Nat.zero_le _), Nat.sub_zero]
  · intro h k n
    exact survH_const h k n 0
  · intro n s h hh0 hh1
    exact first_moment' n s h hh0 hh1
  · intro n h k hh0 hh1 hk0 hk1
    have hu0 : 0 ≤ k * h := mul_nonneg hk0.le hh0
    have hu1 : k * h ≤ 1 := by nlinarith
    have := first_moment' n 0 (k * h) hu0 hu1
    rw [binCDF_n_zero] at this
    have h1 : k * h * (1 - k * h) ^ n ≤ 1 / ((n : ℝ) + 1) := by simpa using this
    rw [le_div_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity)]
    have e : h * (1 - k * h) ^ n * (k * ((n : ℝ) + 1)) =
        k * h * (1 - k * h) ^ n * ((n : ℝ) + 1) := by ring
    rw [e]
    exact h1
  · intro h κ n j hh0 hh1 hκ
    exact survH_prob h κ hh0 hh1 hκ n j

theorem witness : Witness := by
  unfold Witness
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [survH, hardKill]
    norm_num
  · simp [binCDF]
    norm_num
  · simp [binCDF]
    norm_num
  · norm_num
