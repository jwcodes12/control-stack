theorem mul_le_max0 (a φ : ℝ) (h0 : 0 ≤ φ) (h1 : φ ≤ 1) : a * φ ≤ max 0 a := by
  have h2 : a ≤ max 0 a := le_max_right 0 a
  have h3 : 0 ≤ max 0 a := le_max_left 0 a
  calc a * φ ≤ max 0 a * φ := mul_le_mul_of_nonneg_right h2 h0
    _ ≤ max 0 a * 1 := mul_le_mul_of_nonneg_left h1 h3
    _ = max 0 a := mul_one _

theorem t2 : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q φ : Z → ℝ), IsRule φ →
    E P φ ≤ Real.exp η * E Q φ + hs η P Q := by
  intro Z _ η P Q φ hφ
  unfold E hs
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z _
  have h := mul_le_max0 (P z - Real.exp η * Q z) (φ z) (hφ z).1 (hφ z).2
  have e : P z * φ z = Real.exp η * (Q z * φ z) + (P z - Real.exp η * Q z) * φ z := by ring
  linarith

theorem t2att : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q : Z → ℝ),
    ∃ φ, IsRule φ ∧ E P φ = Real.exp η * E Q φ + hs η P Q := by
  intro Z _ η P Q
  refine ⟨fun z => if 0 < P z - Real.exp η * Q z then 1 else 0, ?_, ?_⟩
  · intro z
    dsimp only
    split_ifs <;> norm_num
  · unfold E hs
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z _
    dsimp only
    split_ifs with h
    · rw [max_eq_right h.le]; ring
    · rw [max_eq_left (not_lt.mp h)]; ring

theorem hs0_symm {Z : Type} [Fintype Z] (P Q : Z → ℝ) (hP : ∑ z, P z = 1) (hQ : ∑ z, Q z = 1) :
    hs 0 Q P = hs 0 P Q := by
  unfold hs
  simp only [Real.exp_zero, one_mul]
  have key : ∀ z, max 0 (Q z - P z) = max 0 (P z - Q z) + (Q z - P z) := by
    intro z
    rcases le_total (P z) (Q z) with h | h
    · rw [max_eq_right (show (0:ℝ) ≤ Q z - P z by linarith),
        max_eq_left (show P z - Q z ≤ 0 by linarith)]; ring
    · rw [max_eq_left (show Q z - P z ≤ 0 by linarith),
        max_eq_right (show (0:ℝ) ≤ P z - Q z by linarith)]; ring
  rw [Finset.sum_congr rfl (fun z _ => key z), Finset.sum_add_distrib, Finset.sum_sub_distrib,
    hP, hQ]
  ring

theorem t1 : ∀ (Z : Type) [Fintype Z] (P Q φ : Z → ℝ), IsDist P → IsDist Q → IsRule φ →
    |E P φ - E Q φ| ≤ hs 0 P Q := by
  intro Z _ P Q φ hP hQ hφ
  have h1 := t2 Z 0 P Q φ hφ
  have h2 := t2 Z 0 Q P φ hφ
  rw [hs0_symm P Q hP.2 hQ.2] at h2
  rw [Real.exp_zero, one_mul] at h1 h2
  rw [abs_le]
  constructor <;> linarith

theorem max0_sum_le {X : Type} [Fintype X] (w f : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    max 0 (∑ x, w x * f x) ≤ ∑ x, w x * max 0 (f x) := by
  apply max_le
  · exact Finset.sum_nonneg (fun x _ => mul_nonneg (hw x) (le_max_left _ _))
  · exact Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (le_max_right _ _) (hw x))

theorem t4a : ∀ (X Z : Type) [Fintype X] [Fintype Z] (η : ℝ) (K : X → Z → ℝ) (P Q : X → ℝ),
    IsKernel K → hs η (push K P) (push K Q) ≤ hs η P Q := by
  intro X Z _ _ η K P Q hK
  simp only [hs, push]
  have step : ∀ z, max 0 (∑ x, P x * K x z - Real.exp η * ∑ x, Q x * K x z)
      ≤ ∑ x, K x z * max 0 (P x - Real.exp η * Q x) := by
    intro z
    have e : ∑ x, P x * K x z - Real.exp η * ∑ x, Q x * K x z
        = ∑ x, K x z * (P x - Real.exp η * Q x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro x _; ring
    rw [e]
    exact max0_sum_le (fun x => K x z) _ (fun x => (hK x).1 z)
  calc ∑ z, max 0 (∑ x, P x * K x z - Real.exp η * ∑ x, Q x * K x z)
      ≤ ∑ z, ∑ x, K x z * max 0 (P x - Real.exp η * Q x) :=
        Finset.sum_le_sum (fun z _ => step z)
    _ = ∑ x, ∑ z, K x z * max 0 (P x - Real.exp η * Q x) := Finset.sum_comm
    _ = ∑ x, max 0 (P x - Real.exp η * Q x) := by
      apply Finset.sum_congr rfl; intro x _
      rw [← Finset.sum_mul, (hK x).2, one_mul]

theorem push_contentLaw {X Z C : Type} [Fintype X] [Fintype C] [DecidableEq C]
    (K : C → Z → ℝ) (c : X → C) (P : X → ℝ) :
    push K (contentLaw c P) = push (fun x => K (c x)) P := by
  funext z
  simp only [push, contentLaw, delta, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  simp [Finset.sum_ite_eq']

theorem t4b : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ)
      (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ), ContentOnly M c →
      hs η (push M PA) (push M PH) ≤ hs η (contentLaw c PA) (contentLaw c PH) := by
  intro X Z C _ _ _ _ η M c PA PH hM
  obtain ⟨K, hK, hMK⟩ := hM
  have hM' : M = fun x => K (c x) := funext hMK
  subst hM'
  rw [← push_contentLaw K c PA, ← push_contentLaw K c PH]
  exact t4a C Z η K _ _ hK

theorem delta_dist {C : Type} [Fintype C] [DecidableEq C] (e : C) : IsDist (delta e) := by
  constructor
  · intro e'; unfold delta; split_ifs <;> norm_num
  · simp [delta]

theorem push_decode {X Z C : Type} [Fintype X] [Fintype Z] [DecidableEq C]
    (M : X → Z → ℝ) (c : X → C) (g : Z → C) (hM : IsKernel M)
    (hg : ∀ x z, M x z ≠ 0 → g z = c x)
    (P : X → ℝ) : push (fun z => delta (g z)) (push M P) = contentLaw c P := by
  funext e
  simp only [push, contentLaw, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  have h : ∀ z, P x * M x z * delta (g z) e = P x * delta (c x) e * M x z := by
    intro z
    by_cases h : M x z = 0
    · rw [h]; ring
    · rw [hg x z h]; ring
  rw [Finset.sum_congr rfl (fun z _ => h z), ← Finset.mul_sum, (hM x).2, mul_one]

theorem t4c : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C] (η : ℝ)
      (M : X → Z → ℝ) (c : X → C) (PA PH : X → ℝ),
      IsKernel M → ContentPreserving M c →
      hs η (contentLaw c PA) (contentLaw c PH) ≤ hs η (push M PA) (push M PH) := by
  intro X Z C _ _ _ _ η M c PA PH hM hc
  obtain ⟨g, hg⟩ := hc
  rw [← push_decode M c g hM hg PA, ← push_decode M c g hM hg PH]
  exact t4a Z C η _ _ _ (fun z => delta_dist (g z))

theorem t5d : ∀ (Z : Type) [Fintype Z] (η : ℝ) (P Q P' Q' : Z → ℝ),
      hs η P Q ≤ hs η P' Q' + ∑ z, max 0 (P z - P' z)
        + Real.exp η * ∑ z, max 0 (Q' z - Q z) := by
  intro Z _ η P Q P' Q'
  unfold hs
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum; intro z _
  have he := Real.exp_pos η
  have h1 := le_max_right 0 (P' z - Real.exp η * Q' z)
  have h2 := le_max_right 0 (P z - P' z)
  have h3 := le_max_right 0 (Q' z - Q z)
  have h1' := le_max_left 0 (P' z - Real.exp η * Q' z)
  have h2' := le_max_left 0 (P z - P' z)
  have h3' := le_max_left 0 (Q' z - Q z)
  apply max_le
  · have := mul_nonneg he.le h3'; linarith
  · have := mul_le_mul_of_nonneg_left h3 he.le; linarith

theorem sum_max0_mix {Z C : Type} [Fintype Z] [Fintype C] (w : Z → ℝ) (hw : ∀ z, 0 ≤ w z)
    (f : Z → C → ℝ) : ∑ e, max 0 (∑ z, w z * f z e) ≤ ∑ z, w z * ∑ e, max 0 (f z e) := by
  calc ∑ e, max 0 (∑ z, w z * f z e) ≤ ∑ e, ∑ z, w z * max 0 (f z e) :=
        Finset.sum_le_sum (fun e _ => max0_sum_le (fun z => w z) (fun z => f z e) hw)
    _ = ∑ z, ∑ e, w z * max 0 (f z e) := Finset.sum_comm
    _ = ∑ z, w z * ∑ e, max 0 (f z e) := by
        apply Finset.sum_congr rfl; intro z _; rw [Finset.mul_sum]

theorem sum_max0_delta_sub_le {C : Type} [Fintype C] [DecidableEq C] (a b : C) :
    ∑ e, max 0 (delta a e - delta b e) ≤ 1 := by
  calc ∑ e, max 0 (delta a e - delta b e) ≤ ∑ e, delta a e := by
        apply Finset.sum_le_sum; intro e _
        apply max_le
        · exact (delta_dist a).1 e
        · have := (delta_dist b).1 e
          linarith
    _ = 1 := (delta_dist a).2

theorem inner_A {Z C : Type} [Fintype Z] [Fintype C] [DecidableEq C] (m : Z → ℝ) (hm : IsDist m)
    (a : C) (g : Z → C) :
    ∑ e, max 0 (delta a e - ∑ z, m z * delta (g z) e) ≤ ∑ z, m z * (if g z = a then 0 else 1) := by
  have h : ∀ e, delta a e - ∑ z, m z * delta (g z) e = ∑ z, m z * (delta a e - delta (g z) e) := by
    intro e
    rw [Finset.sum_congr rfl (fun z _ => mul_sub (m z) (delta a e) (delta (g z) e)),
      Finset.sum_sub_distrib, ← Finset.sum_mul, hm.2, one_mul]
  simp only [h]
  calc _ ≤ ∑ z, m z * ∑ e, max 0 (delta a e - delta (g z) e) := sum_max0_mix m hm.1 _
    _ ≤ _ := by
      apply Finset.sum_le_sum; intro z _
      apply mul_le_mul_of_nonneg_left _ (hm.1 z)
      split_ifs with hz
      · rw [hz]; simp
      · exact sum_max0_delta_sub_le a (g z)

theorem inner_H {Z C : Type} [Fintype Z] [Fintype C] [DecidableEq C] (m : Z → ℝ) (hm : IsDist m)
    (a : C) (g : Z → C) :
    ∑ e, max 0 (∑ z, m z * delta (g z) e - delta a e) ≤ ∑ z, m z * (if g z = a then 0 else 1) := by
  have h : ∀ e, ∑ z, m z * delta (g z) e - delta a e = ∑ z, m z * (delta (g z) e - delta a e) := by
    intro e
    rw [Finset.sum_congr rfl (fun z _ => mul_sub (m z) (delta (g z) e) (delta a e)),
      Finset.sum_sub_distrib, ← Finset.sum_mul, hm.2, one_mul]
  simp only [h]
  calc _ ≤ ∑ z, m z * ∑ e, max 0 (delta (g z) e - delta a e) := sum_max0_mix m hm.1 _
    _ ≤ _ := by
      apply Finset.sum_le_sum; intro z _
      apply mul_le_mul_of_nonneg_left _ (hm.1 z)
      split_ifs with hz
      · rw [hz]; simp
      · exact sum_max0_delta_sub_le (g z) a

theorem push_push {X Z C : Type} [Fintype X] [Fintype Z] (M : X → Z → ℝ) (D : Z → C → ℝ)
    (P : X → ℝ) (e : C) :
    push D (push M P) e = ∑ x, P x * ∑ z, M x z * D z e := by
  simp only [push, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro x _
  apply Finset.sum_congr rfl; intro z _
  ring

theorem approx_A {X Z C : Type} [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
    (γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PA : X → ℝ)
    (hM : IsKernel M) (hPA : IsDist PA)
    (hγ : ∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) :
    ∑ e, max 0 (contentLaw c PA e - push (fun z => delta (g z)) (push M PA) e) ≤ γ := by
  have h : ∀ e, contentLaw c PA e - push (fun z => delta (g z)) (push M PA) e
      = ∑ x, PA x * (delta (c x) e - ∑ z, M x z * delta (g z) e) := by
    intro e
    rw [push_push]
    simp only [contentLaw, push, mul_sub, Finset.sum_sub_distrib]
  simp only [h]
  calc _ ≤ ∑ x, PA x * ∑ e, max 0 (delta (c x) e - ∑ z, M x z * delta (g z) e) :=
        sum_max0_mix PA hPA.1 _
    _ ≤ ∑ x, PA x * γ := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hPA.1 x)
      exact (inner_A (M x) (hM x) (c x) g).trans (hγ x)
    _ = γ := by rw [← Finset.sum_mul, hPA.2, one_mul]

theorem approx_H {X Z C : Type} [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
    (γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PH : X → ℝ)
    (hM : IsKernel M) (hPH : IsDist PH)
    (hγ : ∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) :
    ∑ e, max 0 (push (fun z => delta (g z)) (push M PH) e - contentLaw c PH e) ≤ γ := by
  have h : ∀ e, push (fun z => delta (g z)) (push M PH) e - contentLaw c PH e
      = ∑ x, PH x * (∑ z, M x z * delta (g z) e - delta (c x) e) := by
    intro e
    rw [push_push]
    simp only [contentLaw, push, mul_sub, Finset.sum_sub_distrib]
  simp only [h]
  calc _ ≤ ∑ x, PH x * ∑ e, max 0 (∑ z, M x z * delta (g z) e - delta (c x) e) :=
        sum_max0_mix PH hPH.1 _
    _ ≤ ∑ x, PH x * γ := by
      apply Finset.sum_le_sum; intro x _
      apply mul_le_mul_of_nonneg_left _ (hPH.1 x)
      exact (inner_H (M x) (hM x) (c x) g).trans (hγ x)
    _ = γ := by rw [← Finset.sum_mul, hPH.2, one_mul]

theorem t4c_approx : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (η γ : ℝ) (M : X → Z → ℝ) (c : X → C) (g : Z → C) (PA PH : X → ℝ),
      IsKernel M → IsDist PA → IsDist PH →
      (∀ x, ∑ z, M x z * (if g z = c x then 0 else 1) ≤ γ) →
      hs η (contentLaw c PA) (contentLaw c PH)
        ≤ hs η (push M PA) (push M PH) + (1 + Real.exp η) * γ := by
  intro X Z C _ _ _ _ η γ M c g PA PH hM hPA hPH hγ
  have h1 := t5d C η (contentLaw c PA) (contentLaw c PH)
    (push (fun z => delta (g z)) (push M PA)) (push (fun z => delta (g z)) (push M PH))
  have h2 := t4a Z C η (fun z => delta (g z)) (push M PA) (push M PH)
    (fun z => delta_dist (g z))
  have h3 := approx_A γ M c g PA hM hPA hγ
  have h4 := approx_H γ M c g PH hM hPH hγ
  have h5 := mul_le_mul_of_nonneg_left h4 (Real.exp_pos η).le
  linarith

theorem t4c'1 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X)
      (hB : B.Nonempty) (Q : Z → ℝ) (L : ℝ), IsKernel M → IsDist Q →
      (∀ x ∈ B, ∀ z, M x z ≤ L * Q z) →
      ∑ z, B.sup' hB (fun x => M x z) ≤ L := by
  intro X Z _ _ M B hB Q L _ hQ h
  calc ∑ z, B.sup' hB (fun x => M x z) ≤ ∑ z, L * Q z :=
        Finset.sum_le_sum (fun z _ => Finset.sup'_le hB _ (fun x hx => h x hx z))
    _ = L := by rw [← Finset.mul_sum, hQ.2, mul_one]

theorem t4c'2 : ∀ (X Z : Type) [Fintype X] [Fintype Z] (M : X → Z → ℝ) (B : Finset X)
      (hB : B.Nonempty), IsKernel M → ∃ Q, IsDist Q ∧
        ∀ x ∈ B, ∀ z, M x z ≤ (∑ z', B.sup' hB (fun x' => M x' z')) * Q z := by
  intro X Z _ _ M B hB hM
  obtain ⟨x0, hx0⟩ := id hB
  have hge : ∀ z, M x0 z ≤ B.sup' hB (fun x' => M x' z) :=
    fun z => Finset.le_sup' (fun x' => M x' z) hx0
  have hS1 : 1 ≤ ∑ z', B.sup' hB (fun x' => M x' z') := by
    rw [← (hM x0).2]
    exact Finset.sum_le_sum (fun z _ => hge z)
  have hSpos : 0 < ∑ z', B.sup' hB (fun x' => M x' z') := by linarith
  refine ⟨fun z => B.sup' hB (fun x' => M x' z) / ∑ z', B.sup' hB (fun x' => M x' z'), ?_, ?_⟩
  · constructor
    · intro z
      dsimp only
      apply div_nonneg _ hSpos.le
      exact le_trans ((hM x0).1 z) (hge z)
    · dsimp only
      rw [← Finset.sum_div, div_self hSpos.ne']
  · intro x hx z
    dsimp only
    rw [mul_div_cancel₀ _ hSpos.ne']
    exact Finset.le_sup' (fun x' => M x' z) hx

theorem dom : ∀ (X Z C : Type) [Fintype X] [Fintype Z] [Fintype C] [DecidableEq C]
      (M : X → Z → ℝ) (c : X → C) (PH : X → ℝ) (Bad : X → Prop) (p : ℝ),
      ContentOnly M c → IsDist PH → 0 < p → (∀ x, Bad x → p ≤ contentLaw c PH (c x)) →
      ∀ x, Bad x → ∀ z, M x z ≤ (1 / p) * push M PH z := by
  intro X Z C _ _ _ _ M c PH Bad p hM hPH hp hcov x hx z
  obtain ⟨K, hK, hMK⟩ := hM
  have key : contentLaw c PH (c x) * K (c x) z ≤ push M PH z := by
    simp only [contentLaw, push, Finset.sum_mul, hMK]
    apply Finset.sum_le_sum; intro x' _
    unfold delta
    split_ifs with h
    · rw [h, mul_one]
    · rw [mul_zero, zero_mul]
      exact mul_nonneg (hPH.1 x') ((hK _).1 z)
  have hK0 : 0 ≤ K (c x) z := (hK (c x)).1 z
  have h1 : p * K (c x) z ≤ push M PH z :=
    le_trans (mul_le_mul_of_nonneg_right (hcov x hx) hK0) key
  rw [hMK x]
  calc K (c x) z = (1 / p) * (p * K (c x) z) := by field_simp
    _ ≤ (1 / p) * push M PH z := mul_le_mul_of_nonneg_left h1 (by positivity)

theorem claim : Claim :=
  ⟨t2, t2att, t1, t4a, t4b, t4c, t4c_approx, t5d, t4c'1, t4c'2, dom⟩

theorem idKernel : IsKernel (fun (x : Bool) (z : Bool) => if z = x then (1 : ℝ) else 0) := by
  intro x
  constructor
  · intro z; dsimp only; split_ifs <;> norm_num
  · simp

theorem witness : Witness := by
  unfold Witness
  refine ⟨?_, idKernel, ?_, ?_, ?_⟩
  · simp [hs, Real.exp_zero]
    norm_num
  · refine ⟨id, fun x z h => ?_⟩
    by_contra h'
    apply h
    simp only [id] at h'
    show (if z = x then (1 : ℝ) else 0) = 0
    simp [h']
  · exact ⟨fun e z => if z = e then (1 : ℝ) else 0, idKernel, fun x => rfl⟩
  · have hz : ∀ z : Bool, (Finset.univ : Finset Bool).sup' Finset.univ_nonempty
        (fun x => if z = x then (1 : ℝ) else 0) = 1 := by
      intro z
      apply le_antisymm
      · apply Finset.sup'_le; intro x _; split_ifs <;> norm_num
      · exact Finset.le_sup'_of_le _ (Finset.mem_univ z) (by simp)
    simp only [hz]
    simp
