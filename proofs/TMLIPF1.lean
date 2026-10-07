open PL_TMCERTF1

theorem oneStep : OneStep := by
  intro S A instS G H n s a w eps hw hrow
  unfold BellmanRow
  have hid : (G.cat n s a + ∑ s', G.K n s a s' * w s') - (H.cat n s a + ∑ s', H.K n s a s' * w s') =
      (G.cat n s a - H.cat n s a) + ∑ s', (G.K n s a s' - H.K n s a s') * w s' := by
    rw [show (∑ s', (G.K n s a s' - H.K n s a s') * w s') =
      (∑ s', G.K n s a s' * w s') - ∑ s', H.K n s a s' * w s' by
        simp_rw [sub_mul]; rw [Finset.sum_sub_distrib]]
    ring
  rw [hid]
  calc |(G.cat n s a - H.cat n s a) + ∑ s', (G.K n s a s' - H.K n s a s') * w s'|
      ≤ |G.cat n s a - H.cat n s a| + |∑ s', (G.K n s a s' - H.K n s a s') * w s'| := abs_add_le _ _
    _ ≤ |G.cat n s a - H.cat n s a| + ∑ s', |G.K n s a s' - H.K n s a s'| := by
        refine add_le_add le_rfl ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s' _ => ?_))
        rw [abs_mul]
        have h0 : 0 ≤ w s' := (hw s').1
        rw [abs_of_nonneg h0]
        exact mul_le_of_le_one_right (abs_nonneg _) (hw s').2
    _ ≤ eps := hrow

theorem transfer : Transfer := by
  intro S A instS N G H eps V heps hlaw hcert hrange hgap
  constructor
  · intro s
    simpa [Inflated] using hcert.1 s
  · intro n hn s a th hadm
    have hrow := hgap n hn s a
    have hl := hlaw n hn s a
    have hbell := hcert.2 n hn s a () trivial
    have hmass : (∑ s', H.K n s a s') ≤ 1 := by
      have := hl.2.2
      linarith [hl.1]
    have hdiff :
        (H.cat n s a - G.cat n s a) +
          ∑ s', (H.K n s a s' - G.K n s a s') * V n s' ≤ eps := by
      have hcat : H.cat n s a - G.cat n s a ≤ |G.cat n s a - H.cat n s a| := by
        simpa [abs_sub_comm] using (le_abs_self (H.cat n s a - G.cat n s a))
      have hk (s' : S) :
          (H.K n s a s' - G.K n s a s') * V n s' ≤
            |G.K n s a s' - H.K n s a s'| := by
        have hr := hrange n (Nat.le_of_lt hn) s'
        have habs : |H.K n s a s' - G.K n s a s'| =
            |G.K n s a s' - H.K n s a s'| := by rw [abs_sub_comm]
        calc
          (H.K n s a s' - G.K n s a s') * V n s' ≤
              |H.K n s a s' - G.K n s a s'| * V n s' :=
                mul_le_mul_of_nonneg_right (le_abs_self _) hr.1
          _ ≤ |H.K n s a s' - G.K n s a s'| :=
                mul_le_of_le_one_right (abs_nonneg _) hr.2
          _ = |G.K n s a s' - H.K n s a s'| := habs
      calc
        (H.cat n s a - G.cat n s a) +
            ∑ s', (H.K n s a s' - G.K n s a s') * V n s'
            ≤ |G.cat n s a - H.cat n s a| +
              ∑ s', |G.K n s a s' - H.K n s a s'| := by
                exact add_le_add hcat (Finset.sum_le_sum fun s' _ => hk s')
        _ ≤ eps := hrow
    have hsum :
        (∑ s', (H.K n s a s' - G.K n s a s') * V n s') =
          (∑ s', H.K n s a s' * V n s') - (∑ s', G.K n s a s' * V n s') := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib]
    have hinflate :
        (∑ s', H.K n s a s' * (V n s' + (n : ℝ) * eps)) =
          (∑ s', H.K n s a s' * V n s') + (n : ℝ) * eps *
            (∑ s', H.K n s a s') := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      ring
    have hnreal : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have he : 0 ≤ (n : ℝ) * eps := mul_nonneg hnreal heps
    have hm : (n : ℝ) * eps * (∑ s', H.K n s a s') ≤ (n : ℝ) * eps :=
      mul_le_of_le_one_right he hmass
    have htail :
        (∑ s', H.K n s a s' * V n s') + (n : ℝ) * eps *
            (∑ s', H.K n s a s') ≤
          (∑ s', H.K n s a s' * V n s') + (n : ℝ) * eps :=
      calc
        (∑ s', H.K n s a s' * V n s') +
              (n : ℝ) * eps * (∑ s', H.K n s a s') =
            (n : ℝ) * eps * (∑ s', H.K n s a s') +
              (∑ s', H.K n s a s' * V n s') := by ring
        _ ≤ (n : ℝ) * eps + (∑ s', H.K n s a s' * V n s') :=
          add_le_add hm (le_refl _)
        _ = (∑ s', H.K n s a s' * V n s') + (n : ℝ) * eps := by ring
    have hstep : H.cat n s a + (∑ s', H.K n s a s' * V n s') ≤
        V (n + 1) s + eps := by
      have hid : H.cat n s a + (∑ s', H.K n s a s' * V n s') =
          (G.cat n s a + ∑ s', G.K n s a s' * V n s') +
            ((H.cat n s a - G.cat n s a) +
              ((∑ s', H.K n s a s' * V n s') -
                (∑ s', G.K n s a s' * V n s'))) := by ring
      rw [hsum] at hdiff
      rw [hid]
      linarith [hbell]
    change H.cat n s a +
      (∑ s', H.K n s a s' * (V n s' + (n : ℝ) * eps)) ≤
      V (n + 1) s + ((n + 1 : ℕ) : ℝ) * eps
    rw [hinflate]
    have hcombined : H.cat n s a +
        ((∑ s', H.K n s a s' * V n s') +
          (n : ℝ) * eps * (∑ s', H.K n s a s')) ≤
        V (n + 1) s + eps + (n : ℝ) * eps := by
      linarith [hstep, htail]
    have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
    rw [hcast]
    nlinarith [hcombined]

theorem gridTransfer : GridTransfer := by
  intro P S A instS N G target grid dist L h U hL hh hlaw hcover hlip hgrid p hp
  obtain ⟨q, hqgrid, hdh⟩ := hcover p hp
  obtain ⟨V, hcert, hrange, hupper⟩ := hgrid q hqgrid
  have hgap : RowClose N (G q) (G p) (L * h) := by
    intro n hn s a
    exact le_trans (hlip p hp q hqgrid n hn s a) (mul_le_mul_of_nonneg_left hdh hL)
  have htrans := transfer N (G q) (G p) (L * h) V (mul_nonneg hL hh) (hlaw p hp) hcert hrange hgap
  refine ⟨q, hqgrid, V, hdh, hcert, hrange, hupper, htrans, ?_⟩
  intro s
  have hN := hupper s
  change V N s + (N : ℝ) * (L * h) ≤ U + (N : ℝ) * L * h
  nlinarith [mul_assoc (N : ℝ) L h]

theorem gridRisk : GridRisk := by
  intro P S A instS instA N G target grid dist L h U hL hh hlaw hcover hlip hgrid p hp σ s₀ hσ
  obtain ⟨q, hq, V, -, -, -, -, hcert, hbound⟩ :=
    gridTransfer N G target grid dist L h U hL hh hlaw hcover hlip hgrid p hp
  have hK : ∀ n, n < N → ∀ s a s', 0 ≤ (G p).K n s a s' := fun n hn s a s' => ((hlaw p hp) n hn s a).2.1 s'
  exact le_trans (PLDep_TMCERTF1.claimFx S A N (G p) (Inflated V (L * h)) σ s₀ hK hcert hσ) (hbound s₀)

theorem claim : PL_TMLIPF1.Claim := ⟨oneStep, transfer, gridTransfer, gridRisk⟩

theorem w_lawfulParam : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), LawfulUpTo 1 (paramGame p) := by
  intro p hp n _ s a
  obtain ⟨h0, h1⟩ := hp
  refine ⟨h0, fun _ => ?_, ?_⟩
  · simp only [paramGame]; linarith
  · simp [paramGame]

theorem w_cover : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), ∃ q ∈ pGrid, |p - q| ≤ 1 / 8 := by
  intro p hp
  obtain ⟨h0, h1⟩ := hp
  by_cases hp4 : p ≤ 1 / 4
  · refine ⟨1 / 8, by simp [pGrid], ?_⟩
    rw [abs_le]; constructor <;> linarith
  · refine ⟨3 / 8, by simp [pGrid], ?_⟩
    rw [abs_le]; constructor <;> linarith

theorem w_lip : ∀ p ∈ Set.Icc (0 : ℝ) (1 / 2), ∀ q ∈ pGrid,
    RowClose 1 (paramGame q) (paramGame p) (2 * |p - q|) := by
  intro p _ q _ n _ s a
  simp only [paramGame, Finset.univ_unique, Finset.sum_singleton]
  rw [show (1 - q) - (1 - p) = p - q by ring, abs_sub_comm q p]
  linarith

theorem w_gridCert : ∀ q ∈ pGrid, RiskCertUpTo 1 (fun _ : Unit => paramGame q) (fun _ _ _ _ => True) (gridCert q) ∧
    InRange 1 (gridCert q) ∧ ∀ s, gridCert q 1 s ≤ 3 / 8 := by
  intro q hq
  have hq' : q = 1 / 8 ∨ q = 3 / 8 := by simpa [pGrid] using hq
  have hq0 : 0 ≤ q := by rcases hq' with rfl | rfl <;> norm_num
  have hq1 : q ≤ 3 / 8 := by rcases hq' with rfl | rfl <;> norm_num
  refine ⟨⟨fun s => by simp [gridCert], ?_⟩, ?_, fun s => by simp [gridCert, hq1]⟩
  · intro n hn s a th _
    have : n = 0 := by omega
    subst this
    simp [gridCert, paramGame]
  · intro n hn s
    by_cases h : n = 0
    · simp [gridCert, h]
    · simp only [gridCert, h, if_false]; constructor <;> linarith

theorem witness : PL_TMLIPF1.Witness := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    w_lawfulParam, w_cover, w_lip, w_gridCert, ?_, ?_, ?_⟩
  · intro n _ s a; simp [baseGame, perturbedGame]
  · intro n _ s a; refine ⟨by simp [perturbedGame] <;> norm_num, fun _ => by simp [perturbedGame], ?_⟩
    simp [perturbedGame] <;> norm_num
  · exact ⟨fun s => by simp [zeroCert], fun n _ s a _ _ => by simp [baseGame, zeroCert]⟩
  · intro n _ s; simp [zeroCert]
  · intro h
    have := h.2 0 (by norm_num) () () () trivial
    simp [perturbedGame, zeroCert] at this
    norm_num at this
  · refine ⟨fun s => by simp [Inflated, zeroCert], ?_⟩
    intro n hn s a _ _
    have : n = 0 := by omega
    subst this
    simp [perturbedGame, Inflated, zeroCert]
  · simp [risk, oneσ, perturbedGame]
  · simp [Inflated, zeroCert]
  · intro n _ s a; refine ⟨by simp [accG], fun _ => by simp [accG] <;> norm_num, ?_⟩
    simp [accG] <;> norm_num
  · intro n _ s a; refine ⟨by simp [accH] <;> norm_num, fun _ => by simp [accH] <;> norm_num, ?_⟩
    simp [accH] <;> norm_num
  · intro n _ s a; simp [accG, accH] <;> norm_num
  · exact ⟨fun s => by simp [zeroCert], fun n _ s a _ _ => by simp [accG, zeroCert]⟩
  · intro n _ s; simp [zeroCert]
  · simp [risk, oneσ, accH] <;> norm_num
  · norm_num
  · simp [Inflated, zeroCert] <;> norm_num
  · simp [risk, oneσ, paramGame]
  · norm_num
  · norm_num
