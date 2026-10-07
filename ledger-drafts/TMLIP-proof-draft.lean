open PL_TMLIPF1 PL_TMCERTF1

theorem bellman_row_gap {S A : Type} [Fintype S] (G H : Game S A) (n : ℕ) (s : S) (a : A)
    (w : S → ℝ) (eps : ℝ)
    (hgap : |G.cat n s a - H.cat n s a| + ∑ s', |G.K n s a s' - H.K n s a s'| ≤ eps)
    (hw : ∀ s', 0 ≤ w s' ∧ w s' ≤ 1) :
    BellmanRow H n s a w ≤ BellmanRow G n s a w + eps := by
  have hcat : H.cat n s a ≤ G.cat n s a + |G.cat n s a - H.cat n s a| := by
    have h := le_abs_self (H.cat n s a - G.cat n s a)
    rw [abs_sub_comm] at h
    nlinarith
  have hterm : ∀ s', H.K n s a s' * w s' ≤ G.K n s a s' * w s' + |G.K n s a s' - H.K n s a s'| := by
    intro s'
    have h := le_abs_self ((H.K n s a s' - G.K n s a s') * w s')
    have habs : |(H.K n s a s' - G.K n s a s') * w s'| = |G.K n s a s' - H.K n s a s'| * |w s'| := by
      rw [abs_mul, abs_sub_comm]
    have hwabs : |w s'| ≤ 1 := by
      rw [abs_of_nonneg (hw s').1]
      exact (hw s').2
    have hmul := mul_le_mul_of_nonneg_left hwabs (abs_nonneg (G.K n s a s' - H.K n s a s'))
    calc
      H.K n s a s' * w s' = G.K n s a s' * w s' + (H.K n s a s' - G.K n s a s') * w s' := by ring
      _ ≤ G.K n s a s' * w s' + |(H.K n s a s' - G.K n s a s') * w s'| := by linarith
      _ = G.K n s a s' * w s' + |G.K n s a s' - H.K n s a s'| * |w s'| := by rw [habs]
      _ ≤ G.K n s a s' * w s' + |G.K n s a s' - H.K n s a s'| := by linarith
  have hsum : (∑ s', H.K n s a s' * w s') ≤
      (∑ s', G.K n s a s' * w s') + ∑ s', |G.K n s a s' - H.K n s a s'| := by
    calc
      (∑ s', H.K n s a s' * w s') ≤ ∑ s', (G.K n s a s' * w s' + |G.K n s a s' - H.K n s a s'|) :=
        Finset.sum_le_sum fun s' _ => hterm s'
      _ = (∑ s', G.K n s a s' * w s') + ∑ s', |G.K n s a s' - H.K n s a s'| := by rw [Finset.sum_add_distrib]
  unfold BellmanRow
  linarith

theorem transfer : Transfer := by
  intro S A inst N G H eps V heps hlaw hcert hrange hgap
  constructor
  · intro s
    simpa [Inflated] using hcert.1 s
  · intro n hn s a th htrue
    have hrow := hcert.2 n hn s a () trivial
    change BellmanRow G n s a (V n) ≤ V (n + 1) s at hrow
    have hgapRow := hgap n hn s a
    have hbell := bellman_row_gap G H n s a (V n) eps hgapRow (fun s' => (hrange n (Nat.le_of_lt hn) s'))
    have hmass : (∑ s', H.K n s a s') ≤ 1 := by
      have h := hlaw n hn s a
      linarith [h.1, h.2.2]
    have hscale : (∑ s', H.K n s a s' * ((n : ℝ) * eps)) ≤ (n : ℝ) * eps := by
      calc
        (∑ s', H.K n s a s' * ((n : ℝ) * eps)) = (∑ s', H.K n s a s') * ((n : ℝ) * eps) := by rw [Finset.sum_mul]
        _ ≤ 1 * ((n : ℝ) * eps) := mul_le_mul_of_nonneg_right hmass (mul_nonneg (Nat.cast_nonneg n) heps)
        _ = (n : ℝ) * eps := by ring
    have hsplit : BellmanRow H n s a (fun s' => V n s' + (n : ℝ) * eps) =
        BellmanRow H n s a (V n) + (∑ s', H.K n s a s' * ((n : ℝ) * eps)) := by
      unfold BellmanRow
      change H.cat n s a + (∑ s', H.K n s a s' * (V n s' + (n : ℝ) * eps)) =
        H.cat n s a + (∑ s', H.K n s a s' * V n s') + ∑ s', H.K n s a s' * ((n : ℝ) * eps)
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      ring
    calc
      BellmanRow H n s a (fun s' => V n s' + (n : ℝ) * eps) =
          BellmanRow H n s a (V n) + (∑ s', H.K n s a s' * ((n : ℝ) * eps)) := hsplit
      _ ≤ BellmanRow H n s a (V n) + (n : ℝ) * eps := by nlinarith [hscale]
      _ ≤ BellmanRow G n s a (V n) + eps + (n : ℝ) * eps := by linarith [hbell]
      _ ≤ V (n + 1) s + eps + (n : ℝ) * eps := by linarith [hrow, hbell]
      _ = Inflated V eps (n + 1) s := by simp [Inflated]; push_cast; ring

theorem grid_transfer : GridTransfer := by
  intro P S A instP instS N G target grid dist L h U hL hh hlaw hcover hrow hgrid p hp
  obtain ⟨q, hq, hd0, hdh⟩ := hcover p hp
  obtain ⟨V, hcert, hrange, hbound⟩ := hgrid q hq
  have hclose : RowGap N (G q) (G p) (L * h) := by
    intro n hn s a
    exact le_trans (hrow p q hp hq hd0 n hn s a) (mul_le_mul_of_nonneg_left hdh hL)
  have hcertP := transfer N (G q) (G p) (L * h) V
    (mul_nonneg hL (le_trans hd0 hdh)) (hlaw p hp) hcert hrange hclose
  refine ⟨q, V, hq, hcertP, ?_⟩
  intro s
  have hbound' := hbound s
  have hN : (N : ℝ) * (L * h) = (N : ℝ) * L * h := by ring
  simpa [Inflated, hN] using add_le_add_right hbound' ((N : ℝ) * (L * h))

theorem claim : PL_TMLIPF1.Claim := ⟨transfer, grid_transfer⟩

theorem toy_lawful (p : Fin 2) : LawfulUpTo 1 (toyGame p) := by
  intro n hn s a
  have hn0 : n = 0 := by omega
  subst n
  fin_cases p <;> norm_num [toyGame, toyParam]

theorem toy_cover :
    ∀ p, p ∈ (Finset.univ : Finset (Fin 2)) →
      ∃ q, q ∈ toyGrid ∧ 0 ≤ toyDist p q ∧ toyDist p q ≤ 1 / 4 := by
  intro p hp
  refine ⟨0, by simp [toyGrid], ?_, ?_⟩
  · exact abs_nonneg _
  · fin_cases p <;> norm_num [toyDist, toyParam]

theorem toy_row_close :
    ∀ p q, p ∈ (Finset.univ : Finset (Fin 2)) → q ∈ toyGrid → 0 ≤ toyDist p q →
      RowGap 1 (toyGame q) (toyGame p) (1 * toyDist p q) := by
  intro p q hp hq hd
  have hq0 : q = 0 := by simpa [toyGrid] using hq
  subst q
  intro n hn s a
  have hn0 : n = 0 := by omega
  subst n
  fin_cases p <;> norm_num [RowGap, toyGame, toyParam, toyDist]

theorem toy_grid_cert :
    ∀ q, q ∈ toyGrid → ∃ V,
      RiskCertUpTo 1 (fun _ : Unit => toyGame q) (fun _ _ _ _ => True) V ∧
      InRange 1 V ∧ ∀ s, V 1 s ≤ 0 := by
  intro q hq
  have hq0 : q = 0 := by simpa [toyGrid] using hq
  subst q
  refine ⟨zeroCert, ?_, ?_, ?_⟩
  · constructor
    · intro s
      simp [zeroCert]
    · intro n hn s a th htrue
      have hn0 : n = 0 := by omega
      subst n
      simp [toyGame, toyParam, zeroCert]
  · intro n hn s
    simp [InRange, zeroCert]
  · intro s
    simp [zeroCert]

theorem grid_example : GridWitness := by
  have h := grid_transfer (N := 1) (G := toyGame) (target := Finset.univ) (grid := toyGrid)
    (dist := toyDist) (L := 1) (h := 1 / 4) (U := 0)
  have hL : 0 ≤ (1 : ℝ) := by norm_num
  have hh : 0 ≤ (1 / 4 : ℝ) := by norm_num
  have hlaw : ∀ p, p ∈ (Finset.univ : Finset (Fin 2)) → LawfulUpTo 1 (toyGame p) := by
    intro p hp
    exact toy_lawful p
  have hresult := h hL hh hlaw toy_cover toy_row_close toy_grid_cert
  simpa [GridWitness] using hresult


theorem witness : PL_TMLIPF1.Witness := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n hn s a
    have hn0 : n = 0 := by omega
    subst n
    simp [RowGap, baseGame, perturbedGame]
  · constructor
    · intro s
      simp [zeroCert]
    · intro n hn s a th htrue
      have hn0 : n = 0 := by omega
      subst n
      simp [RiskCertUpTo, zeroCert, baseGame]
  · intro n hn s
    simp [InRange, zeroCert]
  · intro n hn s
    have hn0 : n = 0 ∨ n = 1 := by omega
    rcases hn0 with hn0 | hn0
    · subst n
      simp [Inflated, zeroCert]
    · subst n
      norm_num [Inflated, zeroCert]
  · exact grid_example
