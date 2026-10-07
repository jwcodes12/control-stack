import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-! Combinatorial core of the sharp balanced adaptive converse. -/

namespace ControlStack.AdaptiveBalance

private def slope (b : ℝ) (n : ℕ) : ℝ := b ^ (n + 1) - b ^ n

private lemma slope_mono (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ {n k : ℕ}, n ≤ k → slope b n ≤ slope b k := by
  intro n k hnk
  have hp : b ^ k ≤ b ^ n := pow_le_pow_of_le_one hb0 hb1 hnk
  have hn : 0 ≤ b ^ n := pow_nonneg hb0 _
  have hc : b - 1 ≤ 0 := by linarith
  unfold slope
  rw [show n + 1 = Nat.succ n by omega, pow_succ,
      show k + 1 = Nat.succ k by omega, pow_succ]
  have hmul := mul_le_mul_of_nonpos_right hp hc
  nlinarith [hmul]

private lemma tangent_step (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (m q : ℕ) (hmq : m ≤ q) :
    b ^ (q + 1) + ((m : ℝ) - ((q + 1 : ℕ) : ℝ)) * slope b (q + 1) ≤
      b ^ q + ((m : ℝ) - (q : ℝ)) * slope b q := by
  have hmono := slope_mono b hb0 hb1 (n := q) (k := q + 1) (Nat.le_succ q)
  have hmq' : (m : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by exact_mod_cast (show m ≤ q + 1 by omega)
  have hc : 0 ≤ ((q + 1 : ℕ) : ℝ) - (m : ℝ) := by linarith
  have hprod := mul_le_mul_of_nonneg_left hmono hc
  have hp : b ^ (q + 1) = b ^ q + slope b q := by
    unfold slope
    ring
  have hcast : ((q + 1 : ℕ) : ℝ) = (q : ℝ) + 1 := by norm_num
  rw [hcast] at hprod ⊢
  rw [hp]
  nlinarith [hprod]

theorem balanced_bound (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m q : ℕ) :
    b ^ m ≥ b ^ q + ((m : ℝ) - (q : ℝ)) * (b ^ (q + 1) - b ^ q) := by
  by_cases hmq : m ≤ q
  · have h : ∀ q', m ≤ q' → b ^ m ≥ b ^ q' + ((m : ℝ) - (q' : ℝ)) * slope b q' := by
      intro q' hmq'
      exact Nat.le_induction
        (by simp [slope])
        (fun n hmn ih => (tangent_step b hb0 hb1 m n hmn).trans ih)
        q' hmq'
    have h' := h q hmq
    simpa [slope] using h'
  · have hqm : q ≤ m := Nat.le_of_not_ge hmq
    have h : ∀ m', q ≤ m' → b ^ m' ≥ b ^ q + ((m' : ℝ) - (q : ℝ)) * slope b q := by
      intro m' hqm'
      exact Nat.le_induction
        (by simp [slope])
        (fun n _ ih => by
          have hmono := slope_mono b hb0 hb1 (n := q) (k := n) (by omega)
          have hp : b ^ (n + 1) = b ^ n + slope b n := by
            unfold slope
            ring
          rw [hp]
          push_cast
          nlinarith [ih, hmono])
        m' hqm'
    have h' := h m hqm
    simpa [slope] using h'

theorem aggregate_balanced_budget (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (k q a : ℕ) (_hk : 0 < k) (ha : a < k)
    (counts : Fin k → ℕ)
    (hcounts : ∑ i : Fin k, counts i ≤ k * q + a) :
    ∑ i : Fin k, b ^ (counts i) ≥
      ((k - a : ℕ) : ℝ) * b ^ q + (a : ℝ) * b ^ (q + 1) := by
  let d : ℝ := b ^ (q + 1) - b ^ q
  have hd : d ≤ 0 := by
    dsimp [d]
    have hp : b ^ (q + 1) ≤ b ^ q := pow_le_pow_of_le_one hb0 hb1 (Nat.le_succ q)
    linarith
  have hpoint (i : Fin k) := balanced_bound b hb0 hb1 (counts i) q
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hsum' : (∑ i : Fin k, (b ^ q + ((counts i : ℝ) - (q : ℝ)) * d)) ≤
      ∑ i : Fin k, b ^ (counts i) := by
    simpa [d, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hsum
  have hcastsum : (∑ i : Fin k, (counts i : ℝ)) = ((∑ i : Fin k, counts i : ℕ) : ℝ) := by
    simp
  have hsumformula : (∑ i : Fin k, (b ^ q + ((counts i : ℝ) - (q : ℝ)) * d)) =
      (k : ℝ) * b ^ q + (((∑ i : Fin k, counts i : ℕ) : ℝ) - (k : ℝ) * (q : ℝ)) * d := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hcastsum]
    simp
  have hupper : ((∑ i : Fin k, counts i : ℕ) : ℝ) ≤ (k : ℝ) * (q : ℝ) + (a : ℝ) := by
    exact_mod_cast hcounts
  have hcoef : (((∑ i : Fin k, counts i : ℕ) : ℝ) - (k : ℝ) * (q : ℝ)) ≤ (a : ℝ) := by
    have hmul : (k : ℝ) * (q : ℝ) = ((k * q : ℕ) : ℝ) := by norm_num
    rw [hmul]
    have hnat : ∑ i : Fin k, counts i ≤ k * q + a := hcounts
    have hcast : ((∑ i : Fin k, counts i : ℕ) : ℝ) ≤ ((k * q + a : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    linarith
  have hcoefmul := mul_le_mul_of_nonpos_right hcoef hd
  rw [hsumformula] at hsum'
  have haCast : ((k - a : ℕ) : ℝ) = (k : ℝ) - (a : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt ha)]
  rw [haCast]
  dsimp [d] at hcoefmul ⊢
  nlinarith [hsum', hcoefmul]

/-- With exactly `n` queries allocated among `k` classes, a balanced allocation
minimizes the sum of miss probabilities. -/
theorem aggregate_balanced_exact (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (k n : ℕ) (hk : 0 < k) (counts : Fin k → ℕ)
    (hcounts : ∑ i : Fin k, counts i = n) :
    ∑ i : Fin k, b ^ (counts i) ≥
      ((k - n % k : ℕ) : ℝ) * b ^ (n / k) + ((n % k : ℕ) : ℝ) * b ^ (n / k + 1) := by
  have ha : n % k < k := Nat.mod_lt _ hk
  have hn : (∑ i : Fin k, counts i) ≤ k * (n / k) + n % k := by
    have heq : n = n % k + k * (n / k) := (Nat.mod_add_div n k).symm
    calc
      ∑ i : Fin k, counts i = n := hcounts
      _ = n % k + k * (n / k) := heq
      _ = k * (n / k) + n % k := Nat.add_comm _ _
      _ ≤ k * (n / k) + n % k := le_rfl
  exact aggregate_balanced_budget b hb0 hb1 k (n / k) (n % k) hk ha counts hn

end ControlStack.AdaptiveBalance
