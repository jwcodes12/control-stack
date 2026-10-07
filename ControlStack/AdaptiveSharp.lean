import ControlStack.AdaptiveBalance

/-! A finite path-measure form of the sharp adaptive converse.

This isolates the final pathwise aggregation step from the separate task of
identifying an adaptive tester's all-FLAG transcript law with a finite path
measure. -/

namespace ControlStack.AdaptiveSharp

open ControlStack.AdaptiveBalance

/-- If the reference path measure, weighted by the tester's keep rule, has
total mass one, then summing the all-FLAG likelihood over seeds has the sharp
balanced lower bound. `counts p i` is the number of queries to seed class `i`
on path `p`; the budget condition says each path uses at most `n` queries. -/
theorem weighted_path_balanced
    {P : Type} [Fintype P] (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (k n : ℕ) (hk : 0 < k)
    (mass keep : P → ℝ) (counts : P → Fin k → ℕ)
    (hmass : ∀ p, 0 ≤ mass p)
    (hkeep0 : ∀ p, 0 ≤ keep p)
    (hbudget : ∀ p, ∑ i : Fin k, counts p i ≤ n)
    (haccept : ∑ p : P, mass p * keep p = 1) :
    ((k - n % k : ℕ) : ℝ) * b ^ (n / k) +
        ((n % k : ℕ) : ℝ) * b ^ (n / k + 1) ≤
      ∑ p : P, mass p * keep p * ∑ i : Fin k, b ^ (counts p i) := by
  let target : ℝ :=
    ((k - n % k : ℕ) : ℝ) * b ^ (n / k) +
      ((n % k : ℕ) : ℝ) * b ^ (n / k + 1)
  have hpoint (p : P) : target ≤ ∑ i : Fin k, b ^ (counts p i) := by
    have hbudget' : ∑ i : Fin k, counts p i ≤ k * (n / k) + n % k := by
      have hn : ∑ i : Fin k, counts p i ≤ n := hbudget p
      calc
        ∑ i : Fin k, counts p i ≤ n := hn
        _ = n % k + k * (n / k) := (Nat.mod_add_div n k).symm
        _ = k * (n / k) + n % k := Nat.add_comm _ _
    dsimp [target]
    exact aggregate_balanced_budget b hb0 hb1 k (n / k) (n % k) hk
      (Nat.mod_lt _ hk) (counts p) hbudget'
  have hweighted :
      ∑ p : P, mass p * keep p * target = target := by
    calc
      ∑ p : P, mass p * keep p * target =
          (∑ p : P, mass p * keep p) * target := by rw [Finset.sum_mul]
      _ = target := by rw [haccept]; ring
  calc
    target = ∑ p : P, mass p * keep p * target := hweighted.symm
    _ ≤ ∑ p : P, mass p * keep p * ∑ i : Fin k, b ^ (counts p i) := by
      apply Finset.sum_le_sum
      intro p _
      have hmul := mul_le_mul_of_nonneg_left (hpoint p)
        (mul_nonneg (hmass p) (hkeep0 p))
      simpa [mul_assoc] using hmul

/-- Including the deployment PASS factor `t` and the uniform seed prior gives
the risk lower bound corresponding to the balanced path sum. -/
theorem uniform_seed_risk_balanced
    {P : Type} [Fintype P] (t : ℝ) (ht : 0 ≤ t)
    (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (k n : ℕ) (hk : 0 < k)
    (mass keep : P → ℝ) (counts : P → Fin k → ℕ)
    (hmass : ∀ p, 0 ≤ mass p)
    (hkeep0 : ∀ p, 0 ≤ keep p)
    (hbudget : ∀ p, ∑ i : Fin k, counts p i ≤ n)
    (haccept : ∑ p : P, mass p * keep p = 1) :
    (t / (k : ℝ)) *
        (((k - n % k : ℕ) : ℝ) * b ^ (n / k) +
          ((n % k : ℕ) : ℝ) * b ^ (n / k + 1)) ≤
      (t / (k : ℝ)) *
        ∑ p : P, mass p * keep p * ∑ i : Fin k, b ^ (counts p i) := by
  have h := weighted_path_balanced b hb0 hb1 k n hk mass keep counts
    hmass hkeep0 hbudget haccept
  exact mul_le_mul_of_nonneg_left h (div_nonneg ht (by exact_mod_cast hk.le))

end ControlStack.AdaptiveSharp
