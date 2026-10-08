import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic

/-! Usefulness gate of the SC-01 repair preregistration (PREREG-SC01-REPAIR.md, gateway/scenario/contract.json).

Gate: n = 64 independent lifetimes per condition, outward-rounded (denominator 10^5) one-sided Clopper–Pearson lower
endpoint at tail α = 1/80 must be ≥ 9/10. Model: lifetimes complete independently with probability p (binomial count);
this independence is the preregistration's declared assumption, not proved here.

Proved:
- `gate_pass_iff`: the gate passes exactly at counts 63 and 64. The grid endpoints 90438/10^5 (k = 63) and
  93382/10^5 (k = 64) are valid (their upper tails are ≤ 1/80) and maximal on the grid, and count 62 is rejected
  (its upper tail at 9/10 exceeds 1/80, so its endpoint lies below the floor);
- `false_pass_le`: if p ≤ 9/10, the probability that the gate passes for that condition is ≤ 1/80 (the passing tail
  64 p^63 − 63 p^64 is monotone on [0, 1], and is ≈ 0.00956 at 9/10).
The observed 64/64 + 64/64 result (endpoint 93382/10^5) therefore certifies, conditional on the model, that a
condition with completion probability ≤ 9/10 would have passed with probability ≤ 1/80. -/
namespace ControlStack.ScenarioAUsefulness

/-- binomial upper tail P(X ≥ k), X ~ Bin(64, p) -/
noncomputable def tail (k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc k 64, (Nat.choose 64 j : ℝ) * p ^ j * (1 - p) ^ (64 - j)

/-- probability that the gate passes = P(X ≥ 63) -/
noncomputable def passProb (p : ℝ) : ℝ := tail 63 p

lemma passProb_eq (p : ℝ) : passProb p = 64 * p ^ 63 - 63 * p ^ 64 := by
  unfold passProb tail
  rw [show Finset.Icc 63 64 = {63, 64} by decide]
  simp [Nat.choose]
  ring

lemma passProb_mono : MonotoneOn passProb (Set.Icc 0 1) := by
  have hf : passProb = fun p : ℝ => 64 * p ^ 63 - 63 * p ^ 64 := funext passProb_eq
  have hd : ∀ x : ℝ, HasDerivAt (fun p : ℝ => 64 * p ^ 63 - 63 * p ^ 64)
      (64 * 63 * x ^ 62 * (1 - x)) x := by
    intro x
    have := ((hasDerivAt_pow 63 x).const_mul 64).sub ((hasDerivAt_pow 64 x).const_mul 63)
    convert this using 1
    push_cast; ring
  rw [hf]
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · exact (Continuous.continuousOn (by fun_prop))
  · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have h0 : 0 ≤ x := hx.1.le
    have h1 : 0 ≤ 1 - x := by linarith [hx.2]
    positivity

/-- **Gate validity.** A condition whose true completion probability is at most the 9/10 floor passes the gate with
probability at most 1/80. -/
theorem false_pass_le (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 9 / 10) : passProb p ≤ 1 / 80 := by
  have := passProb_mono ⟨h0, by linarith⟩ ⟨by norm_num, by norm_num⟩ h1
  calc passProb p ≤ passProb (9 / 10) := this
    _ ≤ 1 / 80 := by rw [passProb_eq]; norm_num

/-- Endpoint certificates: the Python checker's grid endpoints are valid and maximal. -/
theorem endpoint64 : tail 64 (93382 / 100000) ≤ 1 / 80 ∧ 1 / 80 < tail 64 (93383 / 100000) := by
  unfold tail; rw [show Finset.Icc 64 64 = {64} by decide]; norm_num

theorem endpoint63 : tail 63 (90438 / 100000) ≤ 1 / 80 ∧ 1 / 80 < tail 63 (90439 / 100000) := by
  unfold tail; rw [show Finset.Icc 63 64 = {63, 64} by decide]
  simp only [Finset.sum_pair (by decide : (63 : ℕ) ≠ 64)]; norm_num [Nat.choose]

/-- count 62 is rejected: its upper tail at the floor exceeds 1/80, so its CP endpoint is below 9/10 -/
theorem reject62 : 1 / 80 < tail 62 (9 / 10) := by
  unfold tail; rw [show Finset.Icc 62 64 = {62, 63, 64} by decide]
  simp only [Finset.sum_insert (by decide : (62 : ℕ) ∉ ({63, 64} : Finset ℕ)),
    Finset.sum_pair (by decide : (63 : ℕ) ≠ 64)]
  norm_num [Nat.choose]

theorem endpoints_clear_floor : (9 : ℝ) / 10 ≤ 90438 / 100000 ∧ (90438 : ℝ) / 100000 ≤ 93382 / 100000 := by
  norm_num

#print axioms passProb_mono
#print axioms false_pass_le
#print axioms endpoint64
#print axioms endpoint63
#print axioms reject62

end ControlStack.ScenarioAUsefulness
