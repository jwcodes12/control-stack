-- EXCERPT of ControlStack/ScenarioAUsefulness.lean: definitions only; theorems and redacted declarations removed. Not compilable alone.
namespace ControlStack.ScenarioAUsefulness

/-- binomial upper tail P(X ≥ k), X ~ Bin(64, p) -/
noncomputable def tail (k : ℕ) (p : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc k 64, (Nat.choose 64 j : ℝ) * p ^ j * (1 - p) ^ (64 - j)

/-- probability that the gate passes = P(X ≥ 63) -/
noncomputable def passProb (p : ℝ) : ℝ := tail 63 p

end ControlStack.ScenarioAUsefulness

