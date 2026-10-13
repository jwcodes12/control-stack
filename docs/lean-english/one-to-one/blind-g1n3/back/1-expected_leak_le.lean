namespace ControlStack.SC07Exfil

def Back_expected_leak_le : Prop :=
  ∀ (q : ℕ) (pr : ℝ) (c : ℕ → ℝ) (b : List ℕ),
    0 < pr →
    (∀ i : ℕ, pr ≤ c i ∧ c i ≤ 1) →
    expLeak c (capped q b) 0 ≤ (q : ℝ) / pr

end ControlStack.SC07Exfil
