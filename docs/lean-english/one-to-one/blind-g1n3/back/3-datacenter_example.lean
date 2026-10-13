namespace ControlStack.SC07Exfil

def Back_datacenter_example : Prop :=
  ceilDiv 800000000000 8000000000 = 100 ∧
    ∀ (b : List ℕ) (c : ℕ → ℝ),
      800000000000 ≤ (capped 8000000000 b).sum →
      (∀ i : ℕ, (5 / 100 : ℝ) ≤ c i ∧ c i ≤ 1) →
      survive c (capped 8000000000 b) 0 ≤ (6 / 1000 : ℝ)

end ControlStack.SC07Exfil
