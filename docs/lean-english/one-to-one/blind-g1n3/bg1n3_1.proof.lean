open ControlStack.SC07Exfil

theorem original_signature : ∀ (q : ℕ) (pr : ℝ) (c : ℕ → ℝ) (b : List ℕ), 0 < pr → (∀ i, pr ≤ c i ∧ c i ≤ 1) → OriginalAt q pr c b := by
  intro q pr c b hpr hc
  exact expected_leak_le q c pr hc hpr b

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro q pr c b hpr hc
  rfl

theorem witness : Witness := by norm_num [Witness, capped, expLeak]
