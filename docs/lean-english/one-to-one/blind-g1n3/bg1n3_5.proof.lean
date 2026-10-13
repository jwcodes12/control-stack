open ControlStack.SC07Liveness

theorem original_signature : ∀ (E : Env) (ops : List Op) (S : ℕ), 0 < E.q → S ≤ total (run E full init ops) → OriginalAt E ops S := by
  intro E ops S hq hS
  exact exfil_needs_windows E hq S ops hS

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro E ops S hq hS
  rfl

theorem witness : Witness := by unfold Witness; decide
