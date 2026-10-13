open ControlStack.SC07Liveness

theorem original_signature : ∀ (E : Env) (s : St) (d : ℕ) (chunks : List ℕ), s.halted = false → d ∈ E.allow → s.used + chunks.sum ≤ E.q → OriginalAt E s d chunks := by
  intro E s d chunks hh hd hq
  exact upload_completes E s d chunks hh hd hq

theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro E s d chunks hh hd hq
  rfl

theorem witness : Witness := by unfold Witness; decide
