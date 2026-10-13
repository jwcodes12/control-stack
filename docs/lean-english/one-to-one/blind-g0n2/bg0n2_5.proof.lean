open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay
theorem claim : Claim := by
  refine ⟨rfl, rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨R, s0, s10, initial_safe 2, runtime_trace, ?_, ?_⟩ <;> decide
