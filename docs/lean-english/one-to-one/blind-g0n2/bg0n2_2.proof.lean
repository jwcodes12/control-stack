open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay
theorem claim : Claim := by
  refine ⟨rfl, rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨R, s7, s8, ?_, tx7, ?_⟩
  · exact trace_preserves R s0 s7 (initial_safe 2) (.cons tx0 (.cons tx1 (.cons tx2 (.cons tx3 (.cons tx4 (.cons tx5 (.cons tx6 (.nil s7))))))))
  · decide
