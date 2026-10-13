open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay
theorem claim : Claim := by
  refine ⟨rfl, rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨R, table, 0, receipts, ?_, transcript_checked, ?_⟩
  · decide
  · decide
