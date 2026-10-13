open ControlStack ControlStack.TrustedBroker ControlStack.Deployment ControlStack.Deployment.TranscriptReplay
theorem claim : Claim := by
  refine ⟨rfl, rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  refine ⟨R, s7, q7, a1, l1, ControlStack.Deployment.TranscriptReplay.now, q8, ?_, rfl, ?_, ?_⟩
  · exact by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals first | rfl | exact ⟨23703, rfl⟩ | exact Or.inl rfl | decide
  · decide
  · exact committed_nonce_unusable R s7 q7 a1 l1 ControlStack.Deployment.TranscriptReplay.now q8 a1 l1 rfl
