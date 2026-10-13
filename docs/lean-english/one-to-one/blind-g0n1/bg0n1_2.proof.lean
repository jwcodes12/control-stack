open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @agent_call_legal

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  exact ⟨clean_accepted, by decide, rfl, by decide, rfl, ControlStack.Deployment.Witnesses.legal_call_positive⟩
