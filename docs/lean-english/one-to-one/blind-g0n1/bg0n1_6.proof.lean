open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @broker_contract

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  exact ⟨ControlStack.Deployment.Witnesses.useful_broker_trace, ControlStack.Deployment.Witnesses.useful_broker_state⟩
