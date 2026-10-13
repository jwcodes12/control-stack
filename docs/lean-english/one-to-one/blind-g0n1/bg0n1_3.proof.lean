open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @protocol_safe

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  exact ⟨ControlStack.Deployment.Witnesses.model_ops_legal, by decide⟩
