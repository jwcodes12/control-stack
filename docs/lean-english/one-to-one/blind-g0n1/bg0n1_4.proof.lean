open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @one_use

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  decide
