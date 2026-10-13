open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @accepted_path_safety_monotone

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  decide
