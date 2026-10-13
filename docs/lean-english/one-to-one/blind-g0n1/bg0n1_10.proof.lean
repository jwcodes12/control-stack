open ControlStack ControlStack.Deployment

theorem original_signature : Orig := @requested_monotonicity_counterexample

theorem claim : Claim := by
  refine ⟨Iff.rfl, Iff.rfl, ?_⟩
  intros
  exact Iff.rfl

theorem witness : Witness := by
  unfold Witness
  decide
