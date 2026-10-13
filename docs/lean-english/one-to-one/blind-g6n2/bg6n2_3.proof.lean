open ControlStack.SC26
theorem original_signature : OrigEnvelope := by
  intro R cap ops
  exact sc26_once R cap ops
theorem claim : Claim := by
  refine ⟨Iff.rfl, ?_⟩
  intro s
  exact Iff.rfl
theorem witness : Witness := by
  unfold Witness
  decide
