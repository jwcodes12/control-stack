open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R cap ops
 rfl
theorem witness : Witness := clean_accepted
