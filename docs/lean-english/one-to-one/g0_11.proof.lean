open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro d R cap ops actual sinkEffects
 rfl
theorem witness : Witness := clean_accepted
