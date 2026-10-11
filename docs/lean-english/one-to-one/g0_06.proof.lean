open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro d r a approvers admins k tx
 rfl
theorem witness : Witness := clean_accepted
