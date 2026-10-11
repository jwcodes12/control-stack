open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro larger start target
 rfl
theorem witness : Witness := clean_accepted
