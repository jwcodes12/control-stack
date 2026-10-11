open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R cap ops
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) : Orig R cap ops := one_use R cap ops
