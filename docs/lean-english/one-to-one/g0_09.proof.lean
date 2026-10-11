open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R cap ops
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : SC26.Roles) (cap : Nat) (ops : List {o : SC26.Op // SC26.legal R o}) : Orig R cap ops := gate_contract R cap ops
