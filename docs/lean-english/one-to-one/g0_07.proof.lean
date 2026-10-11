open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R cap ops
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : SC26.Roles) (cap : Nat) (ops : List SC26.Op) (h : ∀ o ∈ ops, SC26.legal R o) : Orig R cap ops := protocol_safe R cap ops h
