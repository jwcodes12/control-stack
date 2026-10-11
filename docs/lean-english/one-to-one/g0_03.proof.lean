open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro h
 have bad := h clean ⟨2,5,true,false,true⟩ clean_accepted (by decide) rfl rfl
 change (2 : Nat) = 3 at bad
 omega
 theorem witness : Witness := clean_accepted
