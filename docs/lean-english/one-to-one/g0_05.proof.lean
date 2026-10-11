open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro h
 have bad := h clean Witnesses.receiverNode clean_accepted (by decide) rfl Witnesses.receiverNode (by decide)
 exact bad rfl
 theorem witness : Witness := clean_accepted
