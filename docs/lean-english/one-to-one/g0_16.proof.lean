open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro h
 have bad := h clean Witnesses.receiverNode Witnesses.R 1 Witnesses.s5 clean.edges [7] clean_accepted Witnesses.extracted Witnesses.refined
 change (1 : Nat) < 1 at bad
 omega
 theorem witness : Witness := clean_accepted
