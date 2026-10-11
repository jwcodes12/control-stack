open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro t
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : TrustedBroker.Roles) (cap : Nat) (t : TrustedBroker.State) (trace : TrustedBroker.Trace R (TrustedBroker.initial cap) t) : Orig t := broker_contract R cap t trace
