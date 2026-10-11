open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro t
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : TrustedBroker.Roles) (s t : TrustedBroker.State) (coherent : TrustedBroker.Coherent s) (step : TrustedBroker.Step R s t) : Orig t := TrustedBroker.transaction_coherent R s t coherent step
