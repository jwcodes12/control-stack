open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro t
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : TrustedBroker.Roles) (s t : TrustedBroker.State) (safe : TrustedBroker.Safe s) (step : TrustedBroker.Step R s t) : Orig t := TrustedBroker.transaction_preserves R s t safe step
