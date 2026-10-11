open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro t
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : TrustedBroker.Roles) (s t : TrustedBroker.State) (safe : TrustedBroker.Safe s) (trace : TrustedBroker.Trace R s t) : Orig t := TrustedBroker.trace_preserves R s t safe trace
