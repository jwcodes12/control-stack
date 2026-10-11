open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R table rs start
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : TrustedBroker.Roles) (table : IndexedBrokerTable R) (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat) (verified : CheckedTrace.verified table.step start rs = true) : Orig R table rs start := indexed_receipts_sound R table rs start verified
