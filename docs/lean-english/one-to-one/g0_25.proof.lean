open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro now a l
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (now : Nat) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) : Orig now a l := TranscriptReplay.replay_was_not_allowed now a l
