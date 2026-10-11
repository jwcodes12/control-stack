open ControlStack ControlStack.Deployment
theorem claim : Claim := by
 intro R s r a l now q b m
 rfl
theorem witness : Witness := clean_accepted

theorem original_contract (R : TrustedBroker.Roles) (s : TrustedBroker.State) (r : TrustedBroker.Request) (a : TrustedBroker.Approval) (l : TrustedBroker.Lease) (now : Nat) (q : TrustedBroker.Request) (b : TrustedBroker.Approval) (m : TrustedBroker.Lease) (same : q.nonce = r.nonce) : Orig R s r a l now q b m := TrustedBroker.committed_nonce_unusable R s r a l now q b m same
