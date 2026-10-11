namespace PL_provenance
open ControlStack ControlStack.Deployment ControlStack.TrustedBroker
def ReviewProvenance (R : Roles) (s : State) : Prop :=
  ∀ digest reviewer, s.reviews digest = some reviewer →
    R.reviewer reviewer ∧ s.artifacts digest = true

/-- State-level ownership and review facts for each retained approval.
No release digest/destination log exists; no per-release matching assertion is made. -/
def ApprovalProvenance (R : Roles) (s : State) : Prop :=
  ∀ nonce a, s.approvals nonce = some a →
    R.approver a.signer ∧ R.agent a.agent ∧ s.artifacts a.digest = true ∧
    (∃ reviewer, s.reviews a.digest = some reviewer ∧ R.reviewer reviewer) ∧
    (∃ l, s.leases a.lease = some l ∧ l.agent = a.agent)

def Claim : Prop := ∀ (d : IR) (R : Roles) (cap : Nat) (t : State) (sinkNonces : List Nat), BrokerProtocolRefinement d R cap t sinkNonces → ∀ nonce ∈ sinkNonces, ∃ a, t.approvals nonce = some a ∧ a.used = true ∧ R.approver a.signer ∧ R.agent a.agent ∧ t.artifacts a.digest = true ∧ (∃ reviewer, t.reviews a.digest = some reviewer ∧ R.reviewer reviewer) ∧ (∃ l, t.leases a.lease = some l ∧ l.agent = a.agent)
def Witness : Prop := Trace Deployment.Witnesses.R (initial 1) Deployment.Witnesses.s5 ∧ Deployment.Witnesses.s5.spent = 1
end PL_provenance
