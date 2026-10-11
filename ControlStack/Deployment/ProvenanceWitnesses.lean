import ControlStack.Deployment.Provenance
import ControlStack.Deployment.Witnesses

/-!
Positive and negative *model* witnesses. No live container or artifact bytes
are used. The negative is a state that cannot arise through the guarded Step
trace, highlighting the premise that model transitions are faithfully enforced.
-/

namespace ControlStack.Deployment.ProvenanceWitnesses
open ControlStack
open ControlStack.Deployment
open ControlStack.Deployment.Provenance

/-- A completed, guarded model trace carries review/approval/lease provenance. -/
theorem approved_publication_provenance :
    ∀ nonce ∈ ([7] : List Nat), ∃ a,
      Witnesses.s5.approvals nonce = some a ∧ a.used = true ∧
      Witnesses.R.approver a.signer ∧ Witnesses.R.agent a.agent ∧
      Witnesses.s5.artifacts a.digest = true ∧
      (∃ reviewer, Witnesses.s5.reviews a.digest = some reviewer ∧
        Witnesses.R.reviewer reviewer) ∧
      (∃ l, Witnesses.s5.leases a.lease = some l ∧ l.agent = a.agent) :=
  deployment_broker_provenance clean Witnesses.R 1 Witnesses.s5 [7] Witnesses.refined

/-- Explicitly violating retained review state breaks approval provenance. -/
def unreviewedState : TrustedBroker.State :=
  { Witnesses.s4 with reviews := fun _ => none }

theorem unreviewed_approval_refutes :
    ¬ ApprovalProvenance Witnesses.R unreviewedState := by
  intro h
  have present : unreviewedState.approvals 7 = some Witnesses.approval := by decide
  obtain ⟨_, _, _, ⟨reviewer, lookup, _⟩, _⟩ :=
    h 7 Witnesses.approval present
  simp [unreviewedState] at lookup

end ControlStack.Deployment.ProvenanceWitnesses

#print axioms ControlStack.Deployment.ProvenanceWitnesses.approved_publication_provenance
#print axioms ControlStack.Deployment.ProvenanceWitnesses.unreviewed_approval_refutes
