import ControlStack.Deployment.ProvenanceWitnesses
import ControlStack.Deployment.Witnesses

/-!
Composes accepted IR writer exclusivity, joint broker budget/nonce guarantees,
and retained-state publication provenance under the SAME broker refinement.
The model's publication sublist and authority extraction are assumed; neither
is an observed live-runtime correspondence or immutable per-release evidence.
-/
namespace ControlStack.Deployment.ComposedAssurance
open ControlStack
open ControlStack.Deployment

/-- The broker-branch combined assurance, including *all* sink edges captured
by the finite IR (not merely edges marked authority). -/
theorem accepted_joint_claim (d : IR) (r : Node) (R : TrustedBroker.Roles)
    (cap : Nat) (t : TrustedBroker.State) (actualEdges : List Edge)
    (sinkNonces : List Nat) (h : Accepted d)
    (extraction : ExtractionFaithful d r actualEdges)
    (refinement : BrokerProtocolRefinement d R cap t sinkNonces) :
    (∀ e ∈ actualEdges, e.target = d.sink →
      e.source = d.receiver ∧ e.write = true) ∧
    ¬ R.agent r.uid ∧
    sinkNonces.Nodup ∧ sinkNonces.length ≤ cap ∧
    (∀ nonce ∈ sinkNonces, ∃ a, t.approvals nonce = some a ∧ a.used = true ∧
      R.approver a.signer ∧ R.agent a.agent ∧ t.artifacts a.digest = true ∧
      (∃ reviewer, t.reviews a.digest = some reviewer ∧ R.reviewer reviewer) ∧
      (∃ l, t.leases a.lease = some l ∧ l.agent = a.agent)) := by
  obtain ⟨_, noCallerCollision, unique, bounded, _⟩ :=
    deployment_broker_safe d r R cap t actualEdges sinkNonces h extraction refinement
  refine ⟨?_, noCallerCollision, unique, bounded, ?_⟩
  · intro e member sink
    exact h.writers.1 e (extraction.authority.captured e member) sink
  · exact Provenance.deployment_broker_provenance d R cap t sinkNonces refinement

/-- One nonempty model deployment witnesses Accepted, extraction and the
broker refinement simultaneously, not merely individually. -/
theorem all_hypotheses_satisfiable :
    Accepted clean ∧
    ExtractionFaithful clean Witnesses.receiverNode clean.edges ∧
    BrokerProtocolRefinement clean Witnesses.R 1 Witnesses.s5 [7] ∧
    ([7] : List Nat) ≠ [] := by
  exact ⟨clean_accepted, Witnesses.extracted, Witnesses.refined, by decide⟩

theorem witness_combined_nonce_and_provenance :
    ([7] : List Nat).Nodup ∧ ([7] : List Nat).length ≤ 1 ∧
    (∀ nonce ∈ ([7] : List Nat), ∃ a,
      Witnesses.s5.approvals nonce = some a ∧ a.used = true ∧
      Witnesses.R.approver a.signer ∧ Witnesses.R.agent a.agent ∧
      Witnesses.s5.artifacts a.digest = true ∧
      (∃ reviewer, Witnesses.s5.reviews a.digest = some reviewer ∧
        Witnesses.R.reviewer reviewer) ∧
      (∃ l, Witnesses.s5.leases a.lease = some l ∧ l.agent = a.agent)) := by
  have h := accepted_joint_claim clean Witnesses.receiverNode Witnesses.R 1
    Witnesses.s5 clean.edges [7] clean_accepted Witnesses.extracted Witnesses.refined
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

end ControlStack.Deployment.ComposedAssurance

#print axioms ControlStack.Deployment.ComposedAssurance.accepted_joint_claim
#print axioms ControlStack.Deployment.ComposedAssurance.all_hypotheses_satisfiable
#print axioms ControlStack.Deployment.ComposedAssurance.witness_combined_nonce_and_provenance
