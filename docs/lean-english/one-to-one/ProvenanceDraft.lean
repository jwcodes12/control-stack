import ControlStack.Deployment.R2Contracts
namespace ControlStack.Deployment.OneToOne
open ControlStack
open TrustedBroker

/-- Present review entries are authentic role assertions about existing artifacts.
This does not assert semantic harmlessness or retain the original reviewer after overwrite. -/
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

theorem initial_review (R : Roles) (cap : Nat) : ReviewProvenance R (initial cap) := by
  simp [ReviewProvenance, initial]
theorem initial_approval (R : Roles) (cap : Nat) : ApprovalProvenance R (initial cap) := by
  simp [ApprovalProvenance, initial]

theorem review_step (R : Roles) (s t : State)
    (h : ReviewProvenance R s) (step : Step R s t) : ReviewProvenance R t := by
  cases step with
  | stage uid digest live role =>
    intro key reviewer lookup
    obtain ⟨role, artifact⟩ := h key reviewer lookup
    exact ⟨role,by simp [put,artifact]⟩
  | review uid digest live role existsArtifact =>
    intro key reviewer lookup
    by_cases eq : key = digest
    · subst key
      simp [put] at lookup
      subst reviewer
      exact ⟨role,existsArtifact⟩
    · exact h key reviewer (by simpa [put,eq] using lookup)
  | release now r a l allowed => exact h
  | deny => exact h
  | issue => exact h
  | approve => exact h
  | revoke => exact h
  | halt => exact h

theorem approval_step (R : Roles) (s t : State)
    (reviews : ReviewProvenance R s) (h : ApprovalProvenance R s)
    (step : Step R s t) : ApprovalProvenance R t := by
  cases step with
  | deny => exact h
  | halt => exact h
  | stage uid digest live role =>
    intro nonce a lookup
    obtain ⟨signer,agent,artifact,review,lease⟩ := h nonce a lookup
    exact ⟨signer,agent,by simp [put,artifact],review,lease⟩
  | review uid digest live role existsArtifact =>
    intro nonce a lookup
    obtain ⟨signer,agent,artifact,oldReview,lease⟩ := h nonce a lookup
    refine ⟨signer,agent,artifact,?_,lease⟩
    by_cases eq : a.digest = digest
    · exact ⟨uid,by simp [put,eq],role⟩
    · obtain ⟨reviewer,lookup,role⟩ := oldReview
      exact ⟨reviewer,by simpa [put,eq] using lookup,role⟩
  | issue uid key l now live role agent fresh budget unused active future =>
    intro nonce a lookup
    obtain ⟨signer,agent,artifact,review,v,hv,owner⟩ := h nonce a lookup
    have ne : a.lease ≠ key := by intro eq; rw [eq,fresh] at hv; cases hv
    exact ⟨signer,agent,artifact,review,v,by simpa [put,ne] using hv,owner⟩
  | revoke uid key l live role lease =>
    intro nonce a lookup
    obtain ⟨signer,agent,artifact,review,v,hv,owner⟩ := h nonce a lookup
    refine ⟨signer,agent,artifact,review,?_⟩
    by_cases eq : a.lease = key
    · rw [eq,lease] at hv
      have same : l = v := Option.some.inj hv
      subst v
      exact ⟨{l with revoked := true},by simp [put,eq],owner⟩
    · exact ⟨v,by simpa [put,eq] using hv,owner⟩
  | approve uid nonce a l now reviewer live role signer agent fresh unused review reviewRole distinct lease owner active leaseFuture future =>
    intro key b lookup
    by_cases eq : key = nonce
    · subst key
      simp [put] at lookup
      subst b
      exact ⟨signer.symm ▸ role,agent,(reviews a.digest reviewer review).2,⟨reviewer,review,reviewRole⟩,⟨l,lease,owner⟩⟩
    · exact h key b (by simpa [put,eq] using lookup)
  | release now r a l allowed =>
    intro key b lookup
    have old : ∃ v, s.approvals key = some v ∧ b = {v with used := true} ∨ s.approvals key = some b := by
      by_cases eq : key = r.nonce
      · subst key
        simp [committed,put] at lookup
        exact ⟨a,Or.inl ⟨allowed.2.2.1,lookup.symm⟩⟩
      · exact ⟨b,Or.inr (by simpa [committed,put,eq] using lookup)⟩
    obtain ⟨v,hv⟩ := old
    have data : R.approver b.signer ∧ R.agent b.agent ∧ s.artifacts b.digest = true ∧
        (∃ reviewer, s.reviews b.digest = some reviewer ∧ R.reviewer reviewer) ∧
        (∃ v, s.leases b.lease = some v ∧ v.agent = b.agent) := by
      rcases hv with ⟨hv,rfl⟩ | hv
      · exact h key v hv
      · exact h key b hv
    obtain ⟨signer,agent,artifact,review,v,hv,owner⟩ := data
    refine ⟨signer,agent,artifact,review,?_⟩
    by_cases eq : b.lease = r.lease
    · rw [eq,allowed.2.2.2.2.2.2.2.2.2.2.1] at hv
      have same : l = v := Option.some.inj hv
      subst v
      exact ⟨{l with used := l.used + r.cost},by simp [committed,put,eq],owner⟩
    · exact ⟨v,by simpa [committed,put,eq] using hv,owner⟩

theorem trace_provenance (R : Roles) (s t : State)
    (review : ReviewProvenance R s) (approval : ApprovalProvenance R s)
    (trace : Trace R s t) : ReviewProvenance R t ∧ ApprovalProvenance R t := by
  induction trace with
  | nil => exact ⟨review,approval⟩
  | cons step _ ih => exact ih (review_step R _ _ review step) (approval_step R _ _ review approval step)

theorem deployment_broker_provenance (d : IR) (R : Roles) (cap : Nat)
    (t : State) (sinkNonces : List Nat)
    (refinement : BrokerProtocolRefinement d R cap t sinkNonces) :
    ∀ nonce ∈ sinkNonces, ∃ a, t.approvals nonce = some a ∧ a.used = true ∧
      R.approver a.signer ∧ R.agent a.agent ∧ t.artifacts a.digest = true ∧
      (∃ reviewer, t.reviews a.digest = some reviewer ∧ R.reviewer reviewer) ∧
      (∃ l, t.leases a.lease = some l ∧ l.agent = a.agent) := by
  have hp := (trace_provenance R _ _ (initial_review R cap) (initial_approval R cap) refinement.transactions).2
  have coherent := trace_coherent R _ _ (initial_coherent cap) refinement.transactions
  intro nonce member
  obtain ⟨a,lookup,used⟩ := (coherent nonce).mp (refinement.publication.subset (by simpa using member))
  exact ⟨a,lookup,used,hp nonce a lookup⟩
end ControlStack.Deployment.OneToOne
#print axioms ControlStack.Deployment.OneToOne.deployment_broker_provenance
