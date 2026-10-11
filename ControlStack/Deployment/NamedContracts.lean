import ControlStack.Deployment.Contracts

/-!
Named *views* of the current broker and deployment conditions. These do not
change the legacy predicates or their runtime meaning. The iff lemmas ensure
that proof refactors cannot silently drop any of the original guards.
-/

namespace ControlStack.TrustedBroker

structure AllowedFields (roles : Roles) (s : State) (now : Nat) (r : Request) (a : Approval) (l : Lease) : Prop where
  not_halted : s.halted = false
  caller_is_agent : roles.agent r.uid
  stored_approval : s.approvals r.nonce = some a
  approval_unused : a.used = false
  same_digest : a.digest = r.digest
  same_destination : a.destination = r.destination
  same_agent : a.agent = r.uid
  same_lease : a.lease = r.lease
  signer_is_approver : roles.approver a.signer
  approval_unexpired : now < a.expires
  stored_lease : s.leases r.lease = some l
  lease_owned : l.agent = r.uid
  lease_active : l.revoked = false
  lease_unexpired : now < l.expires
  positive_cost : 0 < r.cost
  within_lease_budget : l.used + r.cost ≤ l.budget
  within_joint_budget : s.spent + r.cost ≤ s.cap
  artifact_staged : s.artifacts r.digest = true
  artifact_intact : s.intact r.digest = true
  reviewed_digest : ∃ reviewer, s.reviews r.digest = some reviewer
  nonce_not_consumed : r.nonce ∉ s.consumed

/-- Bidirectional specification equivalence: retains every historical guard. -/
theorem allowed_iff_allowedfields (roles : Roles) (s : State) (now : Nat) (r : Request) (a : Approval) (l : Lease) :
    Allowed roles s now r a l ↔ AllowedFields roles s now r a l := by
  constructor
  · intro h
    rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20⟩
  · intro h
    exact ⟨h.not_halted, h.caller_is_agent, h.stored_approval, h.approval_unused, h.same_digest, h.same_destination, h.same_agent, h.same_lease, h.signer_is_approver, h.approval_unexpired, h.stored_lease, h.lease_owned, h.lease_active, h.lease_unexpired, h.positive_cost, h.within_lease_budget, h.within_joint_budget, h.artifact_staged, h.artifact_intact, h.reviewed_digest, h.nonce_not_consumed⟩

end ControlStack.TrustedBroker

namespace ControlStack.Deployment

structure BaseAcceptedFields (d : IR) : Prop where
  edges_known : ∀ e ∈ d.edges, e.unknown = false
  sink_authority_only_receiver : ∀ e ∈ d.edges, e.authority = true → e.target = d.sink → e.source = d.receiver
  database_authority_custody : ∀ e ∈ d.edges, e.authority = true → e.target = d.database → e.source = d.receiver ∨ e.source = d.broker
  no_privileged_or_host_network : ∀ n ∈ d.nodes, n.privileged = false ∧ n.hostNetwork = false
  agents_uid_distinct_from_receiver : ∀ r ∈ d.nodes, r.id = d.receiver → ∀ a ∈ d.nodes, a.agent = true → a.uid ≠ r.uid
  receiver_can_write_sink : ∃ e ∈ d.edges, e.source = d.receiver ∧ e.target = d.sink ∧ e.authority = true
  positive_uids : ∀ n ∈ d.nodes, 0 < n.uid

/-- Bidirectional specification equivalence: retains every historical guard. -/
theorem baseAccepted_iff_baseacceptedfields (d : IR) :
    BaseAccepted d ↔ BaseAcceptedFields d := by
  constructor
  · intro h
    rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
    exact ⟨h0, h1, h2, h3, h4, h5, h6⟩
  · intro h
    exact ⟨h.edges_known, h.sink_authority_only_receiver, h.database_authority_custody, h.no_privileged_or_host_network, h.agents_uid_distinct_from_receiver, h.receiver_can_write_sink, h.positive_uids⟩

structure WritersCheckedFields (d : IR) : Prop where
  sink_edges_receiver_writes : ∀ e ∈ d.edges, e.target = d.sink → e.source = d.receiver ∧ e.write = true
  database_edges_custody : ∀ e ∈ d.edges, e.target = d.database → e.source = d.broker ∨ e.source = d.receiver
  unique_sink_writer : (d.edges.filter (fun e => e.target == d.sink && e.write)).map Edge.source = [d.receiver]
  two_database_writers : (d.edges.filter (fun e => e.target == d.database && e.write)).length = 2
  broker_database_writer_exists : ∃ e ∈ d.edges, e.target = d.database ∧ e.write = true ∧ e.source = d.broker
  receiver_database_writer_exists : ∃ e ∈ d.edges, e.target = d.database ∧ e.write = true ∧ e.source = d.receiver

/-- Bidirectional specification equivalence: retains every historical guard. -/
theorem writersChecked_iff_writerscheckedfields (d : IR) :
    WritersChecked d ↔ WritersCheckedFields d := by
  constructor
  · intro h
    rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
    exact ⟨h0, h1, h2, h3, h4, h5⟩
  · intro h
    exact ⟨h.sink_edges_receiver_writes, h.database_edges_custody, h.unique_sink_writer, h.two_database_writers, h.broker_database_writer_exists, h.receiver_database_writer_exists⟩

structure AcceptedFields (d : IR) : Prop where
  basic : BaseAcceptedFields d
  roles : RoleChecked d
  identities : IdentityChecked d
  runtime : ∀ n ∈ d.nodes, n.runtimeMatch = true
  writers : WritersCheckedFields d
  bypass : NoBypass d

/-- Existing Accepted already has six named fields; expand its two nested checks. -/
theorem accepted_iff_named (d : IR) : Accepted d ↔ AcceptedFields d := by
  constructor
  · intro h
    exact ⟨(baseAccepted_iff_baseacceptedfields d).mp h.basic,
      h.roles, h.identities, h.runtime,
      (writersChecked_iff_writerscheckedfields d).mp h.writers, h.bypass⟩
  · intro h
    exact ⟨(baseAccepted_iff_baseacceptedfields d).mpr h.basic,
      h.roles, h.identities, h.runtime,
      (writersChecked_iff_writerscheckedfields d).mpr h.writers, h.bypass⟩

end ControlStack.Deployment

#print axioms ControlStack.TrustedBroker.allowed_iff_allowedfields
#print axioms ControlStack.Deployment.baseAccepted_iff_baseacceptedfields
#print axioms ControlStack.Deployment.writersChecked_iff_writerscheckedfields
#print axioms ControlStack.Deployment.accepted_iff_named
