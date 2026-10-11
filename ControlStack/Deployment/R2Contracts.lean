import ControlStack.Deployment.Contracts
import ControlStack.Core.CheckedTrace

namespace ControlStack.Deployment
inductive AvoidedPath (d : IR) (start : Nat) : Nat → Prop
  | refl : AvoidedPath d start start
  | step (e : Edge) (member : e ∈ d.edges)
      (broker : e.target ≠ d.broker) (receiver : e.target ≠ d.receiver)
      (prior : AvoidedPath d start e.source) : AvoidedPath d start e.target

theorem path_in_closed (d : IR) (start target : Nat) (set : List Nat)
    (initial : start ∈ set)
    (closed : ∀ e ∈ d.edges, e.source ∈ set →
      e.target ≠ d.broker → e.target ≠ d.receiver → e.target ∈ set)
    (path : AvoidedPath d start target) : target ∈ set := by
  induction path with
  | refl => exact initial
  | step e member broker receiver _ ih => exact closed e member ih broker receiver

theorem accepted_no_avoided_path (d : IR) (h : Accepted d)
    (a : Node) (member : a ∈ d.nodes) (agent : a.agent = true) :
    ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database := by
  obtain ⟨initial, sink, database, closed⟩ := h.bypass a member agent
  exact ⟨fun p => sink (path_in_closed d a.id d.sink _ initial closed p),
    fun p => database (path_in_closed d a.id d.database _ initial closed p)⟩

theorem path_edge_subset (d larger : IR)
    (subset : ∀ e ∈ d.edges, e ∈ larger.edges)
    (broker : d.broker = larger.broker) (receiver : d.receiver = larger.receiver)
    (start target : Nat) (path : AvoidedPath d start target) :
    AvoidedPath larger start target := by
  induction path with
  | refl => exact .refl
  | step e member hb hr _ ih =>
    exact .step e (subset e member) (by simpa only [broker] using hb)
      (by simpa only [receiver] using hr) ih

theorem accepted_path_safety_monotone (d larger : IR)
    (subset : ∀ e ∈ d.edges, e ∈ larger.edges)
    (nodes : d.nodes = larger.nodes)
    (broker : d.broker = larger.broker) (receiver : d.receiver = larger.receiver)
    (sink : d.sink = larger.sink) (database : d.database = larger.database)
    (accepted : Accepted larger) (a : Node) (member : a ∈ d.nodes)
    (agent : a.agent = true) :
    ¬ AvoidedPath d a.id d.sink ∧ ¬ AvoidedPath d a.id d.database := by
  have safe := accepted_no_avoided_path larger accepted a (by simpa only [nodes] using member) agent
  exact ⟨fun p => safe.1 (sink ▸ path_edge_subset d larger subset broker receiver _ _ p),
    fun p => safe.2 (database ▸ path_edge_subset d larger subset broker receiver _ _ p)⟩

def sinkOnly : IR := {clean with edges := [⟨3,4,true,false,true⟩]}
def noBrokerDB : IR := {clean with edges := [⟨3,4,true,false,true⟩,⟨3,5,true,false,true⟩]}
def noReceiverDB : IR := {clean with edges := [⟨3,4,true,false,true⟩,⟨2,5,true,false,true⟩]}
theorem requested_monotonicity_counterexample :
    sinkOnly.nodes = clean.nodes ∧ (∀ e ∈ sinkOnly.edges, e ∈ clean.edges) ∧
    (∃ e ∈ sinkOnly.edges, e.source = sinkOnly.receiver ∧ e.target = sinkOnly.sink ∧ e.write = true) ∧
    Accepted clean ∧ ¬ Accepted sinkOnly := by decide
theorem missing_broker_writer_counterexample :
    (∀ e ∈ noBrokerDB.edges, e ∈ clean.edges) ∧ Accepted clean ∧ ¬ Accepted noBrokerDB := by decide
theorem missing_receiver_writer_counterexample :
    (∀ e ∈ noReceiverDB.edges, e ∈ clean.edges) ∧ Accepted clean ∧ ¬ Accepted noReceiverDB := by decide
end ControlStack.Deployment


namespace ControlStack.Deployment
open ControlStack

theorem broker_step_cap (R : TrustedBroker.Roles) (s t : TrustedBroker.State)
    (step : TrustedBroker.Step R s t) : t.cap = s.cap := by
  cases step <;> rfl

theorem broker_trace_cap (R : TrustedBroker.Roles) (s t : TrustedBroker.State)
    (trace : TrustedBroker.Trace R s t) : t.cap = s.cap := by
  induction trace with
  | nil => rfl
  | cons step _ ih => exact ih.trans (broker_step_cap R _ _ step)

theorem broker_step_release_count (R : TrustedBroker.Roles) (s t : TrustedBroker.State)
    (count : s.consumed.length = s.releases)
    (step : TrustedBroker.Step R s t) : t.consumed.length = t.releases := by
  cases step <;> simp_all [TrustedBroker.committed]

theorem broker_trace_release_count (R : TrustedBroker.Roles) (s t : TrustedBroker.State)
    (count : s.consumed.length = s.releases)
    (trace : TrustedBroker.Trace R s t) : t.consumed.length = t.releases := by
  induction trace with
  | nil => exact count
  | cons step _ ih => exact ih (broker_step_release_count R _ _ count step)

/-- Actual sink records are indexed in admission order, not wall-clock publication
order. This unproved correspondence allows admitted-but-unpublished records.
Caller binding and model transactions are separate from authority extraction. -/
structure BrokerProtocolRefinement (d : IR) (R : TrustedBroker.Roles) (cap : Nat)
    (t : TrustedBroker.State) (sinkNonces : List Nat) : Prop where
  transactions : TrustedBroker.Trace R (TrustedBroker.initial cap) t
  callerBinding : ∀ uid, R.agent uid → ∃ a ∈ d.nodes, a.agent = true ∧ uid = a.uid
  publication : List.Sublist sinkNonces.reverse t.consumed

/-- Conditional authority, joint broker quota, one-use approvals and sink bound.
This theorem uses TrustedBroker, not SC26. Publication may lag admissions; equality
of admissions and actual effects is neither asserted nor needed. -/
theorem deployment_broker_safe (d : IR) (r : Node) (R : TrustedBroker.Roles)
    (cap : Nat) (t : TrustedBroker.State) (actualEdges : List Edge)
    (sinkNonces : List Nat) (h : Accepted d)
    (extraction : ExtractionFaithful d r actualEdges)
    (refinement : BrokerProtocolRefinement d R cap t sinkNonces) :
    (∀ e ∈ actualEdges, e.authority = true → e.target = d.sink → e.source = d.receiver) ∧
    ¬ R.agent r.uid ∧ sinkNonces.Nodup ∧ sinkNonces.length ≤ cap ∧
    (∀ nonce ∈ sinkNonces, ∃ a, t.approvals nonce = some a ∧ a.used = true) := by
  have safe := broker_contract R cap t refinement.transactions
  have coherent := TrustedBroker.trace_coherent R _ _
    (TrustedBroker.initial_coherent cap) refinement.transactions
  have count := broker_trace_release_count R _ _ (by rfl) refinement.transactions
  have capEq := broker_trace_cap R _ _ refinement.transactions
  have unique : sinkNonces.Nodup := by
    have hr := refinement.publication.nodup safe.2.2.1
    simpa using hr
  have bound : sinkNonces.length ≤ cap := by
    have size := refinement.publication.length_le
    simp only [List.length_reverse] at size
    change t.cap = cap at capEq
    calc
      sinkNonces.length ≤ t.consumed.length := size
      _ = t.releases := count
      _ ≤ t.spent := safe.2.1
      _ ≤ t.cap := safe.1
      _ = cap := capEq
  refine ⟨fun e he ha hs => runtime_exclusive d actualEdges h extraction.authority e he ha hs,
    ?_, unique, bound, ?_⟩
  · intro agent
    obtain ⟨a, member, role, uid⟩ := refinement.callerBinding r.uid agent
    exact agent_not_receiver_uid d h r a extraction.receiverNode extraction.receiverID member role uid.symm
  · intro nonce member
    exact (coherent nonce).mp (refinement.publication.subset (by simpa using member))
end ControlStack.Deployment

namespace ControlStack.Deployment
open ControlStack
/-- Finite state identifiers refer to complete instantiated broker states.
Every executable table transition has a kernel-checked TrustedBroker step.
Identifiers avoid inventing decidable equality for arbitrary function states. -/
structure IndexedBrokerTable (R : TrustedBroker.Roles) where
  interpret : Nat → TrustedBroker.State
  step : Nat → Nat → Nat
  checked : ∀ s op, TrustedBroker.Step R (interpret s) (interpret (step s op))

theorem indexed_receipts_sound (R : TrustedBroker.Roles) (table : IndexedBrokerTable R)
    (rs : List (CheckedTrace.Receipt Nat Nat)) (start : Nat)
    (verified : CheckedTrace.verified table.step start rs = true) :
    TrustedBroker.Trace R (table.interpret start)
      (table.interpret (CheckedTrace.recordedEnd start rs)) := by
  induction rs generalizing start with
  | nil => exact .nil _
  | cons r tail ih =>
    have hpair : (r.before = start ∧ r.after = table.step start r.op) ∧
        CheckedTrace.verified table.step r.after tail = true := by
      simpa only [CheckedTrace.verified, Bool.and_eq_true, decide_eq_true_eq] using verified
    have step := table.checked start r.op
    rw [← hpair.1.2] at step
    exact .cons step (ih r.after hpair.2)
end ControlStack.Deployment
#print axioms ControlStack.Deployment.path_in_closed
#print axioms ControlStack.Deployment.accepted_no_avoided_path
#print axioms ControlStack.Deployment.path_edge_subset
#print axioms ControlStack.Deployment.accepted_path_safety_monotone
#print axioms ControlStack.Deployment.requested_monotonicity_counterexample
#print axioms ControlStack.Deployment.missing_broker_writer_counterexample
#print axioms ControlStack.Deployment.missing_receiver_writer_counterexample
#print axioms ControlStack.Deployment.broker_step_cap
#print axioms ControlStack.Deployment.broker_trace_cap
#print axioms ControlStack.Deployment.broker_step_release_count
#print axioms ControlStack.Deployment.broker_trace_release_count
#print axioms ControlStack.Deployment.deployment_broker_safe
#print axioms ControlStack.Deployment.indexed_receipts_sound
